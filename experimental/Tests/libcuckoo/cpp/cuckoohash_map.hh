/** \file */

#ifndef _CUCKOOHASH_MAP_HH
#define _CUCKOOHASH_MAP_HH

struct VALUE {
};

struct KEY {
};

#include <algorithm>
#include <array>
#include <atomic>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <iterator>
#include <limits>
#include <list>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <thread>
#include <type_traits>
#include <utility>
#include <vector>

#include "cuckoohash_config.hh"
#include "cuckoohash_util.hh"
#include "libcuckoo_bucket_container.hh"

// A constexpr version of pow that we can use for various compile-time
// constants and checks.
static constexpr std::size_t const_pow(std::size_t a, std::size_t b) {
  return (b == 0) ? 1 : a * const_pow(a, b - 1);
}

// Type of the partial key
typedef uint8_t partial_t;

// The type of the buckets container
typedef libcuckoo_bucket_container buckets_t;

typedef std::hash<KEY> Hash;
typedef std::equal_to<KEY> KeyEqual;
typedef std::ptrdiff_t difference_type;
typedef Hash hasher;
typedef KeyEqual key_equal;

// Counter type
typedef int64_t counter_type;

// A fast, lightweight spinlock
LIBCUCKOO_SQUELCH_PADDING_WARNING
class LIBCUCKOO_ALIGNAS(64) spinlock {
public:
  spinlock() : elem_counter_(0) { lock_.clear(); }

  spinlock(const spinlock &other) : elem_counter_(other.elem_counter()) {
    lock_.clear();
  }

  spinlock &operator=(const spinlock &other) {
    elem_counter() = other.elem_counter();
    return *this;
  }

  void lock() noexcept {
    while (lock_.test_and_set(std::memory_order_acq_rel))
      ;
  }

  void unlock() noexcept { lock_.clear(std::memory_order_release); }

  bool try_lock() noexcept {
    return !lock_.test_and_set(std::memory_order_acq_rel);
  }

  counter_type &elem_counter() noexcept { return elem_counter_; }

  counter_type elem_counter() const noexcept { return elem_counter_; }

private:
  std::atomic_flag lock_;
  counter_type elem_counter_;
};

typedef std::vector<spinlock> locks_t;

struct all_locks_list_node {
  all_locks_list_node(size_t lock_count) : elt(lock_count), next(nullptr) { }

  locks_t elt;
  all_locks_list_node *next;
};

class all_locks_t {
public:
  all_locks_t(size_t lock_count) {
    tail_ = new all_locks_list_node(lock_count);
    head_ = tail_;
  }

  void append(all_locks_list_node *new_tail) {
    tail_->next = new_tail;
    tail_ = new_tail;
  }

  all_locks_list_node *get_tail() {
    return tail_;
  }

private:
  all_locks_list_node *head_;
  all_locks_list_node *tail_;
};

// Classes for managing locked buckets. By storing and moving around sets of
// locked buckets in these classes, we can ensure that they are unlocked
// properly.

class LockManager {
public:
  LockManager() : lock(nullptr) { }
  LockManager(spinlock *i_lock) : lock(i_lock) { }

  LockManager(const LockManager& other) : lock(nullptr) {
    std::swap(lock, other.lock);
  }

  LockManager& operator=(const LockManager& other) {
    std::swap(lock, other.lock);
    return *this;
  }
  
  ~LockManager() {
    if (lock != nullptr) {
      lock->unlock();
    }
  }

  void reset() {
    if (lock != nullptr) {
      lock->unlock();
      lock = nullptr;
    }
  }

  void swap(const LockManager& other) {
    std::swap(lock, other.lock);
  }

private:
  mutable spinlock *lock;
};

static constexpr size_type kMaxNumLocks = 1UL << 16;

// lock_ind converts an index into buckets to an index into locks.
static inline size_type lock_ind(const size_type bucket_ind) {
  return bucket_ind & (kMaxNumLocks - 1);
}

class TwoBuckets {
public:
  TwoBuckets() {}
  TwoBuckets(locks_t &locks, size_type i1_, size_type i2_)
      : i1(i1_), i2(i2_), first_manager_(&locks[lock_ind(i1)]),
        second_manager_((lock_ind(i1) != lock_ind(i2)) ? &locks[lock_ind(i2)]
                                                       : nullptr) {}
  TwoBuckets(const TwoBuckets& other)
    : i1(other.i1), i2(other.i2) {
    first_manager_.swap(other.first_manager_);
    second_manager_.swap(other.second_manager_);
  }

  TwoBuckets& operator=(const TwoBuckets& other) {
    i1 = other.i1;
    i2 = other.i2;
    first_manager_.swap(other.first_manager_);
    second_manager_.swap(other.second_manager_);
    return *this;
  }

  void unlock() {
    first_manager_.reset();
    second_manager_.reset();
  }

  size_type i1, i2;

private:
  LockManager first_manager_, second_manager_;
};

// The maximum number of items in a cuckoo BFS path. It determines the
// maximum number of slots we search when cuckooing.
static constexpr uint8_t MAX_BFS_PATH_LEN = 5;

// b_slot holds the information for a BFS path through the table.
struct b_slot {
  // The bucket of the last item in the path.
  size_type bucket;
  // a compressed representation of the slots for each of the buckets in
  // the path. pathcode is sort of like a base-slot_per_bucket number, and
  // we need to hold at most MAX_BFS_PATH_LEN slots. Thus we need the
  // maximum pathcode to be at least SLOT_PER_BUCKET^(MAX_BFS_PATH_LEN).
  uint16_t pathcode;
  static_assert(const_pow(SLOT_PER_BUCKET, MAX_BFS_PATH_LEN) <
                    std::numeric_limits<decltype(pathcode)>::max(),
                "pathcode may not be large enough to encode a cuckoo "
                "path");
  // The 0-indexed position in the cuckoo path this slot occupies. It must
  // be less than MAX_BFS_PATH_LEN, and also able to hold negative values.
  int8_t depth;
  static_assert(MAX_BFS_PATH_LEN - 1 <=
                    std::numeric_limits<decltype(depth)>::max(),
                "The depth type must able to hold a value of"
                " MAX_BFS_PATH_LEN - 1");
  static_assert(-1 >= std::numeric_limits<decltype(depth)>::min(),
                "The depth type must be able to hold a value of -1");
  b_slot() {}
  b_slot(const size_type b, const uint16_t p, const decltype(depth) d)
      : bucket(b), pathcode(p), depth(d) {
    assert(d < MAX_BFS_PATH_LEN);
  }
};

// b_queue is the queue used to store b_slots for BFS cuckoo hashing.
class b_queue {
public:
  b_queue() noexcept : first_(0), last_(0) {}

  void enqueue(b_slot x) {
    assert(!full());
    slots_[last_++] = x;
  }

  b_slot dequeue() {
    assert(!empty());
    assert(first_ < last_);
    b_slot &x = slots_[first_++];
    return x;
  }

  bool empty() const { return first_ == last_; }

  bool full() const { return last_ == MAX_CUCKOO_COUNT; }

private:
  // The size of the BFS queue. It holds just enough elements to fulfill a
  // MAX_BFS_PATH_LEN search for two starting buckets, with no circular
  // wrapping-around. For one bucket, this is the geometric sum
  // sum_{k=0}^{MAX_BFS_PATH_LEN-1} SLOT_PER_BUCKET^k
  // = (1 - SLOT_PER_BUCKET^MAX_BFS_PATH_LEN) / (1 - SLOT_PER_BUCKET)
  //
  // Note that if SLOT_PER_BUCKET == 1, then this simply equals
  // MAX_BFS_PATH_LEN.
  static_assert(SLOT_PER_BUCKET > 0,
                "SLOT_PER_BUCKET must be greater than 0.");
  static constexpr size_type MAX_CUCKOO_COUNT =
      2 * ((SLOT_PER_BUCKET == 1)
           ? MAX_BFS_PATH_LEN
           : (const_pow(SLOT_PER_BUCKET, MAX_BFS_PATH_LEN) - 1) /
             (SLOT_PER_BUCKET - 1));
  // An array of b_slots. Since we allocate just enough space to complete a
  // full search, we should never exceed the end of the array.
  b_slot slots_[MAX_CUCKOO_COUNT];
  // The index of the head of the queue in the array
  size_type first_;
  // One past the index of the last_ item of the queue in the array.
  size_type last_;
};

// Contains a hash and partial for a given key. The partial key is used for
// partial-key cuckoohashing, and for finding the alternate bucket of that a
// key hashes to.
struct hash_value {
  size_type hash;
  partial_t partial;
};

class AllLocksManager {
public:
  AllLocksManager(all_locks_list_node *i_first_locked)
    : first_locked(i_first_locked), active(true) {
  }

  AllLocksManager(const AllLocksManager& other)
    : first_locked(other.first_locked), active(true) {
    other.active = false;
  }

  AllLocksManager& operator=(const AllLocksManager& other) = delete;

  ~AllLocksManager() {
    if (active) {
      for (all_locks_list_node *it = first_locked; it != nullptr; it = it->next) {
        locks_t &locks = it->elt;
        for (spinlock &lock : locks) {
          lock.unlock();
        }
      }
    }
  }
  
private:
  mutable bool active;
  all_locks_list_node *first_locked;
};

// Status codes for internal functions

enum cuckoo_status {
  ok,
  failure,
  failure_key_not_found,
  failure_key_duplicated,
  failure_table_full,
  failure_under_expansion,
};

// A composite type for functions that need to return a table position, and
// a status code.
struct table_position {
  size_type index;
  size_type slot;
  cuckoo_status status;
};

// CuckooRecord holds one position in a cuckoo path. Since cuckoopath
// elements only define a sequence of alternate hashings for different hash
// values, we only need to keep track of the hash values being moved, rather
// than the keys themselves.
struct CuckooRecord {
  size_type bucket;
  size_type slot;
  hash_value hv;
};

// An array of CuckooRecords
typedef std::array<CuckooRecord, MAX_BFS_PATH_LEN> CuckooRecords;

/**
 * A concurrent hash table
 */
class cuckoohash_map {
public:
  /** @name Type Declarations */
  /**@{*/

  /**@}*/

  /** @name Constructors, Destructors, and Assignment */
  /**@{*/

  /**
   * Creates a new cuckohash_map instance
   *
   * @param n the number of elements to reserve space for initially
   * @param hf hash function instance to use
   * @param equal equality function instance to use
   */
  cuckoohash_map(size_type n = LIBCUCKOO_DEFAULT_SIZE, const Hash &hf = Hash(),
                 const KeyEqual &equal = KeyEqual())
      : hash_fn_(hf), eq_fn_(equal), buckets_(reserve_calc(n)),
        all_locks_(std::min(bucket_count(), size_type(kMaxNumLocks))),
        minimum_load_factor_(LIBCUCKOO_DEFAULT_MINIMUM_LOAD_FACTOR),
        maximum_hashpower_(LIBCUCKOO_NO_MAXIMUM_HASHPOWER) {
  }

  /**
   * Eliminate copy assignment operator.
   */

  cuckoohash_map(const cuckoohash_map &other) = delete;
  cuckoohash_map &operator=(const cuckoohash_map &other) = delete;

  /**@}*/

  /** @name Table Details
   *
   * Methods for getting information about the table. Methods that query
   * changing properties of the table are not synchronized with concurrent
   * operations, and may return out-of-date information if the table is being
   * concurrently modified. They will also continue to work after the container
   * has been moved.
   *
   */
  /**@{*/

  /**
   * Returns the function that hashes the keys
   *
   * @return the hash function
   */
  hasher hash_function() const { return hash_fn_; }

  /**
   * Returns the function that compares keys for equality
   *
   * @return the key comparison function
   */
  key_equal key_eq() const { return eq_fn_; }

  /**
   * Returns the hashpower of the table, which is log<SUB>2</SUB>(@ref
   * bucket_count()).
   *
   * @return the hashpower
   */
  size_type hashpower() const { return buckets_.hashpower(); }

  /**
   * Returns the number of buckets in the table.
   *
   * @return the bucket count
   */
  size_type bucket_count() const { return buckets_.size(); }

  /**
   * Returns whether the table is empty or not.
   *
   * @return true if the table is empty, false otherwise
   */
  bool empty() const { return size() == 0; }

  /**
   * Returns the number of elements in the table.
   *
   * @return number of elements in the table
   */
  size_type size() const {
    counter_type s = 0;
    for (spinlock &lock : get_current_locks()) {
      s += lock.elem_counter();
    }
    assert(s >= 0);
    return static_cast<size_type>(s);
  }

  /** Returns the current capacity of the table, that is, @ref bucket_count()
   * &times.
   *
   * @return capacity of table
   */
  size_type capacity() const { return bucket_count() * SLOT_PER_BUCKET; }

  /**
   * Returns the percentage the table is filled, that is, @ref size() &divide;
   * @ref capacity().
   *
   * @return load factor of the table
   */
  double load_factor() const {
    return static_cast<double>(size()) / static_cast<double>(capacity());
  }

  /**
   * Sets the minimum load factor allowed for automatic expansions. If an
   * expansion is needed when the load factor of the table is lower than this
   * threshold, ERROR_LOAD_FACTOR_TOO_LOW is returned. It will not be
   * returned for an explicitly-triggered expansion.
   *
   * @param mlf the load factor to set the minimum to
   * @param error the error code - ERROR_INVALID_ARGUMENT if the given
   * load factor is less than 0.0 or greater than 1.0
   */
  void minimum_load_factor(const double mlf, int &error) {
    if (mlf < 0.0) {
      error = ERROR_INVALID_ARGUMENT;
    } else if (mlf > 1.0) {
      error = ERROR_INVALID_ARGUMENT;
    }
    else {
      minimum_load_factor_.store(mlf, std::memory_order_release);
      error = ERROR_NONE;
    }
  }

  /**
   * Returns the minimum load factor of the table
   *
   * @return the minimum load factor
   */
  double minimum_load_factor() const {
    return minimum_load_factor_.load(std::memory_order_acquire);
  }

  /**
   * Sets the maximum hashpower the table can be. If set to @ref
   * LIBCUCKOO_NO_MAXIMUM_HASHPOWER, there will be no limit on the hashpower.
   * Otherwise, the table will not be able to expand beyond the given
   * hashpower, either by an explicit or an automatic expansion.
   *
   * @param mhp the hashpower to set the maximum to
   * @param error the returned error code - ERROR_INVALID_ARGUMENT
   * if the current hashpower exceeds the limit
   */
  void maximum_hashpower(size_type mhp, int &error) {
    if (hashpower() > mhp) {
      error = ERROR_INVALID_ARGUMENT;
    }
    else {
      maximum_hashpower_.store(mhp, std::memory_order_release);
      error = ERROR_NONE;
    }
  }

  /**
   * Returns the maximum hashpower of the table
   *
   * @return the maximum hashpower
   */
  size_type maximum_hashpower() const {
    return maximum_hashpower_.load(std::memory_order_acquire);
  }

  /**@}*/

  /**
   * Copies the value associated with @p key into @p val. @c
   * mapped_type must be @c CopyAssignable.
   */
  bool find(const KEY &key, mapped_type &val) const {
    const hash_value hv = hashed_key(key);
    const auto b = snapshot_and_lock_two(hv);
    const table_position pos = cuckoo_find(key, hv.partial, b.i1, b.i2);
    if (pos.status == ok) {
      val = buckets_[pos.index].mapped(pos.slot);
      return true;
    } else {
      return false;
    }
  }

  /** Searches the table for @p key, and returns the associated value it
   * finds. @c mapped_type must be @c CopyConstructible.
   *
   * @param key the key to search for
   * @return the value associated with the given key
   * @param error the returned error code
   */
  mapped_type find(const KEY &key, int &error) const {
    const hash_value hv = hashed_key(key);
    const auto b = snapshot_and_lock_two(hv);
    const table_position pos = cuckoo_find(key, hv.partial, b.i1, b.i2);
    if (pos.status == ok) {
      error = ERROR_NONE;
      return buckets_[pos.index].mapped(pos.slot);
    } else {
      error = ERROR_OUT_OF_RANGE;
      return mapped_type();
    }
  }

  /**
   * Returns whether or not @p key is in the table.
   */
  bool contains(const KEY &key) const {
    const hash_value hv = hashed_key(key);
    const auto b = snapshot_and_lock_two(hv);
    const table_position pos = cuckoo_find(key, hv.partial, b.i1, b.i2);
    if (pos.status == ok) {
      return true;
    } else {
      return false;
    }
  }

  /**
   * Updates the value associated with @p key to @p val.
   * @c mapped_type must be @c MoveAssignable or @c
   * CopyAssignable.
   */
  bool update(const KEY &key, const VALUE &val) {
    const hash_value hv = hashed_key(key);
    const auto b = snapshot_and_lock_two(hv);
    const table_position pos = cuckoo_find(key, hv.partial, b.i1, b.i2);
    if (pos.status == ok) {
      buckets_[pos.index].mapped(pos.slot) = val;
      return true;
    } else {
      return false;
    }
  }

  /**
   * Inserts the key-value pair into the table.
   */
  bool insert(const KEY &key, const VALUE &val, int &error) {
    hash_value hv = hashed_key(key);
    auto b = snapshot_and_lock_two(hv);
    table_position pos = cuckoo_insert_loop(hv, b, key, error);
    if (pos.status == ok) {
      add_to_bucket(pos.index, pos.slot, hv.partial, key, val);
      return true;
    } else {
      return false;
    }
  }

  /**
   * Inserts the key-value pair into the table. If the key is already in the
   * table, assigns the existing mapped value to @p val.
   */
  bool insert_or_assign(const KEY &key, const VALUE &val, int &error) {
    hash_value hv = hashed_key(key);
    auto b = snapshot_and_lock_two(hv);
    table_position pos = cuckoo_insert_loop(hv, b, key, error);
    if (pos.status == ok) {
      add_to_bucket(pos.index, pos.slot, hv.partial, key, val);
      return true;
    } else if (error == ERROR_NONE) {
      buckets_[pos.index].mapped(pos.slot) = val;
      return false;
    }
    else {
      return false;
    }
  }

  /**
   * Erases the key from the table. Equivalent to calling @ref erase_fn with a
   * functor that just returns true.
   */
  bool erase(const KEY &key) {
    const hash_value hv = hashed_key(key);
    const auto b = snapshot_and_lock_two(hv);
    const table_position pos = cuckoo_find(key, hv.partial, b.i1, b.i2);
    if (pos.status == ok) {
      del_from_bucket(pos.index, pos.slot);
      return true;
    } else {
      return false;
    }
  }

  /**
   * Resizes the table to the given hashpower. If this hashpower is not larger
   * than the current hashpower, then it decreases the hashpower to the
   * maximum of the specified value and the smallest hashpower that can hold
   * all the elements currently in the table.
   *
   * @param n the hashpower to set for the table
   * @return true if the table changed size, false otherwise
   */
  bool rehash(size_type n, int &error) { return cuckoo_rehash(n, error); }

  /**
   * Reserve enough space in the table for the given number of elements. If
   * the table can already hold that many elements, the function will shrink
   * the table to the smallest hashpower that can hold the maximum of the
   * specified amount and the current table size.
   *
   * @param n the number of elements to reserve space for
   * @return true if the size of the table changed, false otherwise
   */
  bool reserve(size_type n, int &error) { return cuckoo_reserve(n, error); }

  /**
   * Removes all elements in the table, calling their destructors.
   */
  void clear() {
    auto all_locks_manager = snapshot_and_lock_all();
    cuckoo_clear();
  }

  /**@}*/

private:
  // Hashing types and functions

  // true if the key is small and simple, which means using partial keys for
  // lookup would probably slow us down
  static constexpr bool is_simple =
      std::is_pod<key_type>::value && sizeof(key_type) <= 8;

  hash_value hashed_key(const KEY &key) const {
    const size_type hash = hash_function()(key);
    return {hash, partial_key(hash)};
  }

  size_type hashed_key_only_hash(const KEY &key) const {
    return hash_function()(key);
  }

  // hashsize returns the number of buckets corresponding to a given
  // hashpower.
  static inline size_type hashsize(const size_type hp) {
    return size_type(1) << hp;
  }

  // hashmask returns the bitmask for the buckets array corresponding to a
  // given hashpower.
  static inline size_type hashmask(const size_type hp) {
    return hashsize(hp) - 1;
  }

  // The partial key must only depend on the hash value. It cannot change with
  // the hashpower, because, in order for `cuckoo_fast_double` to work
  // properly, the alt_index must only grow by one bit at the top each time we
  // expand the table.
  static partial_t partial_key(const size_type hash) {
    const uint64_t hash_64bit = hash;
    const uint32_t hash_32bit = (static_cast<uint32_t>(hash_64bit) ^
                                 static_cast<uint32_t>(hash_64bit >> 32));
    const uint16_t hash_16bit = (static_cast<uint16_t>(hash_32bit) ^
                                 static_cast<uint16_t>(hash_32bit >> 16));
    const uint8_t hash_8bit = (static_cast<uint8_t>(hash_16bit) ^
                               static_cast<uint8_t>(hash_16bit >> 8));
    return hash_8bit;
  }

  // index_hash returns the first possible bucket that the given hashed key
  // could be.
  static inline size_type index_hash(const size_type hp, const size_type hv) {
    return hv & hashmask(hp);
  }

  // alt_index returns the other possible bucket that the given hashed key
  // could be. It takes the first possible bucket as a parameter. Note that
  // this function will return the first possible bucket if index is the
  // second possible bucket, so alt_index(ti, partial, alt_index(ti, partial,
  // index_hash(ti, hv))) == index_hash(ti, hv).
  static inline size_type alt_index(const size_type hp, const partial_t partial,
                                    const size_type index) {
    // ensure tag is nonzero for the multiply. 0xc6a4a7935bd1e995 is the
    // hash constant from 64-bit MurmurHash2
    const size_type nonzero_tag = static_cast<size_type>(partial) + 1;
    return (index ^ (nonzero_tag * 0xc6a4a7935bd1e995)) & hashmask(hp);
  }

  // After taking a lock on the table for the given bucket, this function will
  // check the hashpower to make sure it is the same as what it was before the
  // lock was taken. If it isn't unlock the bucket and return
  // ERROR_HASHPOWER_CHANGED instead of ERROR_NONE.
  inline int check_hashpower(size_type hp, spinlock &lock) const {
    if (hashpower() != hp) {
      lock.unlock();
      LIBCUCKOO_DBG("%s", "hashpower changed\n");
      return ERROR_HASHPOWER_CHANGED;
    }
    else {
      return ERROR_NONE;
    }
  }

  // locks the given bucket index.
  //
  // sets error to ERROR_HASHPOWER_CHANGED if it changed after taking the lock.
  LockManager lock_one(size_type hp, size_type i, int &error) const {
    locks_t &locks = get_current_locks();
    spinlock &lock = locks[lock_ind(i)];
    lock.lock();
    error = check_hashpower(hp, lock);
    if (error != ERROR_NONE) {
      return nullptr;
    }
    return LockManager(&lock);
  }

  // locks the two bucket indexes, always locking the earlier index first to
  // avoid deadlock. If the two indexes are the same, it just locks one.
  //
  // sets error to ERROR_HASHPOWER_CHANGED if it changed after taking the lock.

  TwoBuckets lock_two(size_type hp, size_type i1, size_type i2, int &error) const {
    size_type l1 = lock_ind(i1);
    size_type l2 = lock_ind(i2);
    if (l2 < l1) {
      std::swap(l1, l2);
    }
    locks_t &locks = get_current_locks();
    locks[l1].lock();
    error = check_hashpower(hp, locks[l1]);
    if (error != ERROR_NONE) {
      return TwoBuckets();
    }
    if (l2 != l1) {
      locks[l2].lock();
    }
    return TwoBuckets(locks, i1, i2);
  }

  // lock_three locks the three bucket indexes in numerical order, returning
  // the containers as a two (i1 and i2) and a one (i3). The one will not be
  // active if i3 shares a lock index with i1 or i2.
  //
  // sets error to ERROR_HASHPOWER_CHANGED if it changed after taking the lock.
  std::pair<TwoBuckets, LockManager> lock_three(size_type hp, size_type i1,
                                                size_type i2, size_type i3,
                                                int &error)
                                                const {
    std::array<size_type, 3> l{{lock_ind(i1), lock_ind(i2), lock_ind(i3)}};
    // Lock in order.
    if (l[2] < l[1])
      std::swap(l[2], l[1]);
    if (l[2] < l[0])
      std::swap(l[2], l[0]);
    if (l[1] < l[0])
      std::swap(l[1], l[0]);
    locks_t &locks = get_current_locks();
    locks[l[0]].lock();
    error = check_hashpower(hp, locks[l[0]]);
    if (error != ERROR_NONE) {
      return std::make_pair(TwoBuckets(), nullptr);
    }
    if (l[1] != l[0]) {
      locks[l[1]].lock();
    }
    if (l[2] != l[1]) {
      locks[l[2]].lock();
    }
    return std::make_pair(TwoBuckets(locks, i1, i2),
                          LockManager((lock_ind(i3) == lock_ind(i1) ||
                                       lock_ind(i3) == lock_ind(i2))
                                          ? nullptr
                                          : &locks[lock_ind(i3)]));
  }

  // snapshot_and_lock_two loads locks the buckets associated with the given
  // hash value, making sure the hashpower doesn't change before the locks are
  // taken. Thus it ensures that the buckets and locks corresponding to the
  // hash value will stay correct as long as the locks are held. It returns
  // the bucket indices associated with the hash value and the current
  // hashpower.
  TwoBuckets snapshot_and_lock_two(const hash_value &hv) const {
    while (true) {
      // Keep the current hashpower and locks we're using to compute the buckets
      const size_type hp = hashpower();
      const size_type i1 = index_hash(hp, hv.hash);
      const size_type i2 = alt_index(hp, hv.partial, i1);
      int error;
      TwoBuckets tb = lock_two(hp, i1, i2, error);
      if (error == ERROR_HASHPOWER_CHANGED) {
        // The hashpower changed while taking the locks. Try again.
        continue;
      }
      else {
        return tb;
      }
    }
  }

  // snapshot_and_lock_all takes all the locks, and returns a deleter object
  // that releases the locks upon destruction. Note that after taking all the
  // locks, it is okay to resize the buckets_ container, since no other threads
  // should be accessing the buckets. This should only be called if we are not
  // in locked_table mode, and after this function is over, we will be in
  // locked_table mode. When the deleter object goes out of scope, we will be
  // out of locked_table mode.
  AllLocksManager snapshot_and_lock_all() {
    all_locks_list_node *first_locked = all_locks_.get_tail();
    all_locks_list_node *current_locks = first_locked;
    while (current_locks != nullptr) {
      locks_t &locks = current_locks->elt;
      for (spinlock &lock : locks) {
        lock.lock();
      }
      current_locks = current_locks->next;
    }
    // Once we have taken all the locks of the "current" container, nobody
    // else can do locking operations on the table.
    return AllLocksManager(first_locked);
  }

  // Searching types and functions

  // cuckoo_find searches the table for the given key, returning the position
  // of the element found, or a failure status code if the key wasn't found.
  // It expects the locks to be taken and released outside the function.
  table_position cuckoo_find(const KEY &key, const partial_t partial,
                             const size_type i1, const size_type i2) const {
    int slot = try_read_from_bucket(buckets_[i1], partial, key);
    if (slot != -1) {
      return table_position{i1, static_cast<size_type>(slot), ok};
    }
    slot = try_read_from_bucket(buckets_[i2], partial, key);
    if (slot != -1) {
      return table_position{i2, static_cast<size_type>(slot), ok};
    }
    return table_position{0, 0, failure_key_not_found};
  }

  // try_read_from_bucket will search the bucket for the given key and return
  // the index of the slot if found, or -1 if not found.
  int try_read_from_bucket(const bucket &b, const partial_t partial,
                           const KEY &key) const {
    // Silence a warning from MSVC about partial being unused if is_simple.
    (void)partial;
    for (int i = 0; i < static_cast<int>(SLOT_PER_BUCKET); ++i) {
      if (!b.occupied(i) || (!is_simple && partial != b.partial(i))) {
        continue;
      } else if (key_eq()(b.key(i), key)) {
        return i;
      }
    }
    return -1;
  }

  // Insertion types and function

  /**
   * Runs cuckoo_insert in a loop until it succeeds in insert, so
   * we pulled out the loop to avoid duplicating logic.
   *
   * @param hv the hash value of the key
   * @param b bucket locks
   * @param key the key to insert
   * @return table_position of the location to insert the new element, or the
   * site of the duplicate element with a status code if there was a duplicate.
   * In either case, the locks will still be held after the function ends.
   * @param error the returned error code, e.g., ERROR_LOAD_FACTOR_TOO_LOW
   * if expansion is necessary but the load factor of the table is below
   * the threshold
   */
  table_position cuckoo_insert_loop(hash_value hv, TwoBuckets &b, const KEY &key, int &error) {
    error = ERROR_NONE;
    table_position pos;
    while (true) {
      const size_type hp = hashpower();
      pos = cuckoo_insert(hv, b, key);
      switch (pos.status) {
      case ok:
      case failure_key_duplicated:
        return pos;
      case failure_table_full:
        // Expand the table and try again, re-grabbing the locks
        cuckoo_fast_double(hp, true /* auto resize */, error);
        if (error != ERROR_NONE) {
          return pos;
        }
        b = snapshot_and_lock_two(hv);
        break;
      case failure_under_expansion:
        // The table was under expansion while we were cuckooing. Re-grab the
        // locks and try again.
        b = snapshot_and_lock_two(hv);
        break;
      default:
        assert(false);
      }
    }
  }

  // cuckoo_insert tries to find an empty slot in either of the buckets to
  // insert the given key into, performing cuckoo hashing if necessary. It
  // expects the locks to be taken outside the function. Before inserting, it
  // checks that the key isn't already in the table. cuckoo hashing presents
  // multiple concurrency issues, which are explained in the function. The
  // following return states are possible:
  //
  // ok -- Found an empty slot, locks will be held on both buckets after the
  // function ends, and the position of the empty slot is returned
  //
  // failure_key_duplicated -- Found a duplicate key, locks will be held, and
  // the position of the duplicate key will be returned
  //
  // failure_under_expansion -- Failed due to a concurrent expansion
  // operation. Locks are released. No meaningful position is returned.
  //
  // failure_table_full -- Failed to find an empty slot for the table. Locks
  // are released. No meaningful position is returned.
  table_position cuckoo_insert(const hash_value hv, TwoBuckets &b, const KEY &key) {
    int res1, res2;
    bucket &b1 = buckets_[b.i1];
    if (!try_find_insert_bucket(b1, res1, hv.partial, key)) {
      return table_position{b.i1, static_cast<size_type>(res1),
                            failure_key_duplicated};
    }
    bucket &b2 = buckets_[b.i2];
    if (!try_find_insert_bucket(b2, res2, hv.partial, key)) {
      return table_position{b.i2, static_cast<size_type>(res2),
                            failure_key_duplicated};
    }
    if (res1 != -1) {
      return table_position{b.i1, static_cast<size_type>(res1), ok};
    }
    if (res2 != -1) {
      return table_position{b.i2, static_cast<size_type>(res2), ok};
    }

    // We are unlucky, so let's perform cuckoo hashing.
    size_type insert_bucket = 0;
    size_type insert_slot = 0;
    cuckoo_status st = run_cuckoo(b, insert_bucket, insert_slot);
    if (st == failure_under_expansion) {
      // The run_cuckoo operation operated on an old version of the table,
      // so we have to try again. We signal to the calling insert method
      // to try again by returning failure_under_expansion.
      return table_position{0, 0, failure_under_expansion};
    } else if (st == ok) {
      assert(!get_current_locks()[lock_ind(b.i1)].try_lock());
      assert(!get_current_locks()[lock_ind(b.i2)].try_lock());
      assert(!buckets_[insert_bucket].occupied(insert_slot));
      assert(insert_bucket == index_hash(hashpower(), hv.hash) ||
             insert_bucket == alt_index(hashpower(), hv.partial,
                                        index_hash(hashpower(), hv.hash)));
      // Since we unlocked the buckets during run_cuckoo, another insert
      // could have inserted the same key into either b.i1 or
      // b.i2, so we check for that before doing the insert.
      table_position pos = cuckoo_find(key, hv.partial, b.i1, b.i2);
      if (pos.status == ok) {
        pos.status = failure_key_duplicated;
        return pos;
      }
      return table_position{insert_bucket, insert_slot, ok};
    }
    assert(st == failure);
    LIBCUCKOO_DBG("hash table is full (hashpower = %zu, hash_items = %zu,"
                  "load factor = %.2f), need to increase hashpower\n",
                  hashpower(), size(), load_factor());
    return table_position{0, 0, failure_table_full};
  }

  // add_to_bucket will insert the given key-value pair into the slot. The key
  // and value will be move-constructed into the table, so they are not valid
  // for use afterwards.
  void add_to_bucket(const size_type bucket_ind, const size_type slot,
                     const partial_t partial, const KEY &key, const VALUE& val) {
    buckets_.setKV(bucket_ind, slot, partial, key, val);
    ++get_current_locks()[lock_ind(bucket_ind)].elem_counter();
  }

  // try_find_insert_bucket will search the bucket for the given key, and for
  // an empty slot. If the key is found, we store the slot of the key in
  // `slot` and return false. If we find an empty slot, we store its position
  // in `slot` and return true. If no duplicate key is found and no empty slot
  // is found, we store -1 in `slot` and return true.
  bool try_find_insert_bucket(const bucket &b, int &slot,
                              const partial_t partial, const KEY &key) const {
    // Silence a warning from MSVC about partial being unused if is_simple.
    (void)partial;
    slot = -1;
    for (int i = 0; i < static_cast<int>(SLOT_PER_BUCKET); ++i) {
      if (b.occupied(i)) {
        if (!is_simple && partial != b.partial(i)) {
          continue;
        }
        if (key_eq()(b.key(i), key)) {
          slot = i;
          return false;
        }
      } else {
        slot = i;
      }
    }
    return true;
  }

  // run_cuckoo performs cuckoo hashing on the table in an attempt to free up
  // a slot on either of the insert buckets, which are assumed to be locked
  // before the start. On success, the bucket and slot that was freed up is
  // stored in insert_bucket and insert_slot. In order to perform the search
  // and the swaps, it has to release the locks, which can lead to certain
  // concurrency issues, the details of which are explained in the function.
  // If run_cuckoo returns ok (success), then `b` will be active, otherwise it
  // will not.
  cuckoo_status run_cuckoo(TwoBuckets &b, size_type &insert_bucket,
                           size_type &insert_slot) {
    // We must unlock the buckets here, so that cuckoopath_search and
    // cuckoopath_move can lock buckets as desired without deadlock.
    // cuckoopath_move has to move something out of one of the original
    // buckets as its last operation, and it will lock both buckets and
    // leave them locked after finishing. This way, we know that if
    // cuckoopath_move succeeds, then the buckets needed for insertion are
    // still locked. If cuckoopath_move fails, the buckets are unlocked and
    // we try again. This unlocking does present two problems. The first is
    // that another insert on the same key runs and, finding that the key
    // isn't in the table, inserts the key into the table. Then we insert
    // the key into the table, causing a duplication. To check for this, we
    // search the buckets for the key we are trying to insert before doing
    // so (this is done in cuckoo_insert, and requires that both buckets are
    // locked). Another problem is that an expansion runs and changes the
    // hashpower, meaning the buckets may not be valid anymore. In this
    // case, the cuckoopath functions will have returned
    // ERROR_HASHPOWER_CHANGED, which we detect and handle here.
    size_type hp = hashpower();
    b.unlock();
    CuckooRecords cuckoo_path;
    bool done = false;
    int error;
    while (!done) {
      const int depth =
          cuckoopath_search(hp, cuckoo_path, b.i1, b.i2, error);
      if (error == ERROR_HASHPOWER_CHANGED) {
        return failure_under_expansion;
      }
      if (depth < 0) {
        break;
      }

      if (cuckoopath_move(hp, cuckoo_path, depth, b, error)) {
        insert_bucket = cuckoo_path[0].bucket;
        insert_slot = cuckoo_path[0].slot;
        assert(insert_bucket == b.i1 || insert_bucket == b.i2);
        assert(!get_current_locks()[lock_ind(b.i1)].try_lock());
        assert(!get_current_locks()[lock_ind(b.i2)].try_lock());
        assert(!buckets_[insert_bucket].occupied(insert_slot));
        done = true;
        break;
      }
      if (error == ERROR_HASHPOWER_CHANGED) {
        return failure_under_expansion;
      }
    }
    return done ? ok : failure;
  }

  // cuckoopath_search finds a cuckoo path from one of the starting buckets to
  // an empty slot in another bucket. It returns the depth of the discovered
  // cuckoo path on success, and -1 on failure. Since it doesn't take locks on
  // the buckets it searches, the data can change between this function and
  // cuckoopath_move. Thus cuckoopath_move checks that the data matches the
  // cuckoo path before changing it.
  //
  // sets error to ERROR_HASHPOWER_CHANGED if it changed during the search.
  int cuckoopath_search(const size_type hp, CuckooRecords &cuckoo_path,
                        const size_type i1, const size_type i2, int &error) {
    error = ERROR_NONE;
    b_slot x = slot_search(hp, i1, i2, error);
    if (x.depth == -1) {
      return -1;
    }
    // Fill in the cuckoo path slots from the end to the beginning.
    for (int i = x.depth; i >= 0; i--) {
      cuckoo_path[i].slot = x.pathcode % SLOT_PER_BUCKET;
      x.pathcode /= SLOT_PER_BUCKET;
    }
    // Fill in the cuckoo_path buckets and keys from the beginning to the
    // end, using the final pathcode to figure out which bucket the path
    // starts on. Since data could have been modified between slot_search
    // and the computation of the cuckoo path, this could be an invalid
    // cuckoo_path.
    CuckooRecord &first = cuckoo_path[0];
    if (x.pathcode == 0) {
      first.bucket = i1;
    } else {
      assert(x.pathcode == 1);
      first.bucket = i2;
    }
    {
      const auto lock_manager = lock_one(hp, first.bucket, error);
      if (error != ERROR_NONE) {
        return -1;
      }
      const bucket &b = buckets_[first.bucket];
      if (!b.occupied(first.slot)) {
        // We can terminate here
        return 0;
      }
      first.hv = hashed_key(b.key(first.slot));
    }
    for (int i = 1; i <= x.depth; ++i) {
      CuckooRecord &curr = cuckoo_path[i];
      const CuckooRecord &prev = cuckoo_path[i - 1];
      assert(prev.bucket == index_hash(hp, prev.hv.hash) ||
             prev.bucket ==
                 alt_index(hp, prev.hv.partial, index_hash(hp, prev.hv.hash)));
      // We get the bucket that this slot is on by computing the alternate
      // index of the previous bucket
      curr.bucket = alt_index(hp, prev.hv.partial, prev.bucket);
      const auto lock_manager = lock_one(hp, curr.bucket, error);
      if (error != ERROR_NONE) {
        return -1;
      }
      const bucket &b = buckets_[curr.bucket];
      if (!b.occupied(curr.slot)) {
        // We can terminate here
        return i;
      }
      curr.hv = hashed_key(b.key(curr.slot));
    }
    return x.depth;
  }

  // cuckoopath_move moves keys along the given cuckoo path in order to make
  // an empty slot in one of the buckets in cuckoo_insert. Before the start of
  // this function, the two insert-locked buckets were unlocked in run_cuckoo.
  // At the end of the function, if the function returns true (success), then
  // both insert-locked buckets remain locked. If the function is
  // unsuccessful, then both insert-locked buckets will be unlocked.
  //
  // sets error to ERROR_HASHPOWER_CHANGED if it changed during the move.
  bool cuckoopath_move(const size_type hp, CuckooRecords &cuckoo_path,
                       size_type depth, TwoBuckets &b, int &error) {
    error = ERROR_NONE;
    if (depth == 0) {
      // There is a chance that depth == 0, when try_add_to_bucket sees
      // both buckets as full and cuckoopath_search finds one empty. In
      // this case, we lock both buckets. If the slot that
      // cuckoopath_search found empty isn't empty anymore, we unlock them
      // and return false. Otherwise, the bucket is empty and insertable,
      // so we hold the locks and return true.
      const size_type bucket = cuckoo_path[0].bucket;
      assert(bucket == b.i1 || bucket == b.i2);
      b = lock_two(hp, b.i1, b.i2, error);
      if (error != ERROR_NONE) {
        return false;
      }
      if (!buckets_[bucket].occupied(cuckoo_path[0].slot)) {
        return true;
      } else {
        b.unlock();
        return false;
      }
    }

    while (depth > 0) {
      CuckooRecord &from = cuckoo_path[depth - 1];
      CuckooRecord &to = cuckoo_path[depth];
      const size_type fs = from.slot;
      const size_type ts = to.slot;
      TwoBuckets twob;
      LockManager extra_manager;
      if (depth == 1) {
        // Even though we are only swapping out of one of the original
        // buckets, we have to lock both of them along with the slot we
        // are swapping to, since at the end of this function, they both
        // must be locked. We store tb inside the extrab container so it
        // is unlocked at the end of the loop.
        std::tie(twob, extra_manager) =
             lock_three(hp, b.i1, b.i2, to.bucket, error);
      } else {
        twob = lock_two(hp, from.bucket, to.bucket, error);
      }
      if (error != ERROR_NONE) {
        return false;
      }

      bucket &fb = buckets_[from.bucket];
      bucket &tb = buckets_[to.bucket];

      // We plan to kick out fs, but let's check if it is still there;
      // there's a small chance we've gotten scooped by a later cuckoo. If
      // that happened, just... try again. Also the slot we are filling in
      // may have already been filled in by another thread, or the slot we
      // are moving from may be empty, both of which invalidate the swap.
      // We only need to check that the hash value is the same, because,
      // even if the keys are different and have the same hash value, then
      // the cuckoopath is still valid.
      if (tb.occupied(ts) || !fb.occupied(fs) ||
          hashed_key_only_hash(fb.key(fs)) != from.hv.hash) {
        return false;
      }

      buckets_.setKV(to.bucket, ts, fb.partial(fs), fb.key(fs),
                     fb.mapped(fs));
      buckets_.eraseKV(from.bucket, fs);
      if (depth == 1) {
        // Hold onto the locks contained in twob
        b = twob;
      }
      depth--;
    }
    return true;
  }

  // slot_search searches for a cuckoo path using breadth-first search. It
  // starts with the i1 and i2 buckets, and, until it finds a bucket with an
  // empty slot, adds each slot of the bucket in the b_slot. If the queue runs
  // out of space, it fails.
  //
  // sets error to ERROR_HASHPOWER_CHANGED if it changed during the search
  b_slot slot_search(const size_type hp, const size_type i1,
                     const size_type i2, int &error) {
    b_queue q;
    // The initial pathcode informs cuckoopath_search which bucket the path
    // starts on
    q.enqueue(b_slot(i1, 0, 0));
    q.enqueue(b_slot(i2, 1, 0));
    while (!q.empty()) {
      b_slot x = q.dequeue();
      auto lock_manager = lock_one(hp, x.bucket, error);
      if (error != ERROR_NONE) {
        return b_slot(0, 0, -1);
      }
      bucket &b = buckets_[x.bucket];
      // Picks a (sort-of) random slot to start from
      size_type starting_slot = x.pathcode % SLOT_PER_BUCKET;
      for (size_type i = 0; i < SLOT_PER_BUCKET; ++i) {
        uint16_t slot = (starting_slot + i) % SLOT_PER_BUCKET;
        if (!b.occupied(slot)) {
          // We can terminate the search here
          x.pathcode = x.pathcode * SLOT_PER_BUCKET + slot;
          return x;
        }

        // If x has less than the maximum number of path components,
        // create a new b_slot item, that represents the bucket we would
        // have come from if we kicked out the item at this slot.
        const partial_t partial = b.partial(slot);
        if (x.depth < MAX_BFS_PATH_LEN - 1) {
          assert(!q.full());
          b_slot y(alt_index(hp, partial, x.bucket),
                   x.pathcode * SLOT_PER_BUCKET + slot, x.depth + 1);
          q.enqueue(y);
        }
      }
    }
    // We didn't find a short-enough cuckoo path, so the search terminated.
    // Return a failure value.
    return b_slot(0, 0, -1);
  }

  // cuckoo_fast_double will double the size of the table by taking advantage
  // of the properties of index_hash and alt_index. If the key's move
  // constructor is not noexcept, we use cuckoo_expand_simple, since that
  // provides a strong exception guarantee.
  cuckoo_status cuckoo_fast_double(size_type current_hp, bool auto_resize,
                                   int &error) {
    error = ERROR_NONE;
    if (!std::is_nothrow_move_constructible<key_type>::value ||
        !std::is_nothrow_move_constructible<mapped_type>::value) {
      LIBCUCKOO_DBG("%s", "cannot run cuckoo_fast_double because key-value"
                          " pair is not nothrow move constructible");
      return cuckoo_expand_simple(current_hp + 1, auto_resize, error);
    }
    const size_type new_hp = current_hp + 1;
    auto all_locks_manager = snapshot_and_lock_all();
    cuckoo_status st = check_resize_validity(current_hp, new_hp, auto_resize, error);
    if (st != ok) {
      return st;
    }

    // We must re-hash the table, moving items in each bucket to a different
    // one. The hash functions are carefully designed so that when doubling the
    // number of buckets, each element either stays in its existing bucket or
    // goes to exactly one new bucket. This means we can re-hash each bucket in
    // parallel. We create a new empty buckets container and move all the
    // elements from the old container to the new one.
    buckets_t new_buckets(new_hp);
    // For certain types, MSVC may decide that move_buckets() cannot throw and
    // so the catch block below is dead code. Since that won't always be true,
    // we just disable the warning here.
    LIBCUCKOO_SQUELCH_DEADCODE_WARNING_BEGIN;
    size_type start = 0;
    size_type end = hashsize(current_hp);
    static const size_type num_threads =
        std::max(std::thread::hardware_concurrency(), 1U);
    size_type work_per_thread = (end - start) / num_threads;
    std::vector<std::thread> threads;
    threads.reserve(num_threads);
    std::vector<int> errors(num_threads, ERROR_NONE);
    for (size_type i = 0; i < num_threads - 1; ++i) {
      threads.emplace_back(move_buckets_static, this, std::ref(new_buckets), current_hp, new_hp, start, start + work_per_thread,
                           std::ref(errors[i]));
      start += work_per_thread;
    }
    threads.emplace_back(move_buckets_static, this, std::ref(new_buckets), current_hp, new_hp, start, end, std::ref(errors.back()));
    for (size_type i = 0; i < num_threads; ++i) {
      threads[i].join();
    }
    error = ERROR_NONE;
    for (size_type i = 0; i < num_threads; ++i) {
      if (errors[i] != ERROR_NONE) {
        error = errors[i];
        return failure;
      }
    }
    LIBCUCKOO_SQUELCH_DEADCODE_WARNING_END;

    // Resize the locks array if necessary. This is done before we update the
    // hashpower so that other threads don't grab the new hashpower and the old
    // locks
    maybe_resize_locks(size_type(1) << new_hp);
    // Swap the old and new buckets. The old bucket data will be destroyed when
    // the function exits
    buckets_.swap(new_buckets);
    return ok;
  }

  static void cuckoo_expand_simple_thread_routine(cuckoohash_map *old_map,
                                                  cuckoohash_map *new_map,
                                                  size_type i, size_type end,
                                                  int& error)
  {
    error = ERROR_NONE;
    for (; i < end; ++i) {
      for (size_type j = 0; j < SLOT_PER_BUCKET; ++j) {
        if (old_map->buckets_[i].occupied(j)) {
          new_map->insert(old_map->buckets_[i].key(j),
                          old_map->buckets_[i].mapped(j), error);
          if (error != ERROR_NONE) {
            break;
          }
        }
      }
    }
  }

  void move_buckets(buckets_t &new_buckets, size_type current_hp,
                    size_type new_hp, size_type start_ind, size_type end_ind,
                    int &error) {
    error = ERROR_NONE;
    for (size_type old_bucket_ind = start_ind; old_bucket_ind < end_ind;
         ++old_bucket_ind) {
      // By doubling the table size, the index_hash and alt_index of
      // each key got one bit added to the top, at position
      // current_hp, which means anything we have to move will either
      // be at the same bucket position, or exactly
      // hashsize(current_hp) later than the current bucket
      bucket &old_bucket = buckets_[old_bucket_ind];
      const size_type new_bucket_ind = old_bucket_ind + hashsize(current_hp);
      size_type new_bucket_slot = 0;

      // For each occupied slot, either move it into its same position in the
      // new buckets container, or to the first available spot in the new
      // bucket in the new buckets container.
      for (size_type old_bucket_slot = 0; old_bucket_slot < SLOT_PER_BUCKET;
           ++old_bucket_slot) {
        if (!old_bucket.occupied(old_bucket_slot)) {
          continue;
        }
        const hash_value hv = hashed_key(old_bucket.key(old_bucket_slot));
        const size_type old_ihash = index_hash(current_hp, hv.hash);
        const size_type old_ahash =
            alt_index(current_hp, hv.partial, old_ihash);
        const size_type new_ihash = index_hash(new_hp, hv.hash);
        const size_type new_ahash = alt_index(new_hp, hv.partial, new_ihash);
        size_type dst_bucket_ind, dst_bucket_slot;
        if ((old_bucket_ind == old_ihash && new_ihash == new_bucket_ind) ||
            (old_bucket_ind == old_ahash && new_ahash == new_bucket_ind)) {
          // We're moving the key to the new bucket
          dst_bucket_ind = new_bucket_ind;
          dst_bucket_slot = new_bucket_slot++;
        } else {
          // We're moving the key to the old bucket
          assert((old_bucket_ind == old_ihash && new_ihash == old_ihash) ||
                 (old_bucket_ind == old_ahash && new_ahash == old_ahash));
          dst_bucket_ind = old_bucket_ind;
          dst_bucket_slot = old_bucket_slot;
        }
        new_buckets.setKV(dst_bucket_ind, dst_bucket_slot++,
                          old_bucket.partial(old_bucket_slot),
                          old_bucket.key(old_bucket_slot),
                          old_bucket.mapped(old_bucket_slot));
      }
    }
  }

  static void move_buckets_static(cuckoohash_map *m, buckets_t &new_buckets, size_type current_hp,
                                  size_type new_hp, size_type start_ind, size_type end_ind,
                                  int &error) {
      m->move_buckets(new_buckets, current_hp, new_hp, start_ind, end_ind, error);
  }

  cuckoo_status check_resize_validity(const size_type orig_hp,
                                      const size_type new_hp,
                                      bool auto_resize,
                                      int &error) {
    error = ERROR_NONE;
    const size_type mhp = maximum_hashpower();
    if (mhp != LIBCUCKOO_NO_MAXIMUM_HASHPOWER && new_hp > mhp) {
      error = ERROR_MAXIMUM_HASH_POWER_EXCEEDED;
      return failure;
    }
    if (auto_resize && load_factor() < minimum_load_factor()) {
      error = ERROR_LOAD_FACTOR_TOO_LOW;
      return failure;
    }
    if (hashpower() != orig_hp) {
      // Most likely another expansion ran before this one could grab the
      // locks
      LIBCUCKOO_DBG("%s", "another expansion is on-going\n");
      return failure_under_expansion;
    }
    return ok;
  }

  // When we expand the contanier, we may need to expand the locks array, if
  // the current locks array is smaller than the maximum size and also smaller
  // than the number of buckets in the upcoming buckets container. In this
  // case, we grow the locks array to the smaller of the maximum lock array
  // size and the bucket count. This is done by allocating an entirely new lock
  // container, taking all the locks, copying over the counters, and then
  // finally adding it to the end of `all_locks_`, thereby designating it the
  // "current" locks container. It is the responsibility of the caller to
  // unlock all locks taken, including the new locks, whenever it is done with
  // them, so that old threads can resume and potentially re-start.
  void maybe_resize_locks(size_type new_bucket_count) {
    locks_t &current_locks = get_current_locks();
    if (!(current_locks.size() < kMaxNumLocks &&
          current_locks.size() < new_bucket_count)) {
      return;
    }

    all_locks_list_node *new_tail = new all_locks_list_node(std::min(size_type(kMaxNumLocks), new_bucket_count));
    locks_t &new_locks = new_tail->elt;
    for (spinlock &lock : new_locks) {
      lock.lock();
    }
    assert(new_locks.size() > current_locks.size());
    std::copy(current_locks.begin(), current_locks.end(), new_locks.begin());
    all_locks_.append(new_tail);
  }

  // cuckoo_expand_simple will resize the table to at least the given
  // new_hashpower. When we're shrinking the table, if the current table
  // contains more elements than can be held by new_hashpower, the resulting
  // hashpower will be greater than `new_hp`. It needs to take all the bucket
  // locks, since no other operations can change the table during expansion.
  // sets error to ERROR_MAXIMUM_HASH_POWER_EXCEEDED if we're expanding beyond the
  // maximum hashpower, and we have an actual limit.
  cuckoo_status cuckoo_expand_simple(size_type new_hp, bool auto_resize, int &error) {
    auto all_locks_manager = snapshot_and_lock_all();
    const size_type hp = hashpower();
    cuckoo_status st = check_resize_validity(hp, new_hp, auto_resize, error);
    if (st != ok) {
      return st;
    }
    // Creates a new hash table with hashpower new_hp and adds all
    // the elements from the old buckets.
    cuckoohash_map new_map(hashsize(new_hp) * SLOT_PER_BUCKET,
                           hash_function(), key_eq());

    size_type start = 0;
    size_type end = hashsize(new_hp);
    static const size_type num_threads =
        std::max(std::thread::hardware_concurrency(), 1U);
    size_type work_per_thread = (end - start) / num_threads;
    std::vector<std::thread> threads;
    threads.reserve(num_threads);
    std::vector<int> errors(num_threads, ERROR_NONE);
    for (size_type i = 0; i < num_threads - 1; ++i) {
      threads.emplace_back(cuckoo_expand_simple_thread_routine, this, &new_map, start, start + work_per_thread,
                           std::ref(errors[i]));
      start += work_per_thread;
    }
    threads.emplace_back(cuckoo_expand_simple_thread_routine, this, &new_map, start, end, std::ref(errors.back()));
    for (size_type i = 0; i < num_threads; ++i) {
      threads[i].join();
    }
    error = ERROR_NONE;
    for (size_type i = 0; i < num_threads; ++i) {
      if (errors[i] != ERROR_NONE) {
        error = errors[i];
        return failure;
      }
    }

    // Swap the current buckets containers with new_map's. This is okay,
    // because we have all the locks, so nobody else should be reading from the
    // buckets array. Then the old buckets array will be deleted when new_map
    // is deleted. We also resize the locks array if necessary.
    maybe_resize_locks(new_map.bucket_count());
    buckets_.swap(new_map.buckets_);
    return ok;
  }

  // Deletion functions

  // Removes an item from a bucket, decrementing the associated counter as
  // well.
  void del_from_bucket(const size_type bucket_ind, const size_type slot) {
    buckets_.eraseKV(bucket_ind, slot);
    --get_current_locks()[lock_ind(bucket_ind)].elem_counter();
  }

  // Empties the table, calling the destructors of all the elements it removes
  // from the table. It assumes the locks are taken as necessary.
  cuckoo_status cuckoo_clear() {
    buckets_.clear();
    for (spinlock &lock : get_current_locks()) {
      lock.elem_counter() = 0;
    }
    return ok;
  }

  // Rehashing functions

  bool cuckoo_rehash(size_type n, int &error) {
    const size_type hp = hashpower();
    if (n == hp) {
      error = ERROR_NONE;
      return false;
    }
    return cuckoo_expand_simple(n, false /* auto resize: no */, error) == ok;
  }

  bool cuckoo_reserve(size_type n, int &error) {
    const size_type hp = hashpower();
    const size_type new_hp = reserve_calc(n);
    if (new_hp == hp) {
      error = ERROR_NONE;
      return false;
    }
    return cuckoo_expand_simple(new_hp, false /* auto resize: no */, error) == ok;
  }

  // Miscellaneous functions

  // reserve_calc takes in a parameter specifying a certain number of slots
  // for a table and returns the smallest hashpower that will hold n elements.
  static size_type reserve_calc(const size_type n) {
    const size_type buckets = (n + SLOT_PER_BUCKET - 1) / SLOT_PER_BUCKET;
    size_type blog2;
    for (blog2 = 0; (size_type(1) << blog2) < buckets; ++blog2)
      ;
    assert(n <= buckets * SLOT_PER_BUCKET && buckets <= hashsize(blog2));
    return blog2;
  }

  locks_t &get_current_locks() const { return all_locks_.get_tail()->elt; }

  // Member variables

  // The hash function
  hasher hash_fn_;

  // The equality function
  key_equal eq_fn_;

  // container of buckets. The size or memory location of the buckets cannot be
  // changed unless all the locks are taken on the table. Thus, it is only safe
  // to access the buckets_ container when you have at least one lock held.
  buckets_t buckets_;

  // A linked list of all lock containers. We never discard lock containers,
  // since there is currently no mechanism for detecting when all threads are
  // done looking at the memory. The back lock container in this list is
  // designated the "current" one, and is used by all operations taking locks.
  // This container can be modified if either it is empty (which should only
  // occur during construction), or if the modifying thread has taken all the
  // locks on the existing "current" container. In the latter case, a
  // modification must take place before a modification to the hashpower, so
  // that other threads can detect the change and adjust appropriately. Marked
  // mutable so that const methods can access and take locks.
  mutable all_locks_t all_locks_;

  // stores the minimum load factor allowed for automatic expansions. Whenever
  // an automatic expansion is triggered (during an insertion where cuckoo
  // hashing fails, for example), we check the load factor against this
  // double, and return an error if it's lower than this value. It can be
  // used to signal when the hash function is bad or the input adversarial.
  std::atomic<double> minimum_load_factor_;

  // stores the maximum hashpower allowed for any expansions. If set to
  // NO_MAXIMUM_HASHPOWER, this limit will be disregarded.
  std::atomic<size_type> maximum_hashpower_;
};

#endif // _CUCKOOHASH_MAP_HH
