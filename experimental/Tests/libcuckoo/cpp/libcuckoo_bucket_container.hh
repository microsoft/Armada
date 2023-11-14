#ifndef LIBCUCKOO_BUCKET_CONTAINER_H
#define LIBCUCKOO_BUCKET_CONTAINER_H

#include <array>
#include <atomic>
#include <cassert>
#include <cstddef>
#include <iostream>
#include <memory>
#include <type_traits>
#include <utility>

#include "cuckoohash_util.hh"
#include "cuckoohash_config.hh"

typedef uint8_t Partial;
typedef KEY key_type;
typedef VALUE mapped_type;
typedef std::pair<const KEY, VALUE> value_type;
typedef Partial partial_t;
typedef std::size_t size_type;
typedef value_type & reference;
typedef const value_type & const_reference;
typedef value_type * pointer;
typedef const value_type * const_pointer;
typedef std::pair<KEY, VALUE> storage_value_type;

/*
 * The bucket type holds SLOT_PER_BUCKET key-value pairs, along with their
 * partial keys and occupancy info. It uses aligned_storage arrays to store
 * the keys and values to allow constructing and destroying key-value pairs
 * in place. The lifetime of bucket data should be managed by the container.
 * It is the user's responsibility to confirm whether the data they are
 * accessing is live or not.
 */
class bucket {
public:
  bucket() noexcept : occupied_{} {}

  const value_type &kvpair(size_type ind) const {
    return *static_cast<const value_type *>(
        static_cast<const void *>(&values_[ind]));
  }
  value_type &kvpair(size_type ind) {
    return *static_cast<value_type *>(static_cast<void *>(&values_[ind]));
  }

  const key_type &key(size_type ind) const {
    return storage_kvpair(ind).first;
  }

  const mapped_type &mapped(size_type ind) const {
    return storage_kvpair(ind).second;
  }
  mapped_type &mapped(size_type ind) { return storage_kvpair(ind).second; }

  partial_t partial(size_type ind) const { return partials_[ind]; }
  partial_t &partial(size_type ind) { return partials_[ind]; }

  bool occupied(size_type ind) const { return occupied_[ind]; }
  bool &occupied(size_type ind) { return occupied_[ind]; }

private:
  friend class libcuckoo_bucket_container;

  const storage_value_type &storage_kvpair(size_type ind) const {
    return *static_cast<const storage_value_type *>(
        static_cast<const void *>(&values_[ind]));
  }
  storage_value_type &storage_kvpair(size_type ind) {
    return *static_cast<storage_value_type *>(
        static_cast<void *>(&values_[ind]));
  }

  std::array<typename std::aligned_storage<sizeof(storage_value_type),
                                           alignof(storage_value_type)>::type,
             SLOT_PER_BUCKET>
      values_;
  std::array<partial_t, SLOT_PER_BUCKET> partials_;
  std::array<bool, SLOT_PER_BUCKET> occupied_;
};

/**
 * libcuckoo_bucket_container manages storage of key-value pairs for the table.
 * It stores the items inline in uninitialized memory, and keeps track of which
 * slots have live data and which do not. It also stores a partial hash for
 * each live key. It is sized by powers of two.
 */
class libcuckoo_bucket_container {
public:

  libcuckoo_bucket_container(size_type hp)
      : hashpower_(hp), buckets_(new bucket[size()]) {
    // The bucket default constructor is nothrow, so we don't have to
    // worry about dealing with exceptions when constructing all the
    // elements.
    static_assert(std::is_nothrow_constructible<bucket>::value,
                  "libcuckoo_bucket_container requires bucket to be nothrow "
                  "constructible");
  }

  ~libcuckoo_bucket_container() noexcept { destroy_buckets(); }

  libcuckoo_bucket_container &operator=(const libcuckoo_bucket_container &bc) = delete;
  libcuckoo_bucket_container(const libcuckoo_bucket_container &bc) = delete;

  void swap(libcuckoo_bucket_container &bc) noexcept {
    // Regardless of whether we actually swapped the allocators or not, it will
    // always be okay to do the remainder of the swap. This is because if the
    // allocators were swapped, then the subsequent operations are okay. If the
    // allocators weren't swapped but compare equal, then we're okay. If they
    // weren't swapped and compare unequal, then behavior is undefined, so
    // we're okay.
    size_t bc_hashpower = bc.hashpower();
    bc.hashpower(hashpower());
    hashpower(bc_hashpower);
    std::swap(buckets_, bc.buckets_);
  }

  size_type hashpower() const {
    return hashpower_.load(std::memory_order_acquire);
  }

  void hashpower(size_type val) {
    hashpower_.store(val, std::memory_order_release);
  }

  size_type size() const { return size_type(1) << hashpower(); }

  bucket &operator[](size_type i) { return buckets_[i]; }
  const bucket &operator[](size_type i) const { return buckets_[i]; }

  // Constructs live data in a bucket
  void setKV(size_type ind, size_type slot, partial_t p, const KEY &k, const VALUE& value) {
    bucket &b = buckets_[ind];
    assert(!b.occupied(slot));
    b.partial(slot) = p;
    storage_value_type &kv = b.storage_kvpair(slot);
    kv.first = k;
    kv.second = value;
    //	traits_::construct(allocator_, std::addressof(b.storage_kvpair(slot)), k, value);
    // This must occur last, to enforce a strong exception guarantee
    b.occupied(slot) = true;
  }

  // Destroys live data in a bucket
  void eraseKV(size_type ind, size_type slot) {
    bucket &b = buckets_[ind];
    assert(b.occupied(slot));
    b.occupied(slot) = false;
  }

  // Destroys all the live data in the buckets
  void clear() noexcept {
    static_assert(
        std::is_nothrow_destructible<key_type>::value &&
            std::is_nothrow_destructible<mapped_type>::value,
        "libcuckoo_bucket_container requires key and value to be nothrow "
        "destructible");
    for (size_type i = 0; i < size(); ++i) {
      bucket &b = buckets_[i];
      for (size_type j = 0; j < SLOT_PER_BUCKET; ++j) {
        if (b.occupied(j)) {
          eraseKV(i, j);
        }
      }
    }
  }

private:
  void destroy_buckets() noexcept {
    if (buckets_ == nullptr) {
      return;
    }
    // The bucket default constructor is nothrow, so we don't have to
    // worry about dealing with exceptions when constructing all the
    // elements.
    static_assert(std::is_nothrow_destructible<bucket>::value,
                  "libcuckoo_bucket_container requires bucket to be nothrow "
                  "destructible");
    clear();
    delete buckets_;
    buckets_ = nullptr;
  }

  // This needs to be atomic, since it can be read and written by multiple
  // threads not necessarily synchronized by a lock.
  std::atomic<size_type> hashpower_;
  // These buckets are protected by striped locks (external to the
  // BucketContainer), which must be obtained before accessing a bucket.
  bucket *buckets_;
};

#endif // LIBCUCKOO_BUCKET_CONTAINER_H
