/** \file */

#ifndef _CUCKOOHASH_UTIL_HH
#define _CUCKOOHASH_UTIL_HH

#include "cuckoohash_config.hh" // for LIBCUCKOO_DEBUG
#include <exception>
#include <thread>
#include <utility>
#include <vector>

#if LIBCUCKOO_DEBUG
//! When \ref LIBCUCKOO_DEBUG is 0, LIBCUCKOO_DBG will printing out status
//! messages in various situations
#define LIBCUCKOO_DBG(fmt, ...)                                                \
  fprintf(stderr, "\x1b[32m"                                                   \
                  "[libcuckoo:%s:%d:%lu] " fmt ""                              \
                  "\x1b[0m",                                                   \
          __FILE__, __LINE__,                                                  \
          std::hash<std::thread::id>()(std::this_thread::get_id()),            \
          __VA_ARGS__)
#else
//! When \ref LIBCUCKOO_DEBUG is 0, LIBCUCKOO_DBG does nothing
#define LIBCUCKOO_DBG(fmt, ...)                                                \
  do {                                                                         \
  } while (0)
#endif

/**
 * alignas() requires GCC >= 4.9, so we stick with the alignment attribute for
 * GCC.
 */
#ifdef __GNUC__
#define LIBCUCKOO_ALIGNAS(x) __attribute__((aligned(x)))
#else
#define LIBCUCKOO_ALIGNAS(x) alignas(x)
#endif

/**
 * At higher warning levels, MSVC produces an annoying warning that alignment
 * may cause wasted space: "structure was padded due to __declspec(align())".
 */
#ifdef _MSC_VER
#define LIBCUCKOO_SQUELCH_PADDING_WARNING __pragma(warning(suppress : 4324))
#else
#define LIBCUCKOO_SQUELCH_PADDING_WARNING
#endif

/**
 * At higher warning levels, MSVC may issue a deadcode warning which depends on
 * the template arguments given. For certain other template arguments, the code
 * is not really "dead".
 */
#ifdef _MSC_VER
#define LIBCUCKOO_SQUELCH_DEADCODE_WARNING_BEGIN                               \
  do {                                                                         \
    __pragma(warning(push));                                                   \
    __pragma(warning(disable : 4702))                                          \
  } while (0)
#define LIBCUCKOO_SQUELCH_DEADCODE_WARNING_END __pragma(warning(pop))
#else
#define LIBCUCKOO_SQUELCH_DEADCODE_WARNING_BEGIN
#define LIBCUCKOO_SQUELCH_DEADCODE_WARNING_END
#endif

#define ERROR_NONE                         0
#define ERROR_INVALID_ARGUMENT             1
#define ERROR_OUT_OF_RANGE                 2
#define ERROR_HASHPOWER_CHANGED            3
#define ERROR_LOAD_FACTOR_TOO_LOW          4
#define ERROR_MAXIMUM_HASH_POWER_EXCEEDED  5

#endif // _CUCKOOHASH_UTIL_HH
