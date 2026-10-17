/* The module tests fill arena allocations so an unwritten field cannot
   depend on fresh heap pages containing zero bytes. */
#undef malloc
#include <stdlib.h>
#include <string.h>

void *ledger_test_malloc(size_t size) {
  void *memory = malloc(size);
  if (memory != NULL) memset(memory, 0xa5, size);
  return memory;
}
