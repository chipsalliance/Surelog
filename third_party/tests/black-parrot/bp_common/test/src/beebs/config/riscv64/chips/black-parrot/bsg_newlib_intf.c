#include <stdlib.h>
#include <machine/dramfs_fs.h>

extern int putchar(int c);

void dramfs_init(void) {
  if(dramfs_fs_init() < 0) {
    exit(-1);
  }
}

void dramfs_exit(int exit_status) {
  exit(exit_status);
}

void dramfs_sendchar(char ch) {
  putchar((int)ch);
}
