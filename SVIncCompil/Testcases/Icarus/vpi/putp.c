#include "veriuser.h"

static int
calltf(char *data)
{
    char *inst = tf_getinstance();

    tf_putp (0, 69);
    tf_putp (1, 11);
    tf_iputp(2, 22, inst);
    tf_putp(99, 99);

    tf_putrealp (3, 3.3);
    tf_iputrealp(4, 4.4, inst);
    tf_putrealp(99, 9.9);

    return 0;
}

static int sizetf() { return 32; }

s_tfcell veriusertfs[2] = {
  {userfunction, 0, 0, sizetf, calltf, 0, "$mytest", 1},
  {0, 0, 0, 0, 0, 0, 0, 0}
};

static void veriusertfs_register(void)
{
      veriusertfs_register_table(veriusertfs);
}

void (*vlog_startup_routines[])() = { &veriusertfs_register, 0 };
