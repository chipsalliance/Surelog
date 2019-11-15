#include "veriuser.h"

static int
calltf(char *data)
{
    char *inst = tf_getinstance();

    io_printf("tf_mipname()\t\t-> %s\n", tf_mipname());
    io_printf("tf_imipname(inst)\t-> %s\n", tf_imipname(inst));

    return 0;
}

static int sizetf() { return 32; }

s_tfcell veriusertfs[2] = {
  {usertask, 0, 0, sizetf, calltf, 0, "$mytest", 1},
  {0, 0, 0, 0, 0, 0, 0, 0}
};


static void veriusertfs_register(void)
{
      veriusertfs_register_table(veriusertfs);
}

void (*vlog_startup_routines[])() = { &veriusertfs_register, 0 };
