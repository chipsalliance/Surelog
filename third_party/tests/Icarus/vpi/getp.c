#include "veriuser.h"

static int
calltf(char *data)
{
    int i;
    char *inst = tf_getinstance();

    for (i = 1; i < 5; i++) {
	io_printf("tf_getp(%d)\t\t-> %d\n", i, tf_getp(i));
	io_printf("tf_igetp(%d,inst)\t-> %d\n", i, tf_igetp(i,inst));
	io_printf("tf_getrealp(%d)\t\t-> %f\n", i, tf_getrealp(i));
	io_printf("tf_igetrealp(%d,inst)\t-> %f\n",
	    i, tf_igetrealp(i,inst));
    }

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
