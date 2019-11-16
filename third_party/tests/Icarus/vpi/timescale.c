#include "veriuser.h"

static int
mytest(char *data)
{
    int ht, lt;
    char *cp;
    char *inst = tf_getinstance();
    char *name = tf_spname();

    io_printf("Module %s\n", name);

    lt = tf_gettime();
    io_printf("\ttf_gettime()\t\t\t-> %d\n", lt);

    cp = tf_strgettime();
    io_printf("\ttf_strgettime()\t\t\t-> %s\n", cp);

    lt = tf_getlongtime(&ht);
    io_printf("\ttf_getlongtime()\t\t-> %d/%d\n", ht, lt);

    lt = tf_igetlongtime(&ht, inst);
    io_printf("\ttf_igetlongtime(inst)\t\t-> %d/%d\n", ht, lt);
    
    lt = tf_gettimeprecision();
    io_printf("\ttf_gettimeprecision()\t\t-> %d\n", lt);

    lt = tf_igettimeprecision(inst);
    io_printf("\ttf_igettimeprecision(inst)\t-> %d\n", lt);
    
    lt = tf_gettimeunit();
    io_printf("\ttf_gettimeunit()\t\t-> %d\n", lt);

    lt = tf_igettimeunit(inst);
    io_printf("\ttf_gettimeunit(inst)\t\t-> %d\n", lt);

    lt = tf_igettimeunit(0);
    io_printf("\ttf_gettimeunit(0)\t\t-> %d\n", lt);

    return 0;
}

static int return_32() { return 32; }

s_tfcell veriusertfs[2] = {
  { usertask, 0, 0, return_32, mytest, 0, "$mytest", 1},
  {0, 0, 0, 0, 0, 0, 0, 0}
};

// Icarus registration
p_tfcell icarus_veriusertfs(void) {
    return veriusertfs;
}

  // Icarus Verilog compatibility
static void veriusertfs_register(void)
{
      veriusertfs_register_table(veriusertfs);
}

void (*vlog_startup_routines[])() = { &veriusertfs_register, 0 };
