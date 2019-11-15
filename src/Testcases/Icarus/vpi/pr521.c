#include <vpi_user.h>
#include <veriuser.h>

char *veriuser_version_str = "Test PLI v0.1 ";

static int pli_test()
{
   int a;
   a = tf_getp(1);
   printf ("PLI Parameter received 0x%x\n",a);
   return 0;
}
   
static int return_32()
{
  return (32);
}


static s_tfcell veriusertfs[] = {
  {userfunction, 0, 0, return_32, pli_test, 0, "$pli_test", 1},
  /* all entry must be entered before this line */
  {0, 0, 0, 0, 0, 0, 0, 0}  /* this must be the last entry */
};

static void veriusertfs_register(void) {
	veriusertfs_register_table(veriusertfs);
}

void (*vlog_startup_routines[])() = { &veriusertfs_register, 0 };
