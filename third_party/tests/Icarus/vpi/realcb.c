/*
 * Copyright (c) 2003 Stephen Williams (steve@icarus.com)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */
#ifdef HAVE_CVS_IDENT
#ident "$Id: realcb.c,v 1.1 2003/02/10 05:14:13 stevewilliams Exp $"
#endif

/*
 * This program tests change callbacks on real variables.
 */
# include  <vpi_user.h>
# include  <assert.h>

static int watchreal_cb(p_cb_data cb)
{
      s_vpi_value value;
      vpiHandle arg = (vpiHandle) (cb->user_data);

      value.format = vpiRealVal;
      vpi_get_value(arg, &value);
      assert(value.format == vpiRealVal);

      vpi_printf("watchreal: %s = %f\n",
		 vpi_get_str(vpiName, arg),
		 value.value.real);

      return 0;
}

static int my_watchreal_calltf(char *xx)
{
      struct t_cb_data cb;
      struct t_vpi_time time;

      vpiHandle sys = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, sys);

      vpiHandle arg;

      time.type = vpiSimTime;
      time.low = 0;
      time.high = 0;

      while (0 != (arg = vpi_scan(argv))) {

	    assert(vpi_get(vpiType, arg) == vpiRealVar);

	    cb.reason = cbValueChange;
	    cb.cb_rtn = watchreal_cb;
	    cb.time = &time;
	    cb.obj = arg;
	    cb.user_data = (char*)arg;
	    vpi_register_cb(&cb);

      }

      return 0;
}

static void my_watchreal_register()
{
      s_vpi_systf_data tf_data;

      tf_data.type      = vpiSysTask;
      tf_data.tfname    = "$my_watchreal";
      tf_data.calltf    = my_watchreal_calltf;
      tf_data.compiletf = 0;
      tf_data.sizetf    = 0;
      vpi_register_systf(&tf_data);

}

void (*vlog_startup_routines[])() = {
      my_watchreal_register,
      0
};

/*
 * $Log: realcb.c,v $
 * Revision 1.1  2003/02/10 05:14:13  stevewilliams
 *  Add the vpi/realcb test.
 *
 */

