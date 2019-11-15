/*
 * Copyright (c) 2001 Picture Elements, Inc.
 *    Stephen Williams (steve@picturel.com)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version. In order to redistribute the software in
 *    binary form, you will need a Picture Elements Binary Software
 *    License.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 *  ---
 *    You should also have recieved a copy of the Picture Elements
 *    Binary Software License offer along with the source. This offer
 *    allows you to obtain the right to redistribute the software in
 *    binary (compiled) form. If you have not received it, contact
 *    Picture Elements, Inc., 777 Panoramic Way, Berkeley, CA 94704.
 */
#ident "$Id: putp2.c,v 1.1 2003/06/26 03:21:33 stevewilliams Exp $"

#include "veriuser.h"

static int calltf(int user_data, int reason)
{
    char *inst = tf_getinstance();

    tf_putp (0, tf_getp(1));

    return 0;
}

static int sizetf(int user_data, int reason) { return 32; }

s_tfcell veriusertfs[2] = {
  {userfunction,
   0,
   0,
   sizetf,
   calltf,
   0,
   "$copy_test",
   1
  },
  {0, 0, 0, 0, 0, 0, 0, 0}
};

static void veriusertfs_register(void)
{
      veriusertfs_register_table(veriusertfs);
}

void (*vlog_startup_routines[])() = { &veriusertfs_register, 0 };

/*
 * $Log: putp2.c,v $
 * Revision 1.1  2003/06/26 03:21:33  stevewilliams
 *  Add putp2 test
 *
 */

