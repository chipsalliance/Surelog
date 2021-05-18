#!/bin/sh
echo "#if defined(__powerpc__)
echo -n ARCH_POWERPC
#elif defined(__x86_64__) || defined(__i386__)
echo -n ARCH_X86
#elif defined(__arm__)
echo -n ARCH_ARM
#else
echo -n ARCH_UNKNOWN
#endif" | $1cpp | /bin/sh

