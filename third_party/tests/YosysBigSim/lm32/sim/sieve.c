// A simple Sieve of Eratosthenes

#ifdef TESTBENCH
#  include <stdint.h>
#  include <stdbool.h>
#  include <stdio.h>
#else
   typedef unsigned int uint32_t;
   typedef unsigned char bool;
#endif

#define BITMAP_SIZE 64
#define OUTPORT 0xff000004

static uint32_t bitmap[BITMAP_SIZE/32];

static void bitmap_set(uint32_t idx)
{
	bitmap[idx/32] |= 1 << (idx % 32);
}

static bool bitmap_get(uint32_t idx)
{
	return (bitmap[idx/32] & (1 << (idx % 32))) != 0;
}

static void output(uint32_t val)
{
#ifdef TESTBENCH
	printf("%d\n", (int)val);
#else
	*((volatile uint32_t*)OUTPORT) = val;
#endif
}

int main()
{
	uint32_t i, j, k;
	output(2);
	for (i = 0; i < BITMAP_SIZE; i++) {
		if (bitmap_get(i))
			continue;
		output(3+2*i);
		for (j = 2*(3+2*i);; j += 3+2*i) {
			if (j%2 == 0)
				continue;
			k = (j-3)/2;
			if (k >= BITMAP_SIZE)
				break;
			bitmap_set(k);
		}
	}
	return 0;
}

