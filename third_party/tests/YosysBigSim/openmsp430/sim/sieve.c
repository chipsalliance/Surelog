// A simple Sieve of Eratosthenes

#include <stdint.h>
#include <stdbool.h>
#ifndef MSP430
#  include <stdio.h>
#endif

#define BITMAP_SIZE 64
#define OUTPORT 0x0100

static uint16_t bitmap[BITMAP_SIZE/16];

static void bitmap_set(uint16_t idx)
{
	bitmap[idx/16] |= 1 << (idx % 16);
}

static bool bitmap_get(uint16_t idx)
{
	return (bitmap[idx/16] & (1 << (idx % 16))) != 0;
}

static void output(uint16_t val)
{
#ifndef MSP430
	printf("%d\n",  val);
#else
	*((volatile uint16_t*)OUTPORT) = val;
#endif
}

int main()
{
	uint16_t i, j, k;
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
	output(0);
	return 0;
}

