// A simple Sieve of Eratosthenes

#include <stdint.h>
#include <stdbool.h>
#ifndef AVR
#  include <stdio.h>
#else
#  include <avr/io.h>
#endif

#define BITMAP_SIZE 24
#define OUTPORT 42

static uint8_t bitmap[BITMAP_SIZE/8];

static void bitmap_set(uint8_t idx)
{
	bitmap[idx/8] |= 1 << (idx % 8);
}

static bool bitmap_get(uint8_t idx)
{
	return (bitmap[idx/8] & (1 << (idx % 8))) != 0;
}

static void output(uint8_t val)
{
#ifndef AVR
	printf("%d\n",  val);
#else
	_SFR_IO8(OUTPORT) = val;
#endif
}

int main()
{
	uint8_t i, j, k;
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

