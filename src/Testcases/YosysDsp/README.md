# DSP Filters - a selection of digital filters from @ZipCPU

Source: https://github.com/ZipCPU/dspfilters/tree/49b9a0235f88c34b9a997b1aa9a634ad130ea719

Currently three designs exist:

- **fastfir_fixedtaps** A 1-output per clock finite impulse response (FIR) filter,
  configured as a 12-bit 128-tap band-pass filter.

- **slowfil_fixedtaps** A 1-output per number-of-taps clocks finite impulse response 
  (FIR) filter, configured as a 12-bit 128-tap band-pass filter. This original variant 
  uses a ring-buffer to store all input samples.

- **slowfil_srl_fixedtaps** A 1-output per number-of-taps clocks finite impulse
  response (FIR) filter, configured as a 12-bit 128-tap band-pass filter. This is a
  modified variant of the original slowfil that uses a shift-register approach to
  store all input samples.

The 12-bit 128-tap band pass filter has the following performance characteristics:
- 0-200Hz: -119.27dB
- 300-500Hz: 0.00dB
- 600-1000Hz: -119.27dB
coefficients generated using http://t-filter.engineerjs.com
