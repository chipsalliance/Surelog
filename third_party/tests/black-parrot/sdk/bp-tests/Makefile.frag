BP_TESTS_C = \
  hello_world           \
  bubblesort_demo       \
  streaming_accelerator_demo \
  streaming_accelerator_zipline\
  coherent_accelerator_demo\
  copy_example          \
  mc_sanity_1           \
  mc_sanity_2           \
  mc_sanity_3           \
  mc_sanity_4           \
  mc_sanity_6           \
  mc_sanity_8           \
  mc_sanity_12          \
  mc_sanity_16          \
  mc_template_1         \
  mc_template_2         \
  mc_rand_walk_1        \
  mc_rand_walk_2        \
  mc_rand_walk_3        \
  mc_rand_walk_4        \
  mc_rand_walk_6        \
  mc_rand_walk_8        \
  mc_rand_walk_12       \
  mc_rand_walk_16       \
  mc_work_share_sort_1  \
  mc_work_share_sort_2  \
  mc_work_share_sort_3  \
  mc_work_share_sort_4  \
  mc_work_share_sort_6  \
  mc_work_share_sort_8  \
  mc_work_share_sort_12 \
  mc_work_share_sort_16 \
  cache_hammer          \
  jalr_illegal          \
  satp_nofence          \
  timer_interrupt_test  \
  loop_test             \
  cache_flush           \
  stream_hammer         \
  domain_fault          \
  eaddr_fault           \
  paging                \
  mapping               \
  mstatus_fs            \
  wfi_test              \
  uncached_mode_test    \
  amo_nonblocking       \
  amo_interrupt         \

BP_TESTS_CPP = \
  virtual               \
  constructor           \
  template              \
  unwinding             \
  vector                \
  map

BP_TESTS = $(BP_TESTS_C) $(BP_TESTS_CPP)

