import OpenvmFv.Airs.LessThanAuxCols

set_option linter.unusedVariables false

#define_air "MemoryBaseAuxCols" using "openvm_encapsulation" where
  Column["prev_timestamp"]
  SubAir["timestamp_lt_aux": "LessThanAuxCols_2" width := 2]

#define_air "MemoryReadAuxCols" using "openvm_encapsulation" where
  SubAir["base": "MemoryBaseAuxCols" width := 3]

#define_air "MemoryWriteAuxCols_4" using "openvm_encapsulation" where
  SubAir["base": "MemoryBaseAuxCols" width := 3]
  Column["prev_data_0"]
  Column["prev_data_1"]
  Column["prev_data_2"]
  Column["prev_data_3"]
