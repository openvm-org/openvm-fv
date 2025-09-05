structure MinimalInstruction (F: Type) where
  is_valid : F
  opcode: F

structure AdapterAirContext (F: Type) where
  to_pc : Option F
  reads : Fin 2 → Fin 4 → F
  writes : Fin 4 → F
  instruction : MinimalInstruction F
