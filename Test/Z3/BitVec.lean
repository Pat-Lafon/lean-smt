import Smt

-- === BitVec basics ===

-- XOR commutativity
theorem z3_bv_xor_comm (x y : BitVec 8) : x ^^^ y = y ^^^ x := by
  smt (solver := .z3)

-- AND commutativity
theorem z3_bv_and_comm (x y : BitVec 8) : x &&& y = y &&& x := by
  smt (solver := .z3)

-- OR commutativity
theorem z3_bv_or_comm (x y : BitVec 8) : x ||| y = y ||| x := by
  smt (solver := .z3)

-- Addition commutativity
theorem z3_bv_add_comm (x y : BitVec 8) : x + y = y + x := by
  smt (solver := .z3)

-- Self-XOR is zero
theorem z3_bv_xor_self (x : BitVec 8) : x ^^^ x = 0 := by
  smt (solver := .z3)

-- Self-AND is identity
theorem z3_bv_and_self (x : BitVec 8) : x &&& x = x := by
  smt (solver := .z3)

-- Self-OR is identity
theorem z3_bv_or_self (x : BitVec 8) : x ||| x = x := by
  smt (solver := .z3)

-- Verify all proofs are sorry-free
#print axioms z3_bv_xor_comm
#print axioms z3_bv_and_comm
#print axioms z3_bv_or_comm
#print axioms z3_bv_add_comm
#print axioms z3_bv_xor_self
#print axioms z3_bv_and_self
#print axioms z3_bv_or_self
