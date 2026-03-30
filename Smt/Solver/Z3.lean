import Lean
import Z3

namespace Smt.Solver.Z3

open Lean

/-- Result of a Z3 solver query. -/
inductive Result where
  | sat
  | unsat
  | unknown (reason : String)

/-- Result of a Z3 solver query with theory hint collection. -/
inductive HintResult where
  /-- Satisfiable. -/
  | sat
  /-- Unsatisfiable, with collected clause events from Z3's CDCL engine.
      Each `ClauseEvent` has a `proofHint` (identifying the theory rule),
      `deps` (dependency indices), and `literals` (clause disjuncts). -/
  | unsat (clauses : Array Z3.ClauseEvent)
  /-- Unknown, with a reason string. -/
  | unknown (reason : String)

/-- Run a Z3 solver on an SMT-LIB2 query string.
    Returns `sat`, `unsat`, or `unknown` with a reason.

    This uses Z3's FFI bindings to parse the SMT-LIB query,
    assert all formulas, and check satisfiability.

    The query string should contain SMT-LIB2 commands (set-logic,
    declare-const, assert, etc.) but NOT check-sat — that is
    handled internally by the solver. -/
def solve (query : String) (timeout : Option Nat) : MetaM Result := do
  let result ← show IO _ from Z3.Env.run do
    let ctx ← Z3.Context.newWithProofs
    let solver ← Z3.Solver.new ctx
    -- Set timeout via solver parameters if specified
    if let .some secs := timeout then
      let params ← Z3.Params.new ctx
      Z3.Params.setUInt params "timeout" (1000 * secs.toUInt32)
      Z3.Solver.setParams solver params
    -- Parse SMT-LIB2 query — this processes all declarations and
    -- returns the conjunction of all (assert ...) formulas
    let formula ← Z3.Context.parseSMTLIB2String ctx query
    Z3.Solver.assert solver formula
    -- Check satisfiability
    let res ← Z3.Solver.checkSat solver
    match res with
    | .false => return Result.unsat
    | .true  => return Result.sat
    | .undef =>
      let reason ← Z3.Solver.getReasonUnknown solver
      return Result.unknown reason
  return result

/-- Run a Z3 solver with clause event collection via `Z3_solver_register_on_clause`.

    Like `solve`, but registers an on-clause callback before solving. On unsat,
    returns the collected clause events which include theory inference hints
    (farkas, euf, bound, inst, etc.) that can be used for proof reconstruction.

    The callback collects ALL clause events during solving. Filtering for
    theory-relevant hints is done on the Lean side. -/
def solveWithHints (query : String) (timeout : Option Nat) : MetaM HintResult := do
  let result ← show IO _ from Z3.Env.run do
    let ctx ← Z3.Context.newWithProofs
    let solver ← Z3.Solver.new ctx
    -- Set timeout via solver parameters if specified
    if let .some secs := timeout then
      let params ← Z3.Params.new ctx
      Z3.Params.setUInt params "timeout" (1000 * secs.toUInt32)
      Z3.Solver.setParams solver params
    -- Parse SMT-LIB2 query
    let formula ← Z3.Context.parseSMTLIB2String ctx query
    Z3.Solver.assert solver formula
    -- Register on-clause callback before solving
    let handle ← Z3.Solver.registerOnClause solver
    -- Check satisfiability
    let res ← Z3.Solver.checkSat solver
    match res with
    | .false =>
      let clauses ← Z3.OnClauseHandle.getClauses handle
      return HintResult.unsat clauses
    | .true => return HintResult.sat
    | .undef =>
      let reason ← Z3.Solver.getReasonUnknown solver
      return HintResult.unknown reason
  return result

end Smt.Solver.Z3
