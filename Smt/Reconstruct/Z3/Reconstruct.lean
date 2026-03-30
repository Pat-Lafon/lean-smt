/-
Copyright (c) 2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lafontaine
-/

import Lean
import Z3
import Smt.Reconstruct.Z3.Ast

/-!
# Z3 Hint-Based Proof Reconstruction

Reconstructs proofs from Z3's theory inference hints using `grind`.

The approach:
1. Translate each theory lemma clause from Z3 ASTs to Lean propositions
2. Assert each as a hypothesis in the goal, verified by `grind`
3. Close the enriched goal with `grind`
-/

namespace Smt.Reconstruct.Z3

open Lean Meta

initialize registerTraceClass `smt.reconstruct.z3

/-- Classify a Z3 proof hint AST by its function name. -/
inductive HintKind where
  | assumption
  | del
  | rup
  | srup
  | tseitin
  | thLemma    -- Z3's "th-lemma" (theory lemma: arithmetic, EUF, etc.)
  | quantInst  -- Z3's "quant-inst" (quantifier instantiation)
  | smt        -- Z3's "smt" (general SMT reasoning)
  | andElim    -- Z3's "and-elim"
  | notOrElim  -- Z3's "not-or-elim"
  | defAxiom   -- Z3's "def-axiom" (Tseitin-like definitional axioms)
  | other (name : String)
deriving Repr

/-- Extract the hint kind from a Z3 proof hint AST. -/
def classifyHint (hint : Z3.Ast) : HintKind :=
  if Z3.Ast.getAstKind hint != .app then .other "non-app"
  else
    let fd := Z3.Ast.getFuncDecl hint
    let name := Z3.FuncDecl.getName fd
    match name with
    | "assumption"   => .assumption
    | "del"          => .del
    | "rup"          => .rup
    | "srup"         => .srup
    | "tseitin"      => .tseitin
    | "th-lemma"     => .thLemma
    | "quant-inst"   => .quantInst
    | "smt"          => .smt
    | "and-elim"     => .andElim
    | "not-or-elim"  => .notOrElim
    | "def-axiom"    => .defAxiom
    | other          => .other other

/-- Check if a hint kind represents a theory lemma that needs verification. -/
def HintKind.isTheoryLemma : HintKind → Bool
  | .thLemma | .quantInst | .smt | .defAxiom => true
  | _ => false

/-- Try to prove a goal using `grind`. Returns `true` if successful. -/
private def tryGrind (mv : MVarId) : MetaM Bool := do
  try
    let config : Grind.Config := { instances := 1000 }
    let params ← Grind.mkDefaultParams config
    let result ← Grind.main mv params
    return result.failure?.isNone
  catch _ =>
    return false

/-- Reconstruct a proof from Z3's theory inference hints.

Given the preprocessed goal `mv` and the collected theory clauses,
translate each clause to a Lean proposition, verify it with `grind`,
assert it as a hypothesis, and then close the enriched goal.

Returns the list of remaining (skipped) goals, if any. -/
def reconstructFromHints
    (mv : MVarId)
    (clauses : Array Z3.ClauseEvent)
    (userNames : Std.HashMap String Expr)
    : MetaM (List MVarId) := do
  trace[smt.reconstruct.z3] "reconstructing from {clauses.size} clause events"
  -- Phase 1: Filter for theory lemmas, translate and verify each
  let mut verifiedHints : Array (Expr × Expr) := #[]  -- (type, proof)
  let mut skippedGoals : List MVarId := []
  for clause in clauses do
    let hintKind := classifyHint clause.proofHint
    trace[smt.reconstruct.z3] "clause: kind={repr hintKind} lits={clause.literals.size}"
    -- Only process theory lemmas
    unless hintKind.isTheoryLemma do continue
    trace[smt.reconstruct.z3] "processing {repr hintKind} hint with {clause.literals.size} literals"
    try
      -- Translate clause literals to a Lean disjunction
      let clauseType ← translateClause clause.literals userNames
      trace[smt.reconstruct.z3] "translated clause type: {clauseType}"
      -- Create a fresh metavariable for this lemma
      let lemmaVar ← mkFreshExprMVar (some clauseType)
      let lemmaMV := lemmaVar.mvarId!
      -- Try to prove it with grind
      let proved ← tryGrind lemmaMV
      if proved then
        trace[smt.reconstruct.z3] "verified theory lemma"
        verifiedHints := verifiedHints.push (clauseType, lemmaVar)
      else
        trace[smt.reconstruct.z3] "could not verify theory lemma, skipping"
    catch e =>
      trace[smt.reconstruct.z3] "error translating/verifying hint: {e.toMessageData}"

  -- Phase 2: Assert verified hints into the goal context and close with grind
  trace[smt.reconstruct.z3] "asserting {verifiedHints.size} verified hints into goal"
  let mut currentMV := mv
  for (type, proof) in verifiedHints do
    currentMV ← currentMV.assert (← mkFreshId) type proof
    let (_, mv') ← currentMV.intro1
    currentMV := mv'

  -- Phase 3: Try to close the enriched goal
  trace[smt.reconstruct.z3] "closing enriched goal with grind"
  let closed ← tryGrind currentMV
  if closed then
    trace[smt.reconstruct.z3] "goal closed successfully"
    return skippedGoals
  else
    trace[smt.reconstruct.z3] "could not close goal"
    throwError "smt (solver := .z3): Z3 returned unsat but proof reconstruction failed. \
      Try using '+trust' to skip proof checking, or provide more hints."

end Smt.Reconstruct.Z3
