/-
Copyright (c) 2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lafontaine
-/

import Lean
import Std.Tactic.BVDecide
import Z3
import Smt.Reconstruct.Z3.Ast
import Smt.Util

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
  | mp         -- Z3's "mp" (modus ponens)
  | mpTilde    -- Z3's "mp~" (modus ponens variant)
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
    | "mp"           => .mp
    | "mp~"          => .mpTilde
    | other          => .other other

/-- Check if a hint kind represents a clause that should be processed as a hint. -/
def HintKind.isProcessable : HintKind → Bool
  | .thLemma | .quantInst | .smt | .defAxiom | .mp | .mpTilde => true
  | _ => false

/-- Check if a name is a user-defined inductive suitable for grind case splitting.
    Uses `Smt.Util.isSmtDatatype` (module-based check) and also excludes
    types that grind already handles natively. -/
private def isCustomInductive (nm : Name) : MetaM Bool := do
  if Grind.isBuiltinEagerCases nm then return false
  return Smt.Util.isSmtDatatype (← getEnv) nm

/-- Check if an inductive is a finite, non-recursive type suitable for
    transitive case splitting discovery (enums and simple structures).
    Excludes recursive types like Nat, Int, List, Tree, etc. -/
private def isFiniteInductive (nm : Name) : MetaM Bool := do
  if !(← isCustomInductive nm) then return false
  let env ← getEnv
  let some (.inductInfo iv) := env.find? nm | return false
  -- Check no constructor has a recursive argument (field of type nm)
  for ctorNm in iv.ctors do
    let ctorInfo ← getConstInfo ctorNm
    let hasRecursive ← Meta.forallTelescopeReducing ctorInfo.type fun args _ => do
      for arg in args do
        let argTy ← Meta.inferType arg
        if argTy.getAppFn.isConstOf nm then
          return true
      return false
    if hasRecursive then return false
  return true

/-- Collect non-builtin inductive type names from local context variables,
    including inductive types that appear as fields of collected datatypes. -/
private def collectDatatypeNames (mv : MVarId) : MetaM (Array Name) := do
  let lctx ← mv.getDecl >>= fun d => pure d.lctx
  let mut result : Array Name := #[]
  -- Phase 1: collect from local context variable types
  for decl in lctx do
    if decl.isAuxDecl then continue
    let ty ← mv.withContext (Meta.whnf decl.type)
    let tyOfTy ← mv.withContext (Meta.inferType ty)
    unless tyOfTy.isSort && !tyOfTy.isProp do continue
    let head := ty.getAppFn
    if let .const nm _ := head then
      if ← isFiniteInductive nm then
        unless result.contains nm do
          result := result.push nm
  -- Phase 2: transitively collect inductive types from constructor fields
  let env ← getEnv
  let mut i := 0
  while i < result.size do
    let nm := result[i]!
    if let some (.inductInfo iv) := env.find? nm then
      for ctorNm in iv.ctors do
        let ctorInfo ← getConstInfo ctorNm
        let fieldNames ← Meta.forallTelescopeReducing ctorInfo.type fun args _ => do
          let mut names : Array Name := #[]
          for arg in args do
            let argTy ← Meta.inferType arg
            let argHead := argTy.getAppFn
            if let .const fieldNm _ := argHead then
              if ← isFiniteInductive fieldNm then
                names := names.push fieldNm
          return names
        for fieldNm in fieldNames do
          unless result.contains fieldNm do
            result := result.push fieldNm
    i := i + 1
  return result

/-- Try to prove a goal using `grind`, registering any custom datatypes
    in the goal context for case splitting via `@[grind cases]`. -/
private def tryGrind (mv : MVarId) : MetaM Bool := do
  try
    let config : Grind.Config := { instances := 1000 }
    let defaultExt ← Grind.getDefaultExtensionState
    -- Register custom datatypes for eager case splitting
    let dtNames ← collectDatatypeNames mv
    let mut casesTypes := defaultExt.casesTypes
    for nm in dtNames do
      trace[smt.reconstruct.z3] "registering {nm} for grind case splitting"
      casesTypes := casesTypes.insert nm true  -- eager
    let ext : Grind.ExtensionState := { defaultExt with casesTypes }
    let params ← Grind.mkParams config #[ext]
    let result ← Grind.main mv params
    return result.failure?.isNone
  catch _ =>
    return false

/-- Try to prove a goal using `bv_decide`. Returns `true` if successful. -/
private def tryBvDecide (mv : MVarId) : MetaM Bool := do
  try
    let remainingGoals ← Lean.Elab.Term.TermElabM.run' do
      Lean.Elab.Tactic.run mv do
        Lean.Elab.Tactic.evalTactic (← `(tactic| bv_decide))
    return remainingGoals.length == 0
  catch _ =>
    return false

/-- Collect `(a, b)` pairs from Int div (`HDiv.hDiv`) and mod (`HMod.hMod`) subexpressions. -/
private def collectIntDivModPairs (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let rec visit (e : Expr) : MetaM (Array (Expr × Expr)) := do
    let mut acc := #[]
    -- Check for HDiv.hDiv α β γ inst a b (6 args) or HMod.hMod α β γ inst a b
    if e.isAppOf ``HDiv.hDiv && e.getAppNumArgs == 6 then
      let args := e.getAppArgs
      let ty ← inferType args[4]!
      if ty.isConstOf ``Int then
        acc := acc.push (args[4]!, args[5]!)
    if e.isAppOf ``HMod.hMod && e.getAppNumArgs == 6 then
      let args := e.getAppArgs
      let ty ← inferType args[4]!
      if ty.isConstOf ``Int then
        acc := acc.push (args[4]!, args[5]!)
    match e with
    | .app f arg =>
      acc := acc ++ (← visit f)
      acc := acc ++ (← visit arg)
    | .lam _ ty body _ =>
      acc := acc ++ (← visit ty)
      acc := acc ++ (← visit body)
    | .forallE _ ty body _ =>
      acc := acc ++ (← visit ty)
      acc := acc ++ (← visit body)
    | .letE _ ty val body _ =>
      acc := acc ++ (← visit ty)
      acc := acc ++ (← visit val)
      acc := acc ++ (← visit body)
    | .mdata _ e => acc := acc ++ (← visit e)
    | _ => pure ()
    return acc
  let raw ← visit e
  -- Deduplicate
  let mut seen : Array (Expr × Expr) := #[]
  for p in raw do
    unless seen.any (fun (a, b) => a == p.1 && b == p.2) do
      seen := seen.push p
  return seen

/-- Assert a lemma as a hypothesis in the goal. Returns the new goal MVar. -/
private def assertLemma (mv : MVarId) (proof : Expr) : MetaM MVarId := do
  let ty ← inferType proof
  let mv' ← mv.assert (← mkFreshId) ty proof
  let (_, mv'') ← mv'.intro1
  return mv''

/-- If the goal mentions Int div/mod, assert key lemmas as hypotheses so `grind` can use them.
    Returns the (possibly enriched) goal MVar. -/
private def enrichWithDivModLemmas (mv : MVarId) : MetaM MVarId := do
  let goalType ← mv.getType
  let pairs ← mv.withContext (collectIntDivModPairs goalType)
  if pairs.isEmpty then return mv
  trace[smt.reconstruct.z3] "found {pairs.size} Int div/mod pairs, asserting lemmas"
  let mut currentMV := mv
  for (a, b) in pairs do
    currentMV ← currentMV.withContext do
      -- Int.mul_ediv_add_emod a b : b * (a / b) + a % b = a  (unconditional)
      let proof ← mkAppM ``Int.mul_ediv_add_emod #[a, b]
      assertLemma currentMV proof
    currentMV ← currentMV.withContext do
      -- Int.emod_neg a b : a % (-b) = a % b  (unconditional)
      let proof ← mkAppM ``Int.emod_neg #[a, b]
      assertLemma currentMV proof
    -- b ≠ 0 → 0 ≤ a % b
    currentMV ← currentMV.withContext do
      let bNeZero ← mkAppM ``Ne #[b, toExpr (0 : Int)]
      let modNonneg ← mkAppM ``LE.le #[toExpr (0 : Int), ← mkAppM ``HMod.hMod #[a, b]]
      let implication ← mkArrow bNeZero modNonneg
      let proofMV ← mkFreshExprMVar (some implication)
      let introMV := proofMV.mvarId!
      let (fvarId, bodyMV) ← introMV.intro `hb
      let proof ← bodyMV.withContext do
        mkAppM ``Int.emod_nonneg #[a, .fvar fvarId]
      bodyMV.assign proof
      assertLemma currentMV proofMV
    -- 0 < b → a % b < b
    currentMV ← currentMV.withContext do
      let bPos ← mkAppM ``LT.lt #[toExpr (0 : Int), b]
      let modLt ← mkAppM ``LT.lt #[← mkAppM ``HMod.hMod #[a, b], b]
      let implication ← mkArrow bPos modLt
      let proofMV ← mkFreshExprMVar (some implication)
      let introMV := proofMV.mvarId!
      let (fvarId, bodyMV) ← introMV.intro `hb
      let proof ← bodyMV.withContext do
        mkAppM ``Int.emod_lt_of_pos #[a, .fvar fvarId]
      bodyMV.assign proof
      assertLemma currentMV proofMV
    -- 0 < -b → a % (-b) < -b
    currentMV ← currentMV.withContext do
      let negB ← mkAppM ``Neg.neg #[b]
      let negBPos ← mkAppM ``LT.lt #[toExpr (0 : Int), negB]
      let modNegB ← mkAppM ``HMod.hMod #[a, negB]
      let modLtNegB ← mkAppM ``LT.lt #[modNegB, negB]
      let implication ← mkArrow negBPos modLtNegB
      let proofMV ← mkFreshExprMVar (some implication)
      let introMV := proofMV.mvarId!
      let (fvarId, bodyMV) ← introMV.intro `hb
      let proof ← bodyMV.withContext do
        mkAppM ``Int.emod_lt_of_pos #[a, .fvar fvarId]
      bodyMV.assign proof
      assertLemma currentMV proofMV
  return currentMV

/-- Try to prove a goal: enrich with div/mod lemmas if needed, then `grind`
    (with datatype case splitting), then `bv_decide`. -/
private def tryProve (mv : MVarId) : MetaM Bool := do
  -- Enrich with div/mod lemmas if the goal mentions Int div/mod
  let mv ← try enrichWithDivModLemmas mv catch _ => pure mv
  -- Try grind on a defensive copy (grind may partially assign the MVar on failure)
  let s ← saveState
  if ← tryGrind mv then return true
  restoreState s
  trace[smt.reconstruct.z3] "grind failed, trying bv_decide"
  tryBvDecide mv

/-- Check if a Z3 AST contains Skolem function references (names with `!`). -/
private partial def hasSkolem (a : Z3.Ast) : Bool :=
  match Z3.Ast.getAstKind a with
  | .app =>
    let fd := Z3.Ast.getFuncDecl a
    let name := Z3.FuncDecl.getName fd
    if name.any (· == '!') then true
    else Z3.Ast.getArgs a |>.any hasSkolem
  | .quantifier => hasSkolem (Z3.Ast.getQuantifierBody a)
  | _ => false

/-- Collect all Skolem function names from a Z3 AST. -/
private partial def collectSkolemNames (a : Z3.Ast) : Array String :=
  match Z3.Ast.getAstKind a with
  | .app =>
    let fd := Z3.Ast.getFuncDecl a
    let name := Z3.FuncDecl.getName fd
    let fromArgs := Z3.Ast.getArgs a |>.foldl (init := #[]) fun acc arg =>
      acc ++ collectSkolemNames arg
    if name.any (· == '!') then #[name] ++ fromArgs else fromArgs
  | .quantifier => collectSkolemNames (Z3.Ast.getQuantifierBody a)
  | _ => #[]

/-- Strip the `!N` suffix from a Skolem function name to get the original binder name.
    E.g., `"r0!1"` → `"r0"`, `"r1!0"` → `"r1"`. -/
private def skolemBaseName (name : String) : String :=
  match name.splitOn "!" with
  | base :: _ => base
  | [] => name

/-- Given a hypothesis `h : ∃ x₁ x₂ ... xₙ, P x₁ ... xₙ` in the context of `mv`,
    destructure it into witness FVars and property hypotheses. Returns:
    - The updated MVar (with witnesses and properties in context)
    - The witness names and FVarIds (corresponding to the existential binders) -/
private partial def destructureExistsHyp (mv : MVarId) (hFVar : FVarId)
    : MetaM (MVarId × Array (String × FVarId)) := do
  mv.withContext do
  let hType ← whnf (← inferType (.fvar hFVar))
  if !hType.isAppOfArity ``Exists 2 then
    return (mv, #[])
  -- Get the binder name from the Exists body (fun x => ...)
  let body := hType.getAppArgs[1]!
  let binderName := match body with
    | .lam n _ _ _ => n.toString
    | _ => "w"
  -- Use Exists.choose and Exists.choose_spec to destructure
  let witness ← mkAppM ``Exists.choose #[.fvar hFVar]
  let witnessTy ← inferType witness
  let spec ← mkAppM ``Exists.choose_spec #[.fvar hFVar]
  let specTy ← inferType spec
  -- Assert witness and spec into context
  let mv' ← mv.assert binderName.toName witnessTy witness
  let (witFv, mv') ← mv'.intro1
  let mv' ← mv'.assert (binderName ++ "_spec").toName specTy spec
  let (specFv, mv') ← mv'.intro1
  -- Recurse if the spec is another existential
  let (mv'', innerWitnesses) ← destructureExistsHyp mv' specFv
  return (mv'', #[(binderName, witFv)] ++ innerWitnesses)

/-- Information extracted from a Z3 quantifier instantiation clause. -/
structure QuantInstInfo where
  /-- The negated ground literals from the mp clause (translated to Lean).
      These are the preconditions that identify instantiation arguments. -/
  groundLiterals : Array Expr
  /-- The Z3 AST of the quantified formula (literal 0, before negation). -/
  quantAst : Z3.Ast

/-- Extract quantifier instantiation info from mp clauses.
    For an mp clause like:
      lit0: ¬(∀ t res, ...)    -- the axiom (may have Skolems in body)
      lit1: ¬(is_node t0)      -- ground precondition (no Skolems)
      lit2: ¬(depth t0 res)    -- ground precondition (no Skolems)
      lit3: ¬(...)              -- conclusion (has Skolems)
    We extract the non-Skolem ground literals and the quantified formula. -/
private def extractQuantInstInfos
    (clauses : Array Z3.ClauseEvent)
    (userNames : Std.HashMap String Expr)
    : MetaM (Array QuantInstInfo) := do
  let mut result : Array QuantInstInfo := #[]
  for clause in clauses do
    let hintKind := classifyHint clause.proofHint
    -- Only look at mp clauses with ≥ 3 literals
    unless hintKind matches .mp | .mpTilde do continue
    unless clause.literals.size >= 3 do continue
    let some lit0 := clause.literals[0]? | continue
    -- Check if literal 0 is a negated quantifier (¬∀...)
    -- In Z3's representation, this is (not (forall ...))
    if Z3.Ast.getAstKind lit0 != .app then continue
    if Z3.FuncDecl.getDeclKind (Z3.Ast.getFuncDecl lit0) != .not then continue
    let notArgs := Z3.Ast.getArgs lit0
    let some innerAst := notArgs[0]? | continue
    if Z3.Ast.getAstKind innerAst != .quantifier then continue
    let quantAst := innerAst
    -- Try to translate the non-Skolem ground literals (lit1..lit_{n-1})
    let mut groundLits : Array Expr := #[]
    for i in [1:clause.literals.size] do
      let some lit := clause.literals[i]? | continue
      if hasSkolem lit then continue
      -- This literal is a negated ground fact. Translate it.
      -- It's of the form ¬P, so translate and extract P.
      try
        let litExpr ← translateAst lit userNames
        -- litExpr is `¬P`, extract P
        if let some p := litExpr.not? then
          groundLits := groundLits.push p
        else
          groundLits := groundLits.push litExpr
      catch _ => continue
    if groundLits.size > 0 then
      trace[smt.reconstruct.z3] "extracted {groundLits.size} ground literals from mp clause"
      result := result.push { groundLiterals := groundLits, quantAst }
  return result

/-- Try to match a QuantInstInfo against a hypothesis. Returns the hypothesis
    if its quantifier prefix matches the Z3 quantified formula. -/
private def matchHypothesis (info : QuantInstInfo) (hyps : Array Expr)
    (userNames : Std.HashMap String Expr) : MetaM (Option Expr) := do
  -- Extract quantifier bound variable sorts from the Z3 AST
  let numBound := Z3.Ast.getQuantifierNumBound info.quantAst
  let mut z3Sorts : Array Expr := #[]
  for i in [:numBound.toNat] do
    try
      let sort := Z3.Ast.getQuantifierBoundSort info.quantAst i.toUInt32
      let leanSort ← translateSort sort userNames
      z3Sorts := z3Sorts.push leanSort
    catch _ => continue
  -- Try to match against each hypothesis
  for hyp in hyps do
    let hypType ← inferType hyp
    -- Count the number of leading ∀ binders and check if sorts match
    let matched ← forallTelescopeReducing hypType fun args _ => do
      if args.size < numBound.toNat then return false
      -- Check if the first numBound sorts match
      let mut allMatch := true
      for i in [:numBound.toNat] do
        if h : i < z3Sorts.size then
          let argType ← inferType args[i]!
          unless ← isDefEq argType z3Sorts[i] do
            allMatch := false
            break
      return allMatch
    if matched then
      trace[smt.reconstruct.z3] "matched hypothesis: {hyp}"
      return some hyp
  return none

/-- Reconstruct a proof from Z3's theory inference hints.

Given the goal `mv` and the collected theory clauses,
translate each clause to a Lean proposition, verify it with `grind`,
assert it as a hypothesis, and then close the enriched goal.

Returns the list of remaining (skipped) goals, if any. -/
def reconstructFromHints
    (mv : MVarId)
    (clauses : Array Z3.ClauseEvent)
    (userNames : Std.HashMap String Expr)
    : MetaM (List MVarId) := do
  trace[smt.reconstruct.z3] "reconstructing from {clauses.size} clause events"
  -- Phase 1: Translate and verify processable clauses
  let mut verifiedHints : Array (Expr × Expr) := #[]  -- (type, proof)
  let mut skippedGoals : List MVarId := []
  let mut theoryCount := 0
  let mut translateErrors : Array MessageData := #[]
  let mut unprovenHints : Array Expr := #[]
  for clause in clauses do
    let hintKind := classifyHint clause.proofHint
    trace[smt.reconstruct.z3] "clause: kind={repr hintKind} lits={clause.literals.size}"
    -- Only process theory lemmas
    unless hintKind.isProcessable do continue
    theoryCount := theoryCount + 1
    trace[smt.reconstruct.z3] "processing {repr hintKind} hint with {clause.literals.size} literals"
    try
      -- Translate clause literals to a Lean disjunction
      let clauseType ← translateClause clause.literals userNames
      trace[smt.reconstruct.z3] "translated clause type: {clauseType}"
      -- Create a fresh metavariable for this lemma
      let lemmaVar ← mkFreshExprMVar (some clauseType)
      let lemmaMV := lemmaVar.mvarId!
      -- Try to prove it
      let proved ← tryProve lemmaMV
      if proved then
        trace[smt.reconstruct.z3] "verified theory lemma"
        verifiedHints := verifiedHints.push (clauseType, lemmaVar)
      else
        trace[smt.reconstruct.z3] "could not verify theory lemma, skipping"
        unprovenHints := unprovenHints.push clauseType
    catch e =>
      let litStrs := clause.literals.map (Z3.Ast.toString' ·)
      let msg := m!"failed to translate {repr hintKind} hint (Z3 literals: {litStrs}): {e.toMessageData}"
      trace[smt.reconstruct.z3] "{msg}"
      translateErrors := translateErrors.push msg

  -- Phase 2: Assert verified hints into the goal context and close
  trace[smt.reconstruct.z3] "asserting {verifiedHints.size} verified hints into goal \
    ({theoryCount} theory lemmas total, {translateErrors.size} translation errors, \
    {unprovenHints.size} unproven)"
  let mut currentMV := mv
  for (type, proof) in verifiedHints do
    currentMV ← currentMV.assert (← mkFreshId) type proof
    let (_, mv') ← currentMV.intro1
    currentMV := mv'

  -- Diagnostic: check if grind could close the goal without hints
  if verifiedHints.size > 0 then
    let sNoHints ← saveState
    let closedWithoutHints ← tryProve mv
    restoreState sNoHints
    if closedWithoutHints then
      trace[smt.reconstruct.z3] "DIAGNOSTIC: grind closed goal WITHOUT Z3 hints \
        (hints were redundant for this goal)"
    else
      trace[smt.reconstruct.z3] "DIAGNOSTIC: grind could NOT close goal without hints \
        ({verifiedHints.size} hints are contributing)"

  -- Phase 2.5: If hints failed to translate (likely Skolem functions), resolve
  -- Skolems by applying hypothesis instantiations and destructuring existentials.
  -- This makes the Skolem witnesses available as FVars, letting us re-translate
  -- the previously-failing clauses.
  let mut extendedNames := userNames
  if translateErrors.size > 0 then
    trace[smt.reconstruct.z3] "extracting quantifier instantiation info from untranslatable clauses"
    let instInfos ← extractQuantInstInfos clauses userNames
    -- Collect all Skolem names from failing clauses
    let mut allSkolemNames : Array String := #[]
    for clause in clauses do
      for lit in clause.literals do
        allSkolemNames := allSkolemNames ++ collectSkolemNames lit
    -- Deduplicate
    let skolemNames := allSkolemNames.toList.eraseDups.toArray
    trace[smt.reconstruct.z3] "found {skolemNames.size} unique Skolem functions: \
      {skolemNames.map skolemBaseName}"
    if instInfos.size > 0 then
      -- Collect all hypotheses from the local context
      let hyps ← currentMV.withContext do
        let mut hyps : Array Expr := #[]
        for decl in (← getLCtx) do
          if decl.isAuxDecl then continue
          if ← Meta.isProp decl.type then
            hyps := hyps.push (.fvar decl.fvarId)
        return hyps
      -- For each instantiation, try to apply the hypothesis and destructure
      for info in instInfos do
        match ← matchHypothesis info hyps userNames with
        | some hyp =>
          trace[smt.reconstruct.z3] "applying matched hypothesis for quantifier instantiation"
          let s ← saveState
          let mut applied := false
          try
            let goalType ← currentMV.getType
            -- Create a fresh goal with the same type, apply hyp to it
            let freshMV ← currentMV.withContext do
              pure (← mkFreshExprMVar (some goalType)).mvarId!
            let subgoals ← freshMV.apply hyp
            let allClosed ← subgoals.allM fun sg => sg.withContext do
              try sg.assumption; return true
              catch _ => pure ()
              let s' ← saveState
              try
                let remainingGoals ← Lean.Elab.Term.TermElabM.run' do
                  Lean.Elab.Tactic.run sg do
                    Lean.Elab.Tactic.evalTactic
                      (← `(tactic| repeat' (first | assumption | constructor)))
                if remainingGoals.length == 0 then return true
              catch _ => pure ()
              restoreState s'
              tryProve sg
            if allClosed then
              -- The freshMV now has a proof of the goal type — assign it
              let proof ← instantiateMVars (.mvar freshMV)
              -- Assert this as a hypothesis and destructure
              currentMV ← currentMV.assert (← mkFreshId) goalType proof
              let (hFv, currentMV') ← currentMV.intro1
              currentMV := currentMV'
              -- Destructure the existential to get witness FVars
              let (currentMV', witnesses) ← destructureExistsHyp currentMV hFv
              currentMV := currentMV'
              applied := true
              -- Build Skolem → FVar mapping
              for (witName, witFv) in witnesses do
                for skName in skolemNames do
                  if skolemBaseName skName == witName then
                    trace[smt.reconstruct.z3] "resolved Skolem '{skName}' → FVar '{witName}'"
                    extendedNames := extendedNames.insert skName (.fvar witFv)
          catch _ => restoreState s
          if !applied then
            -- Strategy 2: Use ground literals to apply hypothesis partially
            -- Construct the hypothesis application using the ground literals as arguments
            -- This handles cases where the goal type ≠ hypothesis conclusion
            pure ()
        | none => continue
      -- Re-translate previously-failing clauses with extended names
      if extendedNames.size > userNames.size then
        trace[smt.reconstruct.z3] "re-translating {translateErrors.size} clauses with \
          {extendedNames.size - userNames.size} resolved Skolem names"
        for clause in clauses do
          let hintKind := classifyHint clause.proofHint
          unless hintKind.isProcessable do continue
          -- Only re-try clauses that have Skolems
          unless clause.literals.any hasSkolem do continue
          try
            let clauseType ← translateClause clause.literals extendedNames
            let lemmaVar ← mkFreshExprMVar (some clauseType)
            let proved ← tryProve lemmaVar.mvarId!
            if proved then
              trace[smt.reconstruct.z3] "verified previously-failing clause after Skolem resolution"
              currentMV ← currentMV.assert (← mkFreshId) clauseType lemmaVar
              let (_, mv') ← currentMV.intro1
              currentMV := mv'
          catch _ => continue

  -- Phase 3: Try to close the enriched goal
  trace[smt.reconstruct.z3] "closing enriched goal"
  let closed ← tryProve currentMV
  if closed then
    trace[smt.reconstruct.z3] "goal closed successfully"
    return skippedGoals
  else
    -- Build a detailed error message
    let goalType ← currentMV.getType
    let mut details : Array MessageData := #[]
    details := details.push m!"Goal after asserting {verifiedHints.size}/{theoryCount} \
      theory lemma hints:"
    details := details.push m!"  {goalType}"
    if !translateErrors.isEmpty then
      details := details.push m!"\n{translateErrors.size} hints failed to translate:"
      for err in translateErrors do
        details := details.push m!"  • {err}"
    if !unprovenHints.isEmpty then
      details := details.push m!"\n{unprovenHints.size} hints translated but could not be \
        verified (grind and bv_decide both failed):"
      for h in unprovenHints do
        details := details.push m!"  • {h}"
    let detailMsg := MessageData.joinSep details.toList "\n"
    throwError "smt (solver := .z3): Z3 returned unsat but proof reconstruction failed.\n\
      \nReconstruction summary:\n{detailMsg}\n\
      \nTry:\n  • `set_option trace.smt.reconstruct.z3 true` for full clause-by-clause details\n  \
      • `smt (solver := .z3) +trust` to skip proof checking"

end Smt.Reconstruct.Z3
