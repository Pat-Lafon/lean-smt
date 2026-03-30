/-
Copyright (c) 2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lafontaine
-/

import Lean
import Z3

/-!
# Z3 AST to Lean Expr Translation

Translates Z3 AST nodes (from theory inference clauses) back to Lean
expressions. This is the reverse of `Smt.Translate.*` — it goes from
Z3's internal representation to Lean `Expr`.

The translation uses `userNames : Std.HashMap String Expr` (the same
`fvNames₂` map from `genUniqueFVarNames`) to resolve user-declared
variables back to their original Lean free variables.

For built-in operations (and, or, +, <, etc.), we dispatch on the
`Z3.DeclKind` from `FuncDecl.getDeclKind`.
-/

namespace Smt.Reconstruct.Z3

open Lean Meta

/-- Translate a Z3 sort to a Lean type expression. -/
def translateSort (s : Z3.Srt) : MetaM Expr := do
  let kind := Z3.Srt.getKindRaw s
  match kind with
  | 1 => return .sort .zero  -- Bool → Prop
  | 2 => return .const ``Int []
  | 3 => return .const ``Int []  -- TODO: use Real when available
  | 4 =>
    let size := Z3.Srt.getBvSize s
    return mkApp (.const ``BitVec []) (toExpr size.toNat)
  | _ => throwError "translateSort: unsupported Z3 sort kind {kind}"

/-- Build a Lean integer literal expression. -/
private def mkIntLit (n : Int) : MetaM Expr := do
  if n ≥ 0 then
    return toExpr n
  else
    mkAppM ``Neg.neg #[toExpr n.natAbs]

/-- Get args of a Z3 AST as an array. -/
private def getArgs (a : Z3.Ast) : Array Z3.Ast :=
  Z3.Ast.getArgs a

/-- Get the i-th arg of a Z3 AST, throwing if out of bounds. -/
private def getArg! (args : Array Z3.Ast) (i : Nat) : MetaM Z3.Ast := do
  match args[i]? with
  | some a => return a
  | none => throwError "getArg!: index {i} out of bounds (size {args.size})"

/-- Translate a Z3 AST to a Lean expression.

`userNames` maps SMT variable names to their original Lean FVar expressions.
`boundVars` tracks quantifier-bound variables as Lean FVars (innermost last).

Z3 uses de Bruijn indices for bound variables inside quantifiers. Index 0
refers to the innermost binder. We maintain `boundVars` as a stack where
the last element is the innermost binder, so de Bruijn index `i` maps to
`boundVars[boundVars.size - 1 - i]`. -/
partial def translateAst (a : Z3.Ast) (userNames : Std.HashMap String Expr)
    (boundVars : Array Expr := #[]) : MetaM Expr := do
  let kind := Z3.Ast.getAstKind a
  match kind with
  | .numeral => translateNumeral a
  | .app => translateApp a userNames boundVars
  | .quantifier => translateQuantifier a userNames boundVars
  | .var => translateVar a boundVars
  | _ => throwError "translateAst: unsupported AST kind {repr kind} for {Z3.Ast.toString' a}"
where
  translateNumeral (a : Z3.Ast) : MetaM Expr := do
    let s := Z3.Ast.getNumeralString a
    let sort := Z3.Ast.getSort a
    let sortKind := Z3.Srt.getKindRaw sort
    -- Int (2) or Real (3)
    if sortKind == 2 || sortKind == 3 then
      match s.toInt? with
      | some n => mkIntLit n
      | none   => throwError "translateNumeral: cannot parse '{s}' as integer"
    else
      throwError "translateNumeral: unsupported sort kind {sortKind} for numeral '{s}'"

  translateApp (a : Z3.Ast) (userNames : Std.HashMap String Expr)
      (boundVars : Array Expr) : MetaM Expr := do
    let fd := Z3.Ast.getFuncDecl a
    let declKind := Z3.FuncDecl.getDeclKind fd
    let args := getArgs a
    let nargs := args.size

    -- Nullary constants
    if nargs == 0 then
      match declKind with
      | .true_  => return .const ``True []
      | .false_ => return .const ``False []
      | _ =>
        let name := Z3.FuncDecl.getName fd
        match userNames[name]? with
        | some e => return e
        | none =>
          match (← getEnv).find? name.toName with
          | some ci => return .const ci.name (ci.numLevelParams.repeat (.zero :: ·) [])
          | none => throwError "translateApp: unknown constant '{name}'"

    match declKind with
    -- Boolean
    | .true_  => return .const ``True []
    | .false_ => return .const ``False []
    | .not =>
      let p ← translateAst (← getArg! args 0) userNames boundVars
      return mkApp (.const ``Not []) p
    | .and =>
      let mut result ← translateAst (← getArg! args 0) userNames boundVars
      for i in [1:nargs] do
        let arg ← translateAst (← getArg! args i) userNames boundVars
        result := mkApp2 (.const ``And []) result arg
      return result
    | .or =>
      let mut result ← translateAst (← getArg! args 0) userNames boundVars
      for i in [1:nargs] do
        let arg ← translateAst (← getArg! args i) userNames boundVars
        result := mkApp2 (.const ``Or []) result arg
      return result
    | .implies =>
      let p ← translateAst (← getArg! args 0) userNames boundVars
      let q ← translateAst (← getArg! args 1) userNames boundVars
      return Expr.forallE `_ p q .default
    | .iff =>
      let p ← translateAst (← getArg! args 0) userNames boundVars
      let q ← translateAst (← getArg! args 1) userNames boundVars
      return mkApp2 (.const ``Iff []) p q
    | .xor =>
      let p ← translateAst (← getArg! args 0) userNames boundVars
      let q ← translateAst (← getArg! args 1) userNames boundVars
      return mkApp (.const ``Not []) (mkApp2 (.const ``Iff []) p q)
    | .eq =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      let ty ← inferType lhs
      return mkApp3 (.const ``Eq [.zero]) ty lhs rhs
    | .distinct =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      let ty ← inferType lhs
      return mkApp (.const ``Not []) (mkApp3 (.const ``Eq [.zero]) ty lhs rhs)
    | .ite =>
      let c ← translateAst (← getArg! args 0) userNames boundVars
      let t ← translateAst (← getArg! args 1) userNames boundVars
      let e ← translateAst (← getArg! args 2) userNames boundVars
      return ← mkAppOptM ``ite #[none, c, none, t, e]
    -- Arithmetic
    | .add =>
      let mut result ← translateAst (← getArg! args 0) userNames boundVars
      for i in [1:nargs] do
        let arg ← translateAst (← getArg! args i) userNames boundVars
        result ← mkAppM ``HAdd.hAdd #[result, arg]
      return result
    | .sub =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HSub.hSub #[lhs, rhs]
    | .mul =>
      let mut result ← translateAst (← getArg! args 0) userNames boundVars
      for i in [1:nargs] do
        let arg ← translateAst (← getArg! args i) userNames boundVars
        result ← mkAppM ``HMul.hMul #[result, arg]
      return result
    | .uminus =>
      let arg ← translateAst (← getArg! args 0) userNames boundVars
      return ← mkAppM ``Neg.neg #[arg]
    | .idiv =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HDiv.hDiv #[lhs, rhs]
    | .mod =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HMod.hMod #[lhs, rhs]
    | .le =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``LE.le #[lhs, rhs]
    | .ge =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``GE.ge #[lhs, rhs]
    | .lt =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``LT.lt #[lhs, rhs]
    | .gt =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``GT.gt #[lhs, rhs]
    -- Uninterpreted function application
    | .uninterpreted =>
      let name := Z3.FuncDecl.getName fd
      let fn ← match userNames[name]? with
        | some e => pure e
        | none => throwError "translateApp: unknown function '{name}'"
      let mut result := fn
      for arg in args do
        let argExpr ← translateAst arg userNames boundVars
        result := mkApp result argExpr
      return result
    | k => throwError "translateApp: unsupported Z3 decl kind {repr k} for {Z3.Ast.toString' a}"

  /-- Translate a Z3 quantifier AST to a Lean forall/exists expression. -/
  translateQuantifier (a : Z3.Ast) (userNames : Std.HashMap String Expr)
      (boundVars : Array Expr) : MetaM Expr := do
    let isForall := Z3.Ast.isQuantifierForall a
    let numBound := Z3.Ast.getQuantifierNumBound a
    let body := Z3.Ast.getQuantifierBody a
    let mut binderInfo : Array (Name × Expr) := #[]
    for i in List.range numBound.toNat do
      let name := Z3.Ast.getQuantifierBoundName a i.toUInt32
      let sort := Z3.Ast.getQuantifierBoundSort a i.toUInt32
      binderInfo := binderInfo.push (name.toName, ← translateSort sort)
    let rec go (idx : Nat) (fvars : Array Expr) (bvs : Array Expr) : MetaM Expr := do
      if idx < binderInfo.size then
        let (name, ty) := binderInfo[idx]!
        withLocalDeclD name ty fun fvar =>
          go (idx + 1) (fvars.push fvar) (bvs.push fvar)
      else
        let bodyExpr ← translateAst body userNames bvs
        if isForall then
          mkForallFVars fvars bodyExpr
        else
          let mut result := bodyExpr
          for i in List.range fvars.size |>.reverse do
            result ← mkAppM ``Exists #[← mkLambdaFVars #[fvars[i]!] result]
          return result
    go 0 #[] boundVars

  /-- Translate a Z3 bound variable (de Bruijn index) to the corresponding Lean FVar. -/
  translateVar (a : Z3.Ast) (boundVars : Array Expr) : MetaM Expr := do
    let idx := Z3.Ast.getVarIndex a
    let pos := boundVars.size - 1 - idx.toNat
    match boundVars[pos]? with
    | some fvar => return fvar
    | none => throwError "translateVar: de Bruijn index {idx} out of range (have {boundVars.size} bound vars)"

/-- Translate an array of Z3 clause literals to a Lean disjunction (Or chain).
    An empty clause translates to `False`.
    A single literal translates to itself. -/
def translateClause (lits : Array Z3.Ast) (userNames : Std.HashMap String Expr) : MetaM Expr := do
  if lits.isEmpty then
    return .const ``False []
  let mut result ← translateAst (← getArg! lits 0) userNames
  for i in [1:lits.size] do
    let lit ← translateAst (← getArg! lits i) userNames
    result := mkApp2 (.const ``Or []) result lit
  return result

end Smt.Reconstruct.Z3
