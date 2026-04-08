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

/-- Create a constant expression with fresh universe level metavariables.
    This is needed for universe-polymorphic constants (like `Eq`, struct projections, etc.)
    where hardcoding all levels to `.zero` would be incorrect. -/
private def mkConstFreshLevels (name : Name) : MetaM Expr := do
  let ci ← getConstInfo name
  let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  return .const name lvls

/-- Translate a Z3 sort to a Lean type expression.
`userNames` is needed to resolve uninterpreted sorts back to their Lean types. -/
def translateSort (s : Z3.Srt) (userNames : Std.HashMap String Expr) : MetaM Expr := do
  let kind := Z3.Srt.getKindRaw s
  match kind with
  | 0 => -- Uninterpreted sort — look up by name
    let name := Z3.Srt.getName s
    match userNames[name]? with
    | some e => inferType e  -- e is an FVar of that type; we want the type itself
    | none =>
      -- The sort name might directly be a type variable name
      match (← getLCtx).findFromUserName? name.toName with
      | some decl => return decl.type
      | none =>
        match (← getEnv).find? name.toName with
        | some ci => return (← mkConstFreshLevels ci.name)
        | none => throwError "translateSort: unknown uninterpreted sort '{name}'"
  | 1 => return .sort .zero  -- Bool → Prop
  | 2 => return .const ``Int []
  | 3 => throwError "translateSort: Real sort (kind 3) is not yet supported. Z3 produced a Real-sorted term but reconstruction only handles Int."
  | 4 =>
    let size := Z3.Srt.getBvSize s
    return mkApp (.const ``BitVec []) (toExpr size.toNat)
  | _ => throwError "translateSort: unsupported Z3 sort kind {kind}"

/-- Build a Lean integer literal expression. Always produces an `Int`-typed expression. -/
private def mkIntLit (n : Int) : MetaM Expr := do
  return toExpr n

/-- Build a Lean BitVec literal expression: `BitVec.ofNat w n`. -/
private def mkBvLit (width : Nat) (val : Nat) : MetaM Expr := do
  let wExpr := toExpr width
  let nExpr := toExpr val
  mkAppM ``BitVec.ofNat #[wExpr, nExpr]

/-- Get args of a Z3 AST as an array. -/
private def getArgs (a : Z3.Ast) : Array Z3.Ast :=
  Z3.Ast.getArgs a

/-- Get the i-th arg of a Z3 AST, throwing if out of bounds. -/
private def getArg! (args : Array Z3.Ast) (i : Nat) : MetaM Z3.Ast := do
  match args[i]? with
  | some a => return a
  | none => throwError "getArg!: index {i} out of bounds (size {args.size})"

/-- Extract constructor name from a Z3 recognizer AST string.
E.g., `"((_ is |Color.blue|) c)"` → `"Color.blue"`. -/
private def extractRecognizerCtorName (astStr : String) : MetaM String := do
  -- Find "(_ is " in the string, then extract until ")"
  let marker := "(_ is "
  let chars := astStr.toList
  let markerChars := marker.toList
  -- Find the marker
  let rec findMarker (cs : List Char) (fuel : Nat) : Option (List Char) :=
    match fuel, cs with
    | 0, _ => none
    | _, [] => none
    | fuel+1, _ =>
      if cs.take markerChars.length == markerChars then
        some (cs.drop markerChars.length)
      else
        findMarker cs.tail fuel
  match findMarker chars chars.length with
  | none => throwError "translateApp: cannot parse recognizer from '{astStr}'"
  | some rest =>
    -- rest starts with the constructor name (possibly |quoted|), find closing ")"
    let rec collectUntilClose (cs : List Char) (acc : List Char) (fuel : Nat) : List Char :=
      match fuel, cs with
      | 0, _ => acc.reverse
      | _, [] => acc.reverse
      | fuel+1, ')' :: _ => acc.reverse
      | fuel+1, c :: cs => collectUntilClose cs (c :: acc) fuel
    let raw := String.mk (collectUntilClose rest [] rest.length)
    -- Strip SMT-LIB quoting (|...|)
    if raw.startsWith "|" && raw.endsWith "|" then
      return String.mk (raw.toList.drop 1 |>.dropLast)
    else
      return raw

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
  | .numeral => translateNumeral a userNames
  | .app => translateApp a userNames boundVars
  | .quantifier => translateQuantifier a userNames boundVars
  | .var => translateVar a boundVars
  | _ => throwError "translateAst: unsupported AST kind {repr kind} for {Z3.Ast.toString' a}"
where
  translateNumeral (a : Z3.Ast) (_userNames : Std.HashMap String Expr) : MetaM Expr := do
    let s := Z3.Ast.getNumeralString a
    let sort := Z3.Ast.getSort a
    let sortKind := Z3.Srt.getKindRaw sort
    if sortKind == 3 then
      throwError "translateNumeral: Real sort (kind 3) is not yet supported for numeral '{s}'"
    if sortKind == 2 then
      -- Int sort
      match s.toInt? with
      | some n => mkIntLit n
      | none   => throwError "translateNumeral: cannot parse '{s}' as integer"
    else if sortKind == 4 then
      -- BitVec sort
      let width := Z3.Srt.getBvSize sort
      match s.toNat? with
      | some n => mkBvLit width.toNat n
      | none   => throwError "translateNumeral: cannot parse '{s}' as bitvector"
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
          | some ci => return (← mkConstFreshLevels ci.name)
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
      mkAppM ``Eq #[lhs, rhs]
    | .distinct =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      let eq ← mkAppM ``Eq #[lhs, rhs]
      return mkApp (.const ``Not []) eq
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
    | .idiv | .div =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HDiv.hDiv #[lhs, rhs]
    | .mod | .rem =>
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
    -- Bitvector operations
    | .bneg =>
      let arg ← translateAst (← getArg! args 0) userNames boundVars
      return ← mkAppM ``Neg.neg #[arg]
    | .badd =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HAdd.hAdd #[lhs, rhs]
    | .bsub =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HSub.hSub #[lhs, rhs]
    | .bmul =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HMul.hMul #[lhs, rhs]
    | .budiv =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HDiv.hDiv #[lhs, rhs]
    | .burem =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HMod.hMod #[lhs, rhs]
    | .bnot =>
      let arg ← translateAst (← getArg! args 0) userNames boundVars
      return ← mkAppM ``Complement.complement #[arg]
    | .band =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HAnd.hAnd #[lhs, rhs]
    | .bor =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HOr.hOr #[lhs, rhs]
    | .bxor =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HXor.hXor #[lhs, rhs]
    | .bshl =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HShiftLeft.hShiftLeft #[lhs, rhs]
    | .blshr =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HShiftRight.hShiftRight #[lhs, rhs]
    | .bule =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``LE.le #[lhs, rhs]
    | .bult =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``LT.lt #[lhs, rhs]
    | .buge =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``GE.ge #[lhs, rhs]
    | .bugt =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``GT.gt #[lhs, rhs]
    | .bconcat =>
      let lhs ← translateAst (← getArg! args 0) userNames boundVars
      let rhs ← translateAst (← getArg! args 1) userNames boundVars
      return ← mkAppM ``HAppend.hAppend #[lhs, rhs]
    -- Uninterpreted function application
    | .uninterpreted =>
      let name := Z3.FuncDecl.getName fd
      let fn ← match userNames[name]? with
        | some e => pure e
        | none =>
          -- Fallback: look up global constants (axiom, opaque, def, etc.)
          -- that were translated to `declare-fun` in the SMT query.
          match (← getEnv).find? name.toName with
          | some ci => pure ((← mkConstFreshLevels ci.name))
          | none => throwError "translateApp: unknown function '{name}'"
      let mut result := fn
      for arg in args do
        let argExpr ← translateAst arg userNames boundVars
        result := mkApp result argExpr
      return result
    | .other raw =>
      let name := Z3.FuncDecl.getName fd
      -- Datatype constructor (Z3_OP_DT_CONSTRUCTOR = 0x800)
      if raw == 0x800 then
        let ctorName := name.toName
        let env ← getEnv
        match env.find? ctorName with
        | some ci =>
          let mut result : Expr := (← mkConstFreshLevels ci.name)
          for arg in args do
            let argExpr ← translateAst arg userNames boundVars
            result := mkApp result argExpr
          return result
        | none => throwError "translateApp: unknown datatype constructor '{name}'"
      -- Datatype recognizer (Z3_OP_DT_RECOGNISER = 0x801, Z3_OP_DT_IS = 0x802)
      -- These appear as ((_ is CtorName) x) — test which constructor was used.
      -- We parse the constructor name from the AST's string representation,
      -- since FuncDecl.toString' loses the constructor identity.
      else if raw == 0x801 || raw == 0x802 then
        let arg ← translateAst (← getArg! args 0) userNames boundVars
        -- Ast.toString' produces e.g. "((_ is |Color.blue|) c)"
        let astStr := Z3.Ast.toString' a
        let ctorNameStr ← extractRecognizerCtorName astStr
        let ctorName := ctorNameStr.toName
        let env ← getEnv
        match env.find? ctorName with
        | some (.ctorInfo cv) =>
          let indInfo ← getConstInfo cv.induct
          let ctor ← mkConstFreshLevels cv.name
          if cv.numFields == 0 then
            -- Nullary constructor: `(_ is Ctor) x` ↦ `x = Ctor`
            return ← mkAppM ``Eq #[arg, ctor]
          else
            -- Non-nullary: `(_ is Ctor) x` ↦ `∃ a₁ ... aₙ, x = Ctor a₁ ... aₙ`
            let ctorType ← inferType ctor
            Meta.forallTelescopeReducing ctorType fun params _ => do
              -- Build `Ctor a₁ ... aₙ`
              let mut applied := ctor
              for p in params do
                applied := mkApp applied p
              -- Build `x = Ctor a₁ ... aₙ`
              let mut body ← mkAppM ``Eq #[arg, applied]
              -- Wrap in existentials from innermost to outermost
              for p in params.reverse do
                body ← mkAppM ``Exists #[← mkLambdaFVars #[p] body]
              return body
        | _ => throwError "translateApp: unknown constructor '{ctorNameStr}' from recognizer '{astStr}'"
      -- Datatype accessor (Z3_OP_DT_ACCESSOR = 0x803)
      -- Accessor names from declare-datatypes are "CtorName.i" (e.g., "Point.mk.0").
      -- We map these back to Lean projection functions.
      else if raw == 0x803 then
        let arg ← translateAst (← getArg! args 0) userNames boundVars
        -- Parse accessor name "CtorName.i" → (ctorName, fieldIndex)
        match name.splitOn "." with
        | parts =>
          -- The last part should be the field index, rest is the constructor name
          if let some idxStr := parts.getLast? then
            if let some idx := idxStr.toNat? then
              -- Reconstruct constructor name (everything except last ".i")
              let ctorParts := parts.dropLast
              let ctorNameStr := ".".intercalate ctorParts
              let ctorName := ctorNameStr.toName
              let env ← getEnv
              match env.find? ctorName with
              | some (.ctorInfo cv) =>
                -- Find the projection function for this field index
                if let some sinfo := getStructureInfo? env cv.induct then
                  if h : idx < sinfo.fieldNames.size then
                    let fieldName := sinfo.fieldNames[idx]
                    let projName := cv.induct ++ fieldName
                    let projInfo ← getConstInfo projName
                    let proj ← mkConstFreshLevels projName
                    return mkApp proj arg
                  else
                    throwError "translateApp: accessor index {idx} out of range for {cv.induct}"
                else
                  -- Not a structure — for plain inductives, we don't have named projections.
                  -- Fall back to matching on field index from the constructor type.
                  throwError "translateApp: accessor for non-structure inductive '{cv.induct}' not yet supported"
              | _ => throwError "translateApp: unknown constructor '{ctorNameStr}' from accessor '{name}'"
            else
              throwError "translateApp: could not parse field index from accessor '{name}'"
          else
            throwError "translateApp: empty accessor name"
      else
        -- Other internal operators by function name
        match name with
        | "div0" | "idiv0" =>
          let lhs ← translateAst (← getArg! args 0) userNames boundVars
          let rhs ← translateAst (← getArg! args 1) userNames boundVars
          return ← mkAppM ``HDiv.hDiv #[lhs, rhs]
        | "mod0" =>
          let lhs ← translateAst (← getArg! args 0) userNames boundVars
          let rhs ← translateAst (← getArg! args 1) userNames boundVars
          return ← mkAppM ``HMod.hMod #[lhs, rhs]
        | _ => throwError "translateApp: unsupported Z3 internal operator '{name}' (raw kind {raw}) for {Z3.Ast.toString' a}"
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
      binderInfo := binderInfo.push (name.toName, ← translateSort sort userNames)
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
