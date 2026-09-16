/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public meta import Lean.Elab.Term
public meta import Lean.Meta.Sym.SymM

/-!
# Rebuilding componentwise categorical constructions

`cast_proofs% t` elaborates `t` at default transparency and rebuilds its structures against the
expected type only where its type does not already match at implicit transparency. Compatibility
proofs retain the expected types and are checked at default transparency.
-/

public meta section

open Lean Meta Elab Term

namespace Mathlib.Tactic.CategoryTheory.CastProofs

/-- Expose component data whose original type does not match the expected type. -/
private def exposeData (value : Expr) : MetaM Expr := withDefault do
  Sym.foldProjs (← whnf value)

/-- Rebuild structures and functions against the expected indices.
Proofs keep the expected type; data must match at implicit transparency. -/
partial def rebuild (value expected : Expr) (depth : Nat := 0) : MetaM Expr := do
  if depth > 64 then
    throwError "cast_proofs%: structure nesting exceeds 64 levels"
  let expected ← instantiateMVars expected
  if ← withImplicit <| isDefEq (← inferType value) expected then
    return ← withDefault <| Sym.foldProjs value
  if ← isProp expected then
    unless ← withDefault <| isDefEq (← inferType value) expected do
      throwError "cast_proofs%: incompatible proof types"
    return ← mkExpectedTypeHint value expected
  let exposed ← exposeData value
  let target ← withImplicit <| whnf expected
  if target.isForall then
    forallTelescope target fun xs body => do
      let value ← rebuild (mkAppN value xs) body (depth + 1)
      mkLambdaFVars xs value
  else if target.getAppFn.isConst && isStructure (← getEnv) target.getAppFn.constName! then
    let name := target.getAppFn.constName!
    let info ← getConstInfoInduct name
    let ctorName := info.ctors.head!
    let ctorInfo ← getConstInfoCtor ctorName
    let ctor := mkAppN (mkConst ctorName target.getAppFn.constLevels!) target.getAppArgs
    let (args, _, result) ← forallMetaTelescope (← inferType ctor)
    unless ← withImplicit <| isDefEq result expected do
      throwError "cast_proofs%: cannot determine constructor parameters"
    for i in [:ctorInfo.numFields] do
      let arg := args[i]!
      let field ← rebuild (.proj name i value) (← inferType arg) (depth + 1)
      arg.mvarId!.assign field
    return ← instantiateMVars (mkAppN ctor args)
  else
    let value := exposed
    unless ← withImplicit <| isDefEq (← inferType value) expected do
      throwError "cast_proofs%: component data still has incompatible types\n\
        {← inferType value}\n{expected}"
    return value

syntax (name := castProofsPercent) "cast_proofs% " term:arg : term

@[term_elab castProofsPercent] def elabCastProofsPercent : TermElab := fun stx expected? => do
  let some expected := expected? | throwError "cast_proofs% requires an expected type"
  let term : Term := ⟨stx[1]⟩
  let value ← withDefault <| elabTermEnsuringType term (some expected)
  synthesizeSyntheticMVarsNoPostponing
  rebuild (← instantiateMVars value) expected

end Mathlib.Tactic.CategoryTheory.CastProofs
