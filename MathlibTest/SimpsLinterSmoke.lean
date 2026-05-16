import Mathlib.Tactic.Simps.Basic

set_option linter.tacticCheckInstances true

/-! ## Negative test — clean projection, no warning expected. -/

structure Wrap (α : Type) where
  carrier : List α

@[simps]
def mkWrap (s : List Nat) : Wrap Nat := { carrier := s }

#check @mkWrap_carrier

/-! ## Positive test — semireducible alias forces an `.implicit`-ill-typed equation. -/

structure Fn where
  toFun : Nat → Nat

/-- A semireducible alias for `Fn`. Unfolds at `.default` but not at `.implicit`. -/
def MyFn : Type := Fn

/-- A simps invocation whose generated equation `idFn_toFun : Fn.toFun idFn = id`
mentions `Fn.toFun` applied to a term of type `MyFn`. Type-checking that application
requires unfolding `MyFn` to `Fn`, which only succeeds at `.default`. We expect the new
linter to fire and suggest marking `MyFn` as `@[implicit_reducible]`. -/
@[simps]
def idFn : MyFn := ({ toFun := id } : Fn)

#check @idFn_toFun

/-! ## Regression: marking the offender `@[implicit_reducible]` silences the warning. -/

set_option allowUnsafeReducibility true
attribute [implicit_reducible] MyFn

@[simps]
def idFn2 : MyFn := ({ toFun := id } : Fn)

#check @idFn2_toFun
