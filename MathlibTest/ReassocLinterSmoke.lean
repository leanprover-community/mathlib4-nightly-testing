import Mathlib.Tactic.CategoryTheory.Reassoc

set_option linter.tacticCheckInstances true

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Negative test — vanilla reassoc on a clean lemma, no warning expected. -/

@[reassoc]
lemma clean_lem {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    f ≫ g = h := w

#check @clean_lem_assoc

/-! ## Positive test — a semireducible alias for `Quiver.Hom` causes the reassoc-generated
lemma's type to be ill-typed at `.implicit`. -/

/-- A semireducible synonym for the morphism type. -/
def MyHom (X Y : C) : Type v := X ⟶ Y

@[reassoc]
lemma alias_lem {X Y Z : C} (f : MyHom X Y) (g : Y ⟶ Z) (h : MyHom X Z)
    (w : (f : X ⟶ Y) ≫ g = h) :
    (f : X ⟶ Y) ≫ g = h := w

#check @alias_lem_assoc

/-! ## Regression: marking the offenders `@[implicit_reducible]` silences the warning. -/

set_option allowUnsafeReducibility true
attribute [implicit_reducible] Quiver.Hom MyHom

@[reassoc]
lemma alias_lem2 {X Y Z : C} (f : MyHom X Y) (g : Y ⟶ Z) (h : MyHom X Z)
    (w : (f : X ⟶ Y) ≫ g = h) :
    (f : X ⟶ Y) ≫ g = h := w

#check @alias_lem2_assoc
