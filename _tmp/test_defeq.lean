import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

-- Test: does set_option propagate through @[simps] to inferDefEqAttr?
set_option backward.defeq.atInstanceTransparency false in
@[simps]
def myWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by simp [NatTrans.naturality]

-- Without set_option
@[simps]
def myWhiskerLeft2 (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by simp [NatTrans.naturality]

open Lean in
#eval do
  let env ← getEnv
  let r1 := defeqAttr.hasTag env `myWhiskerLeft_app
  let r2 := defeqAttr.hasTag env `myWhiskerLeft2_app
  return s!"myWhiskerLeft_app defeq={r1} myWhiskerLeft2_app defeq={r2}"
