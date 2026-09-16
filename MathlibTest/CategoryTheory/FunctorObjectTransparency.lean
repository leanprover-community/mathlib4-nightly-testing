import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sums.Products

open CategoryTheory Functor
open scoped CategoryTheory.Prod

set_option backward.isDefEq.respectTransparency true

-- Projection lemmas that expose hidden maps must remain unavailable to dsimp,
-- including its legacy proof-body check.
open Lean Meta Elab in
run_elab do
  for name in #[``PresheafOfModules.restrictScalarsObj_map,
      ``PresheafOfModules.restrictScalars_map_app, ``SheafOfModules.pushforward_map_val,
      ``CategoryTheory.Sum.functorEquiv_functor_map,
      ``CategoryTheory.Sum.functorEquiv_inverse_map] do
    for useAttr in [true, false] do
      withOptions (backward.dsimp.useDefEqAttr.set · useAttr) do
        if ← isBackwardRflTheorem name then
          logError m!"{name} is available to dsimp (useDefEqAttr = {useAttr})"

section Sums

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  (F : A ⥤ D) (G : B ⥤ D)

example (a : A) : (Sum.inl_ A B).obj a = Sum.inl a := by
  with_reducible_and_instances rfl

example (b : B) : (Sum.inr_ A B).obj b = Sum.inr b := by
  with_reducible_and_instances rfl

example (a : A) : (F.sum' G).obj (Sum.inl a) = F.obj a := by
  with_reducible_and_instances rfl

example {a a' : A} (f : a ⟶ a') : (Sum.inl_ A B).map f = ULift.up f := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example {b b' : B} (f : b ⟶ b') : (Sum.inr_ A B).map f = ULift.up f := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example {a a' : A} (f : a ⟶ a') : (F.sum' G).map ((Sum.inl_ A B).map f) = F.map f := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example (H : A ⊕ B ⥤ D) :
    (Sum.functorEquiv A B D).functor.obj H = (Sum.inl_ A B ⋙ H, Sum.inr_ A B ⋙ H) := by
  with_reducible_and_instances rfl

example : (Sum.functorEquiv A B D).inverse.obj (F, G) = F.sum' G := by
  with_reducible_and_instances rfl

example {H H' : A ⊕ B ⥤ D} (η : H ⟶ H') :
    (Sum.functorEquiv A B D).functor.map η =
      whiskerLeft (Sum.inl_ A B) η ×ₘ whiskerLeft (Sum.inr_ A B) η := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example {F' : A ⥤ D} {G' : B ⥤ D} (η : F ⟶ F') (θ : G ⟶ G') :
    (Sum.functorEquiv A B D).inverse.map (η ×ₘ θ) = NatTrans.sum' η θ := by
  fail_if_success with_reducible_and_instances rfl
  rfl

end Sums

section Modules

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (M N : ModuleCat S)

example : ((ModuleCat.restrictScalars f).obj M : Type _) = M := by
  with_reducible_and_instances rfl

example (g : M ⟶ N) (x : M) : ((ModuleCat.restrictScalars f).map g).hom x = g.hom x := by
  fail_if_success with_reducible_and_instances rfl
  rfl

end Modules

noncomputable section

universe v v₁ v₂ u₁ u₂ u
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Presheaves

open PresheafOfModules

variable {R R' : Dᵒᵖ ⥤ RingCat.{u}} (α : R' ⟶ R) (M N : PresheafOfModules.{v} R)

example (X : Dᵒᵖ) :
    ((restrictScalars α).obj M).obj X = (ModuleCat.restrictScalars (α.app X).hom).obj (M.obj X) := by
  with_reducible_and_instances rfl

example {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    ((M.restrictScalarsObj α).map f).hom x = M.map f x := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example (φ : M ⟶ N) (X : Dᵒᵖ) (x : M.obj X) :
    (((restrictScalars α).map φ).app X).hom x = φ.app X x := by
  fail_if_success with_reducible_and_instances rfl
  rfl

variable {S : Cᵒᵖ ⥤ RingCat.{u}} {F : C ⥤ D} (φ : S ⟶ F.op ⋙ R)

example (X : Cᵒᵖ) : (((pushforward φ).obj M).obj X : Type v) = M.obj (F.op.obj X) := by
  with_reducible_and_instances rfl

example (g : M ⟶ N) (X : Cᵒᵖ) (x : M.obj (F.op.obj X)) :
    (((pushforward φ).map g).app X).hom x = g.app (F.op.obj X) x := by
  fail_if_success with_reducible_and_instances rfl
  rfl

end Presheaves

section Sheaves

open SheafOfModules

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.IsContinuous F J K] {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (M N : SheafOfModules.{v} R)

example (X : Cᵒᵖ) : (((pushforward φ).obj M).val.obj X : Type v) = M.val.obj (F.op.obj X) := by
  with_reducible_and_instances rfl

example (g : M ⟶ N) (X : Cᵒᵖ) (x : M.val.obj (F.op.obj X)) :
    ((((pushforward φ).map g).val).app X).hom x = g.val.app (F.op.obj X) x := by
  fail_if_success with_reducible_and_instances rfl
  rfl

end Sheaves
