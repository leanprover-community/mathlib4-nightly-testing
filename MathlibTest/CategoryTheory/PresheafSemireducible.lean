import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Tactic.CategoryTheory.CastProofs

open CategoryTheory Functor PresheafOfModules

noncomputable section

set_option backward.isDefEq.respectTransparency true

universe v v₁ v₂ u₁ u₂ u
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u})
  (M N : PresheafOfModules.{v} R)

-- All four object fields unfold at instance transparency.
example (X : Dᵒᵖ) : (M.presheaf.obj X : Type v) = M.obj X := by
  with_reducible_and_instances rfl

example : (toPresheaf R).obj M = M.presheaf := by
  with_reducible_and_instances rfl

example (X : Cᵒᵖ) :
    (pushforward₀Obj F R M).obj X = ModuleCat.of _ (M.obj (F.op.obj X)) := by
  with_reducible_and_instances rfl

example : (pushforward₀ F R).obj M = pushforward₀Obj F R M := by
  with_reducible_and_instances rfl

-- Their map fields still require default transparency.
example {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    (M.presheaf.map f).hom x = M.map f x := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example (φ : M ⟶ N) (X : Dᵒᵖ) (x : M.obj X) :
    (((toPresheaf R).map φ).app X).hom x = φ.app X x := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj (F.op.obj X)) :
    ((pushforward₀Obj F R M).map f).hom x = M.map (F.op.map f) x := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example (φ : M ⟶ N) (X : Cᵒᵖ) :
    ((pushforward₀ F R).map φ).app X = φ.app (F.op.obj X) := by
  fail_if_success with_reducible_and_instances rfl
  rfl

-- The comparison needs no preliminary unfolding, even in a restricted context.
example : pushforward₀.{v} F R ⋙ toPresheaf _ ≅
    toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op := by
  with_reducible_and_instances exact cast_proofs% (Iso.refl _)

example (X : Cᵒᵖ) :
    ((pushforward₀CompToPresheaf F R).hom.app M).app X = 𝟙 (M.presheaf.obj (F.op.obj X)) := by
  simp [pushforward₀CompToPresheaf]
