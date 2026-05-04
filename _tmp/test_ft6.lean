import Mathlib.CategoryTheory.Monoidal.Functor.Types

namespace CategoryTheory
open MonoidalCategory

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] map_seq seq_map_assoc types_tensorObj_def types_tensorUnit_def
  LawfulApplicative.pure_seq LawfulApplicative.seq_assoc in
set_option trace.Meta.Tactic.simp.rewrite true in
example (F : Type* → Type*) [Applicative F] [LawfulApplicative F] :
    Functor.LaxMonoidal (ofTypeFunctor F) where
  ε := ↾fun _ ↦ (pure PUnit.unit : F _)
  μ _ _ := ↾fun p ↦ (Prod.mk <$> p.1 <*> p.2 : F _)
  μ_natural_left := by intros; ext ⟨a, b⟩; simp; sorry

end CategoryTheory
