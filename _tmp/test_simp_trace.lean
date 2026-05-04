import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Types.Basic

namespace CategoryTheory
open MonoidalCategory

set_option backward.defeqAttrib.useBackward true in
set_option trace.Meta.Tactic.simp.rewrite true in
attribute [local simp] map_seq seq_map_assoc types_tensorObj_def types_tensorUnit_def
  LawfulApplicative.pure_seq LawfulApplicative.seq_assoc in
example (F : Type* → Type*) [Applicative F] [LawfulApplicative F]
    {X Y : Type*} (f : X ⟶ Y) (X' : Type*)
    (a : (ofTypeFunctor F).obj X) (b : (ofTypeFunctor F).obj X') :
    MonoidalCategoryStruct.whiskerRight ((ofTypeFunctor F).map f) ((ofTypeFunctor F).obj X') ≫
        ↾fun p ↦ Prod.mk <$> p.1 <*> p.2 =
      ((↾fun p ↦ Prod.mk <$> p.1 <*> p.2) ≫
        (ofTypeFunctor F).map (MonoidalCategoryStruct.whiskerRight f X')) := by
  ext ⟨a, b⟩
  simp; rfl
