import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Category.TopCat.Adjunctions

open TopologicalSpace CategoryTheory CategoryTheory.Limits

local notation "forget" => forget TopCat

namespace TopCat

section Colimits

variable {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{u}}

section

variable (c : Cocone (F ⋙ forget))

def coconePtOfCoconeForget : Type _ := c.pt

instance topologicalSpaceCoconePtOfCoconeForget :
    TopologicalSpace (coconePtOfCoconeForget c) :=
  (⨆ j, (F.obj j).str.coinduced (c.ι.app j))

def coconeOfCoconeForget : Cocone F where
  pt := of (coconePtOfCoconeForget c)
  ι := sorry

end

section IsColimit

variable (c : Cocone F) (hc : IsColimit c)

include hc

theorem _root_.TopCat.coinduced_of_isColimit.extracted_1_1 {J : Type v} [inst : Category.{w, v} J] {F : J ⥤ TopCat}
  (c : Cocone F) (hc : IsColimit c) :
  let c' := coconeOfCoconeForget ((forget).mapCocone c);
  let e : of (coconePtOfCoconeForget ((forget).mapCocone c)) ≅ c.1 := sorry;
  (∀ (j : J), c'.ι.app j ≫ e.hom = c.ι.app j) →
      (⨆ i, coinduced (DFunLike.coe (@TopCat.homeoOfIso (@TopCat.of _ (⨆ j, _)) _ e)) (coinduced sorry (F.obj i).str)) =
      (⨆ j, coinduced
          (DFunLike.coe (β := fun (x : TopCat.carrier (Prefunctor.obj _ j)) ↦ TopCat.carrier _) (ConcreteCategory.hom (c.ι.app j)))
          (F.obj j).str) := by
  fail_if_success grind
  sorry
