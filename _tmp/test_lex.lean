import Mathlib.Data.DFinsupp.Lex

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι]
  [∀ i, OrderedCancelAddCommMonoid (α i)]

set_option pp.all false in
example : AddLeftStrictMono (Lex (Π₀ i, α i)) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ ↦ ⟨a, fun j ja ↦ congr_arg _ (lta j ja), by
    dsimp
    sorry⟩⟩
