/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Localizations of localizations

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section



open Function

namespace IsLocalization

section LocalizationLocalization

variable {R : Type*} [CommSemiring R] (M : Submonoid R) {S : Type*} [CommSemiring S] [Algebra R S]
variable (N : Submonoid S) (T : Type*) [CommSemiring T] [Algebra R T]


section

variable [Algebra S T] [IsScalarTower R S T]

-- This should only be defined when `S` is the localization `M⁻¹R`, hence the nolint.
/-- Localizing w.r.t. `M ⊆ R` and then w.r.t. `N ⊆ S = M⁻¹R` is equal to the localization of `R`
w.r.t. this submonoid. See `localization_localization_isLocalization`.
-/
@[nolint unusedArguments]
def localizationLocalizationSubmodule : Submonoid R :=
  (N ⊔ M.map (algebraMap R S)).comap (algebraMap R S)

variable {M N}

@[simp]
theorem mem_localizationLocalizationSubmodule {x : R} :
    x ∈ localizationLocalizationSubmodule M N ↔
      ∃ (y : N) (z : M), algebraMap R S x = y * algebraMap R S z := by
  rw [localizationLocalizationSubmodule, Submonoid.mem_comap, Submonoid.mem_sup]
  constructor
  · rintro ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, e.symm⟩
  · rintro ⟨y, z, e⟩
    exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩

variable (M N)
variable [IsLocalization M S]

theorem localization_localization_map_units [IsLocalization N T]
    (y : localizationLocalizationSubmodule M N) : IsUnit (algebraMap R T y) := by
  obtain ⟨y', z, eq⟩ := mem_localizationLocalizationSubmodule.mp y.prop
  rw [IsScalarTower.algebraMap_apply R S T, eq, map_mul, IsUnit.mul_iff]
  exact ⟨IsLocalization.map_units T y', (IsLocalization.map_units _ z).map (algebraMap S T)⟩

theorem localization_localization_surj [IsLocalization N T] (x : T) :
    ∃ y : R × localizationLocalizationSubmodule M N,
        x * algebraMap R T y.2 = algebraMap R T y.1 := by
  rcases IsLocalization.surj N x with ⟨⟨y, s⟩, eq₁⟩
  -- x = y / s
  rcases IsLocalization.surj M y with ⟨⟨z, t⟩, eq₂⟩
  -- y = z / t
  rcases IsLocalization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩
  -- s = z' / t'
  dsimp only at eq₁ eq₂ eq₃
  refine ⟨⟨z * t', z' * t, ?_⟩, ?_⟩ -- x = y / s = (z * t') / (z' * t)
  · rw [mem_localizationLocalizationSubmodule]
    refine ⟨s, t * t', ?_⟩
    rw [map_mul, ← eq₃, mul_assoc, ← map_mul, mul_comm t, Submonoid.coe_mul]
  · simp only [map_mul, IsScalarTower.algebraMap_apply R S T, ← eq₃, ← eq₂, ← eq₁]
    ring

theorem localization_localization_exists_of_eq [IsLocalization N T] (x y : R) :
    algebraMap R T x = algebraMap R T y →
      ∃ c : localizationLocalizationSubmodule M N, ↑c * x = ↑c * y := by
  rw [IsScalarTower.algebraMap_apply R S T, IsScalarTower.algebraMap_apply R S T,
    IsLocalization.eq_iff_exists N T]
  rintro ⟨z, eq₁⟩
  rcases IsLocalization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩
  dsimp only at eq₂
  suffices (algebraMap R S) (x * z' : R) = (algebraMap R S) (y * z') by
    obtain ⟨c, eq₃ : ↑c * (x * z') = ↑c * (y * z')⟩ := (IsLocalization.eq_iff_exists M S).mp this
    refine ⟨⟨c * z', ?_⟩, ?_⟩
    · rw [mem_localizationLocalizationSubmodule]
      refine ⟨z, c * s, ?_⟩
      rw [map_mul, ← eq₂, Submonoid.coe_mul, map_mul, mul_left_comm]
    · rwa [mul_comm _ z', mul_comm _ z', ← mul_assoc, ← mul_assoc] at eq₃
  rw [map_mul, map_mul, ← eq₂, ← mul_assoc, ← mul_assoc, mul_comm _ (z : S), eq₁,
    mul_comm _ (z : S)]

/-- Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, we have
`N ⁻¹ S = T = (f⁻¹ (N • f(M))) ⁻¹ R`. I.e., the localization of a localization is a localization.
-/
theorem localization_localization_isLocalization [IsLocalization N T] :
    IsLocalization (localizationLocalizationSubmodule M N) T where
  map_units := localization_localization_map_units M N T
  surj := localization_localization_surj M N T
  exists_of_eq := localization_localization_exists_of_eq M N T _ _

include M in
/-- Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, if
`N` contains all the units of `S`, then `N ⁻¹ S = T = (f⁻¹ N) ⁻¹ R`. I.e., the localization of a
localization is a localization.
-/
theorem localization_localization_isLocalization_of_has_all_units [IsLocalization N T]
    (H : ∀ x : S, IsUnit x → x ∈ N) : IsLocalization (N.comap (algebraMap R S)) T := by
  convert localization_localization_isLocalization M N T using 1
  dsimp [localizationLocalizationSubmodule]
  congr
  symm
  rw [sup_eq_left]
  rintro _ ⟨x, hx, rfl⟩
  exact H _ (IsLocalization.map_units _ ⟨x, hx⟩)

include M in
/--
Given a submodule `M ⊆ R` and a prime ideal `p` of `S = M⁻¹R`, with `f : R →+* S` the localization
map, then `T = Sₚ` is the localization of `R` at `f⁻¹(p)`.
-/
theorem isLocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
    [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T (p.comap (algebraMap R S)) := by
  apply localization_localization_isLocalization_of_has_all_units M p.primeCompl T
  intro x hx hx'
  exact (Hp.1 : ¬_) (p.eq_top_of_isUnit_mem hx' hx)

instance (p : Ideal (Localization M)) [p.IsPrime] : Algebra R (Localization.AtPrime p) :=
  inferInstance

instance (p : Ideal (Localization M)) [p.IsPrime] :
    IsScalarTower R (Localization M) (Localization.AtPrime p) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance isLocalization_atPrime_localization_atPrime (p : Ideal (Localization M))
    [p.IsPrime] : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMap R _)) :=
  isLocalization_isLocalization_atPrime_isLocalization M _ _

/-- Given a submodule `M ⊆ R` and a prime ideal `p` of `M⁻¹R`, with `f : R →+* S` the localization
map, then `(M⁻¹R)ₚ` is isomorphic (as an `R`-algebra) to the localization of `R` at `f⁻¹(p)`.
-/
noncomputable def localizationLocalizationAtPrimeIsoLocalization (p : Ideal (Localization M))
    [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap R (Localization M))) ≃ₐ[R] Localization.AtPrime p :=
  IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl _ _

end

variable (S)

/-- Given submonoids `M ≤ N` of `R`, this is the canonical algebra structure
of `M⁻¹S` acting on `N⁻¹S`. -/
noncomputable abbrev localizationAlgebraOfSubmonoidLe (M N : Submonoid R) (h : M ≤ N)
    [IsLocalization M S] [IsLocalization N T] : Algebra S T :=
  (@IsLocalization.lift R _ M S _ _ T _ _ (algebraMap R T)
    (fun y => map_units T ⟨↑y, h y.prop⟩)).toAlgebra

/-- If `M ≤ N` are submonoids of `R`, then the natural map `M⁻¹S →+* N⁻¹S` commutes with the
localization maps -/
theorem localization_isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M ≤ N)
    [IsLocalization M S] [IsLocalization N T] :
    @IsScalarTower R S T _ (localizationAlgebraOfSubmonoidLe S T M N h).toSMul _ :=
  letI := localizationAlgebraOfSubmonoidLe S T M N h
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm

noncomputable instance instAlgebraLocalizationAtPrime (x : Ideal R) [H : x.IsPrime] [IsDomain R] :
    Algebra (Localization.AtPrime x) (Localization (nonZeroDivisors R)) :=
  localizationAlgebraOfSubmonoidLe _ _ x.primeCompl (nonZeroDivisors R)
    (by
      intro a ha
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact fun h => ha (h.symm ▸ x.zero_mem))

instance {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (Localization.AtPrime p) (FractionRing R) :=
  localization_isScalarTower_of_submonoid_le (Localization.AtPrime p) (FractionRing R)
    p.primeCompl (nonZeroDivisors R) p.primeCompl_le_nonZeroDivisors

set_option backward.simpa.using.reducibleClose false in
/-- If `M ≤ N` are submonoids of `R`, then `N⁻¹S` is also the localization of `M⁻¹S` at `N`. -/
theorem isLocalization_of_submonoid_le (M N : Submonoid R) (h : M ≤ N) [IsLocalization M S]
    [IsLocalization N T] [Algebra S T] [IsScalarTower R S T] :
    IsLocalization (N.map (algebraMap R S)) T where
  map_units := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert IsLocalization.map_units T ⟨y, hy⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
  surj y := by
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj N y
    refine ⟨⟨algebraMap R S x, _, _, s.prop, rfl⟩, ?_⟩
    simpa [← IsScalarTower.algebraMap_apply] using e
  exists_of_eq {x₁ x₂} := by
    obtain ⟨⟨y₁, s₁⟩, e₁⟩ := IsLocalization.surj M x₁
    obtain ⟨⟨y₂, s₂⟩, e₂⟩ := IsLocalization.surj M x₂
    refine (Set.exists_image_iff (algebraMap R S) N fun c => c * x₁ = c * x₂).mpr.comp ?_
    dsimp only at e₁ e₂ ⊢
    suffices algebraMap R T (y₁ * s₂) = algebraMap R T (y₂ * s₁) →
        ∃ a : N, algebraMap R S (a * (y₁ * s₂)) = algebraMap R S (a * (y₂ * s₁)) by
      have h₁ := @IsUnit.mul_left_inj T _ _ (algebraMap S T x₁) (algebraMap S T x₂)
        (IsLocalization.map_units T ⟨(s₁ : R), h s₁.prop⟩)
      have h₂ := @IsUnit.mul_left_inj T _ _ ((algebraMap S T x₁) * (algebraMap R T s₁))
        ((algebraMap S T x₂) * (algebraMap R T s₁))
        (IsLocalization.map_units T ⟨(s₂ : R), h s₂.prop⟩)
      simp only [IsScalarTower.algebraMap_apply R S T] at h₁ h₂
      simp only [IsScalarTower.algebraMap_apply R S T, map_mul, ← e₁, ← e₂, ← mul_assoc,
        mul_right_comm _ (algebraMap R S s₂),
        (IsLocalization.map_units S s₁).mul_left_inj,
        (IsLocalization.map_units S s₂).mul_left_inj] at this
      rw [h₂, h₁] at this
      simpa only [mul_comm] using this
    simp_rw [IsLocalization.eq_iff_exists N T, IsLocalization.eq_iff_exists M S]
    intro ⟨a, e⟩
    exact ⟨a, 1, by convert e using 1 <;> simp⟩

/-- If `M ≤ N` are submonoids of `R` such that `∀ x : N, ∃ m : R, m * x ∈ M`, then the
localization at `N` is equal to the localization of `M`. -/
theorem isLocalization_of_is_exists_mul_mem (M N : Submonoid R) [IsLocalization M S] (h : M ≤ N)
    (h' : ∀ x : N, ∃ m : R, m * x ∈ M) : IsLocalization N S where
  map_units y := by
    obtain ⟨m, hm⟩ := h' y
    have := IsLocalization.map_units S ⟨_, hm⟩
    rw [map_mul] at this
    exact (IsUnit.mul_iff.mp this).2
  surj z := by
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M z
    exact ⟨⟨y, _, h s.prop⟩, e⟩
  exists_of_eq {_ _} := by
    rw [IsLocalization.eq_iff_exists M]
    exact fun ⟨x, hx⟩ => ⟨⟨_, h x.prop⟩, hx⟩

theorem mk'_eq_algebraMap_mk'_of_submonoid_le {M N : Submonoid R} (h : M ≤ N) [IsLocalization M S]
    [IsLocalization N T] [Algebra S T] [IsScalarTower R S T] (x : R) (y : {a : R // a ∈ M}) :
    mk' T x ⟨y.1, h y.2⟩ = algebraMap S T (mk' S x y) :=
  mk'_eq_iff_eq_mul.mpr (by simp only [IsScalarTower.algebraMap_apply R S T, ← map_mul, mk'_spec])

end LocalizationLocalization

end IsLocalization

namespace IsFractionRing

variable {R : Type*} [CommRing R] (M : Submonoid R)

open IsLocalization

theorem isFractionRing_of_isLocalization (S T : Type*) [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] [IsLocalization M S] [IsFractionRing R T]
    (hM : M ≤ nonZeroDivisors R) : IsFractionRing S T := by
  have := isLocalization_of_submonoid_le S T M (nonZeroDivisors R) hM
  refine @isLocalization_of_is_exists_mul_mem _ _ _ _ _ _ _ this ?_ ?_
  · exact map_nonZeroDivisors_le M S
  · rintro ⟨x, -, hx⟩
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M x
    use algebraMap R S s
    rw [mul_comm, Subtype.coe_mk, e]
    refine Set.mem_image_of_mem (algebraMap R S) (mem_nonZeroDivisors_iff_right.mpr ?_)
    intro z hz
    apply IsLocalization.injective S hM
    rw [map_zero]
    apply hx
    rw [← (map_units S s).mul_left_inj, mul_assoc, e, ← map_mul, hz, map_zero,
      zero_mul]

theorem isFractionRing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalization M S] [IsFractionRing R T] : IsFractionRing S T := by
  haveI := IsFractionRing.nontrivial R T
  haveI := (algebraMap S T).domain_nontrivial
  apply isFractionRing_of_isLocalization M S T
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hx'
  apply @zero_ne_one S
  rw [← (algebraMap R S).map_one, ← @mk'_one R _ M, @comm _ Eq, mk'_eq_zero_iff]
  exact ⟨⟨x, hx⟩, by simp [hx']⟩

instance {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    IsFractionRing (Localization.AtPrime p) (FractionRing R) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl
    (Localization.AtPrime p) (FractionRing R)

end IsFractionRing
