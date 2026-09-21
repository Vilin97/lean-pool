/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.OpenIdeals

/-!
# Analytic Points of the Adic Spectrum

We define *analytic points* of the valuation spectrum and prove that every point
of `Spa(A, A⁺)` is analytic when `A` is a Tate ring.

## Main definitions

* `ValuationSpectrum.IsAnalytic v` : A point `v : Spv A` is *analytic* if its support
  `supp(v)` is not an open ideal of `A` (Definition 8.35 of Wedhorn).
* `ValuationSpectrum.IsTrivialValuation v` : A point `v : Spv A` has a *trivial valuation*
  if all elements outside the support are `v`-equivalent.
* `ValuationSpectrum.SpaIsAnalytic A` : The adic spectrum `Spa(A, A⁺)` is *analytic* if it
  contains no trivial valuation points.

## Main results

* `IsTateRing.isAnalytic` : If `A` is a Tate ring, then every `v : Spv A` is analytic
  (Proposition 8.36 of Wedhorn).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 8.35, Proposition 8.36
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A point `v : Spv A` is *analytic* if its support `supp(v)` is not an open ideal
(Definition 8.35 of Wedhorn). -/
def IsAnalytic (v : Spv A) : Prop :=
  ¬IsOpen (v.supp : Set A)

/-- **Proposition 8.36 of Wedhorn.** If `A` is a Tate ring, every point of `Spv A` is analytic. -/
theorem IsTateRing.isAnalytic [IsTateRing A] (v : Spv A) : IsAnalytic v := by
  obtain ⟨u, hu_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  intro h_open
  exact (v.mem_supp_iff _).not.mpr (not_vle_zero_of_isUnit u.isUnit v)
    ((instIsPrimeSupp v).radical ▸ hu_nil.mem_ideal_radical h_open)

/-! ### Trivial valuations -/

/-- A point `v : Spv A` has a **trivial valuation** if all elements outside the support are
`v`-equivalent: `v(a) ≤ v(b)` whenever `a ∉ supp(v)` and `b ∉ supp(v)`. This corresponds
to the induced valuation on `A / supp(v)` being the trivial (rank-zero) valuation. -/
def IsTrivialValuation (v : Spv A) : Prop :=
  ∀ a b : A, a ∉ v.supp → b ∉ v.supp → v.vle a b

/-! ### Analytic adic spectra -/

/-- The adic spectrum `Spa(A, A⁺)` is **analytic** if it contains no trivial valuation
points. This is the condition appearing in Scottish Book Problem 10
(cf. Definition 8.35, Proposition 8.36 of Wedhorn). -/
def SpaIsAnalytic (A : Type*) [CommRing A] [TopologicalSpace A] [PlusSubring A] : Prop :=
  ∀ v ∈ Spa A A⁺, ¬ IsTrivialValuation v

end ValuationSpectrum

/-! ### Non-open primes and the ideal of definition -/

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

omit [IsLinearTopology A A] in
/-- If a prime ideal contains the ideal of definition, then it is open. -/
theorem isOpen_of_idealOfDefinition_le (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (hle : P.idealOfDefinition ≤ 𝔭) : IsOpen (𝔭 : Set A) :=
  P.ideal_isOpen_of_nilpotent_le_radical fun _ ha ↦
    Ideal.radical_mono hle (P.isTopologicallyNilpotent_mem_idealOfDefinition_radical ha)

omit [IsLinearTopology A A] in
/-- A non-open prime does not contain the ideal of definition (Lemma 7.45). -/
theorem idealOfDefinition_not_le_of_not_isOpen (P : PairOfDefinition A) {𝔭 : Ideal A}
    [𝔭.IsPrime] (h : ¬IsOpen (𝔭 : Set A)) : ¬P.idealOfDefinition ≤ 𝔭 :=
  fun hle ↦ h (P.isOpen_of_idealOfDefinition_le hle)

omit [IsLinearTopology A A] in
/-- A non-open prime does not contain all of `I`: there exists `a ∈ I` with `a ∉ 𝔭`. -/
theorem exists_mem_I_not_mem_of_not_isOpen (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (h : ¬IsOpen (𝔭 : Set A)) : ∃ a ∈ P.I, (P.A₀.subtype a : A) ∉ 𝔭 := by
  by_contra h_all
  push Not at h_all
  exact P.idealOfDefinition_not_le_of_not_isOpen h
    (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ h_all a ha)

/-! ### Jacobson radical and I-adic completeness -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- If `A₀` is `I`-adically complete, then `I ≤ 𝔪` for every maximal `𝔪`. -/
theorem I_le_maximal_of_isAdicComplete (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔪 : Ideal P.A₀} (h𝔪 : 𝔪.IsMaximal) : P.I ≤ 𝔪 :=
  (IsAdicComplete.le_jacobson_bot (I := P.I)).trans (sInf_le ⟨bot_le, h𝔪⟩)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- If `A₀` is `I`-adically complete and `I ⊄ 𝔭₀`, then `𝔭₀` is not maximal. -/
theorem not_isMaximal_of_I_not_le (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭₀ : Ideal P.A₀} (h : ¬P.I ≤ 𝔭₀) : ¬𝔭₀.IsMaximal :=
  fun h𝔪 ↦ h (P.I_le_maximal_of_isAdicComplete h𝔪)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- If `A₀` is `I`-adically complete and `𝔭₀` is prime, then `I + 𝔭₀ ≠ A₀`
(Lemma 7.45). -/
theorem I_sup_prime_ne_top (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭₀ : Ideal P.A₀} [𝔭₀.IsPrime] : P.I ⊔ 𝔭₀ ≠ ⊤ := by
  intro htop
  obtain ⟨i, hi, p, hp, hip⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
  have h_unit : IsUnit p := by
    have : IsUnit (1 - i) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (by
      change (1 - i) - 1 ∈ (⊥ : Ideal P.A₀).jacobson
      rw [show (1 : ↥P.A₀) - i - 1 = -i from by ring]
      exact neg_mem (IsAdicComplete.le_jacobson_bot (I := P.I) hi))
    rwa [show (1 : ↥P.A₀) - i = p from by linear_combination -hip] at this
  exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem 𝔭₀ hp h_unit)

end PairOfDefinition
