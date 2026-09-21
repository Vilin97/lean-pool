/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Finite projective normalization in a valuation subring

A finite nonzero vector over the fraction field of a valuation ring can be
scaled into the valuation ring so that one coordinate is exactly one.  The
same scalar is used in every coordinate, so all projective ratios and
homogeneous equations are preserved.
-/

namespace Stafford38.Geometry.ProjectiveValuationNormalization

noncomputable section

universe u v

/-- The canonical map from a Noetherian local ring into its proper-ideal
adic completion is injective. -/
theorem adicCompletion_algebraMap_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) :
    Function.Injective (algebraMap R (AdicCompletion I R)) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hmem : x - y ∈ ⨅ n : ℕ, I ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    have heval := congrArg
      (fun z ↦ (AdicCompletion.eval I R n) z) hxy
    change (I ^ n • ⊤ : Ideal R).mkQ x =
      (I ^ n • ⊤ : Ideal R).mkQ y at heval
    simpa using (Submodule.Quotient.eq (I ^ n • ⊤ : Ideal R)).mp heval
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing I hI] at hmem
  exact hmem

/-- A finite family in a valuation ring has a member dividing every member. -/
theorem exists_index_dvd_all
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {ι : Type v} [Finite ι] [Nonempty ι] (a : ι → R) :
    ∃ c, ∀ i, a c ∣ a i := by
  classical
  let := Fintype.ofFinite ι
  classical
  let s : Finset (Associates R) :=
    Finset.univ.image fun i ↦ Associates.mk (a i)
  have hs : s.Nonempty := by
    let i : ι := Classical.choice inferInstance
    exact ⟨Associates.mk (a i), Finset.mem_image.2
      ⟨i, Finset.mem_univ i, rfl⟩⟩
  obtain ⟨m, hm, hminimal⟩ := s.exists_minimal hs
  obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hm
  refine ⟨c, fun i ↦ Associates.dvd_of_mk_le_mk ?_⟩
  have hi : Associates.mk (a i) ∈ s :=
    Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  rw [hc]
  by_contra hnot
  have hnotdvd : ¬a c ∣ a i := by
    intro h
    apply hnot
    rw [← hc]
    exact Associates.mk_le_mk_of_dvd h
  have hreverse : Associates.mk (a i) ≤ m := by
    rw [← hc]
    exact Associates.mk_le_mk_of_dvd
      ((ValuationRing.dvd_total (a c) (a i)).resolve_left hnotdvd)
  exact hnot (hminimal hi hreverse)

/-- A finite nonzero projective vector over a field has a common normalized
lift to any valuation subring of that field. -/
theorem exists_normalized_projective_lift
    {K : Type u} [Field K] (V : ValuationSubring K)
    {ι : Type v} [Finite ι] [Nonempty ι]
    (f : ι → K) (hf : ∃ i, f i ≠ 0) :
    ∃ (chart : ι) (q : ι → V) (scale : K),
      scale ≠ 0 ∧ q chart = 1 ∧
      ∀ i, (q i : K) = scale * f i := by
  classical
  let := Fintype.ofFinite ι
  classical
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors V) f
  let a : ι → V := fun i ↦ (hb i).choose
  have ha : ∀ i, algebraMap V K (a i) =
      algebraMap V K (b : V) * f i := by
    intro i
    simpa only [a, Algebra.smul_def] using (hb i).choose_spec
  obtain ⟨chart, hchart⟩ := exists_index_dvd_all a
  let q : ι → V := fun i ↦
    if h : i = chart then 1 else (hchart i).choose
  have haq : ∀ i, a i = a chart * q i := by
    intro i
    by_cases h : i = chart
    · subst i
      simp [q]
    · simpa [q, h] using (hchart i).choose_spec
  have hb_ne : (b : V) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hbK_ne : algebraMap V K (b : V) ≠ 0 :=
    (IsFractionRing.injective V K).ne hb_ne
  have hchart_ne : a chart ≠ 0 := by
    obtain ⟨i, hi⟩ := hf
    intro hzero
    have hai : a i = 0 := by rw [haq i, hzero, zero_mul]
    have : algebraMap V K (b : V) * f i = 0 := by
      rw [← ha i, hai, map_zero]
    exact hi ((mul_eq_zero.mp this).resolve_left hbK_ne)
  have hchartK_ne : algebraMap V K (a chart) ≠ 0 :=
    (IsFractionRing.injective V K).ne hchart_ne
  let scale : K := algebraMap V K (b : V) / algebraMap V K (a chart)
  refine ⟨chart, q, scale, div_ne_zero hbK_ne hchartK_ne, ?_, ?_⟩
  · simp [q]
  · intro i
    change algebraMap V K (q i) = scale * f i
    apply mul_left_cancel₀ hchartK_ne
    calc
      algebraMap V K (a chart) * algebraMap V K (q i) =
          algebraMap V K (a chart * q i) := by rw [map_mul]
      _ = algebraMap V K (a i) := by rw [← haq i]
      _ = algebraMap V K (b : V) * f i := ha i
      _ = algebraMap V K (a chart) * (scale * f i) := by
        dsimp [scale]
        calc
          algebraMap V K (b : V) * f i =
              (algebraMap V K (a chart) *
                (algebraMap V K (a chart))⁻¹) *
                (algebraMap V K (b : V) * f i) := by
                  rw [mul_inv_cancel₀ hchartK_ne, one_mul]
          _ = algebraMap V K (a chart) *
                ((algebraMap V K (b : V) /
                  algebraMap V K (a chart)) * f i) := by
                  rw [div_eq_mul_inv]
                  ring


end

end Stafford38.Geometry.ProjectiveValuationNormalization
