/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure

/-!
# The spectral measure is supported on the spectrum

`spectralPVM hA` gives no mass to any Borel set of resolvent points:
`specProjection_eq_zero_of_subset_resolventSet`.  This is the last property of
the spectral measure the Davis--Kahan development consumes that does not follow
from the resolvent formula by algebra alone.

The proof is local, and needs no covering argument beyond Mathlib's:

* over a **bounded** set `B` clustered within `r` of a resolvent point `c`, the
  spectral range sits in `dom A` and `A - c` is bounded by `r` there
  (`norm_sub_smul_le_of_mem_specRange`), while `R(c)` inverts `A - c`.  So
  `‖x‖ ≤ ‖R(c)‖ r ‖x‖` for every `x` in the range, and `r ‖R(c)‖ < 1` forces the
  projection to vanish;
* for a general `B` of resolvent points, each `lam ∈ B` gets its own radius
  `r = (‖R(lam)‖ + 1)⁻¹`, which is exactly small enough, and
  `MeasureTheory.measure_null_of_locally_null` assembles the local vanishing
  into `diag ξ B = 0`.  The diagonal measures are honest Borel measures on `ℝ`,
  so the countable subcover is Mathlib's problem, not ours.

Going through the *diagonal measures* rather than the projections directly is
what makes the second step free: `‖E(B) ξ‖ ^ 2 = diag ξ B` welds them together
(`ProjValMeasure.norm_sq_proj_apply`).

## Provenance

*New.*  The Spectra endpoint is
`Spectra.QuantumMechanics.SpectralTheory.spectralPVM_proj_eq_zero_of_subset_resolventSet`,
which is where the theorem selection comes from; the proof is independent --
Spectra derives it from Stieltjes inversion of the Herglotz representation,
which this construction does not have and does not need.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Support

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- **A spectral set clustered around a resolvent point carries no
projection**, provided the clustering radius beats the norm of the resolvent
there.  `R(c)` inverts `A - c`, and on the spectral range `A - c` is bounded by
`r`; if `r ‖R(c)‖ < 1` the two estimates compose to `‖x‖ < ‖x‖`. -/
theorem specProjection_eq_zero_of_norm_resolvent_mul_lt_one
    (B : Set ℝ) (hB : MeasurableSet B) {M c r : ℝ}
    (hbnd : ∀ s ∈ B, |s| ≤ M) (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r)
    (hc : (c : ℂ) ∈ resolventSet A)
    (hsmall : r * ‖resolvent A (c : ℂ)‖ < 1) :
    specProjection hA B hB = 0 := by
  refine ContinuousLinearMap.ext fun y => ?_
  set x : H := specProjection hA B hB y with hxdef
  have hxrange : x ∈ specRange hA B hB := specProjection_mem_specRange hA B hB y
  have hmem : x ∈ A.domain :=
    mem_domain_of_mem_specRange_of_bounded hA B hB hbnd hxrange
  have hb : ‖A ⟨x, hmem⟩ - (c : ℂ) • x‖ ≤ r * ‖x‖ :=
    norm_sub_smul_le_of_mem_specRange hA B hB hbnd hr hcr hxrange hmem
  have hrec : resolvent A (c : ℂ) ((c : ℂ) • (x : H) - A ⟨x, hmem⟩) = x :=
    resolvent_smul_sub_apply hc ⟨x, hmem⟩
  have hb' : ‖(c : ℂ) • x - A ⟨x, hmem⟩‖ ≤ r * ‖x‖ := by
    rwa [norm_sub_rev]
  have hnx : ‖x‖ ≤ ‖resolvent A (c : ℂ)‖ * (r * ‖x‖) := by
    calc ‖x‖ = ‖resolvent A (c : ℂ) ((c : ℂ) • (x : H) - A ⟨x, hmem⟩)‖ := by rw [hrec]
      _ ≤ ‖resolvent A (c : ℂ)‖ * ‖(c : ℂ) • x - A ⟨x, hmem⟩‖ :=
          (resolvent A (c : ℂ)).le_opNorm _
      _ ≤ ‖resolvent A (c : ℂ)‖ * (r * ‖x‖) :=
          mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
  have hx0 : ‖x‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith [norm_nonneg (resolvent A (c : ℂ))]
  simpa [hxdef] using norm_eq_zero.mp hx0

/-- **The diagonal measures are supported on the spectrum.**  A Borel set of
resolvent points is null for every diagonal measure.

Stated before the projection form because it is the one a covering argument can
prove: `diag ξ` is an honest Borel measure on `ℝ`, so
`measure_null_of_locally_null` assembles a purely local statement into a global
one, which the projections themselves cannot do. -/
theorem diag_eq_zero_of_subset_resolventSet
    (B : Set ℝ) (hB : MeasurableSet B)
    (hres : ∀ lam ∈ B, (lam : ℂ) ∈ resolventSet A) (ξ : H) :
    ((spectralPVM hA).diag ξ) B = 0 := by
  refine measure_null_of_locally_null (μ := (spectralPVM hA).diag ξ) B ?_
  intro lam hlam
  set R := resolvent A (lam : ℂ) with hRdef
  have hRnn : (0 : ℝ) ≤ ‖R‖ := norm_nonneg _
  set r : ℝ := (‖R‖ + 1)⁻¹ with hrdef
  have hden : (0 : ℝ) < ‖R‖ + 1 := by linarith
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hsmall : r * ‖R‖ < 1 := by
    rw [hrdef, inv_mul_eq_div]
    exact (div_lt_one hden).mpr (by linarith)
  refine ⟨B ∩ Set.Ioo (lam - r) (lam + r),
    inter_mem_nhdsWithin B (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  set u : Set ℝ := B ∩ Set.Ioo (lam - r) (lam + r) with hudef
  have humeas : MeasurableSet u := hB.inter measurableSet_Ioo
  have hzero : specProjection hA u humeas = 0 := by
    refine specProjection_eq_zero_of_norm_resolvent_mul_lt_one hA u humeas
      (M := |lam| + r) (fun s hs => ?_) hrpos.le (fun s hs => ?_)
      (hres lam hlam) hsmall
    · have h := hs.2
      rw [abs_le]
      constructor
      · nlinarith [neg_abs_le lam, h.1]
      · nlinarith [le_abs_self lam, h.2]
    · have h := hs.2
      rw [abs_le]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hq := (spectralPVM hA).norm_sq_proj_apply u humeas ξ
  rw [show (spectralPVM hA).proj u humeas = specProjection hA u humeas from
      (specProjection_def hA u humeas).symm,
    hzero] at hq
  simp only [zero_apply, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hq
  exact (ENNReal.toReal_eq_zero_iff _).mp hq.symm
    |>.resolve_right (measure_ne_top _ _)

/-- **The spectral measure is supported on the spectrum.**  A Borel set of
resolvent points carries the zero projection. -/
theorem specProjection_eq_zero_of_subset_resolventSet
    (B : Set ℝ) (hB : MeasurableSet B)
    (hres : ∀ lam ∈ B, (lam : ℂ) ∈ resolventSet A) :
    specProjection hA B hB = 0 := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  have hq := (spectralPVM hA).norm_sq_proj_apply B hB ξ
  rw [show (spectralPVM hA).proj B hB = specProjection hA B hB from
      (specProjection_def hA B hB).symm,
    diag_eq_zero_of_subset_resolventSet hA B hB hres ξ] at hq
  simp only [ENNReal.toReal_zero] at hq
  have hz : ‖specProjection hA B hB ξ‖ = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hq
  simpa using norm_eq_zero.mp hz

end Support

end LinearPMap
end TauCeti
