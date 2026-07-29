/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CenteredCanonicalZeroFactor
public import LeanPool.Odlyzko.ExplicitFormula.FiniteZeroSumBound

/-!
# Canonical Zero Sum Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex ComplexConjugate Metric Set

namespace NumberField.Odlyzko

open Classical in
theorem norm_finsum_reflected_centered_le
    {D : ℂ → ℤ} (hfin : D.support.Finite) (hD : ∀ u, 0 ≤ D u)
    {c z : ℂ} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ closedBall c r) :
    ‖∑ᶠ u,
        (D u : ℂ) *
          (conj (u - c) /
            ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ ≤
      ((∑ᶠ u, D u : ℤ) : ℝ) / (R - r) := by
  let S := hfin.toFinset
  have hsupp : D.support ⊆ S := fun u hu ↦ hfin.mem_toFinset.mpr hu
  have hterm :
      (fun u ↦
        (D u : ℂ) *
          (conj (u - c) /
            ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))).support ⊆ S := by
    intro u hu
    simp_all
  have hsumC :
      ∑ᶠ u,
          (D u : ℂ) *
            (conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c))) =
        ∑ u ∈ S,
          (D u : ℂ) *
            (conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c))) :=
    finsum_eq_sum_of_support_subset _ hterm
  have hsumZ : ∑ᶠ u, D u = ∑ u ∈ S, D u :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsumC, hsumZ]
  calc
    ‖∑ u ∈ S,
        (D u : ℂ) *
          (conj (u - c) /
            ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ ≤
        ∑ u ∈ S,
          ‖(D u : ℂ) *
            (conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ u ∈ S, (D u : ℝ) * (1 / (R - r)) := by
      apply Finset.sum_le_sum
      intro u hu
      have huD : 0 ≤ (D u : ℝ) := by simp_all
      rw [norm_mul, norm_intCast, abs_of_nonneg huD]
      exact mul_le_mul_of_nonneg_left
        (norm_conj_div_reflected_centered_le hR hr hrR
          (hinside u (hfin.mem_toFinset.mp hu)) hz) huD
    _ = ((∑ u ∈ S, D u : ℤ) : ℝ) / (R - r) := by
      rw [Int.cast_sum]
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      simp only [one_mul]

open Classical in
theorem norm_finsum_canonicalLogDeriv_le
    {D : ℂ → ℤ} (hfin : D.support.Finite) (hD : ∀ u, 0 ≤ D u)
    {c z : ℂ} {δ r R : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ closedBall c r)
    (hsep : ∀ u ∈ D.support, δ ≤ ‖z - u‖) :
    ‖∑ᶠ u,
        (D u : ℂ) *
          (1 / (z - u) +
            conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ ≤
      ((∑ᶠ u, D u : ℤ) : ℝ) / δ +
        ((∑ᶠ u, D u : ℤ) : ℝ) / (R - r) := by
  have hfinA : Function.HasFiniteSupport
      (fun u ↦ (D u : ℂ) * (1 / (z - u))) := by
    apply hfin.subset
    intro u hu
    simp_all
  have hfinB : Function.HasFiniteSupport
      (fun u ↦
        (D u : ℂ) *
          (conj (u - c) /
            ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))) := by
    apply hfin.subset
    intro u hu
    simp_all
  simp_rw [mul_add]
  rw [finsum_add_distrib hfinA hfinB]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have heq :
        (∑ᶠ u, (D u : ℂ) * (1 / (z - u))) =
          ∑ᶠ u, (D u : ℂ) / (z - u) := by grind
    rw [heq]
    exact norm_finsum_div_sub_le_finsum_div hfin hD hδ hsep
  · exact norm_finsum_reflected_centered_le
      hfin hD hR hr hrR hinside hz

open Classical in
theorem norm_finsum_canonicalLogDeriv_le_of_finsum_le
    {D : ℂ → ℤ} (hfin : D.support.Finite) (hD : ∀ u, 0 ≤ D u)
    {c z : ℂ} {δ r R B : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ closedBall c r)
    (hsep : ∀ u ∈ D.support, δ ≤ ‖z - u‖)
    (hmass : ((∑ᶠ u, D u : ℤ) : ℝ) ≤ B) :
    ‖∑ᶠ u,
        (D u : ℂ) *
          (1 / (z - u) +
            conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ ≤
      B / δ + B / (R - r) := by
  refine (norm_finsum_canonicalLogDeriv_le
    hfin hD hδ hR hr hrR hinside hz hsep).trans ?_
  exact add_le_add
    (div_le_div_of_nonneg_right hmass hδ.le)
    (div_le_div_of_nonneg_right hmass (sub_nonneg.mpr hrR.le))

end NumberField.Odlyzko
