/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStandardPhysicalRecombination
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStandardSourceScaleSummation

/-!
# The scalar-standard maximal-tail closure at one Krause--Lacey node

The fixed-physical-scale estimates are already proved in the standard-source
modules. This file performs the remaining finite maximal-tail bookkeeping in
the high-scale regime used in the source proof. It introduces no analytic
hypothesis: a physical suffix is bounded by the sum of the norms of all of its
layers, and the established geometric scale sum then removes the number of
layers.

This is only the scalar-standard contribution of the bad input. It does not
assert the complete one-node estimate, which additionally requires the exact
good/bad input decomposition and the nonstandard contribution.
-/

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace KrauseLaceyBadScale


noncomputable
section

/-- The physical scales which can occur in a suffix whose lower endpoint is
`k₀`. -/
def standardHighPhysicalScaleSupport
    (S : Finset RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ) : Finset ℤ :=
  (standardPhysicalScaleSupport S scale).filter fun j ↦ k₀ ≤ j

/-- The source's standard maximal tail, restricted to the high regime
`ell ≥ k₀`. In the application `k₀ ≥ 3`, equivalently every amplitude index
is at least one. -/
noncomputable def energyStandardPhysicalTailMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (x : ℝ) : ℝ :=
  ⨆ ell : {ell : ℤ // k₀ ≤ ell},
    ‖energyStandardPhysicalTailAction S f I₀ k₀ scale ell.1 x‖

private theorem integrable_energyStandardPhysicalLayerAction
    (S : Finset RealInterval) {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ) (j : ℤ) :
    Integrable (energyStandardPhysicalLayerAction S f I₀ k₀ scale j) := by
  unfold energyStandardPhysicalLayerAction energyStandardFixedPhysicalSourceAction
  apply integrable_finsetSum
  intro s hs
  apply integrable_finsetSum
  intro I hI
  exact integrable_krauseLaceyLocalizedPiece _ _
    (integrable_badScaleInput S hf I₀ k₀ _)

private theorem aestronglyMeasurable_standardPhysicalTailMaximal
    (S : Finset RealInterval) {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ) :
    AEStronglyMeasurable (energyStandardPhysicalTailMaximal S f I₀ k₀ scale) volume := by
  apply AEMeasurable.aestronglyMeasurable
  apply AEMeasurable.iSup
  intro ell
  apply AEStronglyMeasurable.aemeasurable
  apply AEStronglyMeasurable.norm
  apply Finset.aestronglyMeasurable_fun_sum
  intro j hj
  exact (integrable_energyStandardPhysicalLayerAction S hf I₀ k₀ scale j).aestronglyMeasurable

private theorem norm_energyStandardPhysicalTailAction_le_sum
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (ell : {ell : ℤ // k₀ ≤ ell}) (x : ℝ) :
    ‖energyStandardPhysicalTailAction S f I₀ k₀ scale ell.1 x‖ ≤
      ∑ j ∈ standardHighPhysicalScaleSupport S k₀ scale,
        ‖energyStandardPhysicalLayerAction S f I₀ k₀ scale j x‖ := by
  unfold energyStandardPhysicalTailAction standardHighPhysicalScaleSupport
  calc
    _ ≤ ∑ j ∈ (standardPhysicalScaleSupport S scale).filter (fun j ↦ ell.1 ≤ j),
        ‖energyStandardPhysicalLayerAction S f I₀ k₀ scale j x‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        have h := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨h.1, ell.2.trans h.2⟩
      · intro j hj hnot
        exact norm_nonneg _

theorem energyStandardPhysicalTailMaximal_nonneg
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (x : ℝ) :
    0 ≤ energyStandardPhysicalTailMaximal S f I₀ k₀ scale x := by
  let M := ∑ j ∈ standardHighPhysicalScaleSupport S k₀ scale,
    ‖energyStandardPhysicalLayerAction S f I₀ k₀ scale j x‖
  have hb : BddAbove (Set.range fun ell : {ell : ℤ // k₀ ≤ ell} ↦
      ‖energyStandardPhysicalTailAction S f I₀ k₀ scale ell.1 x‖) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨ell, rfl⟩
    exact norm_energyStandardPhysicalTailAction_le_sum S f I₀ k₀ scale ell x
  exact (norm_nonneg _).trans (le_ciSup hb ⟨k₀, le_rfl⟩)

theorem energyStandardPhysicalTailMaximal_le_sum
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (x : ℝ) :
    energyStandardPhysicalTailMaximal S f I₀ k₀ scale x ≤
      ∑ j ∈ standardHighPhysicalScaleSupport S k₀ scale,
        ‖energyStandardPhysicalLayerAction S f I₀ k₀ scale j x‖ := by
  apply ciSup_le
  intro ell
  exact norm_energyStandardPhysicalTailAction_le_sum S f I₀ k₀ scale ell x

/-- The checked fixed-scale standard estimates imply the source's uniform
maximal-tail `L^q` estimate. There is no cardinality loss: the factor `40*q`
is the already proved geometric scale sum. -/
theorem eLpNorm_energyStandardPhysicalTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    {q : ℝ} (hq : 2 ≤ q) :
    eLpNorm (energyStandardPhysicalTailMaximal S f I₀ k₀ scale)
        (ENNReal.ofReal q) volume ≤
      standardSourceNormBudget f I₀ q * ENNReal.ofReal (40 * q) := by
  let P := standardHighPhysicalScaleSupport S k₀ scale
  let F : ℤ → ℝ → ℂ := fun j x ↦
    (‖energyStandardPhysicalLayerAction S f I₀ k₀ scale j x‖ : ℂ)
  have hP (j : ℤ) (hj : j ∈ P) : k₀ ≤ j :=
    (Finset.mem_filter.mp hj).2
  have hF (j : ℤ) (hj : j ∈ P) : AEStronglyMeasurable (F j) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (integrable_energyStandardPhysicalLayerAction S hf I₀ k₀ scale j).norm.aestronglyMeasurable
  have hbound (j : ℤ) (hj : j ∈ P) :
      eLpNorm (F j) (ENNReal.ofReal q) volume ≤
        standardSourceNormBudget f I₀ q *
          ENNReal.ofReal (((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)) := by
    have heq :
        eLpNorm (F j) (ENNReal.ofReal q) volume =
          eLpNorm (energyStandardPhysicalLayerAction S f I₀ k₀ scale j)
            (ENNReal.ofReal q) volume := by
      apply eLpNorm_congr_norm_ae (hF j hj)
        (integrable_energyStandardPhysicalLayerAction S hf I₀ k₀ scale j).aestronglyMeasurable
      filter_upwards with x
      simp only [F, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    rw [heq]
    exact eLpNorm_energyStandardFixedPhysicalSourceAction_le_budget_mul_ratio
      hf I₀ k₀ j (by omega) (hP j hj) scale hlam hsub
      (fun s ↦ energyStandardPhysicalLayer S f I₀ k₀ s scale j)
      (fun s _ ↦ energyStandardPhysicalLayer_subset S f I₀ k₀ s scale j)
      (fun _ _ I hI ↦ physical_eq_of_mem_energyStandardPhysicalLayer hI) hq
  calc
    eLpNorm (energyStandardPhysicalTailMaximal S f I₀ k₀ scale)
        (ENNReal.ofReal q) volume ≤ eLpNorm (∑ j ∈ P, F j)
          (ENNReal.ofReal q) volume := by
      apply eLpNorm_mono
        (aestronglyMeasurable_standardPhysicalTailMaximal S hf I₀ k₀ scale)
      intro x
      rw [Real.norm_of_nonneg
        (energyStandardPhysicalTailMaximal_nonneg S f I₀ k₀ scale x)]
      have hsum0 : 0 ≤ ∑ j ∈ P,
          ‖energyStandardPhysicalLayerAction S f I₀ k₀ scale j x‖ :=
        Finset.sum_nonneg fun j _ ↦ norm_nonneg _
      rw [show (∑ j ∈ P, F j) x =
          ((∑ j ∈ P,
            ‖energyStandardPhysicalLayerAction S f I₀ k₀ scale j x‖ : ℝ) : ℂ) by
        simp only [Finset.sum_apply, F]
        norm_cast]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum0]
      simpa only [P] using
        energyStandardPhysicalTailMaximal_le_sum S f I₀ k₀ scale x
    _ ≤ standardSourceNormBudget f I₀ q * ENNReal.ofReal (40 * q) := by
      apply eLpNorm_finset_sum_le_budget_mul_forty_mul_q hq P F hbound
      intro j hj
      exact le_trans (by omega : 0 ≤ k₀) (hP j hj)


end
end KrauseLaceyBadScale
end QuadraticCarleson
