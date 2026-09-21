/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardPhysicalL2

/-!
# The exact source physical-suffix parameter range

KL18 uses length-index tails starting at `ell ≥ k₀+s`. Every actual
nonstandard interval already has length at least `2^(k₀+s)`, so the
all-integer maximal function is exactly this source-restricted maximum.
No generation labels or reversed prefix convention enter this identity.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

attribute [local instance] Classical.propDecidable

/-- The supremum of bad length-tail norms over source cutoffs at least `k₀ + s`. -/
noncomputable def nonstandardSourceTailMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (x : ℝ) : ℝ :=
  ⨆ ell : {ell : ℤ // k₀ + s ≤ ell}, ‖badLengthTailAction S f I₀ k₀ s scale N ell.1 x‖

theorem badLengthTailAction_eq_at_max_lower_endpoint
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (ell : ℤ) (x : ℝ) :
    badLengthTailAction S f I₀ k₀ s scale N ell x =
      badLengthTailAction S f I₀ k₀ s scale N (max ell (k₀ + s)) x := by
  by_cases he : k₀ + s ≤ ell
  · rw [max_eq_left he]
  rw [max_eq_right (le_of_not_ge he)]
  unfold badLengthTailAction
  apply Finset.sum_congr rfl
  intro I hI
  have hi := (Finset.mem_filter.mp (hN hI)).2
  have hbase : (2 : ℝ) ^ (k₀ + s) ≤ I.length := by
    rw [hi.1]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hell : (2 : ℝ) ^ ell ≤ I.length :=
    (zpow_le_zpow_right₀ (by norm_num) (le_of_not_ge he)).trans hbase
  rw [ite_eq_left hbase, ite_eq_left hell]

theorem nonstandardSourceTailMaximal_eq_badLengthTailMaximal
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    nonstandardSourceTailMaximal S f I₀ k₀ s scale N x =
      badLengthTailMaximal S f I₀ k₀ s scale N x := by
  have hb : BddAbove (Set.range fun ell : ℤ ↦ ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖) := by
    refine ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x, ?_⟩
    rintro _ ⟨ell, rfl⟩
    exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell x
  have hbr : BddAbove (Set.range fun ell : {ell : ℤ // k₀ + s ≤ ell} ↦
      ‖badLengthTailAction S f I₀ k₀ s scale N ell.1 x‖) := by
    refine ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x, ?_⟩
    rintro _ ⟨ell, rfl⟩
    exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell.1 x
  apply le_antisymm
  · exact ciSup_le fun ell ↦ le_ciSup hb ell.1
  · apply ciSup_le
    intro ell
    rw [badLengthTailAction_eq_at_max_lower_endpoint S f I₀ k₀ s scale N hN ell x]
    exact le_ciSup hbr ⟨max ell (k₀ + s), le_max_right _ _⟩

/-- The complete bound with exactly the source's physical suffix
orientation and lower endpoint. -/
theorem eLpNorm_nonstandardSourceTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) :
    eLpNorm (nonstandardSourceTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
        Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  have he : nonstandardSourceTailMaximal S f I₀ k₀ s scale N =
      badLengthTailMaximal S f I₀ k₀ s scale N := funext
    (nonstandardSourceTailMaximal_eq_badLengthTailMaximal f I₀ k₀ s scale hlam N hN)
  rw [he]
  exact eLpNorm_nonstandard_badLengthTailMaximal_le hf I₀ k₀ s hk₀ scale hlam hparent hsub N hN


end KrauseLaceyBadScale
end QuadraticCarleson
