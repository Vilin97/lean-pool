/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.DyadicIncrements

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/

namespace MarkovProcess

section DyadicGridChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- Uniform control of adjacent increments on one unit dyadic grid controls the increment
between any two ordered grid points by the number of intervening cells. -/
theorem edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le
    {X : NNRat → Ω → E} {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ n),
      edist (X (unitDyadicGrid n k.castSucc) ω)
          (X (unitDyadicGrid n k.succ) ω) ≤ ε)
    (i j : Fin (2 ^ n + 1)) (hij : (i : ℕ) ≤ j) :
    edist (X (unitDyadicGrid n i) ω) (X (unitDyadicGrid n j) ω) ≤
      (j.val - i.val : ℕ) * ε := by
  let f : ℕ → E := fun k ↦
    if hk : k < 2 ^ n + 1 then X (unitDyadicGrid n ⟨k, hk⟩) ω
    else X (unitDyadicGrid n i) ω
  have hf (k : ℕ) (hk : k < 2 ^ n + 1) :
      f k = X (unitDyadicGrid n ⟨k, hk⟩) ω := by
    simp only [f, dif_pos hk]
  calc
    edist (X (unitDyadicGrid n i) ω) (X (unitDyadicGrid n j) ω) =
        edist (f i) (f j) := by rw [hf i i.isLt, hf j j.isLt]
    _ ≤ ∑ _k ∈ Finset.Ico i.val j.val, ε := by
      apply edist_le_Ico_sum_of_edist_le hij
      intro k hik hkj
      have hkpow : k < 2 ^ n := lt_of_lt_of_le hkj (Nat.le_of_lt_succ j.isLt)
      have hksucc : k + 1 < 2 ^ n + 1 := Nat.add_lt_add_right hkpow 1
      rw [hf k (lt_trans hkpow (Nat.lt_succ_self _)), hf (k + 1) hksucc]
      simpa only [Fin.val_castSucc, Fin.val_succ] using! hadj ⟨k, hkpow⟩
    _ = (j.val - i.val : ℕ) * ε := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- Almost surely, on every sufficiently fine unit dyadic grid, the increment between
ordered grid points is bounded by their number of intervening cells times the level's
Kolmogorov--Chentsov threshold. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_le_natCast_mul_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ i j : Fin (2 ^ n + 1),
      (i : ℕ) ≤ j →
        edist (X (unitDyadicGrid n i) ω) (X (unitDyadicGrid n j) ω) ≤
          (j.val - i.val : ℕ) * dyadicIncrementThreshold γ n := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_adjacent_lt_threshold
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro i j hij
  exact edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le
    (fun k ↦ (hn k).le) i j hij

end DyadicGridChaining

section DyadicMultiscale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The canonical inclusion of the level-`n` unit dyadic grid into level `n + 1`.
Its value is twice the old grid index. -/
def unitDyadicRefineIndex (n : ℕ) (i : Fin (2 ^ n + 1)) : Fin (2 ^ (n + 1) + 1) :=
  ⟨2 * i.val, by
    have hi : i.val ≤ 2 ^ n := Nat.le_of_lt_succ i.isLt
    rw [pow_succ]
    omega⟩

@[simp]
theorem unitDyadicRefineIndex_val (n : ℕ) (i : Fin (2 ^ n + 1)) :
    (unitDyadicRefineIndex n i).val = 2 * i.val :=
  rfl

/-- Refinement does not change the represented nonnegative rational time. -/
theorem unitDyadicGrid_refineIndex (n : ℕ) (i : Fin (2 ^ n + 1)) :
    unitDyadicGrid (n + 1) (unitDyadicRefineIndex n i) = unitDyadicGrid n i := by
  simp only [unitDyadicGrid, unitDyadicRefineIndex_val]
  rw [pow_succ]
  push_cast
  field_simp

/-- The canonical level-`n` parent of a point on the level-`n + 1` unit dyadic grid.
It is obtained by rounding the fine-grid index down after division by two. -/
def unitDyadicParentIndex (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) : Fin (2 ^ n + 1) :=
  ⟨i.val / 2, by
    have hi : i.val ≤ 2 ^ (n + 1) := Nat.le_of_lt_succ i.isLt
    have hi' : i.val ≤ 2 ^ n * 2 := by simpa only [pow_succ] using hi
    omega⟩

@[simp]
theorem unitDyadicParentIndex_val (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    (unitDyadicParentIndex n i).val = i.val / 2 :=
  rfl

/-- Refining the parent lies weakly to the left of its child. -/
theorem unitDyadicRefineIndex_parent_le (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    (unitDyadicRefineIndex n (unitDyadicParentIndex n i)).val ≤ i.val := by
  simp only [unitDyadicRefineIndex_val, unitDyadicParentIndex_val]
  omega

/-- A child is at most one fine-grid cell to the right of its refined parent. -/
theorem unitDyadic_child_sub_refineIndex_parent_le_one
    (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    i.val - (unitDyadicRefineIndex n (unitDyadicParentIndex n i)).val ≤ 1 := by
  simp only [unitDyadicRefineIndex_val, unitDyadicParentIndex_val]
  omega

/-- The coarse-grid parent represents the same time as its refinement on the fine grid. -/
theorem unitDyadicGrid_parent_eq_refineIndex
    (n : ℕ) (i : Fin (2 ^ (n + 1) + 1)) :
    unitDyadicGrid n (unitDyadicParentIndex n i) =
      unitDyadicGrid (n + 1) (unitDyadicRefineIndex n (unitDyadicParentIndex n i)) := by
  exact (unitDyadicGrid_refineIndex n (unitDyadicParentIndex n i)).symm

/-- Adjacent-increment control on level `n + 1` controls every child-to-parent increment
by the same threshold. -/
theorem edist_unitDyadicGrid_child_parent_le_of_adjacent_le
    {X : NNRat → Ω → E} {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ (n + 1)),
      edist (X (unitDyadicGrid (n + 1) k.castSucc) ω)
          (X (unitDyadicGrid (n + 1) k.succ) ω) ≤ ε)
    (i : Fin (2 ^ (n + 1) + 1)) :
    edist (X (unitDyadicGrid (n + 1) i) ω)
        (X (unitDyadicGrid n (unitDyadicParentIndex n i)) ω) ≤ ε := by
  let j := unitDyadicRefineIndex n (unitDyadicParentIndex n i)
  have hji : j.val ≤ i.val := unitDyadicRefineIndex_parent_le n i
  have hsub : i.val - j.val ≤ 1 :=
    unitDyadic_child_sub_refineIndex_parent_le_one n i
  calc
    edist (X (unitDyadicGrid (n + 1) i) ω)
        (X (unitDyadicGrid n (unitDyadicParentIndex n i)) ω) =
        edist (X (unitDyadicGrid (n + 1) j) ω)
          (X (unitDyadicGrid (n + 1) i) ω) := by
      rw [edist_comm, unitDyadicGrid_parent_eq_refineIndex]
    _ ≤ (i.val - j.val : ℕ) * ε :=
      edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le hadj j i hji
    _ ≤ (1 : ℝ≥0∞) * ε := by
      have hcast : ((i.val - j.val : ℕ) : ℝ≥0∞) ≤ 1 := by exact_mod_cast hsub
      exact mul_le_mul_of_nonneg_right hcast bot_le
    _ = ε := one_mul ε

/-- Almost surely, on all sufficiently fine consecutive dyadic levels, every child is
within the fine level's Kolmogorov--Chentsov threshold of its canonical parent. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_child_parent_le_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ i : Fin (2 ^ (n + 1) + 1),
      edist (X (unitDyadicGrid (n + 1) i) ω)
          (X (unitDyadicGrid n (unitDyadicParentIndex n i)) ω) ≤
        dyadicIncrementThreshold γ (n + 1) := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_adjacent_lt_threshold
      hX hγ hγq] with ω hω
  rw [Filter.eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, fun n hn i ↦ ?_⟩
  apply edist_unitDyadicGrid_child_parent_le_of_adjacent_le
  intro k
  exact (hN (n + 1) (hn.trans (Nat.le_succ n)) k).le

end DyadicMultiscale

section DyadicAncestorChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The canonical level-`n` ancestor of a point lying `r` dyadic refinements above it. -/
def unitDyadicAncestorIndex (n : ℕ) :
    (r : ℕ) → Fin (2 ^ (n + r) + 1) → Fin (2 ^ n + 1)
  | 0, i => i
  | r + 1, i =>
      unitDyadicAncestorIndex n r (unitDyadicParentIndex (n + r) i)

@[simp]
theorem unitDyadicAncestorIndex_zero (n : ℕ) (i : Fin (2 ^ n + 1)) :
    unitDyadicAncestorIndex n 0 i = i :=
  rfl

@[simp]
theorem unitDyadicAncestorIndex_succ
    (n r : ℕ) (i : Fin (2 ^ (n + (r + 1)) + 1)) :
    unitDyadicAncestorIndex n (r + 1) i =
      unitDyadicAncestorIndex n r (unitDyadicParentIndex (n + r) i) :=
  rfl

/-- Iterating child-to-parent bounds controls the increment from a fine-grid point to its
canonical ancestor by the corresponding finite sum. -/
theorem edist_unitDyadicGrid_ancestor_le_sum_of_child_parent_le
    {X : NNRat → Ω → E} {n r : ℕ} {δ : ℕ → ℝ≥0∞} {ω : Ω}
    (hparent : ∀ s < r, ∀ i : Fin (2 ^ (n + s + 1) + 1),
      edist (X (unitDyadicGrid (n + s + 1) i) ω)
          (X (unitDyadicGrid (n + s) (unitDyadicParentIndex (n + s) i)) ω) ≤
        δ (n + s + 1))
    (i : Fin (2 ^ (n + r) + 1)) :
    edist (X (unitDyadicGrid (n + r) i) ω)
        (X (unitDyadicGrid n (unitDyadicAncestorIndex n r i)) ω) ≤
      ∑ s ∈ Finset.range r, δ (n + s + 1) := by
  induction r with
  | zero =>
      simp only [Nat.add_zero, unitDyadicAncestorIndex_zero, Finset.range_zero,
        Finset.sum_empty, edist_self]
      exact le_rfl
  | succ r ihr =>
      let j := unitDyadicParentIndex (n + r) i
      have hlast :
          edist (X (unitDyadicGrid (n + r + 1) i) ω)
              (X (unitDyadicGrid (n + r) j) ω) ≤ δ (n + r + 1) :=
        hparent r (Nat.lt_succ_self r) i
      have hprevious :
          edist (X (unitDyadicGrid (n + r) j) ω)
              (X (unitDyadicGrid n (unitDyadicAncestorIndex n r j)) ω) ≤
            ∑ s ∈ Finset.range r, δ (n + s + 1) := by
        apply ihr
        intro s hs k
        exact hparent s (hs.trans (Nat.lt_succ_self r)) k
      calc
        edist (X (unitDyadicGrid (n + (r + 1)) i) ω)
            (X (unitDyadicGrid n (unitDyadicAncestorIndex n (r + 1) i)) ω) =
            edist (X (unitDyadicGrid (n + r + 1) i) ω)
              (X (unitDyadicGrid n (unitDyadicAncestorIndex n r j)) ω) := by
          rfl
        _ ≤ edist (X (unitDyadicGrid (n + r + 1) i) ω)
              (X (unitDyadicGrid (n + r) j) ω) +
            edist (X (unitDyadicGrid (n + r) j) ω)
              (X (unitDyadicGrid n (unitDyadicAncestorIndex n r j)) ω) :=
          edist_triangle _ _ _
        _ ≤ δ (n + r + 1) + ∑ s ∈ Finset.range r, δ (n + s + 1) :=
          add_le_add hlast hprevious
        _ = ∑ s ∈ Finset.range (r + 1), δ (n + s + 1) := by
          rw [Finset.sum_range_succ]
          exact add_comm _ _

/-- Almost surely, every sufficiently fine base level admits all finite canonical ancestor
chains, with total increment bounded by the finite sum of dyadic thresholds along the chain. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_ancestor_le_sum_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ r (i : Fin (2 ^ (n + r) + 1)),
      edist (X (unitDyadicGrid (n + r) i) ω)
          (X (unitDyadicGrid n (unitDyadicAncestorIndex n r i)) ω) ≤
        ∑ s ∈ Finset.range r, dyadicIncrementThreshold γ (n + s + 1) := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_child_parent_le_threshold
      hX hγ hγq] with ω hω
  rw [Filter.eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, fun n hn r i ↦ ?_⟩
  apply edist_unitDyadicGrid_ancestor_le_sum_of_child_parent_le
  intro s _hs j
  exact hN (n + s) (hn.trans (Nat.le_add_right n s)) j

end DyadicAncestorChaining

section DyadicAncestorTail

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- Every finite sum of thresholds above base level `n` is bounded by the exact infinite
tail beginning at level `n + 1`. -/
theorem sum_dyadicIncrementThreshold_ancestor_le_tail (γ : ℝ) (n r : ℕ) :
    ∑ s ∈ Finset.range r, dyadicIncrementThreshold γ (n + s + 1) ≤
      dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    sum_dyadicIncrementThreshold_add_le γ (n + 1) r

/-- Almost surely, above every sufficiently fine base level, all finite canonical ancestor
chains are bounded uniformly in their depth and endpoint by the exact infinite threshold
tail. -/
theorem IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_ancestor_le_tail
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ r (i : Fin (2 ^ (n + r) + 1)),
      edist (X (unitDyadicGrid (n + r) i) ω)
          (X (unitDyadicGrid n (unitDyadicAncestorIndex n r i)) ω) ≤
        dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_ancestor_le_sum_threshold
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro r i
  exact (hn r i).trans (sum_dyadicIncrementThreshold_ancestor_le_tail γ n r)

/-- For a positive exponent, the exact infinite threshold-tail bound above level `n`
tends to zero as `n` tends to infinity. -/
theorem tendsto_dyadicIncrementThreshold_ancestor_tail_zero
    {γ : ℝ} (hγ : 0 < γ) :
    Tendsto
      (fun n : ℕ ↦ dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹)
      atTop (nhds 0) := by
  have hratio : dyadicIncrementThresholdRatio γ < 1 :=
    dyadicIncrementThresholdRatio_lt_one hγ
  have hpow : Tendsto (fun n : ℕ ↦ dyadicIncrementThresholdRatio γ ^ n)
      atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
  have hpow_succ : Tendsto (fun n : ℕ ↦ dyadicIncrementThresholdRatio γ ^ (n + 1))
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hpow
  have htail_ne_top : (1 - dyadicIncrementThresholdRatio γ)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hratio).ne'
  simpa only [dyadicIncrementThreshold_eq_ratio_pow, zero_mul] using
    ENNReal.Tendsto.mul_const hpow_succ (Or.inr htail_ne_top)

end DyadicAncestorTail

end MarkovProcess
