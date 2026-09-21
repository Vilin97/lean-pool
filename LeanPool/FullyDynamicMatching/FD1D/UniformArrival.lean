/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Spatial

/-! # Uniform Arrival -/

namespace FD1D

noncomputable section

open Set MeasureTheory

/-!
# Uniform continuous arrivals and dyadic leaf labels

This module identifies a uniform point of `[0,1]` with its depth-`L`
dyadic leaf.  The continuous arrival law pushes forward to the uniform
finite law on `DyadicNode L`, and the point lies in the closed cell
certified by its selected label.
-/

namespace DyadicMass

/-- A complete depth-`L` mass tree whose leaves all have mass `c`. -/
def constantLeafMass : (L : ℕ) → ℝ → DyadicMass L
  | 0, c => .leaf c
  | L + 1, c => .branch (constantLeafMass L c) (constantLeafMass L c)

@[simp]
theorem leafMass_constantLeafMass (L : ℕ) (c : ℝ) (i : DyadicNode L) :
    (constantLeafMass L c).leafMass i = c := by
  induction L with
  | zero =>
      simp [constantLeafMass, leafMass]
  | succ L ih =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · simp [constantLeafMass, ih]
      · simp [constantLeafMass, ih]

@[simp]
theorem total_constantLeafMass (L : ℕ) (c : ℝ) :
    (constantLeafMass L c).total = ((2 ^ L : ℕ) : ℝ) * c := by
  induction L with
  | zero =>
      simp [constantLeafMass, total]
  | succ L ih =>
      simp only [constantLeafMass, total, ih]
      rw [pow_succ]
      push_cast
      ring

theorem allNonneg_constantLeafMass (L : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    (constantLeafMass L c).allNonneg := by
  induction L with
  | zero =>
      simpa [constantLeafMass, allNonneg] using hc
  | succ L ih =>
      simpa [constantLeafMass, allNonneg] using And.intro ih ih

/-- The depth-`L` dyadic mass with mass `1 / 2^L` at every leaf. -/
def uniformArrivalMass (L : ℕ) : DyadicMass L :=
  constantLeafMass L (1 / ((2 ^ L : ℕ) : ℝ))

@[simp]
theorem uniformArrivalMass_leafMass (L : ℕ) (i : DyadicNode L) :
    (uniformArrivalMass L).leafMass i = 1 / ((2 ^ L : ℕ) : ℝ) := by
  simp [uniformArrivalMass]

theorem uniformArrivalMass_isProbability (L : ℕ) :
    (uniformArrivalMass L).IsProbability := by
  constructor
  · exact allNonneg_constantLeafMass L (by positivity)
  · simp only [uniformArrivalMass, total_constantLeafMass]
    have hpow : (((2 ^ L : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp

private theorem piecewiseCDF_constantLeafMass
    (L : ℕ) (c : ℝ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (constantLeafMass L c).piecewiseCDF z =
      ((2 ^ L : ℕ) : ℝ) * c * z := by
  induction L generalizing z with
  | zero =>
      simp [constantLeafMass, piecewiseCDF]
  | succ L ih =>
      simp only [constantLeafMass, piecewiseCDF]
      by_cases hhalf : z ≤ 1 / 2
      · rw [if_pos hhalf, ih ⟨by linarith [hz.1], by linarith⟩]
        rw [pow_succ]
        push_cast
        ring
      · rw [if_neg hhalf, total_constantLeafMass,
          ih ⟨by linarith, by linarith [hz.2]⟩]
        rw [pow_succ]
        push_cast
        ring

@[simp]
theorem uniformArrivalMass_piecewiseCDF
    (L : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (uniformArrivalMass L).piecewiseCDF z = z := by
  rw [uniformArrivalMass, piecewiseCDF_constantLeafMass L _ hz]
  have hpow : (((2 ^ L : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

@[simp]
theorem uniformArrivalMass_quantile
    (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (uniformArrivalMass L).quantile u = u := by
  let q := uniformArrivalMass L
  have hq : q.IsProbability := uniformArrivalMass_isProbability L
  have huTotal : u ≤ q.total := by
    simpa [hq.total_eq_one] using hu.2
  have hquantile :
      q.quantile u ∈ Icc (0 : ℝ) 1 :=
    q.quantile_mem_unit hq.nonneg hu.1 huTotal
  apply le_antisymm
  · apply (q.quantile_le_iff hq.nonneg hu.1 huTotal hu.1 hu.2).2
    change u ≤ (uniformArrivalMass L).piecewiseCDF u
    rw [uniformArrivalMass_piecewiseCDF L hu]
  · have hself :=
      (q.quantile_le_iff hq.nonneg hu.1 huTotal
        hquantile.1 hquantile.2).1 le_rfl
    change u ≤ (uniformArrivalMass L).piecewiseCDF (q.quantile u) at hself
    rw [uniformArrivalMass_piecewiseCDF L hquantile] at hself
    exact hself

/-- The dyadic label assigned to the continuous arrival coordinate `u`. -/
def uniformArrivalLeaf (L : ℕ) (u : ℝ) : DyadicNode L :=
  (uniformArrivalMass L).selectedIndex u

/-- The finite pushforward law of the selected uniform-arrival label. -/
def uniformArrivalLeafLaw (L : ℕ) : FiniteLaw (DyadicNode L) :=
  (uniformArrivalMass L).selectedIndexLaw
    (uniformArrivalMass_isProbability L)

/-- A continuous uniform arrival induces the uniform law on depth-`L` leaves. -/
theorem uniformArrivalLeafLaw_eq_uniform (L : ℕ) :
    uniformArrivalLeafLaw L =
      (FiniteLaw.uniform : FiniteLaw (DyadicNode L)) := by
  apply FiniteLaw.ext
  intro i
  simp [uniformArrivalLeafLaw]

/-- Every arrival in `[0,1]` lies in the closed cell carrying its label. -/
theorem uniformArrival_mem_dyadicCell
    (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    u ∈ dyadicCell (uniformArrivalLeaf L u) := by
  have hcell :=
    SupplyConfiguration.quantile_mem_selectedCell
      (uniformArrivalMass L) (uniformArrivalMass_isProbability L) hu
  rw [uniformArrivalMass_quantile L hu] at hcell
  simpa [uniformArrivalLeaf] using hcell

/--
Under Lebesgue-uniform demand on `[0,1]`, the continuous arrival and its
finite label are almost surely compatible with the certified dyadic cell.
-/
theorem uniformArrival_mem_dyadicCell_ae (L : ℕ) :
    ∀ᵐ u ∂uniformDemand,
      u ∈ dyadicCell (uniformArrivalLeaf L u) := by
  rw [uniformDemand, ae_restrict_iff' measurableSet_Icc]
  filter_upwards with u hu
  exact uniformArrival_mem_dyadicCell L hu

end DyadicMass

end

end FD1D
