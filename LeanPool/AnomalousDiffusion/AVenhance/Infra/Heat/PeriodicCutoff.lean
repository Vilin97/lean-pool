/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic

/-! # Periodic Cutoff

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral Homogenization Filter Topology
open AVenhance.Infra.Torus

namespace AVenhance.Infra.Heat

/-- A smooth, compactly supported partition-of-unity weight for the unit
period. -/
def heatPeriodicCutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x

theorem PeriodicCutoff.heatPeriodicCutoff_partition {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : heatPeriodicCutoff (x - 1) + heatPeriodicCutoff x = 1 := by
  unfold heatPeriodicCutoff
  have h1 : Real.smoothTransition (x + 1) = 1 := by
    simpa [add_comm] using Real.smoothTransition.one_of_one_le
      (show 1 ≤ x + 1 by linarith)
  have h0 : Real.smoothTransition (x - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [show x - 1 + 1 = x by ring, h1, h0]
  ring

/-- The product cutoff on `Vec 2`; its four translates cover a unit cell. -/
def heatPeriodicCutoff2 (x : Vec 2) : ℝ :=
  heatPeriodicCutoff (x 0) * heatPeriodicCutoff (x 1)

/-- The four unit-cell shifts needed to cover the support of the product
cutoff. -/
def heatPeriodicTileShift (b : Bool × Bool) : Fin 2 → ℤ := fun i =>
  if i = 0 then (if b.1 then 0 else -1) else (if b.2 then 0 else -1)

/-- Integer-vector starting point of one periodic heat tile. -/
def heatPeriodicTileStart (b : Bool × Bool) : Fin 2 → ℝ :=
  intVector (heatPeriodicTileShift b)

/-- Translated unit cell associated with a periodic heat tile. -/
def heatPeriodicTile (b : Bool × Bool) : Set (Vec 2) :=
  unitCellAt 2 (heatPeriodicTileStart b)

/-- Translate the one-dimensional periodic heat cutoff according to the Boolean tile index. -/
def PeriodicCutoff.heatShiftedCutoff (b : Bool) (x : ℝ) : ℝ :=
  heatPeriodicCutoff (x + if b then 0 else -1)

theorem PeriodicCutoff.sum_heatShiftedCutoff {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ b : Bool, PeriodicCutoff.heatShiftedCutoff b x = 1 := by
  classical
  have hsum :
      (∑ b : Bool, PeriodicCutoff.heatShiftedCutoff b x) =
        heatPeriodicCutoff (x - 1) + heatPeriodicCutoff x := by
    simp [PeriodicCutoff.heatShiftedCutoff, sub_eq_add_neg, add_comm]
  rw [hsum, PeriodicCutoff.heatPeriodicCutoff_partition hx0 hx1]

/-- On the unit square, the four translates of the product cutoff sum to one. -/
theorem sum_heatPeriodicCutoff2_translates {x : Vec 2}
    (hx : x ∈ unitCell 2) :
    ∑ b : Bool × Bool,
        heatPeriodicCutoff2 (x + intVector (heatPeriodicTileShift b)) = 1 := by
  classical
  have hx0 : 0 ≤ x 0 := (hx 0).1.le
  have hx1 : x 0 ≤ 1 := by simpa [unitCell, unitCellAt] using (hx 0).2
  have hy0 : 0 ≤ x 1 := (hx 1).1.le
  have hy1 : x 1 ≤ 1 := by simpa [unitCell, unitCellAt] using (hx 1).2
  have hfactor :
      (∑ b : Bool × Bool,
          heatPeriodicCutoff (x 0 + if b.1 then 0 else -1) *
            heatPeriodicCutoff (x 1 + if b.2 then 0 else -1)) =
        (∑ b : Bool, PeriodicCutoff.heatShiftedCutoff b (x 0)) *
          (∑ b : Bool, PeriodicCutoff.heatShiftedCutoff b (x 1)) := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul_sum]
    simp [PeriodicCutoff.heatShiftedCutoff]
  have hsum' :
      (∑ b : Bool × Bool,
        heatPeriodicCutoff (x 0 + if b.1 then 0 else -1) *
          heatPeriodicCutoff (x 1 + if b.2 then 0 else -1)) = 1 := by
    rw [hfactor, PeriodicCutoff.sum_heatShiftedCutoff hx0 hx1,
      PeriodicCutoff.sum_heatShiftedCutoff hy0 hy1, one_mul]
  simpa [heatPeriodicCutoff2, heatPeriodicTileShift, heatPeriodicTileStart,
    intVector, Pi.add_apply] using hsum'

theorem heatPeriodicCutoff_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) heatPeriodicCutoff := by
  unfold heatPeriodicCutoff
  exact (Real.smoothTransition.contDiff.comp
      (contDiff_id.add contDiff_const)).sub Real.smoothTransition.contDiff

theorem heatPeriodicCutoff2_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) heatPeriodicCutoff2 := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => heatPeriodicCutoff (x 0)) :=
    heatPeriodicCutoff_contDiff.comp (contDiff_apply ℝ ℝ 0)
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => heatPeriodicCutoff (x 1)) :=
    heatPeriodicCutoff_contDiff.comp (contDiff_apply ℝ ℝ 1)
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Vec 2 => heatPeriodicCutoff (x 0) * heatPeriodicCutoff (x 1))
  exact h0.mul h1

theorem PeriodicCutoff.heatPeriodicCutoff_nonneg (x : ℝ) :
    0 ≤ heatPeriodicCutoff x := by
  unfold heatPeriodicCutoff
  exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem PeriodicCutoff.heatPeriodicCutoff_at_edges (x : ℝ)
    (hx : x = -1 ∨ x = 1) : heatPeriodicCutoff x = 0 := by
  rcases hx with rfl | rfl
  · simp [heatPeriodicCutoff]
  · simp [heatPeriodicCutoff, Real.smoothTransition.one_of_one_le]

theorem PeriodicCutoff.heatPeriodicCutoff2_nonneg (x : Vec 2) :
    0 ≤ heatPeriodicCutoff2 x :=
  mul_nonneg (PeriodicCutoff.heatPeriodicCutoff_nonneg _)
      (PeriodicCutoff.heatPeriodicCutoff_nonneg _)

theorem PeriodicCutoff.fderiv_heatPeriodicCutoff_coord (i j : Fin 2) (x : Vec 2) :
    fderiv ℝ (fun y : Vec 2 => heatPeriodicCutoff (y j)) x (basisVec i) =
      if i = j then deriv heatPeriodicCutoff (x j) else 0 := by
  have hproj :
      fderiv ℝ (fun y : Vec 2 => y j) x = ContinuousLinearMap.proj j :=
    (hasFDerivAt_apply j x).fderiv
  have hprojDiff : DifferentiableAt ℝ (fun y : Vec 2 => y j) x :=
    (hasFDerivAt_apply j x).differentiableAt
  have hcutDiff : DifferentiableAt ℝ heatPeriodicCutoff (x j) :=
    (ContDiff.contDiffAt (x := x j) heatPeriodicCutoff_contDiff).differentiableAt
      (by simp)
  calc
    fderiv ℝ (fun y : Vec 2 => heatPeriodicCutoff (y j)) x (basisVec i) =
        (fderiv ℝ heatPeriodicCutoff (x j) ∘SL
          fderiv ℝ (fun y : Vec 2 => y j) x) (basisVec i) := by
            change fderiv ℝ (heatPeriodicCutoff ∘ (fun y : Vec 2 => y j)) x
              (basisVec i) = _
            rw [fderiv_comp x hcutDiff hprojDiff]
    _ = if i = j then deriv heatPeriodicCutoff (x j) else 0 := by
      rw [hproj]
      by_cases hij : i = j <;> simp [fderiv_eq_smul_deriv, basisVec_apply,
        hij, eq_comm, smul_eq_mul]

theorem fderiv_heatPeriodicCutoff2 (i : Fin 2) (x : Vec 2) :
    fderiv ℝ heatPeriodicCutoff2 x (basisVec i) =
      (if i = 0 then deriv heatPeriodicCutoff (x 0) * heatPeriodicCutoff (x 1)
        else heatPeriodicCutoff (x 0) * deriv heatPeriodicCutoff (x 1)) := by
  let a : Vec 2 → ℝ := fun y => heatPeriodicCutoff (y 0)
  let b : Vec 2 → ℝ := fun y => heatPeriodicCutoff (y 1)
  have hca : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => heatPeriodicCutoff (y 0)) :=
    heatPeriodicCutoff_contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 2))
  have hcb : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => heatPeriodicCutoff (y 1)) :=
    heatPeriodicCutoff_contDiff.comp (contDiff_apply ℝ ℝ (1 : Fin 2))
  have ha : DifferentiableAt ℝ a x :=
    (ContDiff.contDiffAt (x := x) hca).differentiableAt (by simp)
  have hb : DifferentiableAt ℝ b x :=
    (ContDiff.contDiffAt (x := x) hcb).differentiableAt (by simp)
  change fderiv ℝ (a * b) x (basisVec i) = _
  rw [fderiv_mul ha hb]
  fin_cases i
  · dsimp [a, b]
    simp [PeriodicCutoff.fderiv_heatPeriodicCutoff_coord, smul_eq_mul, mul_comm]
  · dsimp [a, b]
    simp [PeriodicCutoff.fderiv_heatPeriodicCutoff_coord, smul_eq_mul]

theorem abs_heatPeriodicCutoff_le_one (x : ℝ) :
    |heatPeriodicCutoff x| ≤ 1 := by
  unfold heatPeriodicCutoff
  have h10 := Real.smoothTransition.nonneg (x + 1)
  have h11 := Real.smoothTransition.le_one (x + 1)
  have h20 := Real.smoothTransition.nonneg x
  have h21 := Real.smoothTransition.le_one x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem norm_heatPeriodicCutoff2_le_one (x : Vec 2) :
    ‖heatPeriodicCutoff2 x‖ ≤ 1 := by
  rw [heatPeriodicCutoff2, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h0 := abs_heatPeriodicCutoff_le_one (x 0)
  have h1 := abs_heatPeriodicCutoff_le_one (x 1)
  calc
    |heatPeriodicCutoff (x 0)| * |heatPeriodicCutoff (x 1)| ≤
        1 * 1 := mul_le_mul h0 h1 (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem PeriodicCutoff.heatPeriodicCutoff_support :
    Function.support heatPeriodicCutoff ⊆ Ioc (-1 : ℝ) 1 := by
  intro x hx
  simp only [Function.mem_support] at hx
  constructor
  · by_contra h
    have hzero : heatPeriodicCutoff x = 0 := by
      unfold heatPeriodicCutoff
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : x + 1 ≤ 0),
        Real.smoothTransition.zero_of_nonpos (by linarith : x ≤ 0)]
      ring
    exact hx hzero
  · by_contra h
    have hzero : heatPeriodicCutoff x = 0 := by
      unfold heatPeriodicCutoff
      rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x + 1),
        Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x)]
      ring
    exact hx hzero

theorem PeriodicCutoff.heatPeriodicCutoff2_support :
    Function.support heatPeriodicCutoff2 ⊆
      Set.pi Set.univ (fun _ : Fin 2 => Ioc (-1 : ℝ) 1) := by
  intro x hx
  simp only [Function.mem_support] at hx
  have h0 : heatPeriodicCutoff (x 0) ≠ 0 := by
    intro h
    apply hx
    simp [heatPeriodicCutoff2, h]
  have h1 : heatPeriodicCutoff (x 1) ≠ 0 := by
    intro h
    apply hx
    simp [heatPeriodicCutoff2, h]
  intro i hi
  have _hi := hi
  fin_cases i
  · exact PeriodicCutoff.heatPeriodicCutoff_support h0
  · exact PeriodicCutoff.heatPeriodicCutoff_support h1

/-- Closed box containing the support of the two-dimensional periodic heat cutoff. -/
def PeriodicCutoff.heatPeriodicCutoff2ClosedBox : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Icc (-1 : ℝ) 1)

theorem PeriodicCutoff.heatPeriodicCutoff2_tsupport_subset_closedBox :
    tsupport heatPeriodicCutoff2 ⊆ PeriodicCutoff.heatPeriodicCutoff2ClosedBox := by
  apply closure_minimal
  · exact PeriodicCutoff.heatPeriodicCutoff2_support.trans fun x hx i hi =>
      Ioc_subset_Icc_self (hx i hi)
  · have hc : IsCompact PeriodicCutoff.heatPeriodicCutoff2ClosedBox := by
      simpa [PeriodicCutoff.heatPeriodicCutoff2ClosedBox] using
        (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
    exact hc.isClosed

theorem heatPeriodicCutoff2_hasCompactSupport :
    HasCompactSupport heatPeriodicCutoff2 := by
  change IsCompact (tsupport heatPeriodicCutoff2)
  have hc : IsCompact PeriodicCutoff.heatPeriodicCutoff2ClosedBox := by
    simpa [PeriodicCutoff.heatPeriodicCutoff2ClosedBox] using
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
  exact hc.of_isClosed_subset (isClosed_tsupport _)
    PeriodicCutoff.heatPeriodicCutoff2_tsupport_subset_closedBox

theorem heatPeriodicCutoff2_coordDeriv_support (i : Fin 2) :
    Function.support (fun x : Vec 2 =>
      fderiv ℝ heatPeriodicCutoff2 x (basisVec i)) ⊆
        Set.pi Set.univ (fun _ : Fin 2 => Ioc (-1 : ℝ) 1) := by
  intro x hx
  simp only [Function.mem_support] at hx
  have hxT : x ∈ tsupport (fun y : Vec 2 =>
      fderiv ℝ heatPeriodicCutoff2 y (basisVec i)) := subset_closure hx
  have hxBox : x ∈ PeriodicCutoff.heatPeriodicCutoff2ClosedBox := by
    exact PeriodicCutoff.heatPeriodicCutoff2_tsupport_subset_closedBox
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)) hxT)
  intro j hj
  have hjBox := hxBox j (Set.mem_univ _)
  have hInterior : x j ∈ Ioc (-1 : ℝ) 1 := by
    constructor
    · by_contra hleft
      have hedge : x j = -1 := by
        apply le_antisymm (le_of_not_gt hleft)
        exact hjBox.1
      have hzero : heatPeriodicCutoff2 x = 0 := by
        unfold heatPeriodicCutoff2
        fin_cases j
        · have hcoord : x 0 = -1 := by simpa using hedge
          simp [PeriodicCutoff.heatPeriodicCutoff_at_edges, Or.inl hcoord]
        · have hcoord : x 1 = -1 := by simpa using hedge
          simp [PeriodicCutoff.heatPeriodicCutoff_at_edges, Or.inl hcoord]
      have hmin : IsLocalMin heatPeriodicCutoff2 x := by
        change ∀ᶠ y in 𝓝 x, heatPeriodicCutoff2 x ≤ heatPeriodicCutoff2 y
        rw [hzero]
        exact Filter.Eventually.of_forall PeriodicCutoff.heatPeriodicCutoff2_nonneg
      have hD := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i))
        hmin.fderiv_eq_zero
      exact hx (by simpa using hD)
    · exact hjBox.2
  exact hInterior

theorem PeriodicCutoff.mem_biUnion_heatPeriodicTile_of_mem_box {x : Vec 2}
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin 2 => Ioc (-1 : ℝ) 1)) :
    x ∈ ⋃ b : Bool × Bool, heatPeriodicTile b := by
  let b : Bool × Bool := (decide (0 < x 0), decide (0 < x 1))
  refine Set.mem_iUnion.mpr ⟨b, ?_⟩
  intro i
  fin_cases i
  · have hi := hx 0 (Set.mem_univ _)
    by_cases hpos : 0 < x 0
    · have hle : x 0 ≤ 1 := hi.2
      simpa [heatPeriodicTile, heatPeriodicTileStart, heatPeriodicTileShift,
        intVector, b, hpos] using (show x 0 ∈ Ioc (0 : ℝ) 1 from ⟨hpos, hle⟩)
    · have hle : x 0 ≤ 0 := le_of_not_gt hpos
      have hlt : -1 < x 0 := hi.1
      simpa [heatPeriodicTile, heatPeriodicTileStart, heatPeriodicTileShift,
        intVector, b, hpos] using (show x 0 ∈ Ioc (-1 : ℝ) 0 from ⟨hlt, hle⟩)
  · have hi := hx 1 (Set.mem_univ _)
    by_cases hpos : 0 < x 1
    · have hle : x 1 ≤ 1 := hi.2
      simpa [heatPeriodicTile, heatPeriodicTileStart, heatPeriodicTileShift,
        intVector, b, hpos] using (show x 1 ∈ Ioc (0 : ℝ) 1 from ⟨hpos, hle⟩)
    · have hle : x 1 ≤ 0 := le_of_not_gt hpos
      have hlt : -1 < x 1 := hi.1
      simpa [heatPeriodicTile, heatPeriodicTileStart, heatPeriodicTileShift,
        intVector, b, hpos] using (show x 1 ∈ Ioc (-1 : ℝ) 0 from ⟨hlt, hle⟩)

theorem PeriodicCutoff.heatPeriodicTile_disjoint {b c : Bool × Bool} (hbc : b ≠ c) :
    Disjoint (heatPeriodicTile b) (heatPeriodicTile c) := by
  apply Set.disjoint_left.mpr
  intro x hxb hxc
  have hdiff : b.1 ≠ c.1 ∨ b.2 ≠ c.2 := by
    by_cases h1 : b.1 ≠ c.1
    · exact Or.inl h1
    · right
      intro h2
      exact hbc (Prod.ext (not_ne_iff.mp h1) h2)
  rcases hdiff with hdiff | hdiff
  · have hb := hxb 0
    have hc := hxc 0
    simp [heatPeriodicTileStart, heatPeriodicTileShift,
      intVector] at hb hc
    cases hbv : b.1 <;> cases hcv : c.1 <;> simp_all <;> linarith
  · have hb := hxb 1
    have hc := hxc 1
    simp [heatPeriodicTileStart, heatPeriodicTileShift,
      intVector] at hb hc
    cases hbv : b.2 <;> cases hcv : c.2 <;> simp_all <;> linarith

theorem PeriodicCutoff.measurable_heatPeriodicTile (b : Bool × Bool) :
    MeasurableSet (heatPeriodicTile b) := by
  exact measurableSet_unitCellAt 2 (heatPeriodicTileStart b)

theorem heatPeriodicCutoff2_support_subset_tiles :
    Function.support heatPeriodicCutoff2 ⊆
      ⋃ b : Bool × Bool, heatPeriodicTile b := by
  intro x hx
  exact PeriodicCutoff.mem_biUnion_heatPeriodicTile_of_mem_box
      (PeriodicCutoff.heatPeriodicCutoff2_support hx)

theorem heatPeriodicCutoff2_coordDeriv_support_subset_tiles (i : Fin 2) :
    Function.support (fun x : Vec 2 =>
      fderiv ℝ heatPeriodicCutoff2 x (basisVec i)) ⊆
        ⋃ b : Bool × Bool, heatPeriodicTile b := by
  intro x hx
  exact PeriodicCutoff.mem_biUnion_heatPeriodicTile_of_mem_box
    (heatPeriodicCutoff2_coordDeriv_support i hx)

theorem heatPeriodicCutoff_deriv_partition {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    deriv heatPeriodicCutoff (x - 1) + deriv heatPeriodicCutoff x = 0 := by
  have heventually :
      (fun y => heatPeriodicCutoff (y - 1) + heatPeriodicCutoff y) =ᶠ[nhds x]
        fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
    exact PeriodicCutoff.heatPeriodicCutoff_partition hy.1.le hy.2.le
  have hconst : HasDerivAt
      (fun y => heatPeriodicCutoff (y - 1) + heatPeriodicCutoff y) 0 x := by
    exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq heventually
  have hleft : HasDerivAt (fun y => heatPeriodicCutoff (y - 1))
      (deriv heatPeriodicCutoff (x - 1)) x := by
    have hcut : HasDerivAt heatPeriodicCutoff
        (deriv heatPeriodicCutoff (x - 1)) (x - 1) :=
      ((ContDiff.contDiffAt (x := x - 1) heatPeriodicCutoff_contDiff).differentiableAt
        (by simp)).hasDerivAt
    convert hcut.comp x (hasDerivAt_id x |>.sub_const 1) using 1
    · rfl
    · simp
  have hright : HasDerivAt heatPeriodicCutoff
      (deriv heatPeriodicCutoff x) x :=
    ((ContDiff.contDiffAt (x := x) heatPeriodicCutoff_contDiff).differentiableAt
      (by simp)).hasDerivAt
  have hsum := hleft.add hright
  exact (hconst.unique hsum).symm

theorem PeriodicCutoff.deriv_smoothTransition_zero_of_value {x : ℝ}
    (hx : Real.smoothTransition x = 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  change ∀ᶠ y in 𝓝 x, Real.smoothTransition x ≤ Real.smoothTransition y
  rw [hx]
  exact Filter.Eventually.of_forall Real.smoothTransition.nonneg

theorem PeriodicCutoff.deriv_smoothTransition_one_of_value {x : ℝ}
    (hx : Real.smoothTransition x = 1) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  change ∀ᶠ y in 𝓝 x, Real.smoothTransition y ≤ Real.smoothTransition x
  rw [hx]
  exact Filter.Eventually.of_forall Real.smoothTransition.le_one

theorem PeriodicCutoff.deriv_heatPeriodicCutoff (x : ℝ) :
    deriv heatPeriodicCutoff x =
      deriv Real.smoothTransition (x + 1) - deriv Real.smoothTransition x := by
  change deriv ((fun y : ℝ => Real.smoothTransition (y + 1)) -
      Real.smoothTransition) x = _
  rw [deriv_sub]
  · rw [deriv_comp_add_const]
  · have ht : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ => Real.smoothTransition (y + 1)) := by
      simpa [Function.comp_def] using ht.comp (contDiff_id.add contDiff_const)
    exact (ContDiff.contDiffAt (x := x) hcomp).differentiableAt (by simp)
  · have ht : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact (ContDiff.contDiffAt (x := x) ht).differentiableAt (by simp)

theorem PeriodicCutoff.deriv_heatPeriodicCutoff_at_left :
    deriv heatPeriodicCutoff (-1) = 0 := by
  rw [PeriodicCutoff.deriv_heatPeriodicCutoff]
  norm_num
  rw [PeriodicCutoff.deriv_smoothTransition_zero_of_value (by simp),
    PeriodicCutoff.deriv_smoothTransition_zero_of_value (by
      exact Real.smoothTransition.zero_of_nonpos (by norm_num))]
  ring

theorem PeriodicCutoff.deriv_heatPeriodicCutoff_at_zero :
    deriv heatPeriodicCutoff 0 = 0 := by
  rw [PeriodicCutoff.deriv_heatPeriodicCutoff]
  norm_num
  rw [PeriodicCutoff.deriv_smoothTransition_one_of_value (by simp),
    PeriodicCutoff.deriv_smoothTransition_zero_of_value (by simp)]
  ring

theorem PeriodicCutoff.deriv_heatPeriodicCutoff_at_right :
    deriv heatPeriodicCutoff 1 = 0 := by
  rw [PeriodicCutoff.deriv_heatPeriodicCutoff]
  norm_num
  rw [PeriodicCutoff.deriv_smoothTransition_one_of_value (by
      exact Real.smoothTransition.one_of_one_le (by norm_num)),
    PeriodicCutoff.deriv_smoothTransition_one_of_value (by simp)]
  ring

theorem heatPeriodicCutoff_deriv_partition_closed {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    deriv heatPeriodicCutoff (x - 1) + deriv heatPeriodicCutoff x = 0 := by
  by_cases hxL : x = 0
  · subst x
    norm_num
    rw [PeriodicCutoff.deriv_heatPeriodicCutoff_at_left,
        PeriodicCutoff.deriv_heatPeriodicCutoff_at_zero]
    ring
  by_cases hxR : x = 1
  · subst x
    norm_num
    rw [PeriodicCutoff.deriv_heatPeriodicCutoff_at_zero,
        PeriodicCutoff.deriv_heatPeriodicCutoff_at_right]
    ring
  exact heatPeriodicCutoff_deriv_partition
    (lt_of_le_of_ne hx0 (Ne.symm hxL))
    (lt_of_le_of_ne hx1 hxR)

/-- Translated derivative of the one-dimensional periodic heat cutoff. -/
def PeriodicCutoff.heatShiftedCutoffDerivative (b : Bool) (x : ℝ) : ℝ :=
  deriv heatPeriodicCutoff (x + if b then 0 else -1)

theorem PeriodicCutoff.sum_heatShiftedCutoffDerivative {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ b : Bool, PeriodicCutoff.heatShiftedCutoffDerivative b x = 0 := by
  have hsum :
      (∑ b : Bool, PeriodicCutoff.heatShiftedCutoffDerivative b x) =
        deriv heatPeriodicCutoff (x - 1) + deriv heatPeriodicCutoff x := by
    simp [PeriodicCutoff.heatShiftedCutoffDerivative, sub_eq_add_neg, add_comm]
  rw [hsum]
  exact heatPeriodicCutoff_deriv_partition_closed hx0 hx1

theorem sum_heatPeriodicCutoff2_coordDeriv_translates
    (i : Fin 2) {x : Vec 2} (hx : x ∈ unitCell 2) :
    ∑ b : Bool × Bool,
      fderiv ℝ heatPeriodicCutoff2
        (x + intVector (heatPeriodicTileShift b)) (basisVec i) = 0 := by
  classical
  have hx0 : 0 ≤ x 0 := (hx 0).1.le
  have hx1 : x 0 ≤ 1 := by simpa [unitCell, unitCellAt] using (hx 0).2
  have hy0 : 0 ≤ x 1 := (hx 1).1.le
  have hy1 : x 1 ≤ 1 := by simpa [unitCell, unitCellAt] using (hx 1).2
  fin_cases i
  · have hfactor :
        (∑ b : Bool × Bool,
          deriv heatPeriodicCutoff
              (x 0 + if b.1 then 0 else -1) *
            heatPeriodicCutoff (x 1 + if b.2 then 0 else -1)) =
          (∑ b : Bool, PeriodicCutoff.heatShiftedCutoffDerivative b (x 0)) *
            (∑ b : Bool, PeriodicCutoff.heatShiftedCutoff b (x 1)) := by
      rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul_sum]
      simp [PeriodicCutoff.heatShiftedCutoffDerivative, PeriodicCutoff.heatShiftedCutoff]
    have hsum :
        (∑ b : Bool × Bool,
          deriv heatPeriodicCutoff
              (x 0 + if b.1 then 0 else -1) *
            heatPeriodicCutoff (x 1 + if b.2 then 0 else -1)) = 0 := by
      rw [hfactor, PeriodicCutoff.sum_heatShiftedCutoffDerivative hx0 hx1,
        zero_mul]
    simpa [fderiv_heatPeriodicCutoff2, heatPeriodicTileShift,
      intVector, Pi.add_apply] using hsum
  · have hfactor :
        (∑ b : Bool × Bool,
          heatPeriodicCutoff (x 0 + if b.1 then 0 else -1) *
            deriv heatPeriodicCutoff
              (x 1 + if b.2 then 0 else -1)) =
          (∑ b : Bool, PeriodicCutoff.heatShiftedCutoff b (x 0)) *
            (∑ b : Bool, PeriodicCutoff.heatShiftedCutoffDerivative b (x 1)) := by
      rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul_sum]
      simp [PeriodicCutoff.heatShiftedCutoffDerivative, PeriodicCutoff.heatShiftedCutoff]
    have hsum :
        (∑ b : Bool × Bool,
          heatPeriodicCutoff (x 0 + if b.1 then 0 else -1) *
            deriv heatPeriodicCutoff
              (x 1 + if b.2 then 0 else -1)) = 0 := by
      rw [hfactor, PeriodicCutoff.sum_heatShiftedCutoff hx0 hx1,
        PeriodicCutoff.sum_heatShiftedCutoffDerivative hy0 hy1, mul_zero]
    simpa [fderiv_heatPeriodicCutoff2, heatPeriodicTileShift,
      intVector, Pi.add_apply] using hsum

/-- Translate a cell integral back to the canonical unit cell. -/
theorem integral_unitCellAt_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : Vec 2 → E) (a : Fin 2 → ℝ) :
    ∫ x in unitCellAt 2 a, F x = ∫ x in unitCell 2, F (x + a) := by
  have hpre : (fun x : Vec 2 => x + a) ⁻¹' unitCellAt 2 a = unitCell 2 := by
    ext x
    simp only [unitCellAt, unitCell, Set.mem_ofPred_eq]
    constructor
    · intro h i
      have hi := h i
      rcases hi with ⟨hi0, hi1⟩
      constructor
      · have hi0' : a i < x i + a i := by simpa using hi0
        linarith
      · have hi1' : x i + a i ≤ a i + 1 := by simpa using hi1
        linarith
    · intro h i
      have hi := h i
      rcases hi with ⟨hi0, hi1⟩
      constructor
      · have hi0' : 0 < x i := by simpa using hi0
        simpa [Pi.add_apply] using add_lt_add_right hi0' (a i)
      · have hi1' : x i ≤ 1 := by simpa using hi1
        have := add_le_add_right hi1' (a i)
        simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using this
  have hmp := (measurePreserving_add_right (volume : Measure (Vec 2)) a).restrict_preimage
    (measurableSet_unitCellAt 2 a)
  rw [hpre] at hmp
  change ∫ x, F x ∂volume.restrict (unitCellAt 2 a) =
    ∫ x, F (x + a) ∂volume.restrict (unitCell 2)
  exact (hmp.integral_comp (MeasurableEquiv.addRight a).measurableEmbedding F).symm

theorem integrable_unitCellAt_translate {E : Type*} [NormedAddCommGroup E]
     {F : Vec 2 → E} {a : Fin 2 → ℝ}
    (hF : IntegrableOn F (unitCellAt 2 a)) :
    IntegrableOn (fun x => F (x + a)) (unitCell 2) := by
  have hpre : (fun x : Vec 2 => x + a) ⁻¹' unitCellAt 2 a = unitCell 2 := by
    ext x
    simp only [unitCellAt, unitCell, Set.mem_ofPred_eq]
    constructor
    · intro h i
      have hi := h i
      rcases hi with ⟨hi0, hi1⟩
      constructor
      · have hi0' : a i < x i + a i := by simpa using hi0
        linarith
      · have hi1' : x i + a i ≤ a i + 1 := by simpa using hi1
        linarith
    · intro h i
      have hi := h i
      rcases hi with ⟨hi0, hi1⟩
      constructor
      · have hi0' : 0 < x i := by simpa using hi0
        simpa [Pi.add_apply] using add_lt_add_right hi0' (a i)
      · have hi1' : x i ≤ 1 := by simpa using hi1
        have := add_le_add_right hi1' (a i)
        simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using this
  have hfull := measurePreserving_add_right (volume : Measure (Vec 2)) a
  have hmp := hfull.restrict_preimage (measurableSet_unitCellAt 2 a)
  rw [hpre] at hmp
  change Integrable (fun x => F (x + a))
    (volume.restrict (unitCell 2))
  exact hmp.integrable_comp_of_integrable hF.integrable

/-- Periodic `L²` data have the same `L²` control on every integer translate
of the unit cell. -/
theorem memLp_periodic_unitCellAt {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (unitCell 2)))
    (hper : IsZdPeriodic f) (n : Fin 2 → ℤ) :
    MemLp f 2 (volume.restrict (unitCellAt 2 (intVector n))) := by
  let c : Vec 2 := intVector n
  have hpre : (fun x : Vec 2 => x + -c) ⁻¹' unitCell 2 = unitCellAt 2 c := by
    ext x
    simp only [unitCellAt, unitCell, Set.mem_ofPred_eq]
    constructor
    · intro h i
      have hi := h i
      rcases hi with ⟨hi0, hi1⟩
      constructor
      · have h0 : 0 < x i - c i := by simpa using hi0
        linarith
      · have h1 : x i - c i ≤ 1 := by simpa using hi1
        linarith
    · intro h i
      have hi := h i
      rcases hi with ⟨hi0, hi1⟩
      constructor
      · have h0 : c i < x i := by simpa using hi0
        have h0' : 0 < x i - c i := by linarith
        simpa using h0'
      · have h1 : x i ≤ c i + 1 := by simpa using hi1
        have h1' : x i - c i ≤ 1 := by linarith
        simpa using h1'
  have hfull := measurePreserving_add_right (volume : Measure (Vec 2)) (-c)
  have hmp := hfull.restrict_preimage (measurableSet_unitCell 2)
  rw [hpre] at hmp
  have htranslated :
      MemLp (fun x : Vec 2 => f (x - c)) 2
        (volume.restrict (unitCellAt 2 c)) :=
    hf.comp_measurePreserving hmp
  have hEq : ∀ x : Vec 2, f (x + -c) = f x := by
    intro x
    have h := hper n (x + -c)
    have hc : x + -c + intVector n = x := by simp [c]
    rw [hc] at h
    exact h.symm
  apply MemLp.ae_eq (Filter.Eventually.of_forall hEq)
  simpa [sub_eq_add_neg] using htranslated

/-- A two-dimensional periodic integral unfolds through the product cutoff.
The premise supplies the local integrability on the four translated cells. -/
theorem integral_periodic_heatPeriodicCutoff2 {g : Vec 2 → ℝ}
    (hper : IsZdPeriodic g)
    (hTile : ∀ b : Bool × Bool, IntegrableOn g (heatPeriodicTile b)) :
    ∫ x, g x * heatPeriodicCutoff2 x = ∫ x in unitCell 2, g x := by
  classical
  let F : Vec 2 → ℝ := fun x => g x * heatPeriodicCutoff2 x
  let S : Set (Vec 2) := ⋃ b : Bool × Bool, heatPeriodicTile b
  have hS4 : S =
      ((heatPeriodicTile (false, false) ∪ heatPeriodicTile (false, true)) ∪
        heatPeriodicTile (true, false)) ∪ heatPeriodicTile (true, true) := by
    ext x
    simp [S]
    tauto
  have hSFin : S =
      ⋃ b ∈ (Finset.univ : Finset (Bool × Bool)), heatPeriodicTile b := by
    rw [hS4]
    ext x
    simp
    tauto
  have hχcont : Continuous heatPeriodicCutoff2 :=
    heatPeriodicCutoff2_contDiff.continuous
  have hFtile : ∀ b : Bool × Bool, IntegrableOn F (heatPeriodicTile b) := by
    intro b
    change Integrable F (volume.restrict (heatPeriodicTile b))
    have hg : Integrable g (volume.restrict (heatPeriodicTile b)) :=
      (hTile b).integrable
    have hmeas : AEStronglyMeasurable F
        (volume.restrict (heatPeriodicTile b)) := by
      dsimp [F]
      exact hg.aestronglyMeasurable.mul
        (hχcont.measurable.aestronglyMeasurable)
    apply hg.mono hmeas
    filter_upwards with x
    dsimp [F]
    have hχ : |heatPeriodicCutoff2 x| ≤ 1 := by
      simpa [Real.norm_eq_abs] using norm_heatPeriodicCutoff2_le_one x
    calc
      |g x * heatPeriodicCutoff2 x| = |g x| * |heatPeriodicCutoff2 x| := abs_mul _ _
      _ ≤ |g x| * 1 := mul_le_mul_of_nonneg_left hχ (abs_nonneg _)
      _ = |g x| := mul_one _
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact MeasurableSet.iUnion PeriodicCutoff.measurable_heatPeriodicTile
  have hFUnion : IntegrableOn F S := by
    rw [hS4]
    exact (((hFtile (false, false)).union (hFtile (false, true))).union
      (hFtile (true, false))).union (hFtile (true, true))
  have hFindicator : Integrable (S.indicator F) volume :=
    hFUnion.integrable_indicator hSmeas
  have hFzero : F =ᵐ[volume] S.indicator F := by
    filter_upwards with x
    by_cases hx : x ∈ S
    · simp [hx]
    · have hnot : x ∉ Function.support heatPeriodicCutoff2 := by
        intro hsup
        exact hx (heatPeriodicCutoff2_support_subset_tiles hsup)
      have hχzero : heatPeriodicCutoff2 x = 0 := by
        by_contra hzero
        exact hnot hzero
      simp [F, hx, hχzero]
  have hFint : Integrable F volume := hFindicator.congr hFzero.symm
  have hFUnionIntegral : ∫ x, F x = ∫ x in S, F x := by
    calc
      ∫ x, F x = ∫ x, S.indicator F x := integral_congr_ae hFzero
      _ = ∫ x in S, F x := integral_indicator hSmeas
  have htilesDisjoint :
      (↑(Finset.univ : Finset (Bool × Bool)) : Set (Bool × Bool)).Pairwise
        (Function.onFun Disjoint heatPeriodicTile) := by
    intro b hb c hc hbc
    exact PeriodicCutoff.heatPeriodicTile_disjoint hbc
  have htileSum := integral_biUnion_finset
    (t := (Finset.univ : Finset (Bool × Bool)))
    (s := heatPeriodicTile) (fun b hb => PeriodicCutoff.measurable_heatPeriodicTile b)
    htilesDisjoint (fun b hb => hFtile b)
  have hsum :
      ∫ x in S, F x = ∑ b : Bool × Bool, ∫ x in heatPeriodicTile b, F x := by
    rw [hSFin]
    exact htileSum
  have hperiodicShift (b : Bool × Bool) (x : Vec 2) :
      g (x + heatPeriodicTileStart b) = g x := by
    simpa [heatPeriodicTileStart] using hper (heatPeriodicTileShift b) x
  have htermInt (b : Bool × Bool) :
      Integrable (fun x : Vec 2 =>
        g x * heatPeriodicCutoff2 (x + heatPeriodicTileStart b))
        (volume.restrict (unitCell 2)) := by
    have htranslated := integrable_unitCellAt_translate (hFtile b)
    have htranslated' :
        Integrable (fun x : Vec 2 => F (x + heatPeriodicTileStart b))
          (volume.restrict (unitCell 2)) := by
      exact htranslated
    exact htranslated'.congr (Filter.Eventually.of_forall fun x => by
      simp [F, hperiodicShift b x])
  have htermsum := integral_finsetSum
    (s := (Finset.univ : Finset (Bool × Bool)))
    (f := fun b x => g x * heatPeriodicCutoff2 (x + heatPeriodicTileStart b))
    (fun b hb => htermInt b)
  have hsumCell :
      (∑ b : Bool × Bool,
        ∫ x in unitCell 2,
          g x * heatPeriodicCutoff2 (x + heatPeriodicTileStart b)) =
        ∫ x in unitCell 2, g x := by
    rw [← htermsum]
    apply setIntegral_congr_fun (measurableSet_unitCell 2)
    intro x hx
    have hpart :
        ∑ b : Bool × Bool,
          heatPeriodicCutoff2 (x + heatPeriodicTileStart b) = 1 := by
      simpa [heatPeriodicTileStart] using
        sum_heatPeriodicCutoff2_translates hx
    calc
      ∑ b : Bool × Bool,
          g x * heatPeriodicCutoff2 (x + heatPeriodicTileStart b) =
        g x * ∑ b : Bool × Bool,
          heatPeriodicCutoff2 (x + heatPeriodicTileStart b) := by
            rw [Finset.mul_sum]
      _ = g x := by
        rw [hpart, mul_one]
  calc
    ∫ x, g x * heatPeriodicCutoff2 x = ∫ x, F x := by rfl
    _ = ∫ x in S, F x := hFUnionIntegral
    _ = ∑ b : Bool × Bool, ∫ x in heatPeriodicTile b, F x := hsum
    _ = ∑ b : Bool × Bool,
        ∫ x in unitCell 2,
          g x * heatPeriodicCutoff2 (x + heatPeriodicTileStart b) := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        ∫ x in heatPeriodicTile b, F x =
            ∫ x in unitCell 2, F (x + heatPeriodicTileStart b) := by
          simpa [heatPeriodicTile] using
            integral_unitCellAt_translate F (heatPeriodicTileStart b)
        _ = ∫ x in unitCell 2,
            g x * heatPeriodicCutoff2 (x + heatPeriodicTileStart b) := by
          apply setIntegral_congr_fun (measurableSet_unitCell 2)
          intro x hx
          simp [F, hperiodicShift b x]
    _ = ∫ x in unitCell 2, g x := hsumCell

/-- Folding against a compactly supported weight sums its translates over one
unit cell. The tilewise integrability premise is convenient for weights such
as derivatives of the partition cutoff. -/
theorem integral_periodic_weight2 {g w q : Vec 2 → ℝ}
    (hper : IsZdPeriodic g)
    (hSupport : Function.support w ⊆
      ⋃ b : Bool × Bool, heatPeriodicTile b)
    (hTile : ∀ b : Bool × Bool,
      IntegrableOn (fun x => g x * w x) (heatPeriodicTile b))
    (hPeriod : ∀ x ∈ unitCell 2,
      ∑ b : Bool × Bool, w (x + heatPeriodicTileStart b) = q x) :
    Integrable (fun x => g x * w x) volume ∧
      ∫ x, g x * w x = ∫ x in unitCell 2, g x * q x := by
  classical
  let F : Vec 2 → ℝ := fun x => g x * w x
  let S : Set (Vec 2) := ⋃ b : Bool × Bool, heatPeriodicTile b
  have hS4 : S =
      ((heatPeriodicTile (false, false) ∪ heatPeriodicTile (false, true)) ∪
        heatPeriodicTile (true, false)) ∪ heatPeriodicTile (true, true) := by
    ext x
    simp [S]
    tauto
  have hSFin : S =
      ⋃ b ∈ (Finset.univ : Finset (Bool × Bool)), heatPeriodicTile b := by
    rw [hS4]
    ext x
    simp
    tauto
  have hFtile : ∀ b : Bool × Bool, IntegrableOn F (heatPeriodicTile b) := by
    exact hTile
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact MeasurableSet.iUnion PeriodicCutoff.measurable_heatPeriodicTile
  have hFUnion : IntegrableOn F S := by
    rw [hS4]
    exact (((hFtile (false, false)).union (hFtile (false, true))).union
      (hFtile (true, false))).union (hFtile (true, true))
  have hFindicator : Integrable (S.indicator F) volume :=
    hFUnion.integrable_indicator hSmeas
  have hFzero : F =ᵐ[volume] S.indicator F := by
    filter_upwards with x
    by_cases hx : x ∈ S
    · simp [hx]
    · have hwzero : w x = 0 := by
        by_contra hw
        exact hx (hSupport (by simp [Function.mem_support, hw]))
      simp [F, hx, hwzero]
  have hFint : Integrable F volume := hFindicator.congr hFzero.symm
  have hFUnionIntegral : ∫ x, F x = ∫ x in S, F x := by
    calc
      ∫ x, F x = ∫ x, S.indicator F x := integral_congr_ae hFzero
      _ = ∫ x in S, F x := integral_indicator hSmeas
  have htilesDisjoint :
      (↑(Finset.univ : Finset (Bool × Bool)) : Set (Bool × Bool)).Pairwise
        (Function.onFun Disjoint heatPeriodicTile) := by
    intro b hb c hc hbc
    exact PeriodicCutoff.heatPeriodicTile_disjoint hbc
  have htileSum := integral_biUnion_finset
    (t := (Finset.univ : Finset (Bool × Bool)))
    (s := heatPeriodicTile) (fun b hb => PeriodicCutoff.measurable_heatPeriodicTile b)
    htilesDisjoint (fun b hb => hFtile b)
  have hsum :
      ∫ x in S, F x = ∑ b : Bool × Bool, ∫ x in heatPeriodicTile b, F x := by
    rw [hSFin]
    exact htileSum
  have hperiodicShift (b : Bool × Bool) (x : Vec 2) :
      g (x + heatPeriodicTileStart b) = g x := by
    simpa [heatPeriodicTileStart] using hper (heatPeriodicTileShift b) x
  have htermInt (b : Bool × Bool) :
      Integrable (fun x : Vec 2 => g x * w (x + heatPeriodicTileStart b))
        (volume.restrict (unitCell 2)) := by
    have htranslated := integrable_unitCellAt_translate (hFtile b)
    have htranslated' :
        Integrable (fun x : Vec 2 => F (x + heatPeriodicTileStart b))
          (volume.restrict (unitCell 2)) := by
      exact htranslated
    exact htranslated'.congr (Filter.Eventually.of_forall fun x => by
      simp [F, hperiodicShift b x])
  have htermsum := integral_finsetSum
    (s := (Finset.univ : Finset (Bool × Bool)))
    (f := fun b x => g x * w (x + heatPeriodicTileStart b))
    (fun b hb => htermInt b)
  have hsumCell :
      (∑ b : Bool × Bool,
        ∫ x in unitCell 2, g x * w (x + heatPeriodicTileStart b)) =
        ∫ x in unitCell 2, g x * q x := by
    rw [← htermsum]
    apply setIntegral_congr_fun (measurableSet_unitCell 2)
    intro x hx
    change (∑ b : Bool × Bool, g x * w (x + heatPeriodicTileStart b)) =
      g x * q x
    rw [← Finset.mul_sum]
    rw [hPeriod x hx]
  constructor
  · exact hFint
  · calc
      ∫ x, g x * w x = ∫ x, F x := by rfl
      _ = ∫ x in S, F x := hFUnionIntegral
      _ = ∑ b : Bool × Bool, ∫ x in heatPeriodicTile b, F x := hsum
      _ = ∑ b : Bool × Bool,
          ∫ x in unitCell 2, g x * w (x + heatPeriodicTileStart b) := by
        apply Finset.sum_congr rfl
        intro b hb
        calc
          ∫ x in heatPeriodicTile b, F x =
              ∫ x in unitCell 2, F (x + heatPeriodicTileStart b) := by
            simpa [heatPeriodicTile] using
              integral_unitCellAt_translate F (heatPeriodicTileStart b)
          _ = ∫ x in unitCell 2,
              g x * w (x + heatPeriodicTileStart b) := by
            apply setIntegral_congr_fun (measurableSet_unitCell 2)
            intro x hx
            simp [F, hperiodicShift b x]
      _ = ∫ x in unitCell 2, g x * q x := hsumCell

end AVenhance.Infra.Heat
