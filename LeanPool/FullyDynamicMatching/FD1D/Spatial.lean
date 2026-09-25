/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.Transport
public import LeanPool.FullyDynamicMatching.FD1D.Markov
public import LeanPool.FullyDynamicMatching.FD1D.Tree

/-! # Spatial -/

@[expose] public section

namespace FD1D

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory

/-!
# Concrete spatial inventory and dyadic quantile selection

This module connects the recursive transport construction to an inventory of
actual points. A supply configuration retains both each real location and
its certified depth-`L` cell label. The recursive quantile selector is given
a finite leaf index, and its law under Lebesgue-uniform demand is computed
exactly, including zero-mass leaves.
-/

/-- Split the left-to-right leaves of a depth-`L + 1` tree into two blocks. -/
def dyadicLeafSumEquiv (L : ℕ) :
    DyadicNode L ⊕ DyadicNode L ≃ DyadicNode (L + 1) :=
  finSumFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_two]))

@[simp]
theorem dyadicLeafSumEquiv_inl_val {L : ℕ} (i : DyadicNode L) :
    (dyadicLeafSumEquiv L (Sum.inl i)).val = i.val := by
  simp [dyadicLeafSumEquiv]

@[simp]
theorem dyadicLeafSumEquiv_inr_val {L : ℕ} (i : DyadicNode L) :
    (dyadicLeafSumEquiv L (Sum.inr i)).val = 2 ^ L + i.val := by
  simp [dyadicLeafSumEquiv, Nat.add_comm]

namespace DyadicMass

/-- The mass of a specified leaf, indexed from left to right. -/
def leafMass : {L : ℕ} → DyadicMass L → DyadicNode L → ℝ
  | 0, leaf mass, _ => mass
  | L + 1, branch left right, i =>
      match (dyadicLeafSumEquiv L).symm i with
      | Sum.inl j => leafMass left j
      | Sum.inr j => leafMass right j

/-- Total mass strictly to the left of a specified leaf. -/
def lowerMass : {L : ℕ} → DyadicMass L → DyadicNode L → ℝ
  | 0, leaf _, _ => 0
  | L + 1, branch left right, i =>
      match (dyadicLeafSumEquiv L).symm i with
      | Sum.inl j => lowerMass left j
      | Sum.inr j => left.total + lowerMass right j

/--
The finite leaf index selected by the same recursive mass comparisons as
`selectedLeaf` and `quantile`.
-/
def selectedIndex : {L : ℕ} → DyadicMass L → ℝ → DyadicNode L
  | 0, leaf _, _ => 0
  | L + 1, branch left right, u =>
      if u ≤ left.total then
        dyadicLeafSumEquiv L (Sum.inl (selectedIndex left u))
      else
        dyadicLeafSumEquiv L
          (Sum.inr (selectedIndex right (u - left.total)))

@[simp]
theorem leafMass_left {L : ℕ} (left right : DyadicMass L)
    (i : DyadicNode L) :
    (branch left right).leafMass
        (dyadicLeafSumEquiv L (Sum.inl i)) = left.leafMass i := by
  simp [leafMass]

@[simp]
theorem leafMass_right {L : ℕ} (left right : DyadicMass L)
    (i : DyadicNode L) :
    (branch left right).leafMass
        (dyadicLeafSumEquiv L (Sum.inr i)) = right.leafMass i := by
  simp [leafMass]

@[simp]
theorem lowerMass_left {L : ℕ} (left right : DyadicMass L)
    (i : DyadicNode L) :
    (branch left right).lowerMass
        (dyadicLeafSumEquiv L (Sum.inl i)) = left.lowerMass i := by
  simp [lowerMass]

@[simp]
theorem lowerMass_right {L : ℕ} (left right : DyadicMass L)
    (i : DyadicNode L) :
    (branch left right).lowerMass
        (dyadicLeafSumEquiv L (Sum.inr i)) =
      left.total + right.lowerMass i := by
  simp [lowerMass]

theorem sum_leafMass {L : ℕ} (q : DyadicMass L) :
    ∑ i, q.leafMass i = q.total := by
  induction q with
  | leaf mass =>
      simp [leafMass, total]
  | @branch L left right ihLeft ihRight =>
      calc
        ∑ i, (branch left right).leafMass i =
            ∑ s : DyadicNode L ⊕ DyadicNode L,
              (branch left right).leafMass (dyadicLeafSumEquiv L s) := by
                symm
                exact (dyadicLeafSumEquiv L).sum_comp
                  (fun i => (branch left right).leafMass i)
        _ = ∑ i, left.leafMass i + ∑ i, right.leafMass i := by
              rw [Fintype.sum_sum_type]
              simp
        _ = (branch left right).total := by
              simp [ihLeft, ihRight, total]

theorem leafMass_nonneg {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) (i : DyadicNode L) :
    0 ≤ q.leafMass i := by
  induction q with
  | leaf mass =>
      change 0 ≤ mass at hq
      simpa [leafMass] using hq
  | @branch L left right ihLeft ihRight =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · simpa using ihLeft hq.1 i
      · simpa using ihRight hq.2 i

theorem lowerMass_nonneg {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) (i : DyadicNode L) :
    0 ≤ q.lowerMass i := by
  induction q with
  | leaf =>
      simp [lowerMass]
  | @branch L left right ihLeft ihRight =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · simpa using ihLeft hq.1 i
      · simp only [lowerMass_right]
        exact add_nonneg (total_nonneg left hq.1) (ihRight hq.2 i)

theorem lowerMass_add_leafMass_le_total {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) (i : DyadicNode L) :
    q.lowerMass i + q.leafMass i ≤ q.total := by
  induction q with
  | leaf mass =>
      simp [lowerMass, leafMass, total]
  | @branch L left right ihLeft ihRight =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · simp only [lowerMass_left, leafMass_left, total]
        exact (ihLeft hq.1 i).trans
          (le_add_of_nonneg_right (total_nonneg right hq.2))
      · simp only [lowerMass_right, leafMass_right, total]
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_left (ihRight hq.2 i) left.total

theorem selectedIndex_measurable {L : ℕ} (q : DyadicMass L) :
    Measurable q.selectedIndex := by
  induction q with
  | leaf =>
      exact measurable_const
  | @branch L left right ihLeft ihRight =>
      apply Measurable.ite (measurableSet_le measurable_id measurable_const)
      · exact (measurable_of_finite
          (fun i : DyadicNode L =>
            dyadicLeafSumEquiv L (Sum.inl i))).comp ihLeft
      · exact (measurable_of_finite
          (fun i : DyadicNode L =>
            dyadicLeafSumEquiv L (Sum.inr i))).comp
              (ihRight.comp (measurable_id.sub measurable_const))

/-- The real endpoint returned by `selectedLeaf` is the indexed cell's left endpoint. -/
theorem selectedLeaf_eq_selectedIndex {L : ℕ} (q : DyadicMass L) (u : ℝ) :
    q.selectedLeaf u =
      (q.selectedIndex u).val / ((2 ^ L : ℕ) : ℝ) := by
  induction q generalizing u with
  | leaf =>
      simp [selectedLeaf, selectedIndex]
  | @branch L left right ihLeft ihRight =>
      simp only [selectedLeaf, selectedIndex]
      by_cases hu : u ≤ left.total
      · rw [ite_eq_left hu, ite_eq_left hu, ihLeft]
        simp only [dyadicLeafSumEquiv_inl_val, pow_succ]
        have hpow : (((2 ^ L : ℕ) : ℝ)) ≠ 0 := by
          exact_mod_cast (pow_ne_zero L (by decide : (2 : ℕ) ≠ 0))
        norm_num
        field_simp [hpow]
      · rw [ite_eq_right hu, ite_eq_right hu, ihRight]
        simp only [dyadicLeafSumEquiv_inr_val, pow_succ]
        have hpow : (((2 ^ L : ℕ) : ℝ)) ≠ 0 := by
          exact_mod_cast (pow_ne_zero L (by decide : (2 : ℕ) ≠ 0))
        norm_num
        field_simp [hpow]

/-- The selected endpoint never lies to the right of the continuous quantile. -/
theorem selectedLeaf_le_quantile {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    q.selectedLeaf u ≤ q.quantile u := by
  induction q generalizing u with
  | leaf mass =>
      simp only [selectedLeaf, quantile]
      exact (quantile_mem_unit (leaf mass) hq hu0 hu1).1
  | @branch L left right ihLeft ihRight =>
      simp only [selectedLeaf, quantile]
      by_cases hu : u ≤ left.total
      · rw [ite_eq_left hu, ite_eq_left hu]
        exact div_le_div_of_nonneg_right
          (ihLeft hq.1 hu0 hu) (by norm_num)
      · rw [ite_eq_right hu, ite_eq_right hu]
        have huLocal0 : 0 ≤ u - left.total := by linarith
        have huLocal1 : u - left.total ≤ right.total := by
          rw [total] at hu1
          linarith
        have hlocal := ihRight hq.2 huLocal0 huLocal1
        apply div_le_div_of_nonneg_right _ (by norm_num)
        linarith

/--
Away from the single boundary point `u = 0`, a leaf is selected exactly on
its right-closed cumulative-mass interval. This formulation handles
zero-mass leaves without any positivity assumption on individual masses.
-/
theorem selectedIndex_eq_iff_mem_massInterval {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ q.total)
    (i : DyadicNode L) :
    q.selectedIndex u = i ↔
      u ∈ Ioc (q.lowerMass i) (q.lowerMass i + q.leafMass i) := by
  induction q generalizing u with
  | leaf mass =>
      rw [Fin.eq_zero i]
      have huMass : u ≤ mass := by simpa [total] using hu1
      simp [selectedIndex, lowerMass, leafMass, hu0, huMass]
  | @branch L left right ihLeft ihRight =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · constructor
        · intro hsel
          have huLeft : u ≤ left.total := by
            by_contra hnot
            rw [selectedIndex, ite_eq_right hnot] at hsel
            have hs := (dyadicLeafSumEquiv L).injective hsel
            simp at hs
          have hlocal : left.selectedIndex u = i := by
            rw [selectedIndex, ite_eq_left huLeft] at hsel
            exact Sum.inl.inj ((dyadicLeafSumEquiv L).injective hsel)
          simpa using (ihLeft hq.1 hu0 huLeft i).mp hlocal
        · intro hmem
          have hmem' :
              u ∈ Ioc (left.lowerMass i)
                (left.lowerMass i + left.leafMass i) := by
            simpa using hmem
          have huLeft : u ≤ left.total := by
            exact hmem'.2.trans
              (left.lowerMass_add_leafMass_le_total hq.1 i)
          have hlocal :=
            (ihLeft hq.1 hu0 huLeft i).mpr hmem'
          simp [selectedIndex, huLeft, hlocal]
      · constructor
        · intro hsel
          have huRight : ¬u ≤ left.total := by
            intro huLeft
            rw [selectedIndex, ite_eq_left huLeft] at hsel
            have hs := (dyadicLeafSumEquiv L).injective hsel
            simp at hs
          have huLocal0 : 0 < u - left.total := by linarith
          have huLocal1 : u - left.total ≤ right.total := by
            rw [total] at hu1
            linarith
          have hlocal : right.selectedIndex (u - left.total) = i := by
            rw [selectedIndex, ite_eq_right huRight] at hsel
            exact Sum.inr.inj ((dyadicLeafSumEquiv L).injective hsel)
          have hinter :=
            (ihRight hq.2 huLocal0 huLocal1 i).mp hlocal
          simp only [lowerMass_right, leafMass_right, mem_Ioc]
          constructor <;> linarith [hinter.1, hinter.2]
        · intro hmem
          simp only [lowerMass_right, leafMass_right, mem_Ioc] at hmem
          have hLower := right.lowerMass_nonneg hq.2 i
          have huRight : ¬u ≤ left.total := by
            intro hu
            linarith [hmem.1, hLower]
          have huLocal0 : 0 < u - left.total := by linarith
          have huLocal1 : u - left.total ≤ right.total := by
            rw [total] at hu1
            linarith
          have hinter :
              u - left.total ∈
                Ioc (right.lowerMass i)
                  (right.lowerMass i + right.leafMass i) := by
            constructor <;> linarith [hmem.1, hmem.2]
          have hlocal :=
            (ihRight hq.2 huLocal0 huLocal1 i).mpr hinter
          simp [selectedIndex, huRight, hlocal]

/-- Lebesgue-uniform demand on the unit interval. -/
def uniformDemand : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

/-- Raw singleton mass of the finite pushforward by `selectedIndex`. -/
def selectedIndexPushforwardMass {L : ℕ} (q : DyadicMass L)
    (i : DyadicNode L) : ℝ :=
  ((Measure.map q.selectedIndex uniformDemand) {i}).toReal

private theorem ae_ne_zero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
  rw [ae_iff]
  simp only [not_ne_iff]
  rw [show {u : ℝ | u = 0} = ({0} : Set ℝ) by ext u; simp]
  exact measure_singleton 0

/--
The pushforward of Lebesgue-uniform demand assigns exactly the declared mass
to every leaf. The only discrepancy between recursive `≤` tie-breaking and
the half-open mass intervals is the null singleton `u = 0`.
-/
theorem selectedIndexPushforwardMass_eq_leafMass {L : ℕ}
    (q : DyadicMass L) (hq : q.IsProbability) (i : DyadicNode L) :
    q.selectedIndexPushforwardMass i = q.leafMass i := by
  unfold selectedIndexPushforwardMass uniformDemand
  rw [Measure.map_apply q.selectedIndex_measurable
    (measurableSet_singleton i)]
  rw [Measure.restrict_apply
    (q.selectedIndex_measurable (measurableSet_singleton i))]
  have hsets :
      (((q.selectedIndex ⁻¹' ({i} : Set (DyadicNode L))) ∩
          Icc (0 : ℝ) 1) : Set ℝ) =ᵐ[volume]
      Ioc (q.lowerMass i) (q.lowerMass i + q.leafMass i) := by
    filter_upwards [ae_ne_zero] with u hu
    apply propext
    change
      (q.selectedIndex u = i ∧ u ∈ Icc (0 : ℝ) 1) ↔
        u ∈ Ioc (q.lowerMass i) (q.lowerMass i + q.leafMass i)
    constructor
    · rintro ⟨hsel, huUnit⟩
      have huPos : 0 < u := lt_of_le_of_ne huUnit.1 (Ne.symm hu)
      exact (q.selectedIndex_eq_iff_mem_massInterval hq.nonneg
        huPos (by simpa [hq.total_eq_one] using huUnit.2) i).mp hsel
    · intro hmem
      have hLower := q.lowerMass_nonneg hq.nonneg i
      have hUpper := q.lowerMass_add_leafMass_le_total hq.nonneg i
      have huPos : 0 < u := by linarith [hmem.1]
      have huTotal : u ≤ q.total := hmem.2.trans hUpper
      constructor
      · exact (q.selectedIndex_eq_iff_mem_massInterval hq.nonneg
          huPos huTotal i).mpr hmem
      · exact ⟨huPos.le, by simpa [hq.total_eq_one] using huTotal⟩
  rw [measure_congr hsets, Real.volume_Ioc]
  have hmass := q.leafMass_nonneg hq.nonneg i
  rw [show q.lowerMass i + q.leafMass i - q.lowerMass i =
    q.leafMass i by ring]
  exact ENNReal.toReal_ofReal hmass

/-- The finite law induced by the demand-driven recursive leaf selector. -/
def selectedIndexLaw {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) : FiniteLaw (DyadicNode L) where
  mass := q.selectedIndexPushforwardMass
  mass_nonneg i := ENNReal.toReal_nonneg
  sum_mass := by
    simp_rw [q.selectedIndexPushforwardMass_eq_leafMass hq]
    rw [q.sum_leafMass, hq.total_eq_one]

@[simp]
theorem selectedIndexLaw_mass {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) (i : DyadicNode L) :
    (q.selectedIndexLaw hq).mass i = q.leafMass i :=
  q.selectedIndexPushforwardMass_eq_leafMass hq i

end DyadicMass

/-! ## Exact spatial configurations -/

/-- Width of one depth-`L` dyadic cell. -/
def dyadicCellWidth (L : ℕ) : ℝ :=
  1 / ((2 ^ L : ℕ) : ℝ)

/-- Left endpoint of a depth-`L` dyadic cell. -/
def dyadicCellLeft {L : ℕ} (i : DyadicNode L) : ℝ :=
  i.val / ((2 ^ L : ℕ) : ℝ)

/-- The closed cell certified for a labeled supply point. -/
def dyadicCell {L : ℕ} (i : DyadicNode L) : Set ℝ :=
  Icc (dyadicCellLeft i) (dyadicCellLeft i + dyadicCellWidth L)

theorem dyadicCellWidth_pos (L : ℕ) :
    0 < dyadicCellWidth L := by
  apply one_div_pos.mpr
  exact_mod_cast Nat.two_pow_pos L

theorem dyadicCell_subset_unit {L : ℕ} (i : DyadicNode L) :
    dyadicCell i ⊆ Icc (0 : ℝ) 1 := by
  intro z hz
  have hi0 : 0 ≤ (i.val : ℝ) := by positivity
  have hi1 : (i.val : ℝ) + 1 ≤ (2 ^ L : ℕ) := by
    exact_mod_cast i.isLt
  constructor
  · exact le_trans (div_nonneg (by positivity)
      (by exact_mod_cast (Nat.two_pow_pos L).le)) hz.1
  · calc
      z ≤ dyadicCellLeft i + dyadicCellWidth L := hz.2
      _ = ((i.val : ℝ) + 1) / ((2 ^ L : ℕ) : ℝ) := by
        simp [dyadicCellLeft, dyadicCellWidth]
        ring
      _ ≤ 1 := by
        have hpow : (0 : ℝ) < (2 ^ L : ℕ) := by
          exact_mod_cast Nat.two_pow_pos L
        rw [div_le_one hpow]
        exact_mod_cast hi1

/--
An exact finite supply configuration: `m` labeled real points, each in the
unit interval and carrying a certified depth-`L` leaf label.
-/
structure SupplyConfiguration (L m : ℕ) where
  /-- Spatial coordinate of each item in the supply configuration. -/
  location : Fin m → ℝ
  /-- Dyadic cell containing each item in the supply configuration. -/
  leaf : Fin m → DyadicNode L
  location_mem_unit : ∀ j, location j ∈ Icc (0 : ℝ) 1
  location_mem_cell : ∀ j, location j ∈ dyadicCell (leaf j)

namespace SupplyConfiguration

variable {L m : ℕ}

/-- Number of configured supply points carrying one leaf label. -/
def leafCount (C : SupplyConfiguration L m) (i : DyadicNode L) : ℕ :=
  (Finset.univ.filter fun j => C.leaf j = i).card

theorem sum_leafCount (C : SupplyConfiguration L m) :
    ∑ i, C.leafCount i = m := by
  classical
  simp only [leafCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Count projection from exact locations to the finite inventory chain. -/
def countState (C : SupplyConfiguration L m) :
    InventoryState (DyadicNode L) m :=
  ⟨C.leafCount, C.sum_leafCount⟩

@[simp]
theorem countState_apply (C : SupplyConfiguration L m) (i : DyadicNode L) :
    C.countState.1 i = C.leafCount i :=
  rfl

/--
A total representative of a leaf. If the leaf is empty, the supplied
fallback is returned; the later a.e. feasibility theorem proves that this
case occurs only on the null exceptional demand set.
-/
def representative (C : SupplyConfiguration L m) (fallback : Fin m)
    (i : DyadicNode L) : Fin m :=
  if h : ∃ j, C.leaf j = i then Classical.choose h else fallback

theorem representative_leaf (C : SupplyConfiguration L m) (fallback : Fin m)
    (i : DyadicNode L) (h : ∃ j, C.leaf j = i) :
    C.leaf (C.representative fallback i) = i := by
  rw [representative, dite_eq_left h]
  exact Classical.choose_spec h

/-- Every positive-mass leaf contains an actual configured supply point. -/
def Supports (C : SupplyConfiguration L m) (q : DyadicMass L) : Prop :=
  ∀ i, 0 < q.leafMass i → ∃ j, C.leaf j = i

theorem supports_of_emptyMass (C : SupplyConfiguration L m)
    (q : DyadicMass L)
    (hempty : ∀ i, C.leafCount i = 0 → q.leafMass i = 0) :
    C.Supports q := by
  intro i hmass
  have hcount : 0 < C.leafCount i := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hmass.ne' (hempty i hzero)
  rcases Finset.card_pos.mp hcount with ⟨j, hj⟩
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

/-- The supply label selected by a uniform demand coordinate. -/
def selectedSupplyIndex (C : SupplyConfiguration L m) (q : DyadicMass L)
    (fallback : Fin m) (u : ℝ) : Fin m :=
  C.representative fallback (q.selectedIndex u)

/-- The actual configured supply location selected by the policy. -/
def selectedSupplyPoint (C : SupplyConfiguration L m) (q : DyadicMass L)
    (fallback : Fin m) (u : ℝ) : ℝ :=
  C.location (C.selectedSupplyIndex q fallback u)

theorem selectedSupplyPoint_measurable (C : SupplyConfiguration L m)
    (q : DyadicMass L) (fallback : Fin m) :
    Measurable (C.selectedSupplyPoint q fallback) := by
  exact (measurable_of_finite
    (fun i : DyadicNode L =>
      C.location (C.representative fallback i))).comp
        q.selectedIndex_measurable

theorem selectedSupplyPoint_mem_unit (C : SupplyConfiguration L m)
    (q : DyadicMass L) (fallback : Fin m) (u : ℝ) :
    C.selectedSupplyPoint q fallback u ∈ Icc (0 : ℝ) 1 :=
  C.location_mem_unit _

/--
Except at the zero demand boundary, the total representative really carries
the recursively selected leaf label.
-/
theorem selectedSupplyIndex_leaf_of_ne_zero
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hu0 : u ≠ 0) :
    C.leaf (C.selectedSupplyIndex q fallback u) = q.selectedIndex u := by
  have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have huTotal : u ≤ q.total := by
    simpa [hq.total_eq_one] using hu.2
  have hinter := (q.selectedIndex_eq_iff_mem_massInterval hq.nonneg
    huPos huTotal (q.selectedIndex u)).mp rfl
  have hmass : 0 < q.leafMass (q.selectedIndex u) := by
    linarith [hinter.1, hinter.2]
  exact C.representative_leaf fallback (q.selectedIndex u)
    (hsupport _ hmass)

/-- The selected configured item is feasible for almost every uniform demand. -/
theorem selectedSupplyIndex_leaf_ae
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) :
    ∀ᵐ u ∂DyadicMass.uniformDemand,
      C.leaf (C.selectedSupplyIndex q fallback u) = q.selectedIndex u := by
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
    rw [ae_iff]
    simp only [not_ne_iff]
    rw [show {u : ℝ | u = 0} = ({0} : Set ℝ) by ext u; simp]
    exact measure_singleton 0
  rw [DyadicMass.uniformDemand, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hne] with u hu0 hu
  exact C.selectedSupplyIndex_leaf_of_ne_zero q hq hsupport fallback hu hu0

/-- The continuous quantile belongs to the cell indexed by `selectedIndex`. -/
theorem quantile_mem_selectedCell
    (q : DyadicMass L) (hq : q.IsProbability)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    q.quantile u ∈ dyadicCell (q.selectedIndex u) := by
  have huTotal : u ≤ q.total := by
    simpa [hq.total_eq_one] using hu.2
  have hle := q.selectedLeaf_le_quantile hq.nonneg hu.1 huTotal
  have hclose := q.selectedLeaf_sub_quantile_le hq.nonneg hu.1 huTotal
  have hleft :
      dyadicCellLeft (q.selectedIndex u) = q.selectedLeaf u := by
    simpa [dyadicCellLeft] using (q.selectedLeaf_eq_selectedIndex u).symm
  rw [dyadicCell, hleft]
  constructor
  · exact hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hclose
    simpa [dyadicCellWidth] using
      (show q.quantile u ≤ q.selectedLeaf u +
          1 / ((2 ^ L : ℕ) : ℝ) by linarith)

/--
For every nonexceptional demand, the actual selected point and continuous
quantile lie in one and the same depth-`L` cell.
-/
theorem selectedSupplyPoint_sub_quantile_le_of_ne_zero
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hu0 : u ≠ 0) :
    |C.selectedSupplyPoint q fallback u - q.quantile u| ≤
      dyadicCellWidth L := by
  have hlabel :=
    C.selectedSupplyIndex_leaf_of_ne_zero q hq hsupport fallback hu hu0
  have hpoint := C.location_mem_cell (C.selectedSupplyIndex q fallback u)
  change C.selectedSupplyPoint q fallback u ∈
    dyadicCell (C.leaf (C.selectedSupplyIndex q fallback u)) at hpoint
  rw [hlabel] at hpoint
  have hquant := quantile_mem_selectedCell q hq hu
  rw [dyadicCell] at hpoint hquant
  rw [abs_le]
  constructor <;> linarith [hpoint.1, hpoint.2, hquant.1, hquant.2]

/-- The one-cell coupling bound holds almost everywhere under uniform demand. -/
theorem selectedSupplyPoint_sub_quantile_le_ae
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) :
    ∀ᵐ u ∂DyadicMass.uniformDemand,
      |C.selectedSupplyPoint q fallback u - q.quantile u| ≤
        dyadicCellWidth L := by
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
    rw [ae_iff]
    simp only [not_ne_iff]
    rw [show {u : ℝ | u = 0} = ({0} : Set ℝ) by ext u; simp]
    exact measure_singleton 0
  rw [DyadicMass.uniformDemand, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hne] with u hu0 hu
  exact C.selectedSupplyPoint_sub_quantile_le_of_ne_zero
    q hq hsupport fallback hu hu0

/-- Expected distance from a uniform demand to the actual selected supply point. -/
def expectedActualDistance (C : SupplyConfiguration L m)
    (q : DyadicMass L) (fallback : Fin m) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, |C.selectedSupplyPoint q fallback u - u|

theorem selectedSupplyDistance_integrable
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (fallback : Fin m) :
    IntegrableOn
      (fun u => |C.selectedSupplyPoint q fallback u - u|)
      (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    ((C.selectedSupplyPoint_measurable q fallback).sub
      measurable_id).abs.aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖|C.selectedSupplyPoint q fallback u - u|‖ ≤ 1
  rw [Real.norm_eq_abs, abs_abs]
  have hs := C.selectedSupplyPoint_mem_unit q fallback u
  exact abs_le.2 ⟨by linarith [hs.1, hu.2], by linarith [hs.2, hu.1]⟩

theorem quantileDistance_integrable
    (q : DyadicMass L) (hq : q.IsProbability) :
    IntegrableOn (fun u => |q.quantile u - u|) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (q.quantile_measurable.sub measurable_id).abs.aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖|q.quantile u - u|‖ ≤ 1
  rw [Real.norm_eq_abs, abs_abs]
  have hqUnit := q.quantile_mem_unit hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
  exact abs_le.2
    ⟨by linarith [hqUnit.1, hu.2], by linarith [hqUnit.2, hu.1]⟩

/--
Selecting an actual occupied point costs at most the exact CDF quantile area
plus one cell width. There is only one discretization term.
-/
theorem expectedActualDistance_le_one_cell
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) :
    C.expectedActualDistance q fallback ≤
      dyadicCellWidth L +
        cdfTransportArea (fun z => q.piecewiseCDF z - z) := by
  have hselected := C.selectedSupplyDistance_integrable q fallback
  have hquant := quantileDistance_integrable q hq
  have hconst :
      IntegrableOn (fun _ : ℝ => dyadicCellWidth L) (Icc (0 : ℝ) 1) :=
    integrableOn_const (C := dyadicCellWidth L) (by simp [Real.volume_Icc])
  have hrhs :
      IntegrableOn
        (fun u => dyadicCellWidth L + |q.quantile u - u|)
        (Icc (0 : ℝ) 1) :=
    hconst.add hquant
  have hclose := C.selectedSupplyPoint_sub_quantile_le_ae
    q hq hsupport fallback
  calc
    C.expectedActualDistance q fallback ≤
        ∫ u in Icc (0 : ℝ) 1,
          dyadicCellWidth L + |q.quantile u - u| := by
      apply integral_mono_ae hselected hrhs
      have hclose' :
          ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
            |C.selectedSupplyPoint q fallback u - q.quantile u| ≤
              dyadicCellWidth L := by
        simpa [DyadicMass.uniformDemand] using hclose
      filter_upwards [hclose'] with u hu
      calc
        |C.selectedSupplyPoint q fallback u - u| ≤
            |C.selectedSupplyPoint q fallback u - q.quantile u| +
              |q.quantile u - u| := abs_sub_le _ _ _
        _ ≤ dyadicCellWidth L + |q.quantile u - u| := by
          linarith
    _ = dyadicCellWidth L +
        ∫ u in Icc (0 : ℝ) 1, |q.quantile u - u| := by
      rw [MeasureTheory.integral_add hconst hquant]
      simp
    _ = dyadicCellWidth L +
        cdfTransportArea (fun z => q.piecewiseCDF z - z) := by
      congr 1
      change (q.quantilePolicy hq).quantileDistance =
        cdfTransportArea (fun z => q.piecewiseCDF z - z)
      exact (q.quantilePolicy hq).quantileDistance_eq_cdfTransportArea

/-! ## Matching the finite deletion kernel -/

/--
If the dyadic leaf masses are a deletion rule's probabilities at the count
projection, support by occupied concrete leaves follows automatically.
-/
theorem supports_of_deletionRule
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i) :
    C.Supports q := by
  apply C.supports_of_emptyMass q
  intro i hi
  rw [hmass i]
  exact R.empty C.countState i (by simpa using hi)

/-- The selected leaf marginal is exactly the deletion marginal. -/
theorem selectedIndexLaw_mass_eq_deletionRule
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i)
    (i : DyadicNode L) :
    (q.selectedIndexLaw hq).mass i = R.prob C.countState i := by
  rw [q.selectedIndexLaw_mass hq, hmass i]

/--
After an independent uniform arrival leaf, the concrete selected-leaf
marginal produces exactly the count transition kernel.
-/
theorem selectedIndex_transition_eq_kernel
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i)
    (y : InventoryState (DyadicNode L) m) :
    (∑ deleted, ∑ arrived,
      if InventoryState.move C.countState deleted arrived = y then
        (q.selectedIndexLaw hq).mass deleted *
          (1 / Fintype.card (DyadicNode L) : ℝ)
      else 0) =
      R.kernel C.countState y := by
  rw [DeletionRule.kernel_apply]
  simp_rw [q.selectedIndexLaw_mass hq, hmass]

/--
Actual-point transport for a configuration realizing a deletion rule: the
empty-leaf condition needed for feasibility is discharged by the rule.
-/
theorem expectedActualDistance_le_one_cell_of_deletionRule
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i)
    (fallback : Fin m) :
    C.expectedActualDistance q fallback ≤
      dyadicCellWidth L +
        cdfTransportArea (fun z => q.piecewiseCDF z - z) :=
  C.expectedActualDistance_le_one_cell q hq
    (C.supports_of_deletionRule q R hmass) fallback

end SupplyConfiguration

end

end FD1D
