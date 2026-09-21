/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import LeanPool.OneManifold.OneMfld.Charts

/-! # Normalization of interval charts

Affine tools for putting interval charts into standard position without changing their
sources: an `HChart` can be rescaled so its target is `Iio 1`, an `OChart` so its target
is `Ioo 0 1`, and an `OChart` with target `Ioo 0 1` can be orientation-reversed
(`x ↦ 1 - x`). H-charts cannot be flipped: the closed end at `0` is a boundary point.
-/

open Set

noncomputable section

/-- Multiplication by a positive constant, as a self-homeomorphism of `ℝ≥0`. -/
def NNReal.mulHomeomorph (c : NNReal) (hc : 0 < c) : NNReal ≃ₜ NNReal where
  toFun x := c * x
  invFun y := c⁻¹ * y
  left_inv := by
    intro x
    exact inv_mul_cancel_left₀ hc.ne' x
  right_inv := by
    intro y
    exact mul_inv_cancel_left₀ hc.ne' y
  continuous_toFun := by
    exact continuous_const.mul continuous_id
  continuous_invFun := by
    exact continuous_const.mul continuous_id

@[simp] lemma NNReal.mulHomeomorph_apply (c : NNReal) (hc : 0 < c) (x : NNReal) :
    NNReal.mulHomeomorph c hc x = c * x := rfl

@[simp] lemma NNReal.mulHomeomorph_symm_apply (c : NNReal) (hc : 0 < c) (y : NNReal) :
    (NNReal.mulHomeomorph c hc).symm y = c⁻¹ * y := rfl

/-- The affine map `x ↦ (x - u) / (v - u)`, as an `OpenPartialHomeomorph ℝ≥0 ℝ≥0` with
source `Ioo u v` and target `Ioo 0 1`. -/
def affineIooOPH (u v : NNReal) (h : u < v) :
    { e : OpenPartialHomeomorph NNReal NNReal //
      e.source = Ioo u v ∧ e.target = Ioo 0 1 ∧
      ∀ x ∈ Ioo u v, e x = (x - u) / (v - u) } := by
  have hvu : 0 < v - u := tsub_pos_of_lt h
  refine ⟨{ toFun := fun x => (x - u) / (v - u)
            invFun := fun y => u + y * (v - u)
            source := Ioo u v
            target := Ioo 0 1
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := isOpen_Ioo
            open_target := isOpen_Ioo
            continuousOn_toFun :=
              ((continuous_id.sub continuous_const).div_const _).continuousOn
            continuousOn_invFun :=
              (continuous_const.add (continuous_id.mul continuous_const)).continuousOn },
    rfl, rfl, fun x _ => rfl⟩
  · intro x hx
    exact ⟨div_pos (tsub_pos_of_lt hx.1) hvu,
      (div_lt_one hvu).mpr (tsub_lt_tsub_right_of_le hx.1.le hx.2)⟩
  · intro y hy
    exact ⟨lt_add_of_pos_right u (mul_pos hy.1 hvu),
      lt_tsub_iff_left.mp (mul_lt_of_lt_one_left hvu hy.2)⟩
  · intro x hx
    show u + (x - u) / (v - u) * (v - u) = x
    rw [div_mul_cancel₀ _ hvu.ne', add_tsub_cancel_of_le hx.1.le]
  · intro y _
    show (u + y * (v - u) - u) / (v - u) = y
    rw [add_tsub_cancel_left, mul_div_cancel_right₀ _ hvu.ne']

/-- The reflection `x ↦ 1 - x`, as an `OpenPartialHomeomorph ℝ≥0 ℝ≥0` with source and
target `Ioo 0 1`. -/
def reflectIooOPH :
    { e : OpenPartialHomeomorph NNReal NNReal //
      e.source = Ioo 0 1 ∧ e.target = Ioo 0 1 ∧
      ∀ x ∈ Ioo (0 : NNReal) 1, e x = 1 - x } := by
  refine ⟨{ toFun := fun x => 1 - x
            invFun := fun y => 1 - y
            source := Ioo 0 1
            target := Ioo 0 1
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := isOpen_Ioo
            open_target := isOpen_Ioo
            continuousOn_toFun := (continuous_const.sub continuous_id).continuousOn
            continuousOn_invFun := (continuous_const.sub continuous_id).continuousOn },
    rfl, rfl, fun x _ => rfl⟩
  · intro x hx
    exact ⟨tsub_pos_of_lt hx.2, tsub_lt_self one_pos hx.1⟩
  · intro y hy
    exact ⟨tsub_pos_of_lt hy.2, tsub_lt_self one_pos hy.1⟩
  · intro x hx
    exact tsub_tsub_cancel_of_le hx.2.le
  · intro y hy
    exact tsub_tsub_cancel_of_le hy.2.le

variable {M : Type*} [TopologicalSpace M]

/-- Rescale an `HChart` so its target is `Iio 1`, without changing its source. -/
def HChart.rescale (a : HChart M) (hne : a.source.Nonempty) :
    { b : HChart M // b.source = a.source ∧ b.target = Iio 1 ∧
      ∃ v : NNReal, 0 < v ∧ a.target = Iio v ∧ ∀ x ∈ a.source, b.toFun x = v⁻¹ * a.toFun x } := by
  let v := a.target_iio.choose
  have hv : Iio v = a.target := a.target_iio.choose_spec
  have hvpos : 0 < v := by
    obtain ⟨y, hy⟩ := chart_target_nonempty a.toOpenPartialHomeomorph hne
    rw [← hv] at hy
    exact lt_of_le_of_lt zero_le hy
  have hipos : 0 < v⁻¹ := inv_pos.mpr hvpos
  have htarget :
      (a.toOpenPartialHomeomorph.transHomeomorph (NNReal.mulHomeomorph v⁻¹ hipos)).target
        = Iio 1 := by
    rw [OpenPartialHomeomorph.transHomeomorph_target, ← hv]
    ext y
    simp only [mem_preimage, NNReal.mulHomeomorph_symm_apply, mem_Iio, inv_inv]
    exact mul_lt_iff_lt_one_right hvpos
  exact ⟨⟨a.toOpenPartialHomeomorph.transHomeomorph (NNReal.mulHomeomorph v⁻¹ hipos),
      ⟨1, htarget.symm⟩⟩,
    rfl, htarget, ⟨v, hvpos, hv.symm, fun x _ => rfl⟩⟩

/-- Rescale an `OChart` so its target is `Ioo 0 1`, without changing its source. -/
def OChart.rescale (a : OChart M) (hne : a.source.Nonempty) :
    { b : OChart M // b.source = a.source ∧ b.target = Ioo 0 1 ∧
      ∃ u v : NNReal, u < v ∧ a.target = Ioo u v ∧
        ∀ x ∈ a.source, b.toFun x = (a.toFun x - u) / (v - u) } := by
  let u := a.target_ioo.choose
  let v := a.target_ioo.choose_spec.choose
  have huv : Ioo u v = a.target := a.target_ioo.choose_spec.choose_spec
  have h : u < v := by
    obtain ⟨y, hy⟩ := chart_target_nonempty a.toOpenPartialHomeomorph hne
    rw [← huv] at hy
    exact hy.1.trans hy.2
  obtain ⟨e, hes, het, hef⟩ := affineIooOPH u v h
  have hsource : (a.toOpenPartialHomeomorph.trans e).source = a.source := by
    rw [OpenPartialHomeomorph.trans_source, hes]
    refine inter_eq_left.mpr fun x hx => ?_
    rw [mem_preimage, huv]
    exact a.toOpenPartialHomeomorph.map_source hx
  have htarget : (a.toOpenPartialHomeomorph.trans e).target = Ioo 0 1 := by
    rw [OpenPartialHomeomorph.trans_target, het]
    refine inter_eq_left.mpr fun y hy => ?_
    rw [mem_preimage, ← huv, ← hes]
    exact e.map_target (by rw [het]; exact hy)
  refine ⟨⟨a.toOpenPartialHomeomorph.trans e, ⟨0, 1, htarget.symm⟩⟩, hsource, htarget,
    ⟨u, v, h, huv.symm, fun x hx => ?_⟩⟩
  have hmem : a.toFun x ∈ Ioo u v := by
    rw [huv]
    exact a.toOpenPartialHomeomorph.map_source hx
  exact hef _ hmem

/-- Reverse the orientation of an `OChart` with target `Ioo 0 1`, without changing its
source. -/
def OChart.flip (a : OChart M) (h01 : a.target = Ioo 0 1) :
    { b : OChart M // b.source = a.source ∧ b.target = Ioo 0 1 ∧
      ∀ x ∈ a.source, b.toFun x = 1 - a.toFun x } := by
  obtain ⟨e, hes, het, hef⟩ := reflectIooOPH
  have hsource : (a.toOpenPartialHomeomorph.trans e).source = a.source := by
    rw [OpenPartialHomeomorph.trans_source, hes]
    refine inter_eq_left.mpr fun x hx => ?_
    rw [mem_preimage, ← h01]
    exact a.toOpenPartialHomeomorph.map_source hx
  have htarget : (a.toOpenPartialHomeomorph.trans e).target = Ioo 0 1 := by
    rw [OpenPartialHomeomorph.trans_target, het]
    refine inter_eq_left.mpr fun y hy => ?_
    rw [mem_preimage, h01, ← hes]
    exact e.map_target (by rw [het]; exact hy)
  refine ⟨⟨a.toOpenPartialHomeomorph.trans e, ⟨0, 1, htarget.symm⟩⟩, hsource, htarget,
    fun x hx => ?_⟩
  have hmem : a.toFun x ∈ Ioo (0 : NNReal) 1 := by
    rw [← h01]
    exact a.toOpenPartialHomeomorph.map_source hx
  exact hef _ hmem

end
