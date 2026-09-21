/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import LeanPool.OneManifold.OneMfld.UnitInterval

/-! # Building blocks for the H-H gluing

Two overlapping boundary charts glue to a *closed* interval, so the glued chart cannot be
`NNReal`-valued (its target would not be open); it must land in the subtype
`UnitInterval`. The pieces:

* `halfOPH` — `x ↦ x/2` embedding `Iio 1 ⊆ ℝ≥0` onto the lower half `[0, 1/2)` of the
  unit interval (open in the subtype since `0` is an endpoint);
* `mobiusOPH k` — the decreasing Möbius map `x ↦ k/(x+k)` embedding all of `ℝ≥0` onto
  the upper piece `(0, 1]` (open in the subtype since `1` is an endpoint) — a decreasing
  reparametrization with no truncated-subtraction issues;
* the frontier of `{y ≤ c}` in the unit interval;
* reflection images of end-segments in `ℝ≥0`, used to re-orient `OChart`s.
-/

open Set Topology

noncomputable section

/-- `x ↦ x/2` as a partial homeomorphism from `ℝ≥0` (source `Iio 1`) to the unit
interval (target the sub-half-interval `[0, 1/2)`, open in the subtype). -/
def halfOPH :
    { e : OpenPartialHomeomorph NNReal UnitInterval //
      e.source = Iio 1 ∧ e.target = {y : UnitInterval | (y : ℝ) < 1/2} ∧
      ∀ x : NNReal, x ∈ Iio (1 : NNReal) → ((e x : ℝ) = x / 2) } := by
  have hmem : ∀ x : NNReal, min ((x : ℝ) / 2) 1 ∈ UnitInterval := fun x =>
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  refine ⟨{ toFun := fun x => ⟨min ((x : ℝ) / 2) 1, hmem x⟩
            invFun := fun y => Real.toNNReal (2 * (y : ℝ))
            source := Iio 1
            target := {y : UnitInterval | (y : ℝ) < 1/2}
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := isOpen_Iio
            open_target := ?_
            continuousOn_toFun :=
              (((NNReal.continuous_coe.div_const 2).min continuous_const).subtype_mk
                hmem).continuousOn
            continuousOn_invFun :=
              (continuous_real_toNNReal.comp
                (continuous_const.mul continuous_subtype_val)).continuousOn },
    rfl, rfl, fun x hx => ?_⟩
  · -- map_source'
    intro x hx
    have hx1 : x < (1 : NNReal) := hx
    have hx' : (x : ℝ) < 1 := by exact_mod_cast hx1
    change min ((x : ℝ) / 2) 1 < 1/2
    rw [min_eq_left (by linarith : (x : ℝ) / 2 ≤ 1)]
    linarith
  · -- map_target'
    intro y hy
    have hy' : (y : ℝ) < 1/2 := hy
    have h2 : (0:ℝ) ≤ 2 * (y : ℝ) := mul_nonneg (by norm_num) y.2.1
    change Real.toNNReal (2 * (y : ℝ)) < 1
    rw [Real.toNNReal_lt_iff_lt_coe h2, NNReal.coe_one]
    linarith
  · -- left_inv'
    intro x hx
    have hx1 : x < (1 : NNReal) := hx
    have hx' : (x : ℝ) < 1 := by exact_mod_cast hx1
    change Real.toNNReal (2 * min ((x : ℝ) / 2) 1) = x
    rw [min_eq_left (by linarith : (x : ℝ) / 2 ≤ 1),
      show 2 * ((x : ℝ) / 2) = (x : ℝ) from by ring]
    exact Real.toNNReal_coe
  · -- right_inv'
    intro y hy
    have hy' : (y : ℝ) < 1/2 := hy
    have h2 : (0:ℝ) ≤ 2 * (y : ℝ) := mul_nonneg (by norm_num) y.2.1
    apply Subtype.ext
    change min ((Real.toNNReal (2 * (y : ℝ)) : ℝ) / 2) 1 = (y : ℝ)
    rw [Real.coe_toNNReal _ h2,
      show 2 * (y : ℝ) / 2 = (y : ℝ) from by ring]
    exact min_eq_left y.2.2
  · -- open_target
    exact isOpen_Iio.preimage continuous_subtype_val
  · -- e x = x / 2 on the source
    have hx1 : x < (1 : NNReal) := hx
    have hx' : (x : ℝ) < 1 := by exact_mod_cast hx1
    exact min_eq_left (by linarith : (x : ℝ) / 2 ≤ 1)

/-- The Möbius map `x ↦ k/(x+k)` (for `k > 0`) as a partial homeomorphism from `ℝ≥0`
(source everything) to the unit interval (target `(0, 1]`, open in the subtype). It is
strictly decreasing, sends `0 ↦ 1`, and tends to `0` at infinity. -/
def mobiusOPH (k : NNReal) (hk : 0 < k) :
    { e : OpenPartialHomeomorph NNReal UnitInterval //
      e.source = univ ∧ e.target = {y : UnitInterval | 0 < (y : ℝ)} ∧
      (∀ x : NNReal, (e x : ℝ) = k / (x + k)) ∧
      (∀ x₁ x₂ : NNReal, x₁ < x₂ → (e x₂ : ℝ) < (e x₁ : ℝ)) } := by
  have hk' : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hden : ∀ x : NNReal, (0:ℝ) < (x : ℝ) + (k : ℝ) := fun x =>
    add_pos_of_nonneg_of_pos x.coe_nonneg hk'
  have hmem : ∀ x : NNReal, (k : ℝ) / ((x : ℝ) + (k : ℝ)) ∈ UnitInterval := fun x =>
    ⟨le_of_lt (div_pos hk' (hden x)),
     (div_le_one (hden x)).mpr (le_add_of_nonneg_left x.coe_nonneg)⟩
  have key : ∀ a : ℝ, (k : ℝ) / ((k : ℝ) / a) = a := fun a => by
    rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hk'.ne', mul_one]
  refine ⟨{ toFun := fun x => ⟨(k : ℝ) / ((x : ℝ) + (k : ℝ)), hmem x⟩
            invFun := fun y => Real.toNNReal ((k : ℝ) / (y : ℝ) - (k : ℝ))
            source := univ
            target := {y : UnitInterval | 0 < (y : ℝ)}
            map_source' := fun x _ => div_pos hk' (hden x)
            map_target' := fun y _ => mem_univ _
            left_inv' := ?_
            right_inv' := ?_
            open_source := isOpen_univ
            open_target := isOpen_Ioi.preimage continuous_subtype_val
            continuousOn_toFun := ((Continuous.div continuous_const
              (NNReal.continuous_coe.add continuous_const)
              (fun x => (hden x).ne')).subtype_mk hmem).continuousOn
            continuousOn_invFun := continuous_real_toNNReal.comp_continuousOn
              ((continuousOn_const.div continuous_subtype_val.continuousOn
                (fun y hy => ne_of_gt (hy : (0:ℝ) < (y : ℝ)))).sub continuousOn_const) },
    rfl, rfl, fun x => rfl, ?_⟩
  · -- left_inv'
    intro x _
    change Real.toNNReal ((k : ℝ) / ((k : ℝ) / ((x : ℝ) + (k : ℝ))) - (k : ℝ)) = x
    rw [key, show (x : ℝ) + (k : ℝ) - (k : ℝ) = (x : ℝ) from by ring]
    exact Real.toNNReal_coe
  · -- right_inv'
    intro y hy
    have hy' : (0:ℝ) < (y : ℝ) := hy
    have hy1 : (y : ℝ) ≤ 1 := y.2.2
    have hknn : (k : ℝ) ≤ (k : ℝ) / (y : ℝ) := by
      rw [le_div_iff₀ hy']
      exact mul_le_of_le_one_right hk'.le hy1
    apply Subtype.ext
    change (k : ℝ) / ((Real.toNNReal ((k : ℝ) / (y : ℝ) - (k : ℝ)) : ℝ) + (k : ℝ)) = (y : ℝ)
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hknn),
      show (k : ℝ) / (y : ℝ) - (k : ℝ) + (k : ℝ) = (k : ℝ) / (y : ℝ) from by ring,
      key]
  · -- strictly decreasing
    intro x₁ x₂ h
    have h' : (x₁ : ℝ) < (x₂ : ℝ) := by exact_mod_cast h
    exact div_lt_div_of_pos_left hk' (hden x₁)
      (by linarith : (x₁ : ℝ) + (k : ℝ) < (x₂ : ℝ) + (k : ℝ))

/-- The frontier of the closed lower piece `{y ≤ c}` of the unit interval is the single
level `{y = c}`, provided `0 < c < 1`. -/
lemma frontier_UIIic {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    frontier {y : UnitInterval | (y : ℝ) ≤ c} = {y : UnitInterval | (y : ℝ) = c} := by
  have hclosed : IsClosed {y : UnitInterval | (y : ℝ) ≤ c} :=
    isClosed_Iic.preimage continuous_subtype_val
  have hint : interior {y : UnitInterval | (y : ℝ) ≤ c}
      = {y : UnitInterval | (y : ℝ) < c} := by
    refine Subset.antisymm ?_ (interior_maximal (fun y (hy : (y : ℝ) < c) => hy.le)
      (isOpen_Iio.preimage continuous_subtype_val))
    intro y hy
    change (y : ℝ) < c
    by_contra hlt
    have hymem : y ∈ {y : UnitInterval | (y : ℝ) ≤ c} := interior_subset hy
    have hyc : (y : ℝ) = c := le_antisymm hymem (not_lt.mp hlt)
    have hS : {y : UnitInterval | (y : ℝ) ≤ c} ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hy
    rw [nhds_subtype] at hS
    obtain ⟨V, hV, hVsub⟩ := Filter.mem_comap.mp hS
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
    set δ := min (ε/2) ((1 - c)/2) with hδdef
    have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ1 : c + δ ≤ 1 := by
      have h := min_le_right (ε/2) ((1 - c)/2)
      have : δ ≤ (1 - c)/2 := h
      linarith
    have hmem : c + δ ∈ UnitInterval := ⟨by linarith, hδ1⟩
    have hballmem : c + δ ∈ Metric.ball (y : ℝ) ε := by
      rw [Metric.mem_ball, hyc, Real.dist_eq,
        show c + δ - c = δ from by ring, abs_of_pos hδ0]
      exact hδε
    have hin : (⟨c + δ, hmem⟩ : UnitInterval) ∈ Subtype.val ⁻¹' V := hball hballmem
    have hle : c + δ ≤ c := hVsub hin
    linarith
  rw [hclosed.frontier_eq, hint]
  ext y
  simp only [mem_sdiff, mem_ofPred_eq, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- Reflection `y ↦ 1 - y` sends the upper end-segment `Ioo p 1 ⊆ ℝ≥0` to the lower
end-segment `Ioo 0 (1-p)`. -/
lemma reflect_image_Ioo_upper {p : NNReal} (_hp : p < 1) :
    (fun y : NNReal => 1 - y) '' Ioo p 1 = Ioo 0 (1 - p) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyp, hy1⟩, rfl⟩
    exact ⟨tsub_pos_of_lt hy1, tsub_lt_tsub_left_of_le hy1.le hyp⟩
  · rintro ⟨hz0, hzp⟩
    have hz1 : z ≤ 1 := (hzp.trans_le tsub_le_self).le
    exact ⟨1 - z, ⟨lt_tsub_comm.mp hzp, tsub_lt_self one_pos hz0⟩,
      tsub_tsub_cancel_of_le hz1⟩

/-- Reflection `y ↦ 1 - y` sends the lower end-segment `Ioo 0 q ⊆ ℝ≥0` (for `q ≤ 1`) to
the upper end-segment `Ioo (1-q) 1`. -/
lemma reflect_image_Ioo_lower {q : NNReal} (_hq0 : 0 < q) (hq1 : q ≤ 1) :
    (fun y : NNReal => 1 - y) '' Ioo 0 q = Ioo (1 - q) 1 := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy0, hyq⟩, rfl⟩
    exact ⟨tsub_lt_tsub_left_of_le hq1 hyq, tsub_lt_self one_pos hy0⟩
  · rintro ⟨hzq, hz1⟩
    refine ⟨1 - z, ⟨tsub_pos_of_lt hz1, ?_⟩, tsub_tsub_cancel_of_le hz1.le⟩
    rw [tsub_lt_iff_right hz1.le]
    exact (tsub_lt_iff_left hq1).mp hzq
