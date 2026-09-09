/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatPrimitiveFactor
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricFlatFactor
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedClasses
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.GCongr

@[expose] public section

/-!
# Uniform flat-weight estimates for radial primitives

The initial coordinate is additive distance from the left endpoint of a fixed
interval `(0,L)`. The constants in the estimates are independent of the point
approaching either endpoint and of any auxiliary shifts in the source.
-/

noncomputable section

namespace NavierStokes.WeightedRadialPrimitive

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open FlatCutoff

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))

def delta (L x : ℝ) : ℝ := min 1 (min x (L - x))
def zeta (cL cR L x : ℝ) : ℝ := edge cL x * edge cR (L - x)
def weight (cL cR L : ℝ) (m : ℕ) (x : ℝ) : ℝ := zeta cL cR L x / delta L x ^ m
def singleWeight (c : ℝ) (m : ℕ) (x : ℝ) : ℝ := edge c x / x ^ m

theorem delta_pos {L x : ℝ} (hx : x ∈ Ioo 0 L) : 0 < delta L x := by
  exact lt_min zero_lt_one (lt_min hx.1 (sub_pos.mpr hx.2))

theorem delta_le_one (L x : ℝ) : delta L x ≤ 1 := min_le_left _ _
theorem delta_le_left (L x : ℝ) : delta L x ≤ x :=
  (min_le_right _ _).trans (min_le_left _ _)
theorem delta_le_right (L x : ℝ) : delta L x ≤ L - x :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem zeta_pos (cL cR : ℝ) {L x : ℝ} (hx : x ∈ Ioo 0 L) : 0 < zeta cL cR L x :=
  mul_pos (edge_pos cL hx.1) (edge_pos cR (sub_pos.mpr hx.2))

theorem zeta_continuous {cL cR : ℝ} (hL : 0 < cL) (hR : 0 < cR) (L : ℝ) :
    Continuous (zeta cL cR L) :=
  (edge_contDiff hL : ContDiff ℝ ∞ _).continuous.mul
    ((edge_contDiff hR : ContDiff ℝ ∞ _).continuous.comp (continuous_const.sub continuous_id))

theorem weight_pos (cL cR : ℝ) (m : ℕ) {L x : ℝ} (hx : x ∈ Ioo 0 L) :
    0 < weight cL cR L m x := div_pos (zeta_pos cL cR hx) (pow_pos (delta_pos hx) m)

theorem zeta_le_weight (cL cR : ℝ) (m : ℕ) {L x : ℝ} (hx : x ∈ Ioo 0 L) :
    zeta cL cR L x ≤ weight cL cR L m x := by
  apply (le_div_iff₀ (pow_pos (delta_pos hx) m)).mpr
  exact mul_le_of_le_one_right (zeta_pos cL cR hx).le
    (pow_le_one₀ (delta_pos hx).le (delta_le_one L x))

/-- Single-edge monotonicity is proved from the exponential formula. -/
theorem edge_mono {c : ℝ} (hc : 0 ≤ c) : Monotone (edge c) := by
  intro x y hxy
  by_cases hx : x ≤ 0
  · rw [edge_of_nonpos c hx]
    exact edge_nonneg c y
  · have hx0 : 0 < x := lt_of_not_ge hx
    have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
    rw [edge_of_pos c hx0, edge_of_pos c hy0]
    apply Real.exp_le_exp.mpr
    have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
    have hd := div_le_div_of_nonneg_left hc (sq_pos_of_pos hx0) hsq
    simpa only [neg_div] using neg_le_neg hd

theorem edge_le_one {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : edge c x ≤ 1 := by
  by_cases hx : x ≤ 0
  · rw [edge_of_nonpos c hx]
    exact zero_le_one
  · rw [edge_of_pos c (lt_of_not_ge hx)]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg x))

theorem singleWeight_nonneg (c : ℝ) (m : ℕ) (x : ℝ) : 0 ≤ singleWeight c m x := by
  by_cases hx : x ≤ 0
  · simp [singleWeight, edge_of_nonpos c hx]
  · exact div_nonneg (edge_nonneg c x) (pow_nonneg (le_of_not_ge hx) m)

theorem singleWeight_continuous {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Continuous (singleWeight c m) := (edge_div_pow_contDiff hc m : ContDiff ℝ ∞ _).continuous

/-- Compactness of the actual transformed improper integral gives one constant
for the primitive, uniformly down to the flat endpoint. -/
theorem single_primitive_uniform {c : ℝ} (hc : 0 < c) (m : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ R →
      intervalIntegral (singleWeight c m) 0 x volume ≤ C * singleWeight c m x := by
  have hF : Continuous (FlatPrimitiveFactor.factor c m (fun _ => 1)) :=
    (FlatPrimitiveFactor.factor_contDiff hc m contDiff_const).continuous
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hF.continuousOn : ContinuousOn _ (Icc (0 : ℝ) R))
  let C := max C₀ 0
  refine ⟨C * R ^ 3, mul_nonneg (le_max_right _ _) (pow_nonneg hR.le _), ?_⟩
  intro x hx hxR
  have hfac : FlatPrimitiveFactor.factor c m (fun _ => 1) x ≤ C :=
    (le_abs_self _).trans ((hC₀ x ⟨hx.le, hxR⟩).trans (le_max_left _ _))
  have hid : intervalIntegral (singleWeight c m) 0 x volume =
      (singleWeight c m x * x ^ 3) * FlatPrimitiveFactor.factor c m (fun _ => 1) x := by
    unfold singleWeight
    simpa only [FlatPrimitive.primitive, FlatPrimitive.integrand, FlatPrimitive.scale,
      singleWeight, mul_one] using
      FlatPrimitiveFactor.primitive_eq_scale_mul_factor c m (fun _ => 1) hx
  rw [hid]
  calc
    _ ≤ (singleWeight c m x * x ^ 3) * C :=
      mul_le_mul_of_nonneg_left hfac
        (mul_nonneg (singleWeight_nonneg c m x) (pow_nonneg hx.le _))
    _ ≤ (singleWeight c m x * R ^ 3) * C := by
      apply mul_le_mul_of_nonneg_right _ (show 0 ≤ C from le_max_right _ _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxR 3) (singleWeight_nonneg c m x)
    _ = (C * R ^ 3) * singleWeight c m x := by ring

theorem delta_left_half {L x : ℝ} (hx : x ≤ L / 2) : delta L x = min 1 x := by
  unfold delta
  rw [min_eq_left (by linarith : x ≤ L - x)]

/-- The two-edge weight on the left half is controlled by two integrable
single-edge weights. This includes all powers of the clipped edge distance. -/
theorem weight_le_left_majorant {cL cR L x : ℝ} (hcR : 0 ≤ cR)
    (m : ℕ) (hx : 0 < x) (hxL : x ≤ L / 2) :
    weight cL cR L m x ≤ singleWeight cL 0 x + singleWeight cL m x := by
  have he : edge cL x * edge cR (L - x) ≤ edge cL x :=
    mul_le_of_le_one_right (edge_nonneg cL x) (edge_le_one hcR _)
  unfold weight zeta
  rw [delta_left_half hxL]
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    exact (div_le_div_of_nonneg_right he (pow_nonneg hx.le m)).trans
      (le_add_of_nonneg_left (singleWeight_nonneg cL 0 x))
  · rw [min_eq_left (le_of_not_ge hx1), one_pow, div_one]
    have h0 : singleWeight cL 0 x = edge cL x := by simp [singleWeight]
    apply he.trans
    rw [h0]
    exact le_add_of_nonneg_right (singleWeight_nonneg cL m x)

theorem weight_reflect (cL cR L : ℝ) (m : ℕ) (x : ℝ) :
    weight cL cR L m (L - x) = weight cR cL L m x := by
  simp only [weight, zeta, delta, sub_sub_cancel, mul_comm, min_comm (L - x) x]

/-- Dividing by the opposite-edge value at the midpoint is a fixed constant,
independent of the variable tending to the left endpoint. -/
theorem left_single_le_weight {cL cR L x : ℝ} (hcR : 0 ≤ cR)
    (m : ℕ) (hx : 0 < x) (hxL : x ≤ L / 2) :
    singleWeight cL m x ≤ (edge cR (L / 2))⁻¹ * weight cL cR L m x := by
  have hL : 0 < L := by linarith
  have hxi : x ∈ Ioo 0 L := ⟨hx, by linarith⟩
  have hδ : 0 < delta L x := delta_pos hxi
  have he : edge cR (L / 2) ≤ edge cR (L - x) := edge_mono hcR (by linarith)
  have hem : 0 < edge cR (L / 2) := edge_pos cR (half_pos hL)
  have hp : singleWeight cL m x ≤ edge cL x / delta L x ^ m :=
    div_le_div_of_nonneg_left (edge_nonneg cL x) (pow_pos hδ m)
      (pow_le_pow_left₀ hδ.le (delta_le_left L x) m)
  have hr : 1 ≤ edge cR (L - x) / edge cR (L / 2) :=
    (le_div_iff₀ hem).mpr (by simpa using he)
  refine hp.trans ?_
  calc
    edge cL x / delta L x ^ m ≤
        (edge cL x / delta L x ^ m) * (edge cR (L - x) / edge cR (L / 2)) :=
      le_mul_of_one_le_right (div_nonneg (edge_nonneg cL x) (pow_nonneg hδ.le m)) hr
    _ = (edge cR (L / 2))⁻¹ * weight cL cR L m x := by
      unfold weight zeta
      ring

theorem left_base_le_weight {cL cR L x : ℝ} (hcR : 0 ≤ cR)
    (m : ℕ) (hx : 0 < x) (hxL : x ≤ L / 2) :
    singleWeight cL 0 x ≤ (edge cR (L / 2))⁻¹ * weight cL cR L m x := by
  have hxi : x ∈ Ioo 0 L := ⟨hx, by linarith⟩
  have h0 := left_single_le_weight (cL := cL) hcR 0 hx hxL
  have hw : weight cL cR L 0 x ≤ weight cL cR L m x := by
    simpa only [weight, pow_zero, div_one] using zeta_le_weight cL cR m hxi
  exact h0.trans (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr (edge_nonneg _ _)))

def wholeMajorant (cL cR L : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  singleWeight cL 0 x + singleWeight cL m x +
    (singleWeight cR 0 (L - x) + singleWeight cR m (L - x))

theorem weight_le_wholeMajorant {cL cR L x : ℝ} (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (m : ℕ) (hx : x ∈ Ioo 0 L) :
    weight cL cR L m x ≤ wholeMajorant cL cR L m x := by
  by_cases hh : x ≤ L / 2
  · exact (weight_le_left_majorant hcR m hx.1 hh).trans
      (le_add_of_nonneg_right (add_nonneg (singleWeight_nonneg cR 0 _)
        (singleWeight_nonneg cR m _)))
  · have hr := weight_le_left_majorant (cL := cR) hcL m (sub_pos.mpr hx.2)
      (show L - x ≤ L / 2 by linarith)
    rw [weight_reflect] at hr
    exact hr.trans (le_add_of_nonneg_left
      (add_nonneg (singleWeight_nonneg cL 0 _) (singleWeight_nonneg cL m _)))

theorem wholeMajorant_continuous {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (L : ℝ) (m : ℕ) : Continuous (wholeMajorant cL cR L m) :=
  ((singleWeight_continuous hcL 0).add (singleWeight_continuous hcL m)).add
    (((singleWeight_continuous hcR 0).add (singleWeight_continuous hcR m)).comp
      (continuous_const.sub continuous_id))

/-- A single global bound for the weighted envelope on the whole finite shell. -/
theorem weight_uniform_bound {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (L : ℝ) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ Ioo (0 : ℝ) L, weight cL cR L m x ≤ D := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((wholeMajorant_continuous hcL hcR L m).continuousOn :
      ContinuousOn _ (Icc (0 : ℝ) L))
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (weight_le_wholeMajorant hcL.le hcR.le m hx).trans
    ((le_abs_self _).trans ((hD x ⟨hx.1.le, hx.2.le⟩).trans (le_max_left _ _)))

theorem middle_weight_lower_bound {cL cR L ρ : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℕ, ∀ x ∈ Icc ρ (L - ρ), d ≤ weight cL cR L m x := by
  obtain ⟨d, hd, hb⟩ := UniformCone.positive_uniform_margin isCompact_Icc
    (zeta_continuous hcL hcR L).continuousOn
    (fun x (hx : x ∈ Icc ρ (L - ρ)) => zeta_pos cL cR
      (show x ∈ Ioo 0 L from ⟨lt_of_lt_of_le hρ hx.1, by linarith [hx.2]⟩))
  refine ⟨d, hd, ?_⟩
  intro m x hx
  exact (hb x hx).trans (zeta_le_weight cL cR m
    ⟨lt_of_lt_of_le hρ hx.1, by linarith [hx.2]⟩)

section Integrals

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The left inverse estimate is uniform at the endpoint, with no loss of
the polynomial edge exponent. It applies to arbitrary Banach-valued sources. -/
theorem left_primitive_uniform
    {cL cR L : ℝ} (hcL : 0 < cL) (hcR : 0 < cR) (hL : 0 < L) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → V) (A : ℝ), 0 ≤ A →
      (∀ s ∈ Ioo (0 : ℝ) L, ‖f s‖ ≤ A * weight cL cR L m s) →
      ∀ x : ℝ, 0 < x → x ≤ L / 2 →
        ‖intervalIntegral f 0 x volume‖ ≤ K * A * weight cL cR L m x := by
  obtain ⟨K₀, hK₀, hb₀⟩ := single_primitive_uniform hcL 0 (half_pos hL)
  obtain ⟨Kₘ, hKₘ, hbₘ⟩ := single_primitive_uniform hcL m (half_pos hL)
  let R := (edge cR (L / 2))⁻¹
  have hR : 0 ≤ R := inv_nonneg.mpr (edge_nonneg _ _)
  refine ⟨(K₀ + Kₘ) * R, mul_nonneg (add_nonneg hK₀ hKₘ) hR, ?_⟩
  intro f A hA hf x hx hxL
  let g : ℝ → ℝ := fun s => A * (singleWeight cL 0 s + singleWeight cL m s)
  have hgc : Continuous g :=
    continuous_const.mul ((singleWeight_continuous hcL 0).add (singleWeight_continuous hcL m))
  have hgn : ∀ s, 0 ≤ g s := fun s => mul_nonneg hA
    (add_nonneg (singleWeight_nonneg cL 0 s) (singleWeight_nonneg cL m s))
  have hbound : ∀ᵐ s ∂volume.restrict (uIoc 0 x), ‖f s‖ ≤ g s := by
    rw [uIoc_of_le hx.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsL : s < L := by linarith [hs.2]
    exact (hf s ⟨hs.1, hsL⟩).trans (mul_le_mul_of_nonneg_left
      (weight_le_left_majorant hcR.le m hs.1 (hs.2.trans hxL)) hA)
  have hi := intervalIntegral.norm_integral_le_abs_of_norm_le hbound (hgc.intervalIntegrable 0 x)
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hx.le hgn)] at hi
  calc
    ‖intervalIntegral f 0 x volume‖ ≤ intervalIntegral g 0 x volume := hi
    _ = A * (intervalIntegral (singleWeight cL 0) 0 x volume +
        intervalIntegral (singleWeight cL m) 0 x volume) := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((singleWeight_continuous hcL 0).intervalIntegrable 0 x)
          ((singleWeight_continuous hcL m).intervalIntegrable 0 x)]
    _ ≤ A * (K₀ * singleWeight cL 0 x + Kₘ * singleWeight cL m x) :=
      mul_le_mul_of_nonneg_left (add_le_add (hb₀ x hx hxL) (hbₘ x hx hxL)) hA
    _ ≤ A * (K₀ * (R * weight cL cR L m x) + Kₘ * (R * weight cL cR L m x)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (left_base_le_weight hcR.le m hx hxL) hK₀)
          (mul_le_mul_of_nonneg_left (left_single_le_weight hcR.le m hx hxL) hKₘ)) hA
    _ = (K₀ + Kₘ) * R * A * weight cL cR L m x := by ring

/-- Reflection gives the corresponding endpoint-uniform right inverse bound. -/
theorem right_primitive_uniform
    {cL cR L : ℝ} (hcL : 0 < cL) (hcR : 0 < cR) (hL : 0 < L) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → V) (A : ℝ), 0 ≤ A →
      (∀ s ∈ Ioo (0 : ℝ) L, ‖f s‖ ≤ A * weight cL cR L m s) →
      ∀ x : ℝ, L / 2 ≤ x → x < L →
        ‖intervalIntegral f x L volume‖ ≤ K * A * weight cL cR L m x := by
  obtain ⟨K, hK, hb⟩ := left_primitive_uniform (V := V) hcR hcL hL m
  refine ⟨K, hK, ?_⟩
  intro f A hA hf x hxL hx
  have hg : ∀ s ∈ Ioo (0 : ℝ) L,
      ‖f (L - s)‖ ≤ A * weight cR cL L m s := by
    intro s hs
    have h := hf (L - s) ⟨sub_pos.mpr hs.2, by linarith [hs.1]⟩
    simpa only [weight_reflect] using h
  have h := hb (fun s => f (L - s)) A hA hg (L - x) (sub_pos.mpr hx) (by linarith)
  simpa only [intervalIntegral.integral_comp_sub_left, sub_sub_cancel, sub_zero,
    weight_reflect] using h

/-- Uniform total and partial mass bounds on the finite shell. Endpoint values
of the source are immaterial to this Lebesgue-integral statement. -/
theorem interval_primitive_uniform
    {cL cR L : ℝ} (hcL : 0 < cL) (hcR : 0 < cR) (hL : 0 < L) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : ℝ → V) (A : ℝ), 0 ≤ A →
      (∀ s ∈ Ioo (0 : ℝ) L, ‖f s‖ ≤ A * weight cL cR L m s) →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ L →
        ‖intervalIntegral f a b volume‖ ≤ D * A := by
  obtain ⟨D, hD, hb⟩ := weight_uniform_bound hcL hcR L m
  refine ⟨D * L, mul_nonneg hD hL.le, ?_⟩
  intro f A hA hf a b ha hab hbL
  have hbound : ∀ s ∈ Ioo a b, ‖f s‖ ≤ A * D := by
    intro s hs
    have hsi : s ∈ Ioo 0 L := ⟨lt_of_le_of_lt ha hs.1, lt_of_lt_of_le hs.2 hbL⟩
    exact (hf s hsi).trans (mul_le_mul_of_nonneg_left (hb s hsi) hA)
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  have hi := norm_setIntegral_le_of_norm_le_const
    (by simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top] : volume (Ioo a b) < ⊤) hbound
  rw [Real.volume_real_Ioo_of_le hab] at hi
  calc
    _ ≤ (A * D) * (b - a) := hi
    _ ≤ (A * D) * L := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hD)
    _ = (D * L) * A := by ring

def compactPrimitive (χ : ℝ → ℝ) (f : ℝ → V) (L x : ℝ) : V :=
  intervalIntegral f 0 x volume - χ x • intervalIntegral f 0 L volume

/-- The actual compactified primitive preserves the same two-edge weighted
envelope. The cutoff is only required to have two plateaus and remain bounded;
no monotonicity of the weight or inverse estimate is assumed. -/
theorem compact_primitive_uniform
    {cL cR L ρ : ℝ} (hcL : 0 < cL) (hcR : 0 < cR) (hL : 0 < L)
    (hρ : 0 < ρ) (hρL : ρ ≤ L / 2) (m : ℕ) (χ : ℝ → ℝ)
    (hχ : ∀ x, |χ x| ≤ 1)
    (hleft : ∀ x, x ≤ ρ → χ x = 0)
    (hright : ∀ x, L - ρ ≤ x → χ x = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → V), Continuous f → ∀ A : ℝ, 0 ≤ A →
      (∀ s ∈ Ioo (0 : ℝ) L, ‖f s‖ ≤ A * weight cL cR L m s) →
      ∀ x ∈ Ioo (0 : ℝ) L,
        ‖compactPrimitive χ f L x‖ ≤ K * A * weight cL cR L m x := by
  obtain ⟨KL, hKL, hbL⟩ := left_primitive_uniform (V := V) hcL hcR hL m
  obtain ⟨KR, hKR, hbR⟩ := right_primitive_uniform (V := V) hcL hcR hL m
  obtain ⟨D, hD, hbD⟩ := interval_primitive_uniform (V := V) hcL hcR hL m
  obtain ⟨d, hd, hbd⟩ := middle_weight_lower_bound (L := L) hcL hcR hρ
  let KM : ℝ := 2 * D / d
  have hKM : 0 ≤ KM := div_nonneg (by positivity) hd.le
  let K : ℝ := KL + KR + KM
  have hKKL : KL ≤ K := by dsimp [K]; linarith
  have hKKR : KR ≤ K := by dsimp [K]; linarith
  have hKKM : KM ≤ K := by dsimp [K]; linarith
  refine ⟨K, le_trans hKL hKKL, ?_⟩
  intro f hfc A hA hf x hx
  have hw := (weight_pos cL cR m hx).le
  by_cases hl : x ≤ ρ
  · simp only [compactPrimitive, hleft x hl, zero_smul, sub_zero]
    exact (hbL f A hA hf x hx.1 (hl.trans hρL)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKKL hA) hw)
  · by_cases hr : L - ρ ≤ x
    · have heq : compactPrimitive χ f L x = -intervalIntegral f x L volume := by
        simp only [compactPrimitive, hright x hr, one_smul]
        rw [intervalIntegral.integral_interval_sub_left (hfc.intervalIntegrable 0 x)
          (hfc.intervalIntegrable 0 L), intervalIntegral.integral_symm]
      rw [heq, norm_neg]
      exact (hbR f A hA hf x (by linarith) hx.2).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKKR hA) hw)
    · have hxd : d ≤ weight cL cR L m x := hbd m x ⟨le_of_not_ge hl, le_of_not_ge hr⟩
      have hp := hbD f A hA hf 0 x le_rfl hx.1.le hx.2.le
      have ht := hbD f A hA hf 0 L le_rfl hL.le le_rfl
      have hn : ‖compactPrimitive χ f L x‖ ≤ 2 * D * A := by
        calc
          _ ≤ ‖intervalIntegral f 0 x volume‖ + ‖χ x • intervalIntegral f 0 L volume‖ :=
            norm_sub_le _ _
          _ ≤ D * A + 1 * (D * A) := by
            rw [norm_smul, Real.norm_eq_abs]
            exact add_le_add hp (mul_le_mul (hχ x) ht (norm_nonneg _) zero_le_one)
          _ = 2 * D * A := by ring
      have hm : 2 * D * A ≤ KM * A * weight cL cR L m x := by
        calc
          _ = KM * A * d := by dsimp [KM]; field_simp
          _ ≤ KM * A * weight cL cR L m x := mul_le_mul_of_nonneg_left hxd (mul_nonneg hKM hA)
      exact (hn.trans hm).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKKM hA) hw)

end Integrals

/-! ### Pullback to logarithmic edge distances on a fixed positive annulus -/

def logLength (a b : ℝ) : ℝ := Real.log (b / a)
def logPosition (a X : ℝ) : ℝ := Real.log (X / a)
def logWeight (cL cR a b : ℝ) (m : ℕ) (X : ℝ) : ℝ :=
  weight cL cR (logLength a b) m (logPosition a X)

theorem logLength_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) : 0 < logLength a b :=
  Real.log_pos ((one_lt_div ha).mpr hab)

theorem logPosition_mem {a b X : ℝ} (ha : 0 < a) (hX : X ∈ Ioo a b) :
    logPosition a X ∈ Ioo 0 (logLength a b) := by
  exact ⟨Real.log_pos ((one_lt_div ha).mpr hX.1),
    Real.log_lt_log (div_pos (lt_trans ha hX.1) ha) (div_lt_div_of_pos_right hX.2 ha)⟩

theorem log_remaining {a b X : ℝ} (ha : 0 < a) (hX : X ∈ Ioo a b) :
    logLength a b - logPosition a X = Real.log (b / X) := by
  have hx := lt_trans ha hX.1
  have hb := lt_trans hx hX.2
  simp only [logLength, logPosition, Real.log_div hb.ne' ha.ne', Real.log_div hx.ne' ha.ne',
    Real.log_div hb.ne' hx.ne']
  ring

/-- The weight is exactly the manuscript's two logarithmic-edge exponential,
with its clipped inverse-edge power. -/
theorem logWeight_formula {a b X : ℝ} (ha : 0 < a) (hX : X ∈ Ioo a b)
    (cL cR : ℝ) (m : ℕ) :
    logWeight cL cR a b m X =
      Real.exp (-cL / (Real.log (X / a)) ^ 2 - cR / (Real.log (b / X)) ^ 2) /
        (min 1 (min (Real.log (X / a)) (Real.log (b / X)))) ^ m := by
  have hp := logPosition_mem ha hX
  rw [logWeight, weight, zeta, delta, edge_of_pos cL hp.1,
    edge_of_pos cR (sub_pos.mpr hp.2), log_remaining ha hX]
  rw [← Real.exp_add]
  simp only [logPosition, neg_div, sub_eq_add_neg]

def expCoordinate (a s : ℝ) : ℝ := a * Real.exp s

theorem expCoordinate_logPosition {a X : ℝ} (ha : 0 < a) (hX : 0 < X) :
    expCoordinate a (logPosition a X) = X := by
  unfold expCoordinate logPosition
  rw [Real.exp_log (div_pos hX ha)]
  field_simp

theorem logPosition_expCoordinate {a : ℝ} (ha : 0 < a) (s : ℝ) :
    logPosition a (expCoordinate a s) = s := by
  unfold logPosition expCoordinate
  have h : a * Real.exp s / a = Real.exp s := by field_simp
  rw [h, Real.log_exp]

theorem expCoordinate_mem {a b s : ℝ} (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Ioo 0 (logLength a b)) : expCoordinate a s ∈ Ioo a b := by
  have hb := lt_trans ha hab
  have hlo : 1 < Real.exp s := Real.one_lt_exp_iff.mpr hs.1
  have hhi : Real.exp s < b / a := by
    have h := Real.exp_lt_exp.mpr hs.2
    simpa only [logLength, Real.exp_log (div_pos hb ha)] using h
  constructor
  · unfold expCoordinate
    nlinarith
  · unfold expCoordinate
    have h := (lt_div_iff₀ ha).mp hhi
    simpa only [mul_comm] using h

section LogIntegrals

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def expPullback (a : ℝ) (f : ℝ → V) (s : ℝ) : V :=
  expCoordinate a s • f (expCoordinate a s)

/-- Actual change of variables, including the radial integration Jacobian. -/
theorem expPullback_integral (a : ℝ) (f : ℝ → V) (hf : Continuous f) (l r : ℝ) :
    intervalIntegral (expPullback a f) l r volume =
      intervalIntegral f (expCoordinate a l) (expCoordinate a r) volume := by
  have hd : ∀ s ∈ uIcc l r, HasDerivAt (expCoordinate a) (expCoordinate a s) s :=
    fun s _ => (Real.hasDerivAt_exp s).const_mul a
  exact intervalIntegral.integral_deriv_smul_comp hd
    (continuous_const.mul Real.continuous_exp).continuousOn hf

theorem expPullback_bound {a b cL cR A : ℝ} (ha : 0 < a) (hab : a < b)
    (m : ℕ) (f : ℝ → V) (_hA : 0 ≤ A)
    (hf : ∀ X ∈ Ioo a b, ‖f X‖ ≤ A * logWeight cL cR a b m X) :
    ∀ s ∈ Ioo 0 (logLength a b),
      ‖expPullback a f s‖ ≤ (b * A) * weight cL cR (logLength a b) m s := by
  intro s hs
  have hX := expCoordinate_mem ha hab hs
  have hXpos := lt_trans ha hX.1
  have hbpos := lt_trans ha hab
  unfold expPullback
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hXpos]
  have h := mul_le_mul hX.2.le (hf _ hX) (norm_nonneg _) hbpos.le
  simpa only [logWeight, logPosition_expCoordinate ha s, mul_assoc] using h

/-- Left logarithmic-edge estimate in the original positive radial variable.
The extra constant is only the fixed upper radial endpoint b. -/
theorem log_left_primitive_uniform
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → V), Continuous f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ‖f X‖ ≤ A * logWeight cL cR a b m X) →
      ∀ X ∈ Ioo a b, logPosition a X ≤ logLength a b / 2 →
        ‖intervalIntegral f a X volume‖ ≤ K * A * logWeight cL cR a b m X := by
  obtain ⟨K, hK, hbound⟩ := left_primitive_uniform (V := V) hcL hcR (logLength_pos ha hab) m
  refine ⟨K * b, mul_nonneg hK (lt_trans ha hab).le, ?_⟩
  intro f hfc A hA hf X hX hhalf
  have hx := logPosition_mem ha hX
  have h := hbound (expPullback a f) (b * A) (mul_nonneg (lt_trans ha hab).le hA)
    (expPullback_bound ha hab m f hA hf) (logPosition a X) hx.1 hhalf
  rw [expPullback_integral a f hfc,
    expCoordinate_logPosition ha (lt_trans ha hX.1)] at h
  simpa only [expCoordinate, Real.exp_zero, mul_one, logWeight, mul_assoc] using h

/-- Right logarithmic-edge estimate in the original positive radial variable. -/
theorem log_right_primitive_uniform
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → V), Continuous f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ‖f X‖ ≤ A * logWeight cL cR a b m X) →
      ∀ X ∈ Ioo a b, logLength a b / 2 ≤ logPosition a X →
        ‖intervalIntegral f X b volume‖ ≤ K * A * logWeight cL cR a b m X := by
  obtain ⟨K, hK, hbound⟩ := right_primitive_uniform (V := V) hcL hcR (logLength_pos ha hab) m
  refine ⟨K * b, mul_nonneg hK (lt_trans ha hab).le, ?_⟩
  intro f hfc A hA hf X hX hhalf
  have hx := logPosition_mem ha hX
  have h := hbound (expPullback a f) (b * A) (mul_nonneg (lt_trans ha hab).le hA)
    (expPullback_bound ha hab m f hA hf) (logPosition a X) hhalf hx.2
  have htop : expCoordinate a (logLength a b) = b := expCoordinate_logPosition ha (lt_trans ha hab)
  rw [expPullback_integral a f hfc, expCoordinate_logPosition ha (lt_trans ha hX.1), htop] at h
  simpa only [logWeight, mul_assoc] using h

/-- The entire weighted source has uniformly bounded mass on the positive
annulus. This also bounds every interior subinterval. -/
theorem log_interval_primitive_uniform
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : ℝ → V) (A : ℝ), 0 ≤ A →
      (∀ X ∈ Ioo a b, ‖f X‖ ≤ A * logWeight cL cR a b m X) →
      ∀ l r : ℝ, a ≤ l → l ≤ r → r ≤ b →
        ‖intervalIntegral f l r volume‖ ≤ D * A := by
  obtain ⟨D, hD, hbound⟩ := weight_uniform_bound hcL hcR (logLength a b) m
  refine ⟨D * (b - a), mul_nonneg hD (sub_pos.mpr hab).le, ?_⟩
  intro f A hA hf l r hal hlr hrb
  have hb : ∀ X ∈ Ioo l r, ‖f X‖ ≤ A * D := by
    intro X hX
    have hXi : X ∈ Ioo a b := ⟨hal.trans_lt hX.1, hX.2.trans_le hrb⟩
    exact (hf X hXi).trans
      (mul_le_mul_of_nonneg_left (hbound _ (logPosition_mem ha hXi)) hA)
  rw [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo]
  have hi := norm_setIntegral_le_of_norm_le_const
    (by simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top] : volume (Ioo l r) < ⊤) hb
  rw [Real.volume_real_Ioo_of_le hlr] at hi
  calc
    _ ≤ (A * D) * (r - l) := hi
    _ ≤ (A * D) * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hD)
    _ = (D * (b - a)) * A := by ring

def logCompactPrimitive (χ : ℝ → ℝ) (f : ℝ → V) (a b X : ℝ) : V :=
  intervalIntegral f a X volume - χ (logPosition a X) • intervalIntegral f a b volume

/-- The compactified primitive preserves the explicit logarithmic two-edge
weight uniformly on the whole positive annulus. -/
theorem log_compact_primitive_uniform
    {a b cL cR ρ : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (hρ : 0 < ρ) (hρL : ρ ≤ logLength a b / 2) (m : ℕ) (χ : ℝ → ℝ)
    (hχ : ∀ x, |χ x| ≤ 1)
    (hleft : ∀ x, x ≤ ρ → χ x = 0)
    (hright : ∀ x, logLength a b - ρ ≤ x → χ x = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → V), Continuous f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ‖f X‖ ≤ A * logWeight cL cR a b m X) →
      ∀ X ∈ Ioo a b,
        ‖logCompactPrimitive χ f a b X‖ ≤ K * A * logWeight cL cR a b m X := by
  obtain ⟨K, hK, hbound⟩ := compact_primitive_uniform (V := V) hcL hcR (logLength_pos ha hab)
    hρ hρL m χ hχ hleft hright
  refine ⟨K * b, mul_nonneg hK (lt_trans ha hab).le, ?_⟩
  intro f hfc A hA hf X hX
  have hgp : Continuous (expPullback a f) :=
    (continuous_const.mul Real.continuous_exp).smul
      (hfc.comp (continuous_const.mul Real.continuous_exp))
  have h := hbound (expPullback a f) hgp (b * A) (mul_nonneg (lt_trans ha hab).le hA)
    (expPullback_bound ha hab m f hA hf) (logPosition a X) (logPosition_mem ha hX)
  have htop : expCoordinate a (logLength a b) = b := expCoordinate_logPosition ha (lt_trans ha hab)
  unfold compactPrimitive at h
  rw [expPullback_integral a f hfc, expPullback_integral a f hfc,
    expCoordinate_logPosition ha (lt_trans ha hX.1), htop] at h
  simpa only [logCompactPrimitive, logWeight, expCoordinate, Real.exp_zero, mul_one,
    mul_assoc] using h

end LogIntegrals

/-! ### Physical cutoffs and auxiliary shifts -/

section PhysicalIntegrals

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def radialCompactPrimitive (χ : ℝ → ℝ) (f : ℝ → V) (a b X : ℝ) : V :=
  intervalIntegral f a X volume - χ X • intervalIntegral f a b volume

/-- Any fixed pair of interior physical plateau thresholds gives positive
logarithmic collars. This derives the collars from the endpoints. -/
theorem exists_log_plateau_width
    {a b c d : ℝ} (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (χ : ℝ → ℝ) (hleft : ∀ X, X ≤ c → χ X = 0)
    (hright : ∀ X, d ≤ X → χ X = 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ logLength a b / 2 ∧
      (∀ s, s ≤ ρ → χ (expCoordinate a s) = 0) ∧
      (∀ s, logLength a b - ρ ≤ s → χ (expCoordinate a s) = 1) := by
  have hab : a < b := hac.trans (hcd.trans hdb)
  have hc := logPosition_mem ha (show c ∈ Ioo a b from ⟨hac, hcd.trans hdb⟩)
  have hd := logPosition_mem ha (show d ∈ Ioo a b from ⟨hac.trans hcd, hdb⟩)
  let ρ := min (logPosition a c) (min (logLength a b - logPosition a d) (logLength a b / 2))
  have hρ : 0 < ρ := lt_min hc.1 (lt_min (sub_pos.mpr hd.2) (half_pos (logLength_pos ha hab)))
  have hρc : ρ ≤ logPosition a c := min_le_left _ _
  have hρd : ρ ≤ logLength a b - logPosition a d :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hρL : ρ ≤ logLength a b / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, hρL, ?_, ?_⟩
  · intro s hs
    apply hleft
    calc
      expCoordinate a s ≤ expCoordinate a (logPosition a c) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hs.trans hρc)) ha.le
      _ = c := expCoordinate_logPosition ha (ha.trans hac)
  · intro s hs
    apply hright
    calc
      d = expCoordinate a (logPosition a d) := (expCoordinate_logPosition ha (ha.trans (hac.trans
        hcd))).symm
      _ ≤ expCoordinate a s :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) ha.le

/-- The cutoff can be specified directly in the physical radial coordinate.
No logarithmic cutoff regularity or assumed inverse bound is required. -/
theorem radial_compact_primitive_uniform
    {a b c d cL cR : ℝ} (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) (χ : ℝ → ℝ)
    (hχ : ∀ X, |χ X| ≤ 1)
    (hleft : ∀ X, X ≤ c → χ X = 0) (hright : ∀ X, d ≤ X → χ X = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → V), Continuous f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ‖f X‖ ≤ A * logWeight cL cR a b m X) →
      ∀ X ∈ Ioo a b,
        ‖radialCompactPrimitive χ f a b X‖ ≤ K * A * logWeight cL cR a b m X := by
  obtain ⟨ρ, hρ, hρL, hl, hr⟩ := exists_log_plateau_width ha hac hcd hdb χ hleft hright
  obtain ⟨K, hK, hbound⟩ := log_compact_primitive_uniform (V := V) ha (hac.trans (hcd.trans hdb))
    hcL hcR hρ hρL m (fun s => χ (expCoordinate a s)) (fun s => hχ _) hl hr
  refine ⟨K, hK, ?_⟩
  intro f hfc A hA hf X hX
  have h := hbound f hfc A hA hf X hX
  simpa only [logCompactPrimitive, radialCompactPrimitive,
    expCoordinate_logPosition ha (ha.trans hX.1)] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A source slice along the actual affine shifted radial characteristic. -/
def radialSlice (M : ℝ) (v : E) (f : ℝ × E → V) (z : ℝ × E) (s : ℝ) : V :=
  f (s, z.2 + (M * (s - z.1)) • v)

omit [NormedSpace ℝ V] in
theorem radialSlice_continuous {f : ℝ × E → V} (hf : Continuous f)
    (M : ℝ) (v : E) (z : ℝ × E) : Continuous (radialSlice M v f z) := by
  exact hf.comp (continuous_id.prodMk
    (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).smul
      continuous_const)))

/-- Auxiliary translation does not change a radial bound that is uniform in
the auxiliary variable. Constants are independent of M, v, and the base point. -/
theorem shifted_radial_compact_primitive_uniform
    {a b c d cL cR : ℝ} (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) (χ : ℝ → ℝ)
    (hχ : ∀ X, |χ X| ≤ 1)
    (hleft : ∀ X, X ≤ c → χ X = 0) (hright : ∀ X, d ≤ X → χ X = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (f : ℝ × E → V), Continuous f →
      ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ∀ Y : E, ‖f (X, Y)‖ ≤ A * logWeight cL cR a b m X) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b →
        ‖radialCompactPrimitive χ (radialSlice M v f z) a b z.1‖ ≤
          K * A * logWeight cL cR a b m z.1 := by
  obtain ⟨K, hK, hbound⟩ := radial_compact_primitive_uniform (V := V)
    ha hac hcd hdb hcL hcR m χ hχ hleft hright
  refine ⟨K, hK, ?_⟩
  intro M v f hfc A hA hf z hz
  exact hbound (radialSlice M v f z) (radialSlice_continuous hfc M v z) A hA
    (fun X hX => hf X hX _) z.1 hz

end PhysicalIntegrals

/-! ### The actual transport operator -/

section Transport

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compactIntegral_eq_radialCompactPrimitive
    {a b M : ℝ} {v : E} {f : ℝ × E → V} (χ : ℝ → ℝ)
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    TransportPrimitive.compactIntegral χ M v f z =
      radialCompactPrimitive χ (radialSlice M v f z) a b z.1 := by
  rw [TransportPrimitive.compactIntegral,
    TransportPrimitive.pastIntegral_eq_radialInterval hf hs,
    TransportPrimitive.totalIntegral_eq_radialInterval hf hs]
  rfl

/-- A uniform weighted inverse bound for the manuscript's actual shifted,
compactified transport primitive. All shifts are quantified after the constant. -/
theorem transport_compact_primitive_uniform
    {a b c d cL cR : ℝ} (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) (χ : ℝ → ℝ)
    (hχ : ∀ X, |χ X| ≤ 1)
    (hleft : ∀ X, X ≤ c → χ X = 0) (hright : ∀ X, d ≤ X → χ X = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (f : ℝ × E → V), Continuous f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ∀ Y : E, ‖f (X, Y)‖ ≤ A * logWeight cL cR a b m X) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b →
        ‖TransportPrimitive.compactIntegral χ M v f z‖ ≤
          K * A * logWeight cL cR a b m z.1 := by
  obtain ⟨K, hK, hbound⟩ := shifted_radial_compact_primitive_uniform (E := E) (V := V)
    ha hac hcd hdb hcL hcR m χ hχ hleft hright
  refine ⟨K, hK, ?_⟩
  intro M v f hf hs A hA hb z hz
  rw [compactIntegral_eq_radialCompactPrimitive χ hf hs]
  exact hbound M v f hf A hA hb z hz

/-- The cutoff itself is the explicit smooth transition constructed in
`TransportPrimitive`; there is no cutoff-existence hypothesis. -/
theorem canonical_transport_compact_uniform
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (f : ℝ × E → V), Continuous f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ∀ Y : E, ‖f (X, Y)‖ ≤ A * logWeight cL cR a b m X) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b →
        ‖TransportPrimitive.compactIntegral (TransportPrimitive.interiorCutoff a b) M v f z‖ ≤
          K * A * logWeight cL cR a b m z.1 := by
  apply transport_compact_primitive_uniform ha
    (c := (2 * a + b) / 3) (d := (a + 2 * b) / 3)
    (by linarith) (by linarith) (by linarith) hcL hcR m
  · intro X
    have h := TransportPrimitive.cutoff_mem_Icc ((2 * a + b) / 3) ((a + 2 * b) / 3) X
    exact (abs_of_nonneg h.1).le.trans h.2
  · exact fun X hX => TransportPrimitive.interiorCutoff_zero hab hX
  · exact fun X hX => TransportPrimitive.interiorCutoff_one hab hX

/-- The uncorrected past primitive obeys the left weighted estimate uniformly
in every auxiliary shift. -/
theorem transport_past_left_uniform
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (f : ℝ × E → V), Continuous f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ∀ Y : E, ‖f (X, Y)‖ ≤ A * logWeight cL cR a b m X) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b → logPosition a z.1 ≤ logLength a b / 2 →
        ‖TransportPrimitive.pastIntegral M v f z‖ ≤ K * A * logWeight cL cR a b m z.1 := by
  obtain ⟨K, hK, hb⟩ := log_left_primitive_uniform (V := V) ha hab hcL hcR m
  refine ⟨K, hK, ?_⟩
  intro M v f hf hs A hA hbound z hz hzhalf
  rw [TransportPrimitive.pastIntegral_eq_radialInterval hf hs]
  exact hb (radialSlice M v f z) (radialSlice_continuous hf M v z) A hA
    (fun X hX => hbound X hX _) z.1 hz hzhalf

/-- The future primitive obeys the right weighted estimate. -/
theorem transport_future_right_uniform
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (f : ℝ × E → V), Continuous f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ∀ Y : E, ‖f (X, Y)‖ ≤ A * logWeight cL cR a b m X) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b → logLength a b / 2 ≤ logPosition a z.1 →
        ‖TransportPrimitive.futureIntegral M v f z‖ ≤ K * A * logWeight cL cR a b m z.1 := by
  obtain ⟨K, hK, hb⟩ := log_right_primitive_uniform (V := V) ha hab hcL hcR m
  refine ⟨K, hK, ?_⟩
  intro M v f hf hs A hA hbound z hz hzhalf
  rw [TransportPrimitive.futureIntegral_eq_radialInterval hf hs]
  exact hb (radialSlice M v f z) (radialSlice_continuous hf M v z) A hA
    (fun X hX => hbound X hX _) z.1 hz hzhalf

/-- A common bound for past and total mass, uniform in every shift and in the
point in the annulus. It is used only on a compact interior collar. -/
theorem transport_mass_uniform
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (M : ℝ) (v : E) (f : ℝ × E → V), Continuous f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      (∀ X ∈ Ioo a b, ∀ Y : E, ‖f (X, Y)‖ ≤ A * logWeight cL cR a b m X) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b →
        ‖TransportPrimitive.pastIntegral M v f z‖ ≤ D * A ∧
        ‖TransportPrimitive.totalIntegral M v f z‖ ≤ D * A := by
  obtain ⟨D, hD, hb⟩ := log_interval_primitive_uniform (V := V) ha hab hcL hcR m
  refine ⟨D, hD, ?_⟩
  intro M v f hf hs A hA hbound z hz
  have hsource : ∀ X ∈ Ioo a b,
      ‖radialSlice M v f z X‖ ≤ A * logWeight cL cR a b m X := fun X hX => hbound X hX _
  rw [TransportPrimitive.pastIntegral_eq_radialInterval hf hs,
    TransportPrimitive.totalIntegral_eq_radialInterval hf hs]
  exact ⟨hb _ A hA hsource a z.1 le_rfl hz.1.le hz.2.le,
    hb _ A hA hsource a b le_rfl hab.le le_rfl⟩

/-- A smooth scalar radial cutoff has bounded actual Fréchet jets on the
entire strip, including its unbounded auxiliary directions. -/
theorem cutoff_finiteJet_bound (a b : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, j ≤ m → ∀ z : ℝ × E, z.1 ∈ Icc a b →
      ‖iteratedFDeriv ℝ j (fun y : ℝ × E => χ y.1) z‖ ≤ B := by
  classical
  have hex : ∀ j : Fin (m + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc a b, ‖iteratedFDeriv ℝ (j : ℕ) χ x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hχ.continuous_iteratedFDeriv (m := (j : ℕ)) (nat_le_smooth j)).continuousOn :
        ContinuousOn (iteratedFDeriv ℝ (j : ℕ) χ) (Icc a b))
    exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  choose C hC hb using hex
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j hj z hz
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hCj : C j' ≤ ∑ k, C k := Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ j')
  have hcomp := (ContinuousLinearMap.fst ℝ ℝ E).iteratedFDeriv_comp_right hχ z
    (i := j) (nat_le_smooth j)
  change iteratedFDeriv ℝ j (fun y : ℝ × E => χ y.1) z = _ at hcomp
  rw [hcomp]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j χ z.1‖ *
        ∏ _ : Fin j, ‖ContinuousLinearMap.fst ℝ ℝ E‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j χ z.1‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ =>
        ContinuousLinearMap.norm_fst_le _ _ _)
    _ = ‖iteratedFDeriv ℝ j χ z.1‖ := mul_one _
    _ ≤ C j' := hb j' z.1 hz
    _ ≤ ∑ k, C k := hCj

private theorem iteratedFDeriv_eq_of_eventuallyEq
    {f g : ℝ × E → V} {z : ℝ × E} (h : f =ᶠ[𝓝 z] g) (j : ℕ) :
    iteratedFDeriv ℝ j f z = iteratedFDeriv ℝ j g z := by
  have hw : f =ᶠ[𝓝[Set.univ] z] g := by simpa only [nhdsWithin_univ] using h
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq h.self_of_nhds j

/-- On an open left logarithmic collar, every actual derivative of the
compactified operator equals the corresponding derivative of the past integral. -/
theorem compact_jet_eq_past_on_left
    {a M ρ : ℝ} {v : E} {f : ℝ × E → V} {χ : ℝ → ℝ}
    (ha : 0 < a) (hleft : ∀ s, s ≤ ρ → χ (expCoordinate a s) = 0)
    (z : ℝ × E) (hz : 0 < z.1) (hzρ : logPosition a z.1 < ρ) (j : ℕ) :
    iteratedFDeriv ℝ j (TransportPrimitive.compactIntegral χ M v f) z =
      iteratedFDeriv ℝ j (TransportPrimitive.pastIntegral M v f) z := by
  apply iteratedFDeriv_eq_of_eventuallyEq (j := j)
  have hp : ∀ᶠ y : ℝ × E in 𝓝 z, 0 < y.1 :=
    continuous_fst.continuousAt.eventually (lt_mem_nhds hz)
  have hinner : ContinuousAt (fun y : ℝ × E => y.1 / a) z :=
    (continuous_fst.div_const a).continuousAt
  have hlog : ContinuousAt (fun y : ℝ × E => logPosition a y.1) z :=
    hinner.log (div_ne_zero hz.ne' ha.ne')
  have hl : ∀ᶠ y : ℝ × E in 𝓝 z, logPosition a y.1 < ρ :=
    hlog.eventually (gt_mem_nhds hzρ)
  filter_upwards [hp, hl] with y hyp hyl
  have hc : χ y.1 = 0 := by
    simpa only [expCoordinate_logPosition ha hyp] using hleft (logPosition a y.1) hyl.le
  simp only [TransportPrimitive.compactIntegral, hc, zero_smul, sub_zero]

/-- On an open right logarithmic collar the compactified operator equals
the negative future integral, including all its actual derivatives. -/
theorem compact_jet_eq_neg_future_on_right
    {a b M ρ : ℝ} {v : E} {f : ℝ × E → V} {χ : ℝ → ℝ}
    (ha : 0 < a) (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    (hright : ∀ s, logLength a b - ρ ≤ s → χ (expCoordinate a s) = 1)
    (z : ℝ × E) (hz : 0 < z.1) (hzρ : logLength a b - ρ < logPosition a z.1) (j : ℕ) :
    iteratedFDeriv ℝ j (TransportPrimitive.compactIntegral χ M v f) z =
      -iteratedFDeriv ℝ j (TransportPrimitive.futureIntegral M v f) z := by
  have heq : TransportPrimitive.compactIntegral χ M v f =ᶠ[𝓝 z]
      -TransportPrimitive.futureIntegral M v f := by
    have hp : ∀ᶠ y : ℝ × E in 𝓝 z, 0 < y.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds hz)
    have hinner : ContinuousAt (fun y : ℝ × E => y.1 / a) z :=
      (continuous_fst.div_const a).continuousAt
    have hlog : ContinuousAt (fun y : ℝ × E => logPosition a y.1) z :=
      hinner.log (div_ne_zero hz.ne' ha.ne')
    have hr : ∀ᶠ y : ℝ × E in 𝓝 z, logLength a b - ρ < logPosition a y.1 :=
      hlog.eventually (lt_mem_nhds hzρ)
    filter_upwards [hp, hr] with y hyp hyr
    have hc : χ y.1 = 1 := by
      simpa only [expCoordinate_logPosition ha hyp] using hright (logPosition a y.1) hyr.le
    exact TransportPrimitive.compactIntegral_eq_neg_future hf hs y hc
  rw [iteratedFDeriv_eq_of_eventuallyEq heq j, iteratedFDeriv_neg_apply]

variable [CompleteSpace V]

/-- Every finite prefix of actual Fréchet derivatives of the compactified
transport inverse preserves the same flat radial envelope. The estimate is
uniform in the shift and in all auxiliary variables. -/
theorem transport_compact_finiteJets_uniform
    {a b c d cL cR : ℝ} (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ X, X ≤ c → χ X = 0) (hright : ∀ X, d ≤ X → χ X = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (f : ℝ × E → V), ContDiff ℝ ∞ f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      (∀ j : ℕ, j ≤ m → ∀ X ∈ Ioo a b, ∀ Y : E,
        ‖iteratedFDeriv ℝ j f (X, Y)‖ ≤ A * logWeight cL cR a b p X) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (TransportPrimitive.compactIntegral χ M v f) z‖ ≤
          K * A * logWeight cL cR a b p z.1 := by
  classical
  have hab : a < b := hac.trans (hcd.trans hdb)
  obtain ⟨ρ, hρ, hρL, hl, hr⟩ := exists_log_plateau_width ha hac hcd hdb χ hleft hright
  obtain ⟨d₀, hd₀, hmiddle⟩ := middle_weight_lower_bound
    (L := logLength a b) hcL hcR (half_pos hρ)
  obtain ⟨B, hB, hcut⟩ := cutoff_finiteJet_bound (E := E) a b χ hχ m
  choose KL hKL hbL using fun j : Fin (m + 1) =>
    transport_past_left_uniform (E := E)
      (V := ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => ℝ × E) V)
      ha hab hcL hcR p
  choose KR hKR hbR using fun j : Fin (m + 1) =>
    transport_future_right_uniform (E := E)
      (V := ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => ℝ × E) V)
      ha hab hcL hcR p
  choose DS hDS hbD using fun j : Fin (m + 1) =>
    transport_mass_uniform (E := E)
      (V := ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => ℝ × E) V)
      ha hab hcL hcR p
  let L := ∑ j, KL j
  let R := ∑ j, KR j
  let D := ∑ j, DS j
  have hL : 0 ≤ L := Finset.sum_nonneg (fun j _ => hKL j)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun j _ => hKR j)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun j _ => hDS j)
  have hLL (j : Fin (m + 1)) : KL j ≤ L := Finset.single_le_sum (fun k _ => hKL k) (Finset.mem_univ
    j)
  have hRR (j : Fin (m + 1)) : KR j ≤ R := Finset.single_le_sum (fun k _ => hKR k) (Finset.mem_univ
    j)
  have hDD (j : Fin (m + 1)) : DS j ≤ D := Finset.single_le_sum (fun k _ => hDS k) (Finset.mem_univ
    j)
  let KM := D * (1 + (2 : ℝ) ^ m * B) / d₀
  have hKM : 0 ≤ KM := div_nonneg (mul_nonneg hD (by positivity)) hd₀.le
  let K := L + R + KM
  have hLK : L ≤ K := by dsimp [K]; linarith
  have hRK : R ≤ K := by dsimp [K]; linarith
  have hMK : KM ≤ K := by dsimp [K]; linarith
  refine ⟨K, hL.trans hLK, ?_⟩
  intro M v f hf hs A hA hsource z hz j hj
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hmass (i : ℕ) (hi : i ≤ m) :
      ‖TransportPrimitive.pastIntegral M v (iteratedFDeriv ℝ i f) z‖ ≤ D * A ∧
      ‖TransportPrimitive.totalIntegral M v (iteratedFDeriv ℝ i f) z‖ ≤ D * A := by
    let i' : Fin (m + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
    have h := hbD i' M v (iteratedFDeriv ℝ i f)
      (TransportPrimitive.iteratedFDeriv_contDiff hf i).continuous
      (TransportPrimitive.iteratedFDeriv_supported hs i) A hA (hsource i hi) z hz
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_right (hDD i') hA),
      h.2.trans (mul_le_mul_of_nonneg_right (hDD i') hA)⟩
  have hw : 0 ≤ logWeight cL cR a b p z.1 :=
    (weight_pos cL cR p (logPosition_mem ha hz)).le
  by_cases hzl : logPosition a z.1 ≤ ρ / 2
  · rw [compact_jet_eq_past_on_left ha hl z (ha.trans hz.1) (by linarith) j,
      TransportPrimitive.iteratedFDeriv_pastIntegral hf hs]
    have h := hbL j' M v (iteratedFDeriv ℝ j f)
      (TransportPrimitive.iteratedFDeriv_contDiff hf j).continuous
      (TransportPrimitive.iteratedFDeriv_supported hs j) A hA (hsource j hj) z hz (by linarith)
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((hLL j').trans hLK) hA) hw)
  · by_cases hzr : logLength a b - ρ / 2 ≤ logPosition a z.1
    · rw [compact_jet_eq_neg_future_on_right ha hf.continuous hs hr z (ha.trans hz.1) (by linarith)
      j,
        norm_neg, TransportPrimitive.iteratedFDeriv_futureIntegral hf hs]
      have h := hbR j' M v (iteratedFDeriv ℝ j f)
        (TransportPrimitive.iteratedFDeriv_contDiff hf j).continuous
        (TransportPrimitive.iteratedFDeriv_supported hs j) A hA (hsource j hj) z hz (by linarith)
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((hRR j').trans hRK) hA) hw)
    · have hwm : d₀ ≤ logWeight cL cR a b p z.1 :=
        hmiddle p (logPosition a z.1) ⟨le_of_not_ge hzl, le_of_not_ge hzr⟩
      have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : ℝ × E => χ y.1) z‖ *
          ‖TransportPrimitive.totalIntegral M v (iteratedFDeriv ℝ (j - i) f) z‖) ≤
          (2 : ℝ) ^ j * B * (D * A) := by
        calc
          _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * (D * A) := by
            apply Finset.sum_le_sum
            intro i hi
            have him : i ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (hcut i him z ⟨hz.1.le, hz.2.le⟩) (Nat.cast_nonneg _))
              (hmass (j - i) ((Nat.sub_le j i).trans hj)).2 (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) hB)
          _ = (2 : ℝ) ^ j * B * (D * A) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            congr 2
            exact_mod_cast Nat.sum_range_choose j
      calc
        _ ≤ ‖TransportPrimitive.pastIntegral M v (iteratedFDeriv ℝ j f) z‖ +
            ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun y : ℝ × E => χ y.1) z‖ *
              ‖TransportPrimitive.totalIntegral M v (iteratedFDeriv ℝ (j - i) f) z‖ :=
          TransportPrimitive.iteratedFDeriv_compactIntegral_norm_le hχ hf hs j z
        _ ≤ D * A + (2 : ℝ) ^ j * B * (D * A) := add_le_add (hmass j hj).1 hsum
        _ ≤ D * A + (2 : ℝ) ^ m * B * (D * A) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hB)
              (mul_nonneg hD hA)) _
        _ = (D * (1 + (2 : ℝ) ^ m * B)) * A := by ring
        _ = KM * A * d₀ := by dsimp [KM]; field_simp
        _ ≤ KM * A * logWeight cL cR a b p z.1 :=
          mul_le_mul_of_nonneg_left hwm (mul_nonneg hKM hA)
        _ ≤ K * A * logWeight cL cR a b p z.1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMK hA) hw

theorem canonical_transport_finiteJets_uniform
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (f : ℝ × E → V), ContDiff ℝ ∞ f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      (∀ j : ℕ, j ≤ m → ∀ X ∈ Ioo a b, ∀ Y : E,
        ‖iteratedFDeriv ℝ j f (X, Y)‖ ≤ A * logWeight cL cR a b p X) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j
          (TransportPrimitive.compactIntegral (TransportPrimitive.interiorCutoff a b) M v f) z‖ ≤
          K * A * logWeight cL cR a b p z.1 := by
  exact transport_compact_finiteJets_uniform (E := E) (V := V) ha
    (c := (2 * a + b) / 3) (d := (a + 2 * b) / 3)
    (by linarith) (by linarith) (by linarith) hcL hcR p m
    (TransportPrimitive.interiorCutoff a b) (TransportPrimitive.interiorCutoff_contDiff a b)
    (fun X hX => TransportPrimitive.interiorCutoff_zero hab hX)
    (fun X hX => TransportPrimitive.interiorCutoff_one hab hX)

end Transport

/-! ### The manuscript's all-jet mean class on a concrete annulus -/

section LogStrip

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A concrete `StripData`: the radial domain and both weights are explicit;
the only inputs beyond the annulus are the positive band scales. -/
noncomputable def logStripData (a b cL cR : ℝ) (ha : 0 < a)
    (hcL : 0 < cL) (hcR : 0 < cR) (ε S : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n) :
    WeightedClasses.StripData (ℝ × E) where
  domain := Prod.fst ⁻¹' Ioo a b
  isOpen_domain := isOpen_Ioo.preimage continuous_fst
  epsilon := ε
  epsilon_pos := hε
  epsilon_le_one := hεone
  slow := S
  one_le_slow := hS
  delta := fun z => delta (logLength a b) (logPosition a z.1)
  delta_pos := fun _ hz => delta_pos (logPosition_mem ha hz)
  zeta := fun z => zeta cL cR (logLength a b) (logPosition a z.1)
  zeta_smooth := by
    have hlog : ContDiffOn ℝ ∞ (fun z : ℝ × E => logPosition a z.1)
        (Prod.fst ⁻¹' Ioo a b) :=
      (contDiffOn_fst.div_const a).log (fun z hz => div_ne_zero (ha.trans hz.1).ne' ha.ne')
    exact ((edge_contDiff hcL : ContDiff ℝ ∞ _).comp_contDiffOn hlog).mul
      ((edge_contDiff hcR : ContDiff ℝ ∞ _).comp_contDiffOn (contDiffOn_const.sub hlog))
  zeta_nonneg := fun _ hz => (zeta_pos cL cR (logPosition_mem ha hz)).le

/-- On the concrete strip, the library majorant is exactly a band amplitude
times the explicit logarithmic radial weight. -/
theorem logStrip_majorant_eq
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (α C : ℝ) (p n : ℕ) (z : ℝ × E) (hz : z.1 ∈ Ioo a b) :
    WeightedClasses.majorant (logStripData a b cL cR ha hcL hcR ε S hε hεone hS)
      (fun _ y => (logStripData a b cL cR ha hcL hcR ε S hε hεone hS).zeta y) α C p n z =
      (C * (ε n) ^ α * (S n) ^ p) * logWeight cL cR a b p z.1 := by
  have hi : 1 ≤ (delta (logLength a b) (logPosition a z.1))⁻¹ :=
    (one_le_inv₀ (delta_pos (logPosition_mem ha hz))).mpr (delta_le_one _ _)
  simp only [WeightedClasses.majorant, WeightedClasses.StripData.growth, logStripData,
    max_eq_right hi, mul_pow, inv_pow, logWeight, weight, div_eq_mul_inv]
  ring

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The concrete compactified shifted inverse preserves the all-jet mean
class `M_α` on the explicit logarithmic annulus. Both radial support and global
smoothness of the input are named hypotheses; neither the inverse estimate nor
smoothness of the output is assumed. The bandwise shifts may be arbitrary. -/
theorem meanClass_canonical_transport
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (α : ℝ) (M : ℕ → ℝ) (v : ℕ → E) (f : ℕ → ℝ × E → V)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : WeightedClasses.MeanClass
      (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f) :
    WeightedClasses.MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α
      (fun n => TransportPrimitive.compactIntegral (TransportPrimitive.interiorCutoff a b)
        (M n) (v n) (f n)) := by
  refine ⟨hclass.weight_nonneg, ?_, ?_⟩
  · intro n
    exact (TransportPrimitive.compactIntegral_contDiff
      (TransportPrimitive.interiorCutoff_contDiff a b) (hf n) (hs n)).contDiffOn
  · intro m
    obtain ⟨C, hC, p, hsource⟩ := hclass.bounds m
    obtain ⟨K, hK, hbound⟩ := canonical_transport_finiteJets_uniform (E := E) (V := V)
      ha hab hcL hcR p m
    refine ⟨K * C, mul_nonneg hK hC, p, ?_⟩
    intro n z hz j hj
    change z.1 ∈ Ioo a b at hz
    have hA : 0 ≤ C * (ε n) ^ α * (S n) ^ p :=
      mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
        (pow_nonneg (zero_le_one.trans (hS n)) p)
    have hinput : ∀ i : ℕ, i ≤ m → ∀ X ∈ Ioo a b, ∀ Y : E,
        ‖iteratedFDeriv ℝ i (f n) (X, Y)‖ ≤
          (C * (ε n) ^ α * (S n) ^ p) * logWeight cL cR a b p X := by
      intro i hi X hX Y
      have hpnt := hsource n (X, Y) hX i hi
      rw [logStrip_majorant_eq ha hcL hcR ε S hε hεone hS α C p n (X, Y) hX] at hpnt
      exact hpnt
    have hout := hbound (M n) (v n) (f n) (hf n) (hs n)
      (C * (ε n) ^ α * (S n) ^ p) hA hinput z hz j hj
    rw [logStrip_majorant_eq ha hcL hcR ε S hε hεone hS α (K * C) p n z hz]
    simpa only [mul_assoc] using hout

/-- The full supported-mean conclusion includes global smoothness and the
original radial support, as required by the smooth zero-extension convention. -/
theorem supported_meanClass_canonical_transport
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (α : ℝ) (M : ℕ → ℝ) (v : ℕ → E) (f : ℕ → ℝ × E → V)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : WeightedClasses.MeanClass
      (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f) :
    let g := fun n => TransportPrimitive.compactIntegral (TransportPrimitive.interiorCutoff a b)
      (M n) (v n) (f n)
    (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, RadialAlias.RadiallySupported a b (g n)) ∧
      WeightedClasses.MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α g := by
  refine ⟨?_, ?_, meanClass_canonical_transport ha hab hcL hcR ε S hε hεone hS α M v f hf hs hclass⟩
  · exact fun n => TransportPrimitive.compactIntegral_contDiff
      (TransportPrimitive.interiorCutoff_contDiff a b) (hf n) (hs n)
  · exact fun n => TransportPrimitive.canonicalCompact_supported hab (hf n).continuous (hs n)

end LogStrip

end NavierStokes.WeightedRadialPrimitive
