/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
import Mathlib.Topology.MetricSpace.Contracting

/-! Banach's theorem applied to the actual singular Volterra integral on continuous paths. -/

@[expose] public section


noncomputable section

namespace EulerVolterraConvolution

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (T : ℝ) (hT : 0 ≤ T) (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ (univ : Set Y)))
variable (hk : IntegrableOn k (Ioc 0 T)) (hk0 : ∀ r ∈ Ioc 0 T, 0 ≤ k r)
variable (hbound : ∀ r ∈ Ioc 0 T, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)

include hK hk hk0 hbound in
/-- The actual Bochner convolution commutes with subtraction of continuous paths. -/
theorem convolution_sub (f g : C(Icc (0 : ℝ) T, Y)) :
    convolution T hT K k hK hk hk0 hbound (f - g) =
      convolution T hT K k hK hk hk0 hbound f - convolution T hT K k hK hk hk0 hbound g := by
  ext t
  change (∫ r in Ioc 0 T, causalIntegrand T hT K (f - g) t r) =
    (∫ r in Ioc 0 T, causalIntegrand T hT K f t r) -
      ∫ r in Ioc 0 T, causalIntegrand T hT K g t r
  rw [← integral_sub (causalIntegrand_integrable T hT K k hK hk hk0 hbound f t)
    (causalIntegrand_integrable T hT K k hK hk hk0 hbound g t)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    by_cases hr : r ≤ t.val <;> simp [causalIntegrand, indicator, hr, extendPath, map_sub]

include hK hk hk0 hbound in
/-- The actual convolution is Lipschitz with constant equal to its scalar kernel mass. -/
theorem convolution_sub_bound (f g : C(Icc (0 : ℝ) T, Y)) :
    ‖convolution T hT K k hK hk hk0 hbound f - convolution T hT K k hK hk hk0 hbound g‖ ≤
      kernelMass T k * ‖f - g‖ := by
  rw [← convolution_sub T hT K k hK hk hk0 hbound]
  exact convolution_bound T hT K k hK hk hk0 hbound (f - g)

/-- Pointwise application of an actual continuous time-dependent nonlinearity to a path. -/
def pathNonlinearity (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (u : C(Icc (0 : ℝ) T, X)) : C(Icc (0 : ℝ) T, Y) where
  toFun t := F t (u t)
  continuous_toFun := hF.comp (continuous_id.prodMk u.continuous)

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- The pointwise nonlinear bound on a ball gives the same bound on continuous paths. -/
theorem pathNonlinearity_bound (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (R M : ℝ) (hM : 0 ≤ M) (hFM : ∀ t x, ‖x‖ ≤ R → ‖F t x‖ ≤ M)
    (u : C(Icc (0 : ℝ) T, X)) (hu : ‖u‖ ≤ R) : ‖pathNonlinearity T F hF u‖ ≤ M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro t
  exact hFM t (u t) ((u.norm_coe_le_norm t).trans hu)

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- A local Lipschitz nonlinearity induces the same local Lipschitz bound on path space. -/
theorem pathNonlinearity_sub_bound (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (R L : ℝ) (hL : 0 ≤ L)
    (hFL : ∀ t x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F t x - F t y‖ ≤ L * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, X)) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖pathNonlinearity T F hF u - pathNonlinearity T F hF v‖ ≤ L * ‖u - v‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hL (norm_nonneg _))).mpr
  intro t
  exact (hFL t (u t) (v t) ((u.norm_coe_le_norm t).trans hu) ((v.norm_coe_le_norm t).trans
      hv)).trans
    (mul_le_mul_of_nonneg_left ((u - v).norm_coe_le_norm t) hL)

/-- The actual nonlinear Volterra map, including the prescribed free evolution. -/
def picard (a : C(Icc (0 : ℝ) T, X)) (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (u : C(Icc (0 : ℝ) T, X)) : C(Icc (0 : ℝ) T, X) :=
  a + convolution T hT K k hK hk hk0 hbound (pathNonlinearity T F hF u)

include hK hk hk0 hbound in
/-- The genuine Picard map preserves the chosen path ball under the explicit scalar budget. -/
theorem picard_bound (a : C(Icc (0 : ℝ) T, X)) (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (R M : ℝ) (hM : 0 ≤ M) (hFM : ∀ t x, ‖x‖ ≤ R → ‖F t x‖ ≤ M)
    (hbudget : ‖a‖ + kernelMass T k * M ≤ R)
    (u : C(Icc (0 : ℝ) T, X)) (hu : ‖u‖ ≤ R) :
    ‖picard T hT K k hK hk hk0 hbound a F hF u‖ ≤ R := by
  have hc := convolution_bound T hT K k hK hk hk0 hbound (pathNonlinearity T F hF u)
  have hn := mul_le_mul_of_nonneg_left (pathNonlinearity_bound T F hF R M hM hFM u hu)
    (kernelMass_nonneg T k hk0)
  apply (norm_add_le a (convolution T hT K k hK hk hk0 hbound (pathNonlinearity T F hF u))).trans
  linarith

include hK hk hk0 hbound in
/-- The actual Picard map has contraction coefficient equal to kernel mass times nonlinear Lipschitz
constant. -/
theorem picard_sub_bound (a : C(Icc (0 : ℝ) T, X)) (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (R L : ℝ) (hL : 0 ≤ L)
    (hFL : ∀ t x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F t x - F t y‖ ≤ L * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, X)) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖picard T hT K k hK hk hk0 hbound a F hF u - picard T hT K k hK hk hk0 hbound a F hF v‖ ≤
      (kernelMass T k * L) * ‖u - v‖ := by
  simp only [picard, add_sub_add_left_eq_sub]
  exact (convolution_sub_bound T hT K k hK hk hk0 hbound _ _).trans
    ((mul_le_mul_of_nonneg_left (pathNonlinearity_sub_bound T F hF R L hL hFL u v hu hv)
      (kernelMass_nonneg T k hk0)).trans_eq (mul_assoc _ _ _).symm)

include hK hk hk0 hbound in
/-- An actual continuous mild solution exists by contraction of the explicitly defined Volterra
integral. -/
theorem exists_mild_solution [CompleteSpace X]
    (a : C(Icc (0 : ℝ) T, X)) (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (R M L : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hFM : ∀ t x, ‖x‖ ≤ R → ‖F t x‖ ≤ M)
    (hFL : ∀ t x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F t x - F t y‖ ≤ L * ‖x - y‖)
    (hbudget : ‖a‖ + kernelMass T k * M ≤ R) (hsmall : kernelMass T k * L < 1) :
    ∃ u : C(Icc (0 : ℝ) T, X), ‖u‖ ≤ R ∧ ∀ t : Icc (0 : ℝ) T,
      u t = a t + ∫ r in (0 : ℝ)..t.val,
        K r (F (projIcc 0 T hT (t.val - r)) (u (projIcc 0 T hT (t.val - r)))) := by
  let P := picard T hT K k hK hk hk0 hbound a F hF
  let B : Set C(Icc (0 : ℝ) T, X) := closedBall 0 R
  have hmap : MapsTo P B B := by
    intro u hu
    have hun : ‖u‖ ≤ R := by simpa only [B, mem_closedBall, dist_zero_right] using hu
    simpa only [B, mem_closedBall, dist_zero_right] using
      picard_bound T hT K k hK hk hk0 hbound a F hF R M hM hFM hbudget u hun
  let c : ℝ≥0 := ⟨kernelMass T k * L, mul_nonneg (kernelMass_nonneg T k hk0) hL⟩
  have hc : ContractingWith c (hmap.restrict P B B) := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    change dist (P u.val) (P v.val) ≤ (kernelMass T k * L) * dist u.val v.val
    rw [dist_eq_norm, dist_eq_norm]
    exact picard_sub_bound T hT K k hK hk hk0 hbound a F hF R L hL hFL u.val v.val
      (by simpa only [B, mem_closedBall, dist_zero_right] using u.property)
      (by simpa only [B, mem_closedBall, dist_zero_right] using v.property)
  have hzero : (0 : C(Icc (0 : ℝ) T, X)) ∈ B := by
      simpa only [B, mem_closedBall, dist_self] using hR
  obtain ⟨u, hu, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hc hzero (edist_ne_top 0 (P 0))
  refine ⟨u, by simpa only [B, mem_closedBall, dist_zero_right] using hu, ?_⟩
  intro t
  have ht := congrArg (fun v : C(Icc (0 : ℝ) T, X) => v t) hfix
  change a t + convolution T hT K k hK hk hk0 hbound (pathNonlinearity T F hF u) t = u t at ht
  rw [convolution_eq_interval T hT K k hK hk hk0 hbound] at ht
  exact ht.symm

end EulerVolterraConvolution
