/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteInitialTrace
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicInterpolation

/-!
# Short-time lower-order interpolation on finite cylinders

A genuine finite-cylinder `C^{2+α,1+α/2}` jet has more regularity than is
visible in either lower-order component alone. Its value is parabolically
Lipschitz from the first spatial and time derivatives, and its spatial
derivative is parabolically Lipschitz from the Hessian and time derivative
by a finite-difference argument.

For a zero-initial jet, the canonical endpoint trace makes the sup norm of
the spatial derivative small. Interpolating that small sup bound with the
uniform Lipschitz bound gives a genuinely small full `C^{0,α}` norm.
-/

@[expose] public noncomputable section
open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteParabolicC2AlphaBanach

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {t₀ T α : ℝ}

/-- A bounded first spatial derivative makes every value slice Lipschitz. -/
lemma value_spatial_lipschitz
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {B : ℝ} (hB : 0 ≤ B)
    (hD : ParabolicBoundedWith B (spaceDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    {t : ℝ} (ht : t ∈ Ioc t₀ T) (x y : X) :
    ‖value u (t, x) - value u (t, y)‖ ≤ B * ‖x - y‖ := by
  apply convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z : X ↦ value u (t, z))
      (f' := fun z ↦ spaceDeriv u (t, z))
  · intro z _
    exact (hasFDerivAt_space u ht z).hasFDerivWithinAt
  · intro z _
    exact hD (by simp [parabolicFiniteCylinder, ht])
  · simp
  · simp

/-- A bounded time derivative makes the value Lipschitz along time lines. -/
lemma value_time_lipschitz
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (hα : 0 < α) {B : ℝ} (hB : 0 ≤ B)
    (htime : ParabolicBoundedWith B (timeDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    {t τ : ℝ} (ht : t ∈ Ioc t₀ T) (hτ : τ ∈ Ioc t₀ T)
    (x : X) :
    ‖value u (t, x) - value u (τ, x)‖ ≤ B * ‖t - τ‖ := by
  have hsegment (a b : ℝ) (ha : a ∈ Ioc t₀ T) (hb : b ∈ Ioc t₀ T)
      (hab : a ≤ b) :
      ‖value u (b, x) - value u (a, x)‖ ≤ B * (b - a) := by
    have hcont : ContinuousOn (fun r : ℝ ↦ value u (r, x)) (Icc a b) := by
      have hc : ContinuousOn
          (ParabolicC0AlphaBanach.representative (valueComponentL u))
          (parabolicFiniteCylinder X t₀ T) :=
        (ParabolicC0AlphaSpace.toSubmodule
          (ParabolicC0AlphaBanach.outL (valueComponentL u))).2.continuousOn hα
      have hmap : Continuous (fun r : ℝ ↦ (r, x)) :=
        continuous_id.prodMk continuous_const
      have hcomp := hc.comp' hmap.continuousOn
        (fun (r : ℝ) (hr : r ∈ Icc a b) ↦ by
          simp only [parabolicFiniteCylinder, Set.mem_prod, Set.mem_Ioc,
            Set.mem_univ, and_true]
          exact ⟨ha.1.trans_le hr.1, hr.2.trans hb.2⟩)
      simpa [Function.comp_def, value, FiniteParabolicC2AlphaAmbient.value,
        ParabolicC0AlphaBanach.representative] using hcomp
    have hderiv : ∀ r ∈ Ico a b,
        HasDerivWithinAt (fun s : ℝ ↦ value u (s, x))
          (timeDeriv u (r, x)) (Ici r) r := by
      intro r hr
      exact (hasDerivAt_time u
        ⟨ha.1.trans_le hr.1, hr.2.trans_le hb.2⟩ x).hasDerivWithinAt
    have hbound : ∀ r ∈ Ico a b, ‖timeDeriv u (r, x)‖ ≤ B := by
      intro r hr
      exact htime (by
        simp only [parabolicFiniteCylinder, Set.mem_prod, Set.mem_Ioc,
          Set.mem_univ, and_true]
        exact ⟨ha.1.trans_le hr.1, (hr.2.trans_le hb.2).le⟩)
    exact norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv hbound
      b (right_mem_Icc.mpr hab)
  by_cases htτ : t ≤ τ
  · simpa [norm_sub_rev, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr htτ)] using
      hsegment t τ ht hτ htτ
  · have hτt : τ ≤ t := le_of_not_ge htτ
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hτt)] using
      hsegment τ t hτ ht hτt

/-- On a cylinder of thickness at most one, bounded first spatial and time
derivatives make the value parabolically Lipschitz. -/
theorem value_parabolicLipschitz
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (hα : 0 < α) (hthin : T - t₀ ≤ 1)
    {Bx Bt : ℝ} (hBx : 0 ≤ Bx) (hBt : 0 ≤ Bt)
    (hD : ParabolicBoundedWith Bx (spaceDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    (htime : ParabolicBoundedWith Bt (timeDeriv u)
      (parabolicFiniteCylinder X t₀ T)) :
    ParabolicHolderWith (Bx + Bt) 1 (value u)
      (parabolicFiniteCylinder X t₀ T) := by
  intro p hp q hq
  have hpt : p.1 ∈ Ioc t₀ T := by simpa [parabolicFiniteCylinder] using hp
  have hqt : q.1 ∈ Ioc t₀ T := by simpa [parabolicFiniteCylinder] using hq
  have hspace := value_spatial_lipschitz u hBx hD hpt p.2 q.2
  have htime' := value_time_lipschitz u hα hBt htime hpt hqt q.2
  have hdspace : ‖p.2 - q.2‖ ≤ parabolicDistance p q := by
    simpa [dist_eq_norm] using parabolicDistance.space_dist_le p q
  have habs : |p.1 - q.1| ≤ T - t₀ := by
    rw [abs_le]
    constructor <;> linarith [hpt.1, hpt.2, hqt.1, hqt.2]
  have habs1 : |p.1 - q.1| ≤ 1 := habs.trans hthin
  have hdtime : ‖p.1 - q.1‖ ≤ parabolicDistance p q := by
    rw [Real.norm_eq_abs]
    have hsqrt := parabolicDistance.sqrt_time_le p q
    have hs0 := Real.sqrt_nonneg |p.1 - q.1|
    calc
      |p.1 - q.1| = Real.sqrt |p.1 - q.1| ^ 2 := by
        rw [Real.sq_sqrt (abs_nonneg _)]
      _ ≤ Real.sqrt |p.1 - q.1| := by
        have hs1 : Real.sqrt |p.1 - q.1| ≤ 1 :=
          Real.sqrt_le_one.mpr habs1
        nlinarith
      _ ≤ parabolicDistance p q := hsqrt
  calc
    ‖value u p - value u q‖ ≤
        ‖value u (p.1, p.2) - value u (p.1, q.2)‖ +
          ‖value u (p.1, q.2) - value u (q.1, q.2)‖ := by
      calc
        _ = ‖(value u p - value u (p.1, q.2)) +
              (value u (p.1, q.2) - value u q)‖ := by congr 1 <;> abel
        _ ≤ _ := norm_add_le _ _
    _ ≤ Bx * ‖p.2 - q.2‖ + Bt * ‖p.1 - q.1‖ :=
      add_le_add hspace htime'
    _ ≤ Bx * parabolicDistance p q + Bt * parabolicDistance p q :=
      add_le_add (mul_le_mul_of_nonneg_left hdspace hBx)
        (mul_le_mul_of_nonneg_left hdtime hBt)
    _ = (Bx + Bt) * parabolicDistance p q ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      ring

/-- A bounded Hessian makes the first spatial derivative Lipschitz on every
full spatial slice. -/
lemma spaceDeriv_spatial_lipschitz
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {B : ℝ} (hB : 0 ≤ B)
    (hD2 : ParabolicBoundedWith B (spaceSecondDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    {t : ℝ} (ht : t ∈ Ioc t₀ T) (x y : X) :
    ‖spaceDeriv u (t, x) - spaceDeriv u (t, y)‖ ≤ B * ‖x - y‖ := by
  apply convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z : X ↦ spaceDeriv u (t, z))
      (f' := fun z ↦ spaceSecondDeriv u (t, z))
  · intro z _
    exact (hasFDerivAt_spaceDeriv u ht z).hasFDerivWithinAt
  · intro z _
    exact hD2 (by simp [parabolicFiniteCylinder, ht])
  · simp
  · simp

/-- First-order Taylor remainder for the value, using only the genuine
second-jet witnesses and the Hessian bound. -/
lemma value_linearization_error_le
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {B : ℝ} (hB : 0 ≤ B)
    (hD2 : ParabolicBoundedWith B (spaceSecondDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    {t : ℝ} (ht : t ∈ Ioc t₀ T) (x v : X)
    (hv : ‖v‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    ‖value u (t, x + a • v) - value u (t, x) -
        a • (spaceDeriv u (t, x) v)‖ ≤ B * a ^ 2 := by
  let F : ℝ → E := fun b ↦
    value u (t, x + b • v) - value u (t, x) -
      b • (spaceDeriv u (t, x) v)
  let F' : ℝ → E := fun b ↦
    (spaceDeriv u (t, x + b • v) - spaceDeriv u (t, x)) v
  have hderiv : ∀ b ∈ Icc (0 : ℝ) a,
      HasDerivWithinAt F (F' b) (Icc 0 a) b := by
    intro b hb
    have hline : HasDerivAt (fun c : ℝ ↦ value u (t, x + c • v))
        (spaceDeriv u (t, x + b • v) v) b := by
      have hi : HasDerivAt (fun c : ℝ ↦ x + c • v) v b := by
        simpa using ((hasDerivAt_id b).smul_const v).const_add x
      exact (hasFDerivAt_space u ht (x + b • v)).comp_hasDerivAt b hi
    have hlin : HasDerivAt (fun c : ℝ ↦ c • (spaceDeriv u (t, x) v))
        (spaceDeriv u (t, x) v) b := by
      simpa using (hasDerivAt_id b).smul_const (spaceDeriv u (t, x) v)
    have hout := (hline.sub_const (value u (t, x))).sub hlin
    refine hout.hasDerivWithinAt.congr ?_ ?_
    · intro c hc
      simp [F]
    · simp [F, F']
  have hbound : ∀ b ∈ Ico (0 : ℝ) a, ‖F' b‖ ≤ B * a := by
    intro b hb
    have hgrad := spaceDeriv_spatial_lipschitz u hB hD2 ht
      (x + b • v) x
    have happly := ContinuousLinearMap.le_opNorm
      (spaceDeriv u (t, x + b • v) - spaceDeriv u (t, x)) v
    calc
      ‖F' b‖ ≤
          ‖spaceDeriv u (t, x + b • v) - spaceDeriv u (t, x)‖ * ‖v‖ := by
        simpa [F'] using happly
      _ ≤ (B * ‖(x + b • v) - x‖) * ‖v‖ := by gcongr
      _ ≤ B * a := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hb.1]
        have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
        have hv2 : ‖v‖ * ‖v‖ ≤ 1 := by nlinarith
        calc
          B * (b * ‖v‖) * ‖v‖ = (B * b) * (‖v‖ * ‖v‖) := by ring
          _ ≤ (B * b) * 1 :=
            mul_le_mul_of_nonneg_left hv2 (mul_nonneg hB hb.1)
          _ ≤ B * a := by
            simpa using mul_le_mul_of_nonneg_left hb.2.le hB
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound a (right_mem_Icc.mpr ha)
  have hF0 : F 0 = 0 := by simp [F]
  rw [hF0, sub_zero] at hmvt
  simpa [F, pow_two, mul_assoc] using hmvt

/-- Finite-difference interpolation: applying the spatial derivative in a
unit vector, its variation between two times is controlled by the square
root of the time separation. -/
lemma spaceDeriv_time_sqrt_apply_le
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (hα : 0 < α)
    {B₂ Bt : ℝ} (hB₂ : 0 ≤ B₂) (hBt : 0 ≤ Bt)
    (hD2 : ParabolicBoundedWith B₂ (spaceSecondDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    (htime : ParabolicBoundedWith Bt (timeDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    {t τ : ℝ} (ht : t ∈ Ioc t₀ T) (hτ : τ ∈ Ioc t₀ T)
    (x v : X) (hv : ‖v‖ ≤ 1) :
    ‖(spaceDeriv u (t, x) - spaceDeriv u (τ, x)) v‖ ≤
      (2 * Bt + 2 * B₂) * Real.sqrt |t - τ| := by
  let δ := Real.sqrt |t - τ|
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  by_cases hδ : δ = 0
  · have htimeeq : t = τ := by
      have habsle : |t - τ| ≤ 0 := Real.sqrt_eq_zero'.mp hδ
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm habsle (abs_nonneg _)))
    subst τ
    simp
  have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδ)
  have hδsq : δ ^ 2 = |t - τ| := Real.sq_sqrt (abs_nonneg _)
  let A : E := value u (t, x + δ • v) - value u (t, x)
  let C : E := value u (τ, x + δ • v) - value u (τ, x)
  have hAt : ‖A - δ • (spaceDeriv u (t, x) v)‖ ≤ B₂ * δ ^ 2 := by
    simpa [A] using value_linearization_error_le u hB₂ hD2 ht x v hv hδ0
  have hAτ : ‖C - δ • (spaceDeriv u (τ, x) v)‖ ≤ B₂ * δ ^ 2 := by
    simpa [C] using value_linearization_error_le u hB₂ hD2 hτ x v hv hδ0
  have hshift := value_time_lipschitz u hα hBt htime ht hτ (x + δ • v)
  have hbase := value_time_lipschitz u hα hBt htime ht hτ x
  have hAC : ‖A - C‖ ≤ 2 * Bt * |t - τ| := by
    have hid : A - C =
        (value u (t, x + δ • v) - value u (τ, x + δ • v)) -
          (value u (t, x) - value u (τ, x)) := by
      simp only [A, C]
      abel
    rw [hid]
    calc
      ‖(value u (t, x + δ • v) - value u (τ, x + δ • v)) -
          (value u (t, x) - value u (τ, x))‖ ≤
          ‖value u (t, x + δ • v) - value u (τ, x + δ • v)‖ +
            ‖value u (t, x) - value u (τ, x)‖ := norm_sub_le _ _
      _ ≤ Bt * ‖t - τ‖ + Bt * ‖t - τ‖ := add_le_add hshift hbase
      _ = 2 * Bt * |t - τ| := by rw [Real.norm_eq_abs]; ring
  have hidentity : δ •
      ((spaceDeriv u (t, x) - spaceDeriv u (τ, x)) v) =
      -(A - δ • (spaceDeriv u (t, x) v)) + (A - C) +
        (C - δ • (spaceDeriv u (τ, x) v)) := by
    simp only [ContinuousLinearMap.sub_apply]
    module
  have hmul : δ *
      ‖(spaceDeriv u (t, x) - spaceDeriv u (τ, x)) v‖ ≤
      δ * ((2 * Bt + 2 * B₂) * δ) := by
    calc
      δ * ‖(spaceDeriv u (t, x) - spaceDeriv u (τ, x)) v‖ =
          ‖δ • ((spaceDeriv u (t, x) - spaceDeriv u (τ, x)) v)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ0]
      _ = ‖-(A - δ • (spaceDeriv u (t, x) v)) + (A - C) +
          (C - δ • (spaceDeriv u (τ, x) v))‖ := congrArg norm hidentity
      _ ≤ ‖A - δ • (spaceDeriv u (t, x) v)‖ + ‖A - C‖ +
          ‖C - δ • (spaceDeriv u (τ, x) v)‖ := by
        calc
          _ ≤ ‖-(A - δ • (spaceDeriv u (t, x) v)) + (A - C)‖ +
              ‖C - δ • (spaceDeriv u (τ, x) v)‖ := norm_add_le _ _
          _ ≤ (‖-(A - δ • (spaceDeriv u (t, x) v))‖ + ‖A - C‖) +
              ‖C - δ • (spaceDeriv u (τ, x) v)‖ :=
            add_le_add (norm_add_le _ _) le_rfl
          _ = _ := by rw [norm_neg]
      _ ≤ B₂ * δ ^ 2 + 2 * Bt * |t - τ| + B₂ * δ ^ 2 :=
        add_le_add (add_le_add hAt hAC) hAτ
      _ = δ * ((2 * Bt + 2 * B₂) * δ) := by rw [← hδsq]; ring
  nlinarith

/-- Operator-norm form of the square-root temporal modulus. -/
theorem spaceDeriv_time_sqrt_le
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (hα : 0 < α)
    {B₂ Bt : ℝ} (hB₂ : 0 ≤ B₂) (hBt : 0 ≤ Bt)
    (hD2 : ParabolicBoundedWith B₂ (spaceSecondDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    (htime : ParabolicBoundedWith Bt (timeDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    {t τ : ℝ} (ht : t ∈ Ioc t₀ T) (hτ : τ ∈ Ioc t₀ T)
    (x : X) :
    ‖spaceDeriv u (t, x) - spaceDeriv u (τ, x)‖ ≤
      (2 * Bt + 2 * B₂) * Real.sqrt |t - τ| := by
  let K : ℝ := (2 * Bt + 2 * B₂) * Real.sqrt |t - τ|
  have hK : 0 ≤ K := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  by_cases hv0 : v = 0
  · subst v
    simp [K]
  let w : X := ‖v‖⁻¹ • v
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, Real.norm_eq_abs, abs_of_pos hvnorm, hvnorm.ne']
  have happly := spaceDeriv_time_sqrt_apply_le u hα hB₂ hBt hD2 htime
    ht hτ x w (by rw [hw])
  have hvrep : ‖v‖ • w = v := by
    simp [w, smul_smul, hvnorm.ne']
  calc
    ‖(spaceDeriv u (t, x) - spaceDeriv u (τ, x)) v‖ =
        ‖(spaceDeriv u (t, x) - spaceDeriv u (τ, x)) (‖v‖ • w)‖ := by rw [hvrep]
    _ = ‖v‖ * ‖(spaceDeriv u (t, x) - spaceDeriv u (τ, x)) w‖ := by
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
    _ ≤ ‖v‖ * K := by
      gcongr
    _ = K * ‖v‖ := by ring

/-- The first spatial derivative is parabolically Lipschitz. -/
theorem spaceDeriv_parabolicLipschitz
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (hα : 0 < α)
    {B₂ Bt : ℝ} (hB₂ : 0 ≤ B₂) (hBt : 0 ≤ Bt)
    (hD2 : ParabolicBoundedWith B₂ (spaceSecondDeriv u)
      (parabolicFiniteCylinder X t₀ T))
    (htime : ParabolicBoundedWith Bt (timeDeriv u)
      (parabolicFiniteCylinder X t₀ T)) :
    ParabolicHolderWith (2 * Bt + 3 * B₂) 1 (spaceDeriv u)
      (parabolicFiniteCylinder X t₀ T) := by
  intro p hp q hq
  have hpt : p.1 ∈ Ioc t₀ T := by simpa [parabolicFiniteCylinder] using hp
  have hqt : q.1 ∈ Ioc t₀ T := by simpa [parabolicFiniteCylinder] using hq
  have hspace := spaceDeriv_spatial_lipschitz u hB₂ hD2 hpt p.2 q.2
  have htime' := spaceDeriv_time_sqrt_le u hα hB₂ hBt hD2 htime hpt hqt q.2
  have hdspace : ‖p.2 - q.2‖ ≤ parabolicDistance p q := by
    simpa [dist_eq_norm] using parabolicDistance.space_dist_le p q
  have hdtime : Real.sqrt |p.1 - q.1| ≤ parabolicDistance p q :=
    parabolicDistance.sqrt_time_le p q
  calc
    ‖spaceDeriv u p - spaceDeriv u q‖ ≤
        ‖spaceDeriv u (p.1, p.2) - spaceDeriv u (p.1, q.2)‖ +
          ‖spaceDeriv u (p.1, q.2) - spaceDeriv u (q.1, q.2)‖ := by
      calc
        _ = ‖(spaceDeriv u p - spaceDeriv u (p.1, q.2)) +
              (spaceDeriv u (p.1, q.2) - spaceDeriv u q)‖ := by congr 1 <;> abel
        _ ≤ _ := norm_add_le _ _
    _ ≤ B₂ * ‖p.2 - q.2‖ +
        (2 * Bt + 2 * B₂) * Real.sqrt |p.1 - q.1| := add_le_add hspace htime'
    _ ≤ B₂ * parabolicDistance p q +
        (2 * Bt + 2 * B₂) * parabolicDistance p q := by
      exact add_le_add (mul_le_mul_of_nonneg_left hdspace hB₂)
        (mul_le_mul_of_nonneg_left hdtime (by linarith))
    _ = (2 * Bt + 3 * B₂) * parabolicDistance p q ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      ring

/-! ## Short-time smallness in the exact source exponent -/

/-- The explicit short-time factor for the gradient `C^{0,α}` norm. -/
def gradientShortTimeFactor (D α : ℝ) : ℝ :=
  D ^ (α / 2) +
    (2 * D ^ (α / 2)) ^ (1 - α) * 5 ^ α

/-- The explicit short-time factor for the value `C^{0,α}` norm. -/
def valueShortTimeFactor (D α : ℝ) : ℝ :=
  D ^ (α / 2) +
    (2 * D ^ (α / 2)) ^ (1 - α) * 2 ^ α

lemma gradientShortTimeFactor_nonneg {D α : ℝ} (hD : 0 ≤ D) :
    0 ≤ gradientShortTimeFactor D α := by
  unfold gradientShortTimeFactor
  exact add_nonneg (Real.rpow_nonneg hD _)
    (mul_nonneg
      (Real.rpow_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hD _)) _)
      (Real.rpow_nonneg (by norm_num) _))

lemma valueShortTimeFactor_nonneg {D α : ℝ} (hD : 0 ≤ D) :
    0 ≤ valueShortTimeFactor D α := by
  unfold valueShortTimeFactor
  exact add_nonneg (Real.rpow_nonneg hD _)
    (mul_nonneg
      (Real.rpow_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hD _)) _)
      (Real.rpow_nonneg (by norm_num) _))

/-- The gradient interpolation factor can be made smaller than any positive
target by shortening the time cylinder. -/
theorem exists_thickness_gradientShortTimeFactor_le
    {α q : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hq : 0 < q) :
    ∃ D₀ > 0, ∀ D : ℝ, 0 ≤ D → D ≤ D₀ →
      gradientShortTimeFactor D α ≤ q := by
  have hhalf : 0 < α / 2 := by positivity
  have hone : 0 < 1 - α := by linarith
  have hpow : ContinuousAt (fun D : ℝ ↦ D ^ (α / 2)) 0 :=
    continuousAt_id.rpow_const (Or.inr hhalf.le)
  have hbase : ContinuousAt (fun D : ℝ ↦ 2 * D ^ (α / 2)) 0 :=
    continuousAt_const.mul hpow
  have hfactor : ContinuousAt (fun D : ℝ ↦ gradientShortTimeFactor D α) 0 := by
    unfold gradientShortTimeFactor
    exact hpow.add
      ((hbase.rpow_const (Or.inr hone.le)).mul continuousAt_const)
  have hzero : gradientShortTimeFactor 0 α = 0 := by
    unfold gradientShortTimeFactor
    rw [Real.zero_rpow hhalf.ne', mul_zero, Real.zero_rpow hone.ne',
      zero_mul, add_zero]
  have hlt : gradientShortTimeFactor 0 α < q := by rw [hzero]; exact hq
  have hev := Filter.Tendsto.eventually_lt_const hlt hfactor
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by positivity, fun D hD hDle ↦ ?_⟩
  have hdist : dist D 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hD]
    linarith
  exact le_of_lt (hball hdist)

/-- The value interpolation factor can be made smaller than any positive
target by shortening the time cylinder. -/
theorem exists_thickness_valueShortTimeFactor_le
    {α q : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hq : 0 < q) :
    ∃ D₀ > 0, ∀ D : ℝ, 0 ≤ D → D ≤ D₀ →
      valueShortTimeFactor D α ≤ q := by
  have hhalf : 0 < α / 2 := by positivity
  have hone : 0 < 1 - α := by linarith
  have hpow : ContinuousAt (fun D : ℝ ↦ D ^ (α / 2)) 0 :=
    continuousAt_id.rpow_const (Or.inr hhalf.le)
  have hbase : ContinuousAt (fun D : ℝ ↦ 2 * D ^ (α / 2)) 0 :=
    continuousAt_const.mul hpow
  have hfactor : ContinuousAt (fun D : ℝ ↦ valueShortTimeFactor D α) 0 := by
    unfold valueShortTimeFactor
    exact hpow.add
      ((hbase.rpow_const (Or.inr hone.le)).mul continuousAt_const)
  have hzero : valueShortTimeFactor 0 α = 0 := by
    unfold valueShortTimeFactor
    rw [Real.zero_rpow hhalf.ne', mul_zero, Real.zero_rpow hone.ne',
      zero_mul, add_zero]
  have hlt : valueShortTimeFactor 0 α < q := by rw [hzero]; exact hq
  have hev := Filter.Tendsto.eventually_lt_const hlt hfactor
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by positivity, fun D hD hDle ↦ ?_⟩
  have hdist : dist D 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hD]
    linarith
  exact le_of_lt (hball hdist)

lemma norm_valueComponentL_le
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    ‖valueComponentL u‖ ≤ ‖u‖ := by
  change ‖u.1.1‖ ≤ ‖u.1‖
  exact norm_fst_le u.1

lemma norm_spaceDerivComponentL_le
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    ‖spaceDerivComponentL u‖ ≤ ‖u‖ := by
  change ‖u.1.2.1‖ ≤ ‖u.1‖
  exact (norm_fst_le u.1.2).trans (norm_snd_le u.1)

lemma norm_spaceSecondDerivComponentL_le
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    ‖spaceSecondDerivComponentL u‖ ≤ ‖u‖ := by
  change ‖u.1.2.2.1‖ ≤ ‖u.1‖
  exact (norm_fst_le u.1.2.2).trans
    ((norm_snd_le u.1.2).trans (norm_snd_le u.1))

lemma norm_timeDerivComponentL_le
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    ‖timeDerivComponentL u‖ ≤ ‖u‖ := by
  change ‖u.1.2.2.2‖ ≤ ‖u.1‖
  exact (norm_snd_le u.1.2.2).trans
    ((norm_snd_le u.1.2).trans (norm_snd_le u.1))

/-- The full `C^{0,α}` norm of the value is short-time small on the
zero-initial subspace. -/
theorem norm_valueComponentL_le_valueShortTimeFactor
    (hT : t₀ < T) (hα0 : 0 < α) (hα1 : α < 1)
    (hthin : T - t₀ ≤ 1)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (hu0 : initialTraceL hT hα0 u = 0) :
    ‖valueComponentL u‖ ≤ valueShortTimeFactor (T - t₀) α * ‖u‖ := by
  let N : ℝ := ‖u‖
  let D : ℝ := T - t₀
  have hN : 0 ≤ N := norm_nonneg u
  have hD : 0 ≤ D := sub_nonneg.mpr hT.le
  have hDb : ParabolicBoundedWith N (spaceDeriv u)
      (parabolicFiniteCylinder X t₀ T) := by
    intro z hz
    rw [← evalCLM_spaceDerivComponentL u z hz]
    calc
      ‖ParabolicC0AlphaBanach.evalCLM z hz (spaceDerivComponentL u)‖ ≤
          ‖ParabolicC0AlphaBanach.evalCLM (E := X →L[ℝ] E) z hz‖ *
            ‖spaceDerivComponentL u‖ :=
        (ParabolicC0AlphaBanach.evalCLM (E := X →L[ℝ] E) z hz).le_opNorm _
      _ ≤ 1 * ‖spaceDerivComponentL u‖ := by
        gcongr
        exact ParabolicC0AlphaBanach.norm_evalCLM_le z hz
      _ ≤ N := by simpa [N] using norm_spaceDerivComponentL_le u
  have htb : ParabolicBoundedWith N (timeDeriv u)
      (parabolicFiniteCylinder X t₀ T) := by
    intro z hz
    rw [← evalCLM_timeDerivComponentL u z hz]
    calc
      ‖ParabolicC0AlphaBanach.evalCLM z hz (timeDerivComponentL u)‖ ≤
          ‖ParabolicC0AlphaBanach.evalCLM (E := E) z hz‖ *
            ‖timeDerivComponentL u‖ :=
        (ParabolicC0AlphaBanach.evalCLM (E := E) z hz).le_opNorm _
      _ ≤ 1 * ‖timeDerivComponentL u‖ := by
        gcongr
        exact ParabolicC0AlphaBanach.norm_evalCLM_le z hz
      _ ≤ N := by simpa [N] using norm_timeDerivComponentL_le u
  have hLip : ParabolicHolderWith (2 * N) 1 (value u)
      (parabolicFiniteCylinder X t₀ T) := by
    simpa only [show N + N = 2 * N by ring] using
      value_parabolicLipschitz u hα0 hthin hN hN hDb htb
  have htrace : ParabolicC0AlphaBanach.finiteInitialTrace hT hα0
      (valueComponentL u) = 0 := by simpa using hu0
  have hbounded : ParabolicBoundedWith (D ^ (α / 2) * N)
      (value u) (parabolicFiniteCylinder X t₀ T) := by
    intro z hz
    have hz' := mem_parabolicFiniteCylinder.mp hz
    let tt : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T :=
      ⟨⟨z.1, hz'.1.le, hz'.2⟩, hz'.1⟩
    have hs := ParabolicC0AlphaBanach.dist_finiteTimeSlice_initial_le
      hT hα0 (valueComponentL u) tt
    have heval : ParabolicC0AlphaBanach.finiteTimeSlice hα0
        (valueComponentL u) tt z.2 = value u z := by
      rw [ParabolicC0AlphaBanach.finiteTimeSlice_apply,
        evalCLM_valueComponentL]
    rw [htrace, dist_zero_right] at hs
    have hs' : ‖value u z‖ ≤
        ‖valueComponentL u‖ * |z.1 - t₀| ^ (α / 2) := by
      rw [← heval]
      exact (ParabolicC0AlphaBanach.finiteTimeSlice hα0
        (valueComponentL u) tt).norm_coe_le_norm z.2 |>.trans hs
    calc
      ‖value u z‖ ≤ ‖valueComponentL u‖ * |z.1 - t₀| ^ (α / 2) := hs'
      _ ≤ N * D ^ (α / 2) := by
        apply mul_le_mul (norm_valueComponentL_le u)
        · apply Real.rpow_le_rpow (abs_nonneg _) _ (by linarith)
          rw [abs_of_nonneg (sub_nonneg.mpr hz'.1.le)]
          exact sub_le_sub_right hz'.2 t₀
        · exact Real.rpow_nonneg (abs_nonneg _) _
        · exact hN
      _ = D ^ (α / 2) * N := by ring
  have hholder : ParabolicHolderWith
      ((2 * (D ^ (α / 2) * N)) ^ (1 - α) * (2 * N) ^ α) α
      (value u) (parabolicFiniteCylinder X t₀ T) := by
    simpa only [one_mul] using parabolicHolderWith_interpolation
      (mul_nonneg (Real.rpow_nonneg hD _) hN)
      (mul_nonneg (by norm_num) hN) hα0.le hα1.le hbounded hLip
  have hnorm : parabolicC0AlphaNorm α (value u)
      (parabolicFiniteCylinder X t₀ T) ≤
      D ^ (α / 2) * N +
        (2 * (D ^ (α / 2) * N)) ^ (1 - α) * (2 * N) ^ α :=
    parabolicC0AlphaNorm_le
      (mul_nonneg (Real.rpow_nonneg hD _) hN)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)) ⟨hbounded, hholder⟩
  have hNpow : N ^ (1 - α) * N ^ α = N := by
    rw [← Real.rpow_add' hN (by norm_num : (1 - α) + α ≠ 0),
      show (1 - α) + α = 1 by ring, Real.rpow_one]
  have hfactor :
      D ^ (α / 2) * N +
          (2 * (D ^ (α / 2) * N)) ^ (1 - α) * (2 * N) ^ α =
        valueShortTimeFactor D α * N := by
    rw [show 2 * (D ^ (α / 2) * N) =
        (2 * D ^ (α / 2)) * N by ring,
      Real.mul_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hD _)) hN,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN]
    calc
      D ^ (α / 2) * N +
          (2 * D ^ (α / 2)) ^ (1 - α) * N ^ (1 - α) *
            (2 ^ α * N ^ α) =
        D ^ (α / 2) * N +
          ((2 * D ^ (α / 2)) ^ (1 - α) * 2 ^ α) *
            (N ^ (1 - α) * N ^ α) := by ring
      _ = D ^ (α / 2) * N +
          ((2 * D ^ (α / 2)) ^ (1 - α) * 2 ^ α) * N := by rw [hNpow]
      _ = valueShortTimeFactor D α * N := by
        simp only [valueShortTimeFactor]
        ring
  have hnormeq : ‖valueComponentL u‖ =
      parabolicC0AlphaNorm α (value u)
        (parabolicFiniteCylinder X t₀ T) := by
    rw [← ParabolicC0AlphaBanach.norm_outL (valueComponentL u),
      ParabolicC0AlphaSpace.norm_def]
    rfl
  rw [hnormeq, ← hfactor]
  exact hnorm

/-- The full `C^{0,α}` norm of the first derivative is short-time small on
the zero-initial subspace. -/
theorem norm_spaceDerivComponentL_le_gradientShortTimeFactor
    (hT : t₀ < T) (hα0 : 0 < α) (hα1 : α < 1)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (hu0 : initialTraceL hT hα0 u = 0) :
    ‖spaceDerivComponentL u‖ ≤
      gradientShortTimeFactor (T - t₀) α * ‖u‖ := by
  let N : ℝ := ‖u‖
  let D : ℝ := T - t₀
  have hN : 0 ≤ N := norm_nonneg u
  have hD : 0 ≤ D := sub_nonneg.mpr hT.le
  have hD2b : ParabolicBoundedWith N (spaceSecondDeriv u)
      (parabolicFiniteCylinder X t₀ T) := by
    intro z hz
    rw [← evalCLM_spaceSecondDerivComponentL u z hz]
    calc
      ‖ParabolicC0AlphaBanach.evalCLM z hz
          (spaceSecondDerivComponentL u)‖ ≤
          ‖ParabolicC0AlphaBanach.evalCLM (E := X →L[ℝ] X →L[ℝ] E) z hz‖ *
            ‖spaceSecondDerivComponentL u‖ :=
        (ParabolicC0AlphaBanach.evalCLM
          (E := X →L[ℝ] X →L[ℝ] E) z hz).le_opNorm _
      _ ≤ 1 * ‖spaceSecondDerivComponentL u‖ := by
        gcongr
        exact ParabolicC0AlphaBanach.norm_evalCLM_le z hz
      _ ≤ N := by simpa [N] using norm_spaceSecondDerivComponentL_le u
  have htb : ParabolicBoundedWith N (timeDeriv u)
      (parabolicFiniteCylinder X t₀ T) := by
    intro z hz
    rw [← evalCLM_timeDerivComponentL u z hz]
    calc
      ‖ParabolicC0AlphaBanach.evalCLM z hz (timeDerivComponentL u)‖ ≤
          ‖ParabolicC0AlphaBanach.evalCLM (E := E) z hz‖ *
            ‖timeDerivComponentL u‖ :=
        (ParabolicC0AlphaBanach.evalCLM (E := E) z hz).le_opNorm _
      _ ≤ 1 * ‖timeDerivComponentL u‖ := by
        gcongr
        exact ParabolicC0AlphaBanach.norm_evalCLM_le z hz
      _ ≤ N := by simpa [N] using norm_timeDerivComponentL_le u
  have hLip : ParabolicHolderWith (5 * N) 1 (spaceDeriv u)
      (parabolicFiniteCylinder X t₀ T) := by
    simpa only [show 2 * N + 3 * N = 5 * N by ring] using
      spaceDeriv_parabolicLipschitz u hα0 hN hN hD2b htb
  have htrace : ParabolicC0AlphaBanach.finiteInitialTrace hT hα0
      (spaceDerivComponentL u) = 0 :=
    finiteInitialTrace_spaceDeriv_eq_zero_of_initialTrace_eq_zero
      hT hα0 u hu0
  have hbounded : ParabolicBoundedWith (D ^ (α / 2) * N)
      (spaceDeriv u) (parabolicFiniteCylinder X t₀ T) := by
    intro z hz
    have hz' := mem_parabolicFiniteCylinder.mp hz
    let tt : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T :=
      ⟨⟨z.1, hz'.1.le, hz'.2⟩, hz'.1⟩
    have hs := ParabolicC0AlphaBanach.dist_finiteTimeSlice_initial_le
      hT hα0 (spaceDerivComponentL u) tt
    have heval : ParabolicC0AlphaBanach.finiteTimeSlice hα0
        (spaceDerivComponentL u) tt z.2 = spaceDeriv u z := by
      rw [ParabolicC0AlphaBanach.finiteTimeSlice_apply,
        evalCLM_spaceDerivComponentL]
    rw [htrace, dist_zero_right] at hs
    have hs' : ‖spaceDeriv u z‖ ≤
        ‖spaceDerivComponentL u‖ * |z.1 - t₀| ^ (α / 2) := by
      rw [← heval]
      exact (ParabolicC0AlphaBanach.finiteTimeSlice hα0
        (spaceDerivComponentL u) tt).norm_coe_le_norm z.2 |>.trans hs
    calc
      ‖spaceDeriv u z‖ ≤
          ‖spaceDerivComponentL u‖ * |z.1 - t₀| ^ (α / 2) := hs'
      _ ≤ N * D ^ (α / 2) := by
        apply mul_le_mul (norm_spaceDerivComponentL_le u)
        · apply Real.rpow_le_rpow (abs_nonneg _) _ (by linarith)
          rw [abs_of_nonneg (sub_nonneg.mpr hz'.1.le)]
          exact sub_le_sub_right hz'.2 t₀
        · exact Real.rpow_nonneg (abs_nonneg _) _
        · exact hN
      _ = D ^ (α / 2) * N := by ring
  have hholder : ParabolicHolderWith
      ((2 * (D ^ (α / 2) * N)) ^ (1 - α) * (5 * N) ^ α) α
      (spaceDeriv u) (parabolicFiniteCylinder X t₀ T) := by
    simpa only [one_mul] using parabolicHolderWith_interpolation
      (mul_nonneg (Real.rpow_nonneg hD _) hN)
      (mul_nonneg (by norm_num) hN) hα0.le hα1.le hbounded hLip
  have hnorm : parabolicC0AlphaNorm α (spaceDeriv u)
      (parabolicFiniteCylinder X t₀ T) ≤
      D ^ (α / 2) * N +
        (2 * (D ^ (α / 2) * N)) ^ (1 - α) * (5 * N) ^ α :=
    parabolicC0AlphaNorm_le
      (mul_nonneg (Real.rpow_nonneg hD _) hN)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)) ⟨hbounded, hholder⟩
  have hNpow : N ^ (1 - α) * N ^ α = N := by
    rw [← Real.rpow_add' hN (by norm_num : (1 - α) + α ≠ 0),
      show (1 - α) + α = 1 by ring, Real.rpow_one]
  have hfactor :
      D ^ (α / 2) * N +
          (2 * (D ^ (α / 2) * N)) ^ (1 - α) * (5 * N) ^ α =
        gradientShortTimeFactor D α * N := by
    rw [show 2 * (D ^ (α / 2) * N) =
        (2 * D ^ (α / 2)) * N by ring,
      Real.mul_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hD _)) hN,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hN]
    calc
      D ^ (α / 2) * N +
          (2 * D ^ (α / 2)) ^ (1 - α) * N ^ (1 - α) *
            (5 ^ α * N ^ α) =
        D ^ (α / 2) * N +
          ((2 * D ^ (α / 2)) ^ (1 - α) * 5 ^ α) *
            (N ^ (1 - α) * N ^ α) := by ring
      _ = D ^ (α / 2) * N +
          ((2 * D ^ (α / 2)) ^ (1 - α) * 5 ^ α) * N := by rw [hNpow]
      _ = gradientShortTimeFactor D α * N := by
        simp only [gradientShortTimeFactor]
        ring
  have hnormeq : ‖spaceDerivComponentL u‖ =
      parabolicC0AlphaNorm α (spaceDeriv u)
        (parabolicFiniteCylinder X t₀ T) := by
    rw [← ParabolicC0AlphaBanach.norm_outL (spaceDerivComponentL u),
      ParabolicC0AlphaSpace.norm_def]
    rfl
  rw [hnormeq, ← hfactor]
  exact hnorm

/-- The first-derivative projection restricted to zero-initial jets. -/
def zeroInitialSpaceDerivL (hT : t₀ < T) (hα : 0 < α) :
    zeroInitialSubmodule (X := X) (E := E) hT hα →L[ℝ]
      ParabolicC0AlphaBanach X (X →L[ℝ] E) α
        (parabolicFiniteCylinder X t₀ T) :=
  spaceDerivComponentL.comp
    ((zeroInitialSubmodule (X := X) (E := E) hT hα).subtypeL)

end FiniteParabolicC2AlphaBanach
end AnalyticPDE
end RicciFlow
