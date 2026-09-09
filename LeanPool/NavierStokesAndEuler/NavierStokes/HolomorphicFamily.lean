/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.CauchyRestriction
public import LeanPool.NavierStokesAndEuler.NavierStokes.CompactSmoothFamily
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Joint real smoothness of smooth families of holomorphic disk functions

A fixed-contour Cauchy formula realizes evaluation inside a disk as a smooth
supremum-norm kernel paired with the supplied Banach-valued curve. This proves
joint smoothness, rather than inferring it from separate smoothness.
-/

@[expose] public section


namespace NavierStokes.HolomorphicFamily

noncomputable section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff Interval

open CauchyRestriction

/-- Angles: an abbreviation for `↥(Icc (0 : ℝ) (2 * Real.pi))`. -/
abbrev Angles := ↥(Icc (0 : ℝ) (2 * Real.pi))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Continuous extension of an angle path, used only inside its integration interval. -/
noncomputable def angleExtend (f : C(Angles, E)) (θ : ℝ) : E :=
  f (projIcc 0 (2 * Real.pi) Real.two_pi_pos.le θ)

omit [NormedSpace ℂ E] in
theorem continuous_angleExtend (f : C(Angles, E)) : Continuous (angleExtend f) :=
  f.continuous.comp continuous_projIcc

omit [NormedSpace ℂ E] in
theorem angleExtend_coe (f : C(Angles, E)) (θ : Angles) : angleExtend f θ = f θ := by
  simp only [angleExtend, projIcc_val]

theorem norm_angleIntegral_le (f : C(Angles, E)) :
    ‖∫ θ in (0 : ℝ)..(2 * Real.pi), angleExtend f θ‖ ≤ (2 * Real.pi) * ‖f‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (f := angleExtend f)
    (fun θ _ => f.norm_coe_le_norm (projIcc 0 (2 * Real.pi) Real.two_pi_pos.le θ))
  calc
    _ ≤ ‖f‖ * |2 * Real.pi - 0| := h
    _ = (2 * Real.pi) * ‖f‖ := by rw [sub_zero, abs_of_pos Real.two_pi_pos]; ring

/-- Integration is a bounded real-linear map on continuous angle paths. -/
noncomputable def angleIntegral : C(Angles, E) →L[ℝ] E :=
  LinearMap.mkContinuous {
    toFun f := ∫ θ in (0 : ℝ)..(2 * Real.pi), angleExtend f θ
    map_add' := by
      intro f g
      exact intervalIntegral.integral_add (continuous_angleExtend f |>.intervalIntegrable _ _)
        (continuous_angleExtend g |>.intervalIntegrable _ _)
    map_smul' := by
      intro r f
      exact intervalIntegral.integral_smul r (angleExtend f)
  } (2 * Real.pi) norm_angleIntegral_le

/-- Sampling the outer circle as a continuous map into the closed disk. -/
noncomputable def circleInput (c : ℂ) {σ : ℝ} (hσ : 0 < σ) : C(Angles, Disk c σ) where
  toFun θ := ⟨circleMap c σ θ, sphere_subset_closedBall (circleMap_mem_sphere c hσ.le θ)⟩
  continuous_toFun := ((continuous_circleMap c σ).comp continuous_subtype_val).subtype_mk _

/-- Circle sampling has operator norm at most one. -/
noncomputable def sampleCircle (c : ℂ) {σ : ℝ} (hσ : 0 < σ) :
    C(Disk c σ, E) →L[ℝ] C(Angles, E) :=
  LinearMap.mkContinuous {
    toFun f := f.comp (circleInput c hσ)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
  } 1 (by
    intro f
    change ‖f.comp (circleInput c hσ)‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using
      (ContinuousMap.norm_le (f.comp (circleInput c hσ)) (norm_nonneg f)).mpr
        (fun θ => f.norm_coe_le_norm _))

/-- Pointwise complex multiplication of a scalar angle path and a vector path. -/
noncomputable def multiplyPaths (k : C(Angles, ℂ)) (v : C(Angles, E)) : C(Angles, E) :=
  ⟨fun θ => k θ • v θ, k.continuous.smul v.continuous⟩

theorem norm_multiplyPaths_le (k : C(Angles, ℂ)) (v : C(Angles, E)) :
    ‖multiplyPaths k v‖ ≤ ‖k‖ * ‖v‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro θ
  change ‖k θ • v θ‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul (k.norm_coe_le_norm _) (v.norm_coe_le_norm _)
    (norm_nonneg _) (norm_nonneg _)

/-- Multiply paths linear, bundling `toFun`, `toFun`, `map_add`, `map_smul` and the required
compatibility proofs. -/
noncomputable def multiplyPathsLinear :
    C(Angles, ℂ) →ₗ[ℝ] C(Angles, E) →ₗ[ℝ] C(Angles, E) where
  toFun k := {
    toFun := multiplyPaths k
    map_add' := by intro f g; ext θ; exact smul_add _ _ _
    map_smul' := by intro r f; ext θ; exact smul_comm _ _ _ }
  map_add' := by intro k l; ext f θ; exact add_smul _ _ _
  map_smul' := by
    intro r k
    ext f θ
    exact smul_assoc r (k θ) (f θ)

/-- A concrete bounded bilinear pairing of continuous contour paths. -/
noncomputable def pathAction :
    C(Angles, ℂ) →L[ℝ] C(Angles, E) →L[ℝ] C(Angles, E) :=
  (multiplyPathsLinear (E := E)).mkContinuous₂
    (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) 1
    (fun k v => by
      change ‖multiplyPaths k v‖ ≤ 1 * ‖k‖ * ‖v‖
      simpa only [one_mul] using norm_multiplyPaths_le k v)

/-- The fixed-circle Cauchy kernel, including the circle's tangent factor. -/
noncomputable def kernel (c : ℂ) (σ : ℝ) (p : ℂ × ℝ) : ℂ :=
  (circleMap 0 σ p.2 * I) * (circleMap c σ p.2 - p.1)⁻¹

theorem contDiffOn_kernel (c : ℂ) (σ : ℝ) :
    ContDiffOn ℝ ∞ (kernel c σ) (ball c σ ×ˢ (univ : Set ℝ)) := by
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => circleMap c σ p.2) :=
    (contDiff_circleMap c σ).comp contDiff_snd
  have ht : ContDiff ℝ ∞ (fun p : ℂ × ℝ => circleMap 0 σ p.2 * I) :=
    ((contDiff_circleMap 0 σ).comp contDiff_snd).mul contDiff_const
  exact ht.contDiffOn.mul ((hc.sub contDiff_fst).contDiffOn.inv
    (fun p hp => sub_ne_zero.mpr (circleMap_ne_mem_ball hp.1 p.2)))

/-- The Cauchy kernel is smooth as a supremum-norm continuous path. -/
noncomputable def kernelPath (c : ℂ) (σ : ℝ) : ℂ → C(Angles, ℂ) :=
  CompactSmoothFamily.family (Icc (0 : ℝ) (2 * Real.pi)) (kernel c σ)

theorem contDiffOn_kernelPath (c : ℂ) (σ : ℝ) :
    ContDiffOn ℝ ∞ (kernelPath c σ) (ball c σ) :=
  CompactSmoothFamily.contDiffOn_family_of_joint (Icc (0 : ℝ) (2 * Real.pi))
    (ball c σ) univ isOpen_ball isOpen_univ (subset_univ _)
    (kernel c σ) (contDiffOn_kernel c σ)

theorem kernelPath_apply (c : ℂ) (σ : ℝ) {z : ℂ} (hz : z ∈ ball c σ) (θ : Angles) :
    kernelPath c σ z θ = (circleMap 0 σ θ * I) * (circleMap c σ θ - z)⁻¹ :=
  CompactSmoothFamily.family_apply_of_joint (Icc (0 : ℝ) (2 * Real.pi)) (subset_univ _)
    (kernel c σ) (contDiffOn_kernel c σ).continuousOn hz θ

/-- Fixed-contour evaluation, defined for every continuous outer-disk input. -/
noncomputable def cauchyValue (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (V : ℝ → C(Disk c σ, E)) (p : ℝ × ℂ) : E :=
  (2 * Real.pi * I : ℂ)⁻¹ • angleIntegral
    (pathAction (E := E) (kernelPath c σ p.2) (sampleCircle c hσ (V p.1)))

/-- Joint smoothness of the actual Cauchy integral follows from bounded
bilinearity and supremum-norm smoothness of its two contour inputs. -/
theorem contDiffOn_cauchyValue (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    {S : Set ℝ} (V : ℝ → C(Disk c σ, E)) (hV : ContDiffOn ℝ ∞ V S) :
    ContDiffOn ℝ ∞ (cauchyValue c hσ V) (S ×ˢ ball c σ) := by
  have hk : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => kernelPath c σ p.2) (S ×ˢ ball c σ) :=
    (contDiffOn_kernelPath c σ).comp contDiffOn_snd (fun p hp => hp.2)
  have hv : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => V p.1) (S ×ˢ ball c σ) :=
    hV.comp contDiffOn_fst (fun p hp => hp.1)
  have hs : ContDiffOn ℝ ∞
      (fun p : ℝ × ℂ => sampleCircle c hσ (V p.1)) (S ×ˢ ball c σ) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := C(Disk c σ, E)) (F := C(Angles, E)) (sampleCircle c hσ)).comp_contDiffOn hv
  have hpa : ContDiff ℝ ∞ (pathAction (E := E)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := C(Angles, ℂ))
      (F := C(Angles, E) →L[ℝ] C(Angles, E)) (pathAction (E := E))
  have hp : ContDiffOn ℝ ∞
      (fun p : ℝ × ℂ => pathAction (E := E) (kernelPath c σ p.2) (sampleCircle c hσ (V p.1)))
      (S ×ˢ ball c σ) :=
    (hpa.comp_contDiffOn hk).clm_apply hs
  exact ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Angles, E)) (F := E) (angleIntegral (E := E))).comp_contDiffOn hp).const_smul _

/-- Continuous disk data supplies the boundary-continuity part of the Cauchy formula. -/
theorem diffContOnCl_of_values (c : ℂ) {σ : ℝ} (v : C(Disk c σ, E)) (F : ℂ → E)
    (hF : DifferentiableOn ℂ F (ball c σ)) (hvalues : ∀ z : Disk c σ, v z = F z) :
    DiffContOnCl ℂ F (ball c σ) := by
  apply DiffContOnCl.mk_ball hF
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert! v.continuous using 1
  funext z
  exact (hvalues z).symm

variable [CompleteSpace E]

/-- The jointly smooth Cauchy expression agrees with every holomorphic slice
represented by the given continuous disk input. -/
theorem cauchyValue_eq (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (V : ℝ → C(Disk c σ, E)) (F : ℝ → ℂ → E) {r : ℝ}
    (hF : DifferentiableOn ℂ (F r) (ball c σ))
    (hvalues : ∀ z : Disk c σ, V r z = F r z) {z : ℂ} (hz : z ∈ ball c σ) :
    cauchyValue c hσ V (r, z) = F r z := by
  have hC := diffContOnCl_of_values c (V r) (F r) hF hvalues
  rw [← hC.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz]
  apply congrArg (fun v : E => (2 * Real.pi * I : ℂ)⁻¹ • v)
  change (∫ θ in (0 : ℝ)..(2 * Real.pi), angleExtend
      (pathAction (E := E) (kernelPath c σ z) (sampleCircle c hσ (V r))) θ) =
    ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap c σ) θ •
      ((circleMap c σ θ - z)⁻¹ • F r (circleMap c σ θ))
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le Real.two_pi_pos.le] at hθ
  have he : angleExtend (pathAction (E := E) (kernelPath c σ z) (sampleCircle c hσ (V r))) θ =
      kernelPath c σ z ⟨θ, hθ⟩ • V r (circleInput c hσ ⟨θ, hθ⟩) := by
    rw [angleExtend, projIcc_of_mem Real.two_pi_pos.le hθ]
    rfl
  rw [he, kernelPath_apply c σ hz, hvalues]
  dsimp only
  rw [deriv_circleMap, mul_smul]
  rfl

/-- A genuine smooth Banach-valued disk family of holomorphic slices is jointly
real smooth throughout the open disk. -/
theorem contDiffOn_of_disk_family (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    {S : Set ℝ} (V : ℝ → C(Disk c σ, E)) (F : ℝ → ℂ → E)
    (hV : ContDiffOn ℝ ∞ V S)
    (hF : ∀ r ∈ S, DifferentiableOn ℂ (F r) (ball c σ))
    (hvalues : ∀ r ∈ S, ∀ z : Disk c σ, V r z = F r z) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => F p.1 p.2) (S ×ˢ ball c σ) := by
  apply (contDiffOn_cauchyValue c hσ V hV).congr
  intro p hp
  exact (cauchyValue_eq c hσ V F (hF p.1 hp.1) (hvalues p.1 hp.1) hp.2).symm

/-- The smaller-disk form used by the Volterra regularity construction. -/
theorem contDiffOn_of_disk_family_smaller (c : ℂ) {ρ σ : ℝ} (hσ : 0 < σ) (hgap : ρ < σ)
    {S : Set ℝ} (V : ℝ → C(Disk c σ, E)) (F : ℝ → ℂ → E)
    (hV : ContDiffOn ℝ ∞ V S)
    (hF : ∀ r ∈ S, DifferentiableOn ℂ (F r) (ball c σ))
    (hvalues : ∀ r ∈ S, ∀ z : Disk c σ, V r z = F r z) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => F p.1 p.2) (S ×ˢ ball c ρ) :=
  (contDiffOn_of_disk_family c hσ V F hV hF hvalues).mono
    (Set.prod_mono Subset.rfl (ball_subset_ball hgap.le))

/-- Real-linear joint derivative: a real radial increment and a complex disk
increment act on the two actual partial derivatives. -/
noncomputable def jointDerivative (a b : E) : ℝ × ℂ →L[ℝ] E :=
  ((1 : ℝ →L[ℝ] ℝ).smulRight a).coprod
    (((1 : ℂ →L[ℂ] ℂ).smulRight b).restrictScalars ℝ)

omit [CompleteSpace E] in
@[simp] theorem jointDerivative_apply (a b : E) (v : ℝ × ℂ) :
    jointDerivative a b v = v.1 • a + v.2 • b := rfl

omit [CompleteSpace E] in
/-- The radial partial derivative is obtained by evaluating the genuine
supremum-norm derivative of the supplied disk curve. -/
theorem hasDerivAt_parameter (c : ℂ) {σ : ℝ} {S : Set ℝ} (hS : IsOpen S)
    (V : ℝ → C(Disk c σ, E)) (F : ℝ → ℂ → E)
    (hV : ContDiffOn ℝ ∞ V S)
    (hvalues : ∀ r ∈ S, ∀ z : Disk c σ, V r z = F r z)
    {r : ℝ} (hr : r ∈ S) (z : Disk c σ) :
    HasDerivAt (fun s => F s z) (deriv V r z) r := by
  have hdV : HasDerivAt V (deriv V r) r :=
    ((hV r hr).contDiffAt (hS.mem_nhds hr)).differentiableAt (by simp) |>.hasDerivAt
  have heval : HasFDerivAt (ContinuousMap.evalCLM ℝ z)
      (ContinuousMap.evalCLM ℝ z) (V r) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := C(Disk c σ, E)) (F := E) (ContinuousMap.evalCLM ℝ z)
  apply (heval.comp_hasDerivAt r hdV).congr_of_eventuallyEq
  filter_upwards [hS.mem_nhds hr] with s hs
  exact (hvalues s hs z).symm

/-- CauchyRestriction's bounded operator is the actual complex partial. -/
theorem hasDerivAt_complex (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (v : C(Disk c σ, E)) (F : ℂ → E)
    (hF : DifferentiableOn ℂ F (ball c σ))
    (hvalues : ∀ z : Disk c σ, v z = F z) (z : Disk c ρ) :
    HasDerivAt F (derivativeCLM c hgap v z) z := by
  rw [derivativeCLM_apply_of_eq c hgap v F (diffContOnCl_of_values c v F hF hvalues) hvalues]
  exact (hF.differentiableAt (isOpen_ball.mem_nhds (z.2.trans_lt hgap))).hasDerivAt

/-- The actual joint Fréchet derivative combines the supremum-norm radial
derivative with the bounded Cauchy differentiation operator. -/
theorem hasFDerivAt_joint (c : ℂ) {ρ σ : ℝ} (hσ : 0 < σ) (hgap : ρ < σ)
    {S : Set ℝ} (hS : IsOpen S) (V : ℝ → C(Disk c σ, E)) (F : ℝ → ℂ → E)
    (hV : ContDiffOn ℝ ∞ V S)
    (hF : ∀ r ∈ S, DifferentiableOn ℂ (F r) (ball c σ))
    (hvalues : ∀ r ∈ S, ∀ z : Disk c σ, V r z = F r z)
    {r : ℝ} (hr : r ∈ S) (z : Disk c ρ) :
    HasFDerivAt (fun p : ℝ × ℂ => F p.1 p.2)
      (jointDerivative (deriv V r ⟨z, closedBall_subset_closedBall hgap.le z.2⟩)
        (derivativeCLM c hgap (V r) z)) (r, (z : ℂ)) := by
  let g : ℝ × ℂ → E := fun p => F p.1 p.2
  let a := deriv V r ⟨z, closedBall_subset_closedBall hgap.le z.2⟩
  let b := derivativeCLM c hgap (V r) z
  let D := fderiv ℝ g (r, (z : ℂ))
  have hz : (z : ℂ) ∈ ball c σ := z.2.trans_lt hgap
  have hg : HasFDerivAt g D (r, (z : ℂ)) :=
    ((contDiffOn_of_disk_family c hσ V F hV hF hvalues (r, (z : ℂ)) ⟨hr, hz⟩).contDiffAt
      ((hS.prod isOpen_ball).mem_nhds ⟨hr, hz⟩)).differentiableAt (by simp) |>.hasFDerivAt
  have ha : HasDerivAt (fun s => F s z) a r :=
    hasDerivAt_parameter c hS V F hV hvalues hr ⟨z, closedBall_subset_closedBall hgap.le z.2⟩
  have hb : HasDerivAt (F r) b (z : ℂ) :=
    hasDerivAt_complex c hgap (V r) (F r) (hF r hr) (hvalues r hr) z
  have hleftD : HasFDerivAt (fun s => F s z) (D.comp (ContinuousLinearMap.inl ℝ ℝ ℂ)) r :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := ℝ) (F := ℝ × ℂ) (G := E)
      (f := fun s : ℝ => (s, (z : ℂ))) (g := g)
      (f' := ContinuousLinearMap.inl ℝ ℝ ℂ) (g' := D) r hg
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) r (z : ℂ))
  have hrightD : HasFDerivAt (F r) (D.comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) (z : ℂ) :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := ℂ) (F := ℝ × ℂ) (G := E)
      (f := fun w : ℂ => (r, w)) (g := g)
      (f' := ContinuousLinearMap.inr ℝ ℝ ℂ) (g' := D) (z : ℂ) hg
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) r (z : ℂ))
  have hleft := hleftD.unique ha.hasFDerivAt
  have hright := hrightD.unique (hb.hasFDerivAt.restrictScalars ℝ)
  have hD : D = jointDerivative a b := by
    apply ContinuousLinearMap.ext
    intro v
    have hl := congrArg (fun L : ℝ →L[ℝ] E => L v.1) hleft
    have hr' := congrArg (fun L : ℂ →L[ℝ] E => L v.2) hright
    change D (v.1, 0) = v.1 • a at hl
    change D (0, v.2) = v.2 • b at hr'
    change D v = v.1 • a + v.2 • b
    calc
      D v = D ((v.1, 0) + (0, v.2)) := by simp only [Prod.mk_add_mk, add_zero, zero_add]
      _ = D (v.1, 0) + D (0, v.2) := map_add D _ _
      _ = v.1 • a + v.2 • b := by rw [hl, hr']
  simpa only [hD] using hg

omit [CompleteSpace E] in
/-- The Cauchy partial has the expected inverse-gap bound. -/
theorem norm_complex_partial_le (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (v : C(Disk c σ, E)) (z : Disk c ρ) :
    ‖derivativeCLM c hgap v z‖ ≤ (σ - ρ)⁻¹ * ‖v‖ := by
  exact ((derivativeCLM c hgap v).norm_coe_le_norm z).trans
    (((derivativeCLM (E := E) c hgap).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_derivativeCLM_le c hgap) (norm_nonneg v)))

omit [CompleteSpace E] in
/-- Real differentiability into a compact-function Banach space upgrades to
complex differentiability when every evaluation has a complex derivative.
The complex linearity is proved by the separating evaluation maps. -/
theorem differentiableAt_of_evaluations {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (G : ℂ → C(K, E)) {z : ℂ} (hG : DifferentiableAt ℝ G z)
    (heval : ∀ x : K, DifferentiableAt ℂ (fun w => G w x) z) :
    DifferentiableAt ℂ G z := by
  let L := fderiv ℝ G z
  let Lc : ℂ →L[ℂ] C(K, E) := (1 : ℂ →L[ℂ] ℂ).smulRight (L 1)
  have hL : Lc.restrictScalars ℝ = L := by
    ext v x
    let T := fderiv ℂ (fun w => G w x) z
    have hEvalMap : HasFDerivAt (ContinuousMap.evalCLM ℝ x)
        (ContinuousMap.evalCLM ℝ x) (G z) :=
      ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := C(K, E)) (F := E)
        (ContinuousMap.evalCLM ℝ x)
    have hreal : HasFDerivAt (fun w => G w x) ((ContinuousMap.evalCLM ℝ x).comp L) z :=
      HasFDerivAt.comp (𝕜 := ℝ) (E := ℂ) (F := C(K, E)) (G := E) z hEvalMap hG.hasFDerivAt
    have hc : HasFDerivAt (fun w => G w x) (T.restrictScalars ℝ) z :=
      (heval x).hasFDerivAt.restrictScalars ℝ
    have heq := hreal.unique hc
    have h1 := congrArg (fun D : ℂ →L[ℝ] E => D 1) heq
    have hv := congrArg (fun D : ℂ →L[ℝ] E => D v) heq
    change L 1 x = T 1 at h1
    change L v x = T v at hv
    change v • L 1 x = L v x
    rw [h1, hv]
    simpa only [smul_eq_mul, mul_one] using (T.map_smul v 1).symm
  exact (hasFDerivAt_of_restrictScalars ℝ (f' := Lc) hG.hasFDerivAt hL).differentiableAt

/-- Joint real smoothness near a compact radial set and holomorphic parameter
slices give genuine complex differentiability of the compact-valued family.
This is the input bridge for compact-family Volterra operators. -/
theorem differentiableOn_family_of_joint {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (K : Set ℝ) [CompactSpace K]
    (U : Set ℂ) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hKV : K ⊆ V)
    (G : ℂ × ℝ → B) (hG : ContDiffOn ℝ ∞ G (U ×ˢ V))
    (hhol : ∀ r ∈ K, DifferentiableOn ℂ (fun z => G (z, r)) U) :
    DifferentiableOn ℂ (CompactSmoothFamily.family (P := ℂ) (Z := ℝ) (E := B) K G) U := by
  have hreal := CompactSmoothFamily.contDiffOn_family_of_joint
    (P := ℂ) (Z := ℝ) (E := B) K U V hU hV hKV G hG
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_of_evaluations (CompactSmoothFamily.family (P := ℂ) (Z := ℝ) (E := B) K G)
    (((hreal z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
  intro x
  have hc := (hhol x x.2).differentiableAt (hU.mem_nhds hz)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hz] with w hw
  exact CompactSmoothFamily.family_apply_of_joint K hKV G hG.continuousOn hw x

end

end NavierStokes.HolomorphicFamily
