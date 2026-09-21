/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Definitions

/-! # Basic Lemmas -/

namespace Homogenization

theorem memLpOn_mono {d : ℕ} {U V : Set (Vec d)} {p : ENNReal} {u : Vec d → ℝ}
    (hVU : V ⊆ U) (hu : MemLpOn U p u) : MemLpOn V p u :=
  hu.mono_measure (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU)

theorem gradMemLpOn_mono {d : ℕ} {U V : Set (Vec d)} {p : ENNReal} {Du : Vec d → Vec d}
    (hVU : V ⊆ U) (hDu : GradMemLpOn U p Du) : GradMemLpOn V p Du := by
  intro i
  exact memLpOn_mono hVU (hDu i)

theorem HasWeakPartialDerivOn.restrict {d : ℕ} {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi := by
  let _ := hVopen
  intro φ hφ_smooth hφ_compact hφ_supp
  have hφ_suppU : tsupport φ ⊆ U := hφ_supp.trans hVU
  have key := h φ hφ_smooth hφ_compact hφ_suppU
  have h1 : ∀ x, x ∉ V → u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_supp hx')
    have hφ_eq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp
  have h2 : ∀ x, x ∉ V → gi x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hφ_supp hx'))]
  have h3 : ∀ x, x ∉ U → u x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    fun x hx => h1 x (fun hx' => hx (hVU hx'))
  have h4 : ∀ x, x ∉ U → gi x * φ x = 0 :=
    fun x hx => h2 x (fun hx' => hx (hVU hx'))
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h2,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h3,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h4,
    key]

theorem HasWeakGradientOn.restrict {d : ℕ} {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := by
  intro i
  exact (h i).restrict hVopen hVU

theorem HasWeakPartialDerivOn.of_contDiff {d : ℕ} {U : Set (Vec d)}
    {i : Fin d} {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDerivOn U i f (fun x => (fderiv ℝ f x) (basisVec i)) := by
  intro φ hφ_smooth hφ_supp hφ_sub
  let ei : Vec d := basisVec i
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
  have hf_cont : Continuous f := hf_diff.continuous
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hfderiv_φ_cont : Continuous (fun x => (fderiv ℝ φ x) ei) := by
    simpa [ei] using
      (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderiv_f_cont : Continuous (fun x => (fderiv ℝ f x) ei) := by
    simpa [ei] using
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ_fderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) := by
    simpa [ei] using hφ_supp.fderiv_apply (𝕜 := ℝ) ei
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simpa [ei] using
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        ((hfderiv_f_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
        ((hf_cont.mul hfderiv_φ_cont).integrable_of_hasCompactSupport hφ_fderiv_supp.mul_left)
        ((hf_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
        (fun x _ => hf_diff.differentiableAt) (fun x _ => hφ_diff.differentiableAt)
  ·
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    simp [image_eq_zero_of_notMem_tsupport hx_notin]
  ·
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    have hφ_eq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp

theorem HasWeakGradientOn.of_contDiff {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakGradientOn U f (fun x i => (fderiv ℝ f x) (basisVec i)) := by
  intro i
  exact HasWeakPartialDerivOn.of_contDiff hf

namespace W1pFunction

@[ext] theorem ext {d : ℕ} {U : Set (Vec d)} {p : ENNReal} {u v : W1pFunction U p}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) : u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl

theorem hasWeakPartialDerivOn {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W1pFunction U p) (i : Fin d) :
    HasWeakPartialDerivOn U i u.toFun (fun x => u.grad x i) :=
  u.hasWeakGradient i

theorem grad_memLp {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W1pFunction U p) (i : Fin d) :
    MemLpOn U p (fun x => u.grad x i) :=
  u.gradMemLp i

theorem memW1p {d : ℕ} {U : Set (Vec d)} {p : ENNReal} (u : W1pFunction U p) :
    MemW1p U p u.toFun :=
  ⟨u, rfl⟩

noncomputable def ofContDiff {d : ℕ} {U : Set (Vec d)} (_hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (hf_supp : HasCompactSupport f)
    (p : ENNReal) : W1pFunction U p :=
  { toFun := f
    grad := fun x i => (fderiv ℝ f x) (basisVec i)
    memLp := by
      have hf_cont : Continuous f := (hf.differentiable (by simp)).continuous
      exact (hf_cont.memLp_of_hasCompactSupport hf_supp).restrict U
    gradMemLp := by
      intro i
      have hderiv_cont : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
        simpa using
          (hf.continuous_fderiv (by simp)).clm_apply continuous_const
      have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i)) := by
        simpa using hf_supp.fderiv_apply (𝕜 := ℝ) (basisVec i)
      exact (hderiv_cont.memLp_of_hasCompactSupport hderiv_supp).restrict U
    hasWeakGradient := HasWeakGradientOn.of_contDiff hf }

/-- Package a globally smooth function as a `W^{1,p}(U)` witness on a bounded
measurable domain. Unlike `ofContDiff`, this constructor does not require
compact support, because boundedness of `U` gives the needed `L^p` control on
the restriction. -/
noncomputable def ofContDiffOnIsSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} {p : ENNReal} (hU : IsSobolevRegularDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) : W1pFunction U p := by
  letI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) := by
    simpa using hU.isFiniteMeasure_restrict_volume
  classical
  have hf_cont : Continuous f := (hf.differentiable (by simp)).continuous
  have hclosure_compact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  let Cf : ℝ := Classical.choose (hclosure_compact.exists_bound_of_continuousOn hf_cont.continuousOn)
  have hCf : ∀ x ∈ closure U, ‖f x‖ ≤ Cf :=
    Classical.choose_spec (hclosure_compact.exists_bound_of_continuousOn hf_cont.continuousOn)
  refine
    { toFun := f
      grad := fun x i => (fderiv ℝ f x) (basisVec i)
      memLp := ?_
      gradMemLp := ?_
      hasWeakGradient := HasWeakGradientOn.of_contDiff hf }
  · refine MeasureTheory.MemLp.of_bound
      (μ := MeasureTheory.volume.restrict U) hf_cont.aestronglyMeasurable Cf ?_
    rw [MeasureTheory.ae_restrict_iff' hU.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hCf x (subset_closure hx)
  · intro i
    have hderiv_cont : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
      simpa using
        (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    let CD : ℝ :=
      Classical.choose (hclosure_compact.exists_bound_of_continuousOn hderiv_cont.continuousOn)
    have hCD : ∀ x ∈ closure U, ‖(fderiv ℝ f x) (basisVec i)‖ ≤ CD :=
      Classical.choose_spec
        (hclosure_compact.exists_bound_of_continuousOn hderiv_cont.continuousOn)
    refine MeasureTheory.MemLp.of_bound
      (μ := MeasureTheory.volume.restrict U) hderiv_cont.aestronglyMeasurable CD ?_
    rw [MeasureTheory.ae_restrict_iff' hU.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hCD x (subset_closure hx)

/-- Bounded open convex domains admit the bounded-domain smooth constructor for
`W^{1,p}`. -/
noncomputable def ofContDiffOnIsOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p : ENNReal} (hU : IsOpenBoundedConvexDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) : W1pFunction U p :=
  ofContDiffOnIsSobolevRegularDomain hU.isSobolevRegularDomain hf

def restrict {d : ℕ} {U V : Set (Vec d)} {p : ENNReal} (u : W1pFunction U p)
    (hVopen : IsOpen V) (hVU : V ⊆ U) : W1pFunction V p :=
  { toFun := u.toFun
    grad := u.grad
    memLp := memLpOn_mono hVU u.memLp
    gradMemLp := gradMemLpOn_mono hVU u.gradMemLp
    hasWeakGradient := u.hasWeakGradient.restrict hVopen hVU }

/-- Upgrade a `W^{1,p}` witness to `W^{1,p}_0` from an explicit supported
smooth approximation package. This is the final zero-trace packaging target:
the support data is an input, not a consequence of domain convexity alone. -/
def toW10pFunction {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W1pFunction U p) (happrox : u.SupportedSmoothApproximation) :
    W10pFunction U p :=
  { toW1pFunction := u
    approx := happrox.approx
    approx_smooth := happrox.approx_smooth
    approx_hasCompactSupport := happrox.approx_hasCompactSupport
    approx_support_subset := happrox.approx_support_subset
    tendsto_approx := happrox.tendsto_approx
    tendsto_approx_grad := happrox.tendsto_approx_grad }

theorem memW10p_of_supportedSmoothApproximation {d : ℕ} {U : Set (Vec d)}
    {p : ENNReal} (u : W1pFunction U p)
    (happrox : u.SupportedSmoothApproximation) :
    MemW10p U p u.toFun :=
  ⟨u.toW10pFunction happrox, rfl⟩

theorem memW10p_of_hasSupportedSmoothApproximation {d : ℕ} {U : Set (Vec d)}
    {p : ENNReal} (u : W1pFunction U p)
    (happrox : u.HasSupportedSmoothApproximation) :
    MemW10p U p u.toFun := by
  rcases happrox with ⟨happrox⟩
  exact u.memW10p_of_supportedSmoothApproximation happrox

end W1pFunction

namespace W10pFunction

theorem memW1p {d : ℕ} {U : Set (Vec d)} {p : ENNReal} (u : W10pFunction U p) :
    MemW1p U p u.toW1pFunction.toFun :=
  u.toW1pFunction.memW1p

noncomputable def ofContDiff {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (hf_sub : tsupport f ⊆ U)
    (p : ENNReal) : W10pFunction U p :=
  { toW1pFunction := W1pFunction.ofContDiff hU (hf.of_le (by simp)) hf_supp p
    approx := fun _ => f
    approx_smooth := by
      intro n
      simpa using hf
    approx_hasCompactSupport := by
      intro n
      simpa using hf_supp
    approx_support_subset := by
      intro n
      simpa using hf_sub
    tendsto_approx := by
      simp [W1pFunction.ofContDiff]
    tendsto_approx_grad := by
      intro i
      simp [W1pFunction.ofContDiff] }

theorem memW10p {d : ℕ} {U : Set (Vec d)} {p : ENNReal} (u : W10pFunction U p) :
    MemW10p U p u.toW1pFunction.toFun :=
  ⟨u, rfl⟩

/-- Every bundled `W10pFunction` exposes its supported smooth approximation
data for the underlying `W1pFunction`. -/
def supportedSmoothApproximation {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W10pFunction U p) :
    u.toW1pFunction.SupportedSmoothApproximation :=
  { approx := u.approx
    approx_smooth := u.approx_smooth
    approx_hasCompactSupport := u.approx_hasCompactSupport
    approx_support_subset := u.approx_support_subset
    tendsto_approx := u.tendsto_approx
    tendsto_approx_grad := u.tendsto_approx_grad }

theorem hasSupportedSmoothApproximation {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W10pFunction U p) :
    u.toW1pFunction.HasSupportedSmoothApproximation :=
  ⟨u.supportedSmoothApproximation⟩

end W10pFunction

theorem memW1p_of_memW10p {d : ℕ} {U : Set (Vec d)} {p : ENNReal} {u : Vec d → ℝ}
    (hu : MemW10p U p u) : MemW1p U p u := by
  rcases hu with ⟨v, rfl⟩
  exact v.memW1p

theorem memW1p_of_contDiffOnIsSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} {p : ENNReal} (hU : IsSobolevRegularDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    MemW1p U p f :=
  by
    simpa using!
      (W1pFunction.ofContDiffOnIsSobolevRegularDomain (U := U) (p := p) hU hf).memW1p

theorem memW1p_of_contDiffOnIsOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p : ENNReal} (hU : IsOpenBoundedConvexDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    MemW1p U p f :=
  by
    simpa using!
      (W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (U := U) (p := p) hU hf).memW1p

theorem memW1p_restrict {d : ℕ} {U V : Set (Vec d)} {p : ENNReal} {u : Vec d → ℝ}
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hu : MemW1p U p u) : MemW1p V p u := by
  rcases hu with ⟨u', rfl⟩
  exact (u'.restrict hVopen hVU).memW1p

end Homogenization
