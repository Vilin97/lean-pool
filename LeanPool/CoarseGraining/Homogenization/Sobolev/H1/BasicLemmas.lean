/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
public import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedNorms
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Definitions
public import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Basic Lemmas -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

theorem memL2On_mono {d : ℕ} {U V : Set (Vec d)} {u : Vec d → ℝ}
    (hVU : V ⊆ U) (hu : MemL2On U u) : MemL2On V u :=
  hu.mono_measure (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU)

theorem gradMemL2On_mono {d : ℕ} {U V : Set (Vec d)} {Du : Vec d → Vec d}
    (hVU : V ⊆ U) (hDu : GradMemL2On U Du) : GradMemL2On V Du := by
  intro i
  exact memL2On_mono hVU (hDu i)

theorem memL2On_openCubeSet_normalizedCubeMeasure {d : ℕ} {Q : TriadicCube d}
    {u : Vec d → ℝ} (hu : MemL2On (openCubeSet Q) u) :
    MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hcube : MeasureTheory.MemLp u (2 : ℝ≥0∞) (cubeMeasure Q) := by
    simpa [MemL2On, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using hu
  simpa [normalizedCubeMeasure] using
    hcube.smul_measure ENNReal.ofReal_ne_top

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

namespace H1Function

@[ext] theorem ext {d : ℕ} {U : Set (Vec d)} {u v : H1Function U}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) : u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl

theorem hasWeakPartialDerivOn {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (i : Fin d) :
    HasWeakPartialDerivOn U i u.toFun (fun x => u.grad x i) :=
  u.hasWeakGradient i

theorem grad_memL2 {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (i : Fin d) :
    MemL2On U (fun x => u.grad x i) :=
  u.gradMemL2 i

theorem grad_memVectorL2 {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    MemVectorL2 U u.grad := by
  simpa [MemVectorL2, volumeMeasureOn] using
    (MeasureTheory.MemLp.of_eval (fun i : Fin d => u.gradMemL2 i))

theorem memL2_normalizedCubeMeasure {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) :
    MeasureTheory.MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
  memL2On_openCubeSet_normalizedCubeMeasure u.memL2

theorem grad_memL2_normalizedCubeMeasure {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (i : Fin d) :
    MeasureTheory.MemLp (fun x => u.grad x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
  memL2On_openCubeSet_normalizedCubeMeasure (u.grad_memL2 i)

theorem memH1 {d : ℕ} {U : Set (Vec d)} (u : H1Function U) : MemH1 U u.toFun :=
  ⟨u, rfl⟩

noncomputable def ofContDiff {d : ℕ} {U : Set (Vec d)} (_hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (hf_supp : HasCompactSupport f) : H1Function U :=
  { toFun := f
    grad := fun x i => (fderiv ℝ f x) (basisVec i)
    memL2 := by
      have hf_cont : Continuous f := (hf.differentiable (by simp)).continuous
      exact (hf_cont.memLp_of_hasCompactSupport hf_supp).restrict U
    gradMemL2 := by
      intro i
      have hderiv_cont : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
        simpa using
          (hf.continuous_fderiv (by simp)).clm_apply continuous_const
      have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i)) := by
        simpa using hf_supp.fderiv_apply (𝕜 := ℝ) (basisVec i)
      exact (hderiv_cont.memLp_of_hasCompactSupport hderiv_supp).restrict U
    hasWeakGradient := HasWeakGradientOn.of_contDiff hf }

/-- Package a globally smooth function as an `H¹(U)` witness on a bounded
measurable domain. Unlike `ofContDiff`, this constructor does not require
compact support, because boundedness of `U` gives the needed `L²` control on
the restriction. -/
noncomputable def ofContDiffOnIsSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) : H1Function U := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  classical
  have hf_cont : Continuous f := (hf.differentiable (by simp)).continuous
  have hclosure_compact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  let Cf : ℝ := Classical.choose (hclosure_compact.exists_bound_of_continuousOn hf_cont.continuousOn)
  have hCf : ∀ x ∈ closure U, ‖f x‖ ≤ Cf :=
    Classical.choose_spec (hclosure_compact.exists_bound_of_continuousOn hf_cont.continuousOn)
  refine
    { toFun := f
      grad := fun x i => (fderiv ℝ f x) (basisVec i)
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := HasWeakGradientOn.of_contDiff hf }
  · refine MeasureTheory.MemLp.of_bound
      (μ := volumeMeasureOn U) hf_cont.aestronglyMeasurable Cf ?_
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
      (μ := volumeMeasureOn U) hderiv_cont.aestronglyMeasurable CD ?_
    rw [MeasureTheory.ae_restrict_iff' hU.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hCD x (subset_closure hx)

/-- Bounded open convex domains admit the bounded-domain smooth constructor for
`H¹`. -/
noncomputable def ofContDiffOnIsOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) : H1Function U :=
  ofContDiffOnIsSobolevRegularDomain hU.isSobolevRegularDomain hf

def restrict {d : ℕ} {U V : Set (Vec d)} (u : H1Function U)
    (hVopen : IsOpen V) (hVU : V ⊆ U) : H1Function V :=
  { toFun := u.toFun
    grad := u.grad
    memL2 := memL2On_mono hVU u.memL2
    gradMemL2 := gradMemL2On_mono hVU u.gradMemL2
    hasWeakGradient := u.hasWeakGradient.restrict hVopen hVU }

noncomputable def restrictToOpenSubcube {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (u : H1Function (openCubeSet Q)) (hR : R ∈ descendantsAtDepth Q j) :
    H1Function (openCubeSet R) :=
  u.restrict (isOpen_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)

@[simp] theorem restrictToOpenSubcube_toFun {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (u : H1Function (openCubeSet Q)) (hR : R ∈ descendantsAtDepth Q j) :
    (u.restrictToOpenSubcube hR).toFun = u.toFun :=
  rfl

@[simp] theorem restrictToOpenSubcube_grad {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (u : H1Function (openCubeSet Q)) (hR : R ∈ descendantsAtDepth Q j) :
    (u.restrictToOpenSubcube hR).grad = u.grad :=
  rfl

theorem grad_memL2_normalizedCubeMeasure_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (u : H1Function (openCubeSet Q)) (hR : R ∈ descendantsAtDepth Q j) (i : Fin d) :
    MeasureTheory.MemLp (fun x => u.grad x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
  simpa using (u.restrictToOpenSubcube hR).grad_memL2_normalizedCubeMeasure i

end H1Function

namespace H10Function

theorem memH1 {d : ℕ} {U : Set (Vec d)} (u : H10Function U) : MemH1 U u.toH1Function.toFun :=
  u.toH1Function.memH1

noncomputable def ofContDiff {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (hf_sub : tsupport f ⊆ U) : H10Function U :=
  { toH1Function := H1Function.ofContDiff hU (hf.of_le (by simp)) hf_supp
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
      simp [H1Function.ofContDiff]
    tendsto_approx_grad := by
      intro i
      simp [H1Function.ofContDiff] }

end H10Function

theorem memH1_of_memH10 {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} (hu : MemH10 U u) :
    MemH1 U u := by
  rcases hu with ⟨v, rfl⟩
  exact v.memH1

theorem memH1_restrict {d : ℕ} {U V : Set (Vec d)} {u : Vec d → ℝ}
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hu : MemH1 U u) : MemH1 V u := by
  rcases hu with ⟨u', rfl⟩
  exact (u'.restrict hVopen hVU).memH1

theorem H10Function.memH10 {d : ℕ} {U : Set (Vec d)} (u : H10Function U) :
    MemH10 U u.toH1Function.toFun :=
  ⟨u, rfl⟩

theorem memH10_of_contDiff {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (hf_sub : tsupport f ⊆ U) :
    MemH10 U f :=
  (H10Function.ofContDiff hU hf hf_supp hf_sub).memH10

theorem memH1_of_contDiffOnIsSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    MemH1 U f :=
  by
    simpa using!
      (H1Function.ofContDiffOnIsSobolevRegularDomain (U := U) hU hf).memH1

theorem memH1_of_contDiffOnIsOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    MemH1 U f :=
  by
    simpa using!
      (H1Function.ofContDiffOnIsOpenBoundedConvexDomain (U := U) hU hf).memH1

end Homogenization
