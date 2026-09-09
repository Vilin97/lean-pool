/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialEmbedding
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual constant-angle embedding preserves the closed gradient
spaces.  Compact ordinary scalar tests give compact cylinder scalar tests,
and the bounded embedding carries their closures into one another. -/

@[expose] public section


noncomputable section

namespace EulerCylinderSpatialEmbedding

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

/-- Scalar lift, defined pointwise by `φ z.1`. -/
def scalarLift (φ : Space → ℝ) : LiftDomain P → ℝ := fun z => φ z.1

theorem scalarLift_compact (φ : Space → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (scalarLift P φ) := by
  apply HasCompactSupport.intro (hφ.prod (isCompact_univ : IsCompact (univ : Set (AddCircle P))))
  intro z hz
  change φ z.1 = 0
  exact image_eq_zero_of_notMem_tsupport (by simpa only [mem_prod,mem_univ,and_true] using hz)

omit [Fact (0 < P)] in
theorem scalarLift_smooth (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : LiftDomain P) :
    ContDiff ℝ ∞ (localLift P (scalarLift P φ) z) :=
  hφ.comp (contDiff_const.add contDiff_fst)

theorem gradient_component (φ : Space → ℝ) (x : Space) (i : Fin 3) :
    gradient φ x i = fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  have h := toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i 1) (y := fderiv ℝ φ x)
  simpa only [gradient,EuclideanSpace.inner_single_right,conj_trivial,one_mul] using h

omit [Fact (0 < P)] in
theorem scalarLift_gradient (κ : ℝ) (m : Space) (φ : Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (z : LiftDomain P) :
    liftedGradient P κ m (scalarLift P φ) z = κ • gradient φ z.1 := by
  have hh : HasFDerivAt (fun y : LiftTangent => z.1+y.1) (fst ℝ Space ℝ) 0 :=
    hasFDerivAt_fst.const_add z.1
  have hf : HasFDerivAt φ (fderiv ℝ φ z.1) (z.1+(0 : LiftTangent).1) := by
    simpa only [Prod.fst_zero,add_zero] using ((hφ.differentiable (by simp)) z.1).hasFDerivAt
  have h := hf.comp (0 : LiftTangent) hh
  have hd : fderiv ℝ (localLift P (scalarLift P φ) z) 0 =
      (fderiv ℝ φ z.1).comp (fst ℝ Space ℝ) := by
    convert! h.fderiv using 1
  ext i
  change κ * (fderiv ℝ (localLift P (scalarLift P φ) z) 0) (EuclideanSpace.single i 1,0) +
    m i * (fderiv ℝ (localLift P (scalarLift P φ) z) 0) (0,1) = κ * gradient φ z.1 i
  rw [hd,gradient_component]
  change κ * fderiv ℝ φ z.1 (EuclideanSpace.single i 1) + m i * fderiv ℝ φ z.1 0 = _
  rw [map_zero,mul_zero,add_zero]

theorem smul_embedding_gradient_mem (κ : ℝ) (m : Space)
    (g : EulerMeanSolenoidal.L2) (hg : g ∈ EulerMeanSolenoidal.gradientSpace) :
    κ • embedding P g ∈ gradientSpace P κ m := by
  let L : EulerMeanSolenoidal.L2 →L[ℝ] LiftL2 P := κ • embedding P
  let K := (gradientSpace P κ m).comap L.toLinearMap
  have hgen : Submodule.span ℝ EulerMeanSolenoidal.gradientGenerators ≤ K := by
    apply Submodule.span_le.mpr
    rintro u ⟨φ,hφc,hφs,hu⟩
    change κ • embedding P u ∈ gradientSpace P κ m
    apply testGradient_mem P κ m
    refine ⟨scalarLift P φ,⟨scalarLift_compact P φ hφc,scalarLift_smooth P φ hφs⟩,?_⟩
    filter_upwards [Lp.coeFn_smul κ (embedding P u),lift_ae P u,
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
        (ν := (volume : Measure (AddCircle P)))).ae hu] with z hs hl hz
    change (κ • embedding P u) z = _
    rw [hs]
    change κ • embedding P u z = _
    rw [show embedding P u z = u z.1 from hl,hz,scalarLift_gradient P κ m φ hφs]
  have hclosed : IsClosed (K : Set EulerMeanSolenoidal.L2) :=
    (gradientSpace_closed P κ m).preimage L.continuous
  exact ((Submodule.span ℝ EulerMeanSolenoidal.gradientGenerators).topologicalClosure_minimal
    hgen hclosed) hg

theorem embedding_gradient_mem (κ : ℝ) (hκ : κ ≠ 0) (m : Space)
    (g : EulerMeanSolenoidal.L2) (hg : g ∈ EulerMeanSolenoidal.gradientSpace) :
    embedding P g ∈ gradientSpace P κ m := by
  have h := (gradientSpace P κ m).smul_mem κ⁻¹ (smul_embedding_gradient_mem P κ m g hg)
  simpa only [smul_smul,inv_mul_cancel₀ hκ,one_smul] using h

end EulerCylinderSpatialEmbedding
