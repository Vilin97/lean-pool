/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Graph

/-! # Coercive Hilbert -/

namespace Homogenization

open scoped RealInnerProductSpace

section CoerciveHilbert

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- The canonical complete Hilbert carrier for the mean-zero coercive `H¹`
layer: the closed mean-zero weak-gradient graph inside
`L²(U) × L²(U; HilbertVec d)`. -/
noncomputable abbrev H1CoerciveHilbertAmbient :=
  WithLp 2 (ScalarL2 U × HilbertVectorL2 U)

noncomputable abbrev h1CoerciveHilbertAmbientEquiv :
    H1CoerciveHilbertAmbient (U := U) ≃L[ℝ] ScalarL2 U × HilbertVectorL2 U :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (ScalarL2 U) (HilbertVectorL2 U)

noncomputable abbrev h1CoerciveHilbertClosedSubmodule :
    ClosedSubmodule ℝ (H1CoerciveHilbertAmbient (U := U)) :=
  (h1MeanZeroGraphClosedSubmodule (U := U)).comap
    (h1CoerciveHilbertAmbientEquiv (U := U)).toContinuousLinearMap

noncomputable abbrev h1CoerciveHilbertSubmodule :
    Submodule ℝ (H1CoerciveHilbertAmbient (U := U)) :=
  (h1CoerciveHilbertClosedSubmodule (U := U)).toSubmodule

noncomputable abbrev H1CoerciveHilbertSpace :=
  ↥(h1CoerciveHilbertSubmodule (U := U))

namespace H1CoerciveHilbert

noncomputable instance : SeminormedAddCommGroup (H1CoerciveHilbertSpace (U := U)) := by
  exact inferInstanceAs (SeminormedAddCommGroup (h1CoerciveHilbertSubmodule (U := U)))

noncomputable instance : NormedAddCommGroup (H1CoerciveHilbertSpace (U := U)) := by
  exact inferInstanceAs (NormedAddCommGroup (h1CoerciveHilbertSubmodule (U := U)))

noncomputable instance : NormedSpace ℝ (H1CoerciveHilbertSpace (U := U)) := by
  exact inferInstanceAs (NormedSpace ℝ (h1CoerciveHilbertSubmodule (U := U)))

noncomputable instance : InnerProductSpace ℝ (H1CoerciveHilbertSpace (U := U)) := by
  exact inferInstanceAs (InnerProductSpace ℝ (h1CoerciveHilbertSubmodule (U := U)))

noncomputable instance : CompleteSpace (H1CoerciveHilbertSpace (U := U)) := by
  simpa [H1CoerciveHilbertSpace, h1CoerciveHilbertSubmodule, h1CoerciveHilbertClosedSubmodule] using!
    (h1CoerciveHilbertClosedSubmodule (U := U)).isClosed.completeSpace_coe

/-- The scalar `L²(U)` value component of a point in the coercive Hilbert
graph. -/
abbrev value (z : H1CoerciveHilbertSpace (U := U)) : ScalarL2 U :=
  z.1.fst

/-- The Hilbert-vector `L²(U)` gradient component of a point in the coercive
Hilbert graph. -/
abbrev gradient (z : H1CoerciveHilbertSpace (U := U)) : HilbertVectorL2 U :=
  z.1.snd

/-- The scalar-value projection from the coercive Hilbert graph. -/
noncomputable def valueCLM : H1CoerciveHilbertSpace (U := U) →L[ℝ] ScalarL2 U :=
  (WithLp.fstL (p := 2) (𝕜 := ℝ) (α := ScalarL2 U) (β := HilbertVectorL2 U)).comp
    (h1CoerciveHilbertSubmodule (U := U)).subtypeL

@[simp] theorem valueCLM_apply (z : H1CoerciveHilbertSpace (U := U)) :
    valueCLM (U := U) z = value (U := U) z :=
  rfl

/-- The gradient projection from the coercive Hilbert graph. -/
noncomputable def gradientCLM : H1CoerciveHilbertSpace (U := U) →L[ℝ] HilbertVectorL2 U :=
  (WithLp.sndL (p := 2) (𝕜 := ℝ) (α := ScalarL2 U) (β := HilbertVectorL2 U)).comp
    (h1CoerciveHilbertSubmodule (U := U)).subtypeL

@[simp] theorem gradientCLM_apply (z : H1CoerciveHilbertSpace (U := U)) :
    gradientCLM (U := U) z = gradient (U := U) z :=
  rfl

/-- The gradient-energy bilinear form on the coercive Hilbert graph. -/
noncomputable def gradientBilin :
    H1CoerciveHilbertSpace (U := U) →L[ℝ] H1CoerciveHilbertSpace (U := U) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (gradientCLM (U := U)) (gradientCLM (U := U))

@[simp] theorem gradientBilin_apply
    (z w : H1CoerciveHilbertSpace (U := U)) :
    gradientBilin (U := U) z w = inner ℝ (gradient (U := U) z) (gradient (U := U) w) := by
  simp [gradientBilin, ContinuousLinearMap.bilinearComp_apply, gradient]

/-- The forcing functional `z ↦ ⟪f, ∇z⟫` on the coercive Hilbert graph. -/
noncomputable def forcingFunctionalCLM {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    H1CoerciveHilbertSpace (U := U) →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
      (Homogenization.toHilbertVectorL2OfVecField hf)).comp
    (gradientCLM (U := U))

@[simp] theorem forcingFunctionalCLM_apply {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (z : H1CoerciveHilbertSpace (U := U)) :
    forcingFunctionalCLM (U := U) hf z =
      inner ℝ (Homogenization.toHilbertVectorL2OfVecField hf) (gradient (U := U) z) := by
  simp only [forcingFunctionalCLM, ContinuousLinearMap.comp_apply, gradientCLM_apply]
  rfl

/-- The scalar forcing functional `z ↦ ⟪F, z⟫` on the coercive Hilbert graph. -/
noncomputable def scalarForcingFunctionalCLM {F : Vec d → ℝ}
    (hF : MemScalarL2 U F) :
    H1CoerciveHilbertSpace (U := U) →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (ScalarL2 U) (Homogenization.toScalarL2 hF)).comp
    (valueCLM (U := U))

@[simp] theorem scalarForcingFunctionalCLM_apply {F : Vec d → ℝ}
    (hF : MemScalarL2 U F) (z : H1CoerciveHilbertSpace (U := U)) :
    scalarForcingFunctionalCLM (U := U) hF z =
      inner ℝ (Homogenization.toScalarL2 hF) (value (U := U) z) := by
  simp only [scalarForcingFunctionalCLM, ContinuousLinearMap.comp_apply, valueCLM_apply]
  rfl

/-- The Riesz representative of the forcing functional on the coercive Hilbert
graph. -/
noncomputable def forcingRieszMap :
    (H1CoerciveHilbertSpace (U := U) →L[ℝ] ℝ) → H1CoerciveHilbertSpace (U := U) :=
  fun ℓ => (InnerProductSpace.toDual ℝ (H1CoerciveHilbertSpace (U := U))).symm ℓ

@[simp] theorem inner_forcingRieszMap_apply
    (ℓ : H1CoerciveHilbertSpace (U := U) →L[ℝ] ℝ)
    (z : H1CoerciveHilbertSpace (U := U)) :
    inner ℝ (forcingRieszMap (U := U) ℓ) z = ℓ z := by
  change inner ℝ
      (((InnerProductSpace.toDual ℝ (H1CoerciveHilbertSpace (U := U))).symm) ℓ) z = ℓ z
  exact
    InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ)
      (E := H1CoerciveHilbertSpace (U := U))
      (x := z)
      (y := (ℓ : StrongDual ℝ (H1CoerciveHilbertSpace (U := U))))

/-- The Riesz representative of the forcing functional on the coercive Hilbert
graph. -/
noncomputable def forcingRieszRep {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    H1CoerciveHilbertSpace (U := U) :=
  forcingRieszMap (U := U) (forcingFunctionalCLM (U := U) hf)

@[simp] theorem inner_forcingRieszRep_apply {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (z : H1CoerciveHilbertSpace (U := U)) :
    inner ℝ (forcingRieszRep (U := U) hf) z =
      forcingFunctionalCLM (U := U) hf z := by
  exact inner_forcingRieszMap_apply (U := U) (forcingFunctionalCLM (U := U) hf) z

/-- Recover the mean-zero `H¹` witness represented by a point of the coercive
Hilbert graph. -/
noncomputable def toH1MeanZeroFunction
    (z : H1CoerciveHilbertSpace (U := U)) : H1MeanZeroFunction U := by
  let zp : ScalarL2 U × HilbertVectorL2 U :=
    (h1CoerciveHilbertAmbientEquiv (U := U)) z.1
  have hzp :
      zp ∈ h1MeanZeroGraphClosedSubmodule (U := U) := by
    exact (ClosedSubmodule.mem_comap).1 z.2
  let hzGraph :
      zp ∈ h1GraphClosedSubmodule (U := U) :=
    (mem_h1MeanZeroGraphClosedSubmodule_iff (U := U) zp).mp hzp |>.1
  let u : H1Function U := toH1FunctionOfMemH1Graph (U := U) zp hzGraph
  have hmean : MeanZeroOn U u.toFun := by
    have hzMean :
        scalarIntegralCLM (U := U) zp.1 = 0 :=
      (mem_h1MeanZeroGraphClosedSubmodule_iff (U := U) zp).mp hzp |>.2
    show ∫ x in U, u x ∂MeasureTheory.volume = 0
    calc
      ∫ x in U, u x ∂MeasureTheory.volume = scalarIntegralCLM (U := U) u.toScalarL2 := by
            symm
            calc
              scalarIntegralCLM (U := U) u.toScalarL2
                  = ∫ x in U, u.toScalarL2 x ∂MeasureTheory.volume := by
                      exact scalarIntegralCLM_apply (U := U) u.toScalarL2
              _ = ∫ x in U, u x ∂MeasureTheory.volume := by
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards [u.coeFn_toScalarL2] with x hu
                    rw [hu]
      _ = scalarIntegralCLM (U := U) zp.1 := by
            have huScalar : u.toScalarL2 = zp.1 := by
              unfold u
              exact toH1FunctionOfMemH1Graph_toScalarL2 (U := U) zp hzGraph
            rw [huScalar]
      _ = 0 := by exact hzMean
  exact ⟨u, hmean⟩

@[simp] theorem toH1MeanZeroFunction_toScalarL2
    (z : H1CoerciveHilbertSpace (U := U)) :
    (toH1MeanZeroFunction (U := U) z).toScalarL2 = value (U := U) z := by
  simp only [toH1MeanZeroFunction, value, H1MeanZeroFunction.toScalarL2,
    toH1FunctionOfMemH1Graph_toScalarL2]
  rfl

@[simp] theorem toH1MeanZeroFunction_gradToHilbertVectorL2
    (z : H1CoerciveHilbertSpace (U := U)) :
    (toH1MeanZeroFunction (U := U) z).gradToHilbertVectorL2 = gradient (U := U) z := by
  simp only [toH1MeanZeroFunction, gradient, H1MeanZeroFunction.gradToHilbertVectorL2,
    toH1FunctionOfMemH1Graph_gradToHilbertVectorL2]
  rfl

theorem norm_value_le_constant_mul_norm_gradient
    (hC : H1CoerciveEstimate U) (z : H1CoerciveHilbertSpace (U := U)) :
    ‖value (U := U) z‖ ≤ hC.fixedValue * ‖gradient (U := U) z‖ := by
  let u : H1MeanZeroFunction U := toH1MeanZeroFunction (U := U) z
  calc
    ‖value (U := U) z‖ = u.valueL2Norm := by
          rw [H1MeanZeroFunction.valueL2Norm]
          have huValue : u.toScalarL2 = value (U := U) z := by
            unfold u
            exact toH1MeanZeroFunction_toScalarL2 (U := U) z
          rw [huValue]
    _ ≤ hC.fixedValue * u.gradientL2Norm := hC.bound u
    _ ≤ hC.fixedValue * ‖u.gradToHilbertVectorL2‖ := by
          exact mul_le_mul_of_nonneg_left
            (H1MeanZeroFunction.gradientL2Norm_le_norm_gradToHilbertVectorL2 (d := d) u)
            hC.constant_nonneg
    _ = hC.fixedValue * ‖gradient (U := U) z‖ := by
          have huGrad : u.gradToHilbertVectorL2 = gradient (U := U) z := by
            unfold u
            exact toH1MeanZeroFunction_gradToHilbertVectorL2 (U := U) z
          rw [huGrad]

theorem norm_le_max_constant_one_mul_norm_gradient
    (hC : H1CoerciveEstimate U) (z : H1CoerciveHilbertSpace (U := U)) :
    ‖z‖ ≤ (hC.fixedValue + 1) * ‖gradient (U := U) z‖ := by
  let a : ℝ := ‖value (U := U) z‖
  let b : ℝ := ‖gradient (U := U) z‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hval : a ≤ hC.fixedValue * b := by
    exact norm_value_le_constant_mul_norm_gradient (d := d) (U := U) hC z
  have hnorm :
      ‖z‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
    calc
      ‖z‖ = ‖(z : H1CoerciveHilbertAmbient (U := U))‖ := by rfl
      _ = Real.sqrt (‖z.1.fst‖ ^ 2 + ‖z.1.snd‖ ^ 2) := by
            exact WithLp.prod_norm_eq_of_L2 (x := z.1)
      _ = Real.sqrt (a ^ 2 + b ^ 2) := by
            rw [show a = ‖z.1.fst‖ by rfl, show b = ‖z.1.snd‖ by rfl]
  have hsqrt_le : Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b := by
    refine Real.sqrt_le_iff.mpr ?_
    constructor
    · positivity
    · nlinarith [ha, hb]
  calc
    ‖z‖ = Real.sqrt (a ^ 2 + b ^ 2) := hnorm
    _ ≤ a + b := hsqrt_le
    _ ≤ (hC.fixedValue + 1) * b := by
          nlinarith [hval, hb, hC.constant_nonneg]

theorem isCoercive_gradientBilin
    (hC : H1CoerciveEstimate U) :
    IsCoercive (gradientBilin (U := U)) := by
  let M : ℝ := hC.fixedValue + 1
  have hM_pos : 0 < M := by
    linarith [hC.constant_nonneg]
  refine ⟨M⁻¹ * M⁻¹, by positivity, ?_⟩
  intro z
  have hbound : ‖z‖ ≤ M * ‖gradient (U := U) z‖ := by
    exact norm_le_max_constant_one_mul_norm_gradient (d := d) (U := U) hC z
  have hscaled : M⁻¹ * ‖z‖ ≤ ‖gradient (U := U) z‖ := by
    calc
      M⁻¹ * ‖z‖ ≤ M⁻¹ * (M * ‖gradient (U := U) z‖) := by
            gcongr
      _ = ‖gradient (U := U) z‖ := by
            rw [← mul_assoc, inv_mul_cancel₀ hM_pos.ne', one_mul]
  have hsq : (M⁻¹ * ‖z‖) ^ 2 ≤ ‖gradient (U := U) z‖ ^ 2 := by
    have hleft_nonneg : 0 ≤ M⁻¹ * ‖z‖ := by
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt hM_pos)) (norm_nonneg _)
    have hright_nonneg : 0 ≤ ‖gradient (U := U) z‖ := norm_nonneg _
    exact sq_le_sq.mpr <| by
      rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
      exact hscaled
  calc
    (M⁻¹ * M⁻¹) * ‖z‖ * ‖z‖ = (M⁻¹ * ‖z‖) ^ 2 := by
          ring
    _ ≤ ‖gradient (U := U) z‖ ^ 2 := hsq
    _ = gradientBilin (U := U) z z := by
          rw [gradientBilin_apply]
          symm
          exact real_inner_self_eq_norm_sq (gradient (U := U) z)

/-- The unique coercive-Hilbert graph element solving the weak gradient problem
with forcing `f`. -/
noncomputable def gradientProblemSolution {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U) :
    H1CoerciveHilbertSpace (U := U) := by
  let hB : IsCoercive (gradientBilin (U := U)) := isCoercive_gradientBilin (U := U) hC
  let e : H1CoerciveHilbertSpace (U := U) ≃L[ℝ] H1CoerciveHilbertSpace (U := U) :=
    hB.continuousLinearEquivOfBilin
  exact e.symm (forcingRieszRep (U := U) hf)

theorem gradientBilin_gradientProblemSolution_apply {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (z : H1CoerciveHilbertSpace (U := U)) :
    gradientBilin (U := U) (gradientProblemSolution hf hC) z =
      forcingFunctionalCLM (U := U) hf z := by
  let hB : IsCoercive (gradientBilin (U := U)) := isCoercive_gradientBilin (U := U) hC
  let e : H1CoerciveHilbertSpace (U := U) ≃L[ℝ] H1CoerciveHilbertSpace (U := U) :=
    hB.continuousLinearEquivOfBilin
  calc
    gradientBilin (U := U) (gradientProblemSolution hf hC) z
        = inner ℝ (e (gradientProblemSolution hf hC)) z := by
            symm
            exact hB.continuousLinearEquivOfBilin_apply (gradientProblemSolution hf hC) z
    _ = inner ℝ (forcingRieszRep (U := U) hf) z := by
          rw [gradientProblemSolution, e.apply_symm_apply]
    _ = forcingFunctionalCLM (U := U) hf z := by
          exact inner_forcingRieszRep_apply (U := U) hf z

/-- The unique coercive-Hilbert graph element solving the scalar right-hand-side
problem with forcing `F`. -/
noncomputable def scalarRhsProblemSolution {F : Vec d → ℝ}
    (hF : MemScalarL2 U F) (hC : H1CoerciveEstimate U) :
    H1CoerciveHilbertSpace (U := U) := by
  let hB : IsCoercive (gradientBilin (U := U)) := isCoercive_gradientBilin (U := U) hC
  let e : H1CoerciveHilbertSpace (U := U) ≃L[ℝ] H1CoerciveHilbertSpace (U := U) :=
    hB.continuousLinearEquivOfBilin
  exact e.symm (forcingRieszMap (U := U) (scalarForcingFunctionalCLM (U := U) hF))

theorem gradientBilin_scalarRhsProblemSolution_apply {F : Vec d → ℝ}
    (hF : MemScalarL2 U F) (hC : H1CoerciveEstimate U)
    (z : H1CoerciveHilbertSpace (U := U)) :
    gradientBilin (U := U) (scalarRhsProblemSolution hF hC) z =
      scalarForcingFunctionalCLM (U := U) hF z := by
  let hB : IsCoercive (gradientBilin (U := U)) := isCoercive_gradientBilin (U := U) hC
  let e : H1CoerciveHilbertSpace (U := U) ≃L[ℝ] H1CoerciveHilbertSpace (U := U) :=
    hB.continuousLinearEquivOfBilin
  calc
    gradientBilin (U := U) (scalarRhsProblemSolution hF hC) z
        = inner ℝ (e (scalarRhsProblemSolution hF hC)) z := by
            symm
            exact hB.continuousLinearEquivOfBilin_apply (scalarRhsProblemSolution hF hC) z
    _ = inner ℝ (forcingRieszMap (U := U)
          (scalarForcingFunctionalCLM (U := U) hF)) z := by
          rw [scalarRhsProblemSolution, e.apply_symm_apply]
    _ = scalarForcingFunctionalCLM (U := U) hF z := by
          exact inner_forcingRieszMap_apply (U := U)
            (scalarForcingFunctionalCLM (U := U) hF) z

end H1CoerciveHilbert

namespace H1MeanZeroFunction

noncomputable def toH1CoerciveHilbertSpace
    (u : H1MeanZeroFunction U) : H1CoerciveHilbertSpace (U := U) := by
  refine ⟨(h1CoerciveHilbertAmbientEquiv (U := U)).symm (u.toScalarL2, u.gradToHilbertVectorL2), ?_⟩
  change
    (h1CoerciveHilbertAmbientEquiv (U := U))
        ((h1CoerciveHilbertAmbientEquiv (U := U)).symm (u.toScalarL2, u.gradToHilbertVectorL2))
      ∈ h1MeanZeroGraphClosedSubmodule (U := U)
  rw [(h1CoerciveHilbertAmbientEquiv (U := U)).apply_symm_apply]
  exact h1MeanZero_pair_mem_h1MeanZeroGraphClosedSubmodule (U := U) u

@[simp] theorem H1CoerciveHilbert_value_toH1CoerciveHilbertSpace
    (u : H1MeanZeroFunction U) :
    H1CoerciveHilbert.value (U := U) (toH1CoerciveHilbertSpace (U := U) u) = u.toScalarL2 := by
  simp [toH1CoerciveHilbertSpace, H1CoerciveHilbert.value]

@[simp] theorem H1CoerciveHilbert_gradient_toH1CoerciveHilbertSpace
    (u : H1MeanZeroFunction U) :
    H1CoerciveHilbert.gradient (U := U) (toH1CoerciveHilbertSpace (U := U) u) =
      u.gradToHilbertVectorL2 := by
  simp [toH1CoerciveHilbertSpace, H1CoerciveHilbert.gradient]

@[simp] theorem H1CoerciveHilbert_forcingFunctionalCLM_apply_toH1CoerciveHilbertSpace
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) (u : H1MeanZeroFunction U) :
    H1CoerciveHilbert.forcingFunctionalCLM (U := U) hf
        (toH1CoerciveHilbertSpace (U := U) u) =
      gradientPairing hf u := by
  rw [H1CoerciveHilbert.forcingFunctionalCLM_apply,
    H1CoerciveHilbert_gradient_toH1CoerciveHilbertSpace]
  rfl

@[simp] theorem H1CoerciveHilbert_scalarForcingFunctionalCLM_apply_toH1CoerciveHilbertSpace
    {F : Vec d → ℝ} (hF : MemScalarL2 U F) (u : H1MeanZeroFunction U) :
    H1CoerciveHilbert.scalarForcingFunctionalCLM (U := U) hF
        (toH1CoerciveHilbertSpace (U := U) u) =
      inner ℝ (Homogenization.toScalarL2 hF) u.toScalarL2 := by
  rw [H1CoerciveHilbert.scalarForcingFunctionalCLM_apply,
    H1CoerciveHilbert_value_toH1CoerciveHilbertSpace]

/-- The mean-zero `H¹` weak solution represented by the coercive Hilbert graph
solution of the gradient problem. -/
noncomputable def gradientProblemSolution {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U) :
    H1MeanZeroFunction U :=
  H1CoerciveHilbert.toH1MeanZeroFunction
    (H1CoerciveHilbert.gradientProblemSolution (d := d) (U := U) hf hC)

theorem gradientProblemSolution_firstVariation {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (u : H1MeanZeroFunction U) :
    inner ℝ
        (gradientProblemSolution (U := U) hf hC).gradToHilbertVectorL2
        u.gradToHilbertVectorL2 =
      gradientPairing hf u := by
  simpa [gradientProblemSolution] using!
    (H1CoerciveHilbert.gradientBilin_gradientProblemSolution_apply
      (d := d)
      (U := U) hf hC
      (toH1CoerciveHilbertSpace (U := U) u))

theorem gradientProblemSolution_firstVariation_eq_integral {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (u : H1MeanZeroFunction U) :
    ∫ x in U,
        vecDot ((gradientProblemSolution (U := U) hf hC).toH1Function.grad x)
          (u.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (f x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  let v : H1MeanZeroFunction U := gradientProblemSolution (U := U) hf hC
  have hpair :
      gradientPairing v.toH1Function.grad_memVectorL2 u = gradientPairing hf u := by
    simpa [v] using! gradientProblemSolution_firstVariation (d := d) (U := U) hf hC u
  calc
    ∫ x in U, vecDot (v.toH1Function.grad x) (u.toH1Function.grad x)
        ∂MeasureTheory.volume = gradientPairing v.toH1Function.grad_memVectorL2 u := by
          symm
          exact gradientPairing_eq_integral (U := U) v.toH1Function.grad_memVectorL2 u
    _ = gradientPairing hf u := hpair
    _ = ∫ x in U, vecDot (f x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
          exact gradientPairing_eq_integral (U := U) hf u

/-- The mean-zero `H¹` weak solution represented by the coercive Hilbert graph
solution of the scalar right-hand-side problem. -/
noncomputable def scalarRhsProblemSolution {F : Vec d → ℝ}
    (hF : MemScalarL2 U F) (hC : H1CoerciveEstimate U) :
    H1MeanZeroFunction U :=
  H1CoerciveHilbert.toH1MeanZeroFunction
    (H1CoerciveHilbert.scalarRhsProblemSolution (d := d) (U := U) hF hC)

theorem scalarRhsProblemSolution_firstVariation {F : Vec d → ℝ}
    (hF : MemScalarL2 U F) (hC : H1CoerciveEstimate U)
    (u : H1MeanZeroFunction U) :
    inner ℝ
        (scalarRhsProblemSolution (U := U) hF hC).gradToHilbertVectorL2
        u.gradToHilbertVectorL2 =
      inner ℝ (Homogenization.toScalarL2 hF) u.toScalarL2 := by
  simpa [scalarRhsProblemSolution] using
    (H1CoerciveHilbert.gradientBilin_scalarRhsProblemSolution_apply
      (d := d) (U := U) hF hC
      (toH1CoerciveHilbertSpace (U := U) u))

theorem scalarRhsProblemSolution_firstVariation_eq_integral {F : Vec d → ℝ}
    (hF : MemScalarL2 U F) (hC : H1CoerciveEstimate U)
    (u : H1MeanZeroFunction U) :
    ∫ x in U,
        vecDot ((scalarRhsProblemSolution (U := U) hF hC).toH1Function.grad x)
          (u.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, F x * u.toH1Function x ∂MeasureTheory.volume := by
  let v : H1MeanZeroFunction U := scalarRhsProblemSolution (U := U) hF hC
  have hpair :
      inner ℝ v.gradToHilbertVectorL2 u.gradToHilbertVectorL2 =
        inner ℝ (Homogenization.toScalarL2 hF) u.toScalarL2 := by
    simpa [v] using scalarRhsProblemSolution_firstVariation (d := d) (U := U) hF hC u
  calc
    ∫ x in U, vecDot (v.toH1Function.grad x) (u.toH1Function.grad x)
        ∂MeasureTheory.volume =
        inner ℝ v.gradToHilbertVectorL2 u.gradToHilbertVectorL2 := by
          symm
          simpa [H1MeanZeroFunction.gradToHilbertVectorL2, H1Function.gradToHilbertVectorL2] using
            inner_toHilbertVectorL2OfVecField_eq_integral
              (U := U)
              v.toH1Function.grad_memVectorL2
              u.toH1Function.grad_memVectorL2
    _ = inner ℝ (Homogenization.toScalarL2 hF) u.toScalarL2 := hpair
    _ = ∫ x in U, F x * u.toH1Function x ∂MeasureTheory.volume := by
          rw [scalarInner_eq_integral]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards
              [Homogenization.coeFn_toScalarL2 hF,
                H1Function.coeFn_toScalarL2 u.toH1Function]
            with x hF' hu
          rw [hF']
          change F x * u.toH1Function.toScalarL2 x = F x * u.toH1Function.toFun x
          rw [hu]

end H1MeanZeroFunction

namespace H1Function

theorem gradientProblemSolution_firstVariation_eq_integral {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (u : H1Function U) :
    ∫ x in U,
        vecDot ((H1MeanZeroFunction.gradientProblemSolution
          (U := U) hf hC).toH1Function.grad x) (u.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (f x) (u.grad x) ∂MeasureTheory.volume := by
  simpa using
    (H1MeanZeroFunction.gradientProblemSolution_firstVariation_eq_integral
      (d := d) (U := U) hf hC u.toMeanZero)

end H1Function

end CoerciveHilbert


end Homogenization
