/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanVelocityPressure
import LeanPool.NavierStokesAndEuler.Euler.MeanFrameCoefficients
import LeanPool.NavierStokesAndEuler.Euler.TimeH1PointwiseBounds
import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEstimates

/-!
# Quantitative time estimates for the genuine mean inverse

The constants depend explicitly and polynomially on the time interval,
coefficient bounds, and the inverse-frame bound. The only square roots are the
proved finite-time trace/Poincaré factors. These are estimates of the actual
Bochner fields and continuous representatives constructed by the inverse.
-/

section

/-!
# The actual bounded linear mean velocity inverse

The physical velocity is `η_t-F_t F⁻¹η`. This formula constructs a bounded
linear map on the original derivative variable, and the genuine H² evolution
identifies it with `F z_t`. Composing with the variational solver gives the
actual linear velocity inverse with an explicit finite-time bound.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive EulerMeanSolenoidal EulerVolterraConvolution EulerTimeH1FieldProduct

/-- The physical velocity formula on actual Bochner derivative fields. -/
def meanVelocityMap (T : ℝ) (hT : 0 ≤ T)
    (FInv F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) : TimeLp T L2 →L[ℝ] TimeLp T L2 :=
  ContinuousLinearMap.id ℝ _ -
    (timeMultiplier T hT F₁).comp ((timeMultiplier T hT FInv).comp (primitiveTimeLp T hT))

/-- The bounded linear formula has its literal pointwise representative. -/
theorem meanVelocityMap_ae (T : ℝ) (hT : 0 ≤ T)
    (FInv F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T L2) :
    (meanVelocityMap T hT FInv F₁ u : ℝ → L2) =ᵐ[timeMeasure T]
      fun t => u t - extendPath T hT F₁ t (extendPath T hT FInv t (realPrimitive T u t)) := by
  filter_upwards [Lp.coeFn_sub u
      (timeMultiplier T hT F₁ (timeMultiplier T hT FInv (primitiveTimeLp T hT u))),
    timeMultiplier_ae T hT F₁ (timeMultiplier T hT FInv (primitiveTimeLp T hT u)),
    timeMultiplier_ae T hT FInv (primitiveTimeLp T hT u), primitiveTimeLp_ae T hT u]
    with t hsub hF₁ hInv hp
  simp only [Pi.sub_apply] at hsub
  change (u-timeMultiplier T hT F₁ (timeMultiplier T hT FInv (primitiveTimeLp T hT u))) t = _
  rw [hsub, hF₁, hInv, hp]

/-- A quantitative bound for the actual linear velocity formula. -/
theorem meanVelocityMap_apply_norm (T : ℝ) (hT : 0 ≤ T)
    (FInv F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T L2) :
    ‖meanVelocityMap T hT FInv F₁ u‖ ≤
      (1+‖F₁‖*‖FInv‖*Real.sqrt (T^2/2))*‖u‖ := by
  have hp : ‖primitiveTimeLp T hT u‖ ≤ Real.sqrt (T^2/2)*‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
    calc
      _ ≤ (T^2/2)*‖u‖^2 := primitiveTimeLp_norm_sq_le T hT u
      _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]
  change ‖u-timeMultiplier T hT F₁ (timeMultiplier T hT FInv (primitiveTimeLp T hT u))‖ ≤ _
  calc
    _ ≤ ‖u‖+‖timeMultiplier T hT F₁ (timeMultiplier T hT FInv (primitiveTimeLp T hT u))‖ :=
      norm_sub_le _ _
    _ ≤ ‖u‖+‖F₁‖*‖timeMultiplier T hT FInv (primitiveTimeLp T hT u)‖ :=
      add_le_add le_rfl (timeApply_bound T hT F₁ _)
    _ ≤ ‖u‖+‖F₁‖*(‖FInv‖*‖primitiveTimeLp T hT u‖) := by
      gcongr
      exact timeApply_bound T hT FInv _
    _ ≤ ‖u‖+‖F₁‖*(‖FInv‖*(Real.sqrt (T^2/2)*‖u‖)) := by
      gcongr
    _ = _ := by ring

namespace StrongMeanEvolution

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- Differentiating the actual displacement reconstruction gives the kinetic identity. -/
theorem kinetic_ae
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) :
    ∀ᵐ t ∂timeMeasure T,
      u t = extendPath T hT F₁ t (s.label t : L2) + s.physicalPath t := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem, operatorPath_hasDerivAt_ae T hT F F₁ hF,
    s.label_derivative, realPrimitive_hasDerivAt_ae T u] with t ht hFt hzt hut
  have hzt' := solenoidalSpace.subtypeL.hasFDerivAt.comp_hasDerivAt t hzt
  have hprod := hFt.clm_apply hzt'
  have heq : realPrimitive T u =ᶠ[𝓝 t]
      fun r => extendPath T hT F r (s.label r : L2) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    have h := ((congrArg (fun x : L2 => F ⟨r, hr⟩ x) (s.label_eq ⟨r, hr⟩)).trans
      (hRight ⟨r, hr⟩ _)).symm
    simpa only [extendPath, projIcc_of_mem hT hr] using h
  exact hut.unique (hprod.congr_of_eventuallyEq heq)

/-- The actual velocity constructed by strong regularity equals the bounded
linear formula on the original solved derivative field. -/
theorem velocityField_eq_meanVelocityMap
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) :
    s.velocityField = meanVelocityMap T hT FInv F₁ u := by
  apply Lp.ext
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc (0 : ℝ) T := ae_restrict_mem measurableSet_Icc
  filter_upwards [hmem, s.kinetic_ae hF hRight, (s.physical_h1 hF).2.1,
    meanVelocityMap_ae T hT FInv F₁ u] with t ht hk hB hv
  have hz : (s.label t : L2) = extendPath T hT FInv t (realPrimitive T u t) := by
    simpa only [extendPath, projIcc_of_mem hT ht] using s.label_eq ⟨t, ht⟩
  rw [hB, hv, hk, ← hz]
  abel

end StrongMeanEvolution

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2)
  (L K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
  (hFInv₀ : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
  (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
    -B * ‖z‖ ^ 2 ≤ ⟪M0 z, z⟫_ℝ + L * ⟪A z, z⟫_ℝ)
  (hsmall : K * (T ^ 2 / 2) + B * T ≤ 1 / 2)

/-- The genuine bounded linear mean velocity inverse on actual forcing classes. -/
def meanVelocitySolver : TimeLp T L2 →L[ℝ] TimeLp T L2 :=
  (meanVelocityMap T hT FInv F₁).comp ((meanDerivatives T hT FInv).subtypeL.comp
    (meanSolver T hT FInv H M0 A L K B hK hB hFInv₀ hH hboundary hsmall))

/-- The actual mean velocity inverse has an explicit finite-time bound. -/
theorem meanVelocitySolver_norm (f : TimeLp T L2) :
    ‖meanVelocitySolver T hT FInv F₁ H M0 A L K B hK hB hFInv₀ hH hboundary hsmall f‖ ≤
      (1+‖F₁‖*‖FInv‖*Real.sqrt (T^2/2))*(2*T*‖f‖) := by
  apply (meanVelocityMap_apply_norm T hT FInv F₁
    (meanSolver T hT FInv H M0 A L K B hK hB hFInv₀ hH hboundary hsmall f : TimeLp T L2)).trans
  exact mul_le_mul_of_nonneg_left
    (meanSolver_norm T hT FInv H M0 A L K B hK hB hFInv₀ hH hboundary hsmall f) (by positivity)

end EulerMeanVariationalInverse

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive EulerMeanSolenoidal EulerVolterraConvolution
  EulerTimeH1FieldProduct EulerTimeH1PointwiseBounds EulerTransverseGramInverse
  EulerTransverseStrongEstimates

-- Cache the inherited structures before forming norms of nested operator paths.
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanStrongEstimates1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanStrongEstimates2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanStrongEstimates3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance

/-- Restricting F to the actual solenoidal subspace does not increase its norm. -/
theorem solenoidalFrame_norm_le (T : ℝ) (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    ‖solenoidalFrame T F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).2
  intro t
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro z
  exact ((F t).le_opNorm (z : L2)).trans
    (mul_le_mul_of_nonneg_right (F.norm_coe_le_norm t) (norm_nonneg z))

/-- The ordinary projection equation is exactly the Gram equation on L²σ. -/
theorem gram_equation_of_ordinary (F F₁ : L2 →L[ℝ] L2) (f : L2) (a v : solenoidalSpace)
    (h : solenoidalProjection (F.adjoint (F (a : L2))) =
      solenoidalProjection (F.adjoint (f - (2 : ℝ) • F₁ (v : L2)))) :
    gram (F.comp solenoidalSpace.subtypeL) a =
      (F.comp solenoidalSpace.subtypeL).adjoint (f-(2 : ℝ) • F₁ (v : L2)) := by
  apply Subtype.ext
  simpa only [gram, adjoint_comp, Submodule.adjoint_subtypeL, comp_apply,
    Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply,
    solenoidalProjection] using h

private theorem norm_sub_sub_two_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f a b : E) : ‖f-a-(2 : ℝ) • b‖ ≤ ‖f‖+‖a‖+2*‖b‖ := by
  calc
    _ ≤ ‖f-a‖+‖(2 : ℝ) • b‖ := norm_sub_le _ _
    _ = ‖f-a‖+2*‖b‖ := by rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ _ := add_le_add (norm_sub_le f a) le_rfl

namespace StrongMeanEvolution

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- Inverse-frame application bounds the actual coordinate velocity by B. -/
theorem velocityLp_norm_le
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x) :
    ‖s.velocityLp‖ ≤ ‖FInv‖*‖s.velocityField‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [timeMultiplier_ae T hT (solenoidalFrame T F) s.velocityLp] with t ht
  have hi := (congrArg (fun x : L2 => FInv (projIcc 0 T hT t) x) ht).trans
    (hInv (projIcc 0 T hT t) (s.velocityLp t : L2))
  calc
    ‖s.velocityLp t‖ = ‖FInv (projIcc 0 T hT t) (s.velocityField t)‖ :=
      (congrArg norm hi).symm
    _ ≤ ‖FInv (projIcc 0 T hT t)‖*‖s.velocityField t‖ := (FInv _).le_opNorm _
    _ ≤ ‖FInv‖*‖s.velocityField t‖ :=
      mul_le_mul_of_nonneg_right (FInv.norm_coe_le_norm _) (norm_nonneg _)

/-- The actual physical velocity obeys the explicit derivative-variable bound. -/
theorem velocityField_norm
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) :
    ‖s.velocityField‖ ≤ (1+‖F₁‖*‖FInv‖*Real.sqrt (T^2/2))*‖u‖ := by
  calc
    ‖s.velocityField‖ = ‖meanVelocityMap T hT FInv F₁ u‖ :=
      congrArg norm (s.velocityField_eq_meanVelocityMap hF hRight)
    _ ≤ _ := meanVelocityMap_apply_norm T hT FInv F₁ u

/-- Combining the two actual bounds controls z_t by the original variational variable. -/
theorem velocityLp_norm_from_input
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) :
    ‖s.velocityLp‖ ≤ ‖FInv‖*((1+‖F₁‖*‖FInv‖*Real.sqrt (T^2/2))*‖u‖) :=
  (s.velocityLp_norm_le hInv).trans
    (mul_le_mul_of_nonneg_left (s.velocityField_norm hF hRight) (norm_nonneg FInv))

/-- The actual strong acceleration pays only the inverse Gram and coefficient norms. -/
theorem acceleration_norm
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x) :
    ‖s.acceleration‖ ≤ (‖FInv‖+1)^2*‖F‖*(‖f‖+2*‖F₁‖*‖s.velocityLp‖) := by
  have heq : ∀ᵐ t ∂timeMeasure T,
      gram (extendPath T hT (solenoidalFrame T F) t) (s.acceleration t) =
      (solenoidalFrame T F (projIcc 0 T hT t)).adjoint
        (f t-(2 : ℝ) • solenoidalFrame T F₁ (projIcc 0 T hT t) (s.velocityLp t)) := by
    filter_upwards [s.equation, s.velocity_ae] with t ht hv
    have hh := congrArg (fun v : solenoidalSpace =>
      solenoidalProjection ((F (projIcc 0 T hT t)).adjoint
        (f t-(2 : ℝ) • F₁ (projIcc 0 T hT t) (v : L2)))) hv
    exact gram_equation_of_ordinary (F (projIcc 0 T hT t)) (F₁ (projIcc 0 T hT t))
      (f t) (s.acceleration t) (s.velocityLp t) (ht.trans hh.symm)
  have h := EulerTransverseStrongEstimates.acceleration_norm T (solenoidalFrame T F)
    (solenoidalFrame T F₁) (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
    (solenoidalFrame_lower T FInv F hInv) hT s.velocityLp s.acceleration f heq
  have h' : ‖s.acceleration‖ ≤ (‖FInv‖+1)^2*‖solenoidalFrame T F‖*
      (‖f‖+2*‖solenoidalFrame T F₁‖*‖s.velocityLp‖) := by
    simpa only [meanFrameCoercivity, inv_inv] using h
  apply h'.trans
  gcongr
  · exact solenoidalFrame_norm_le T F
  · exact solenoidalFrame_norm_le T F₁

/-- The product-rule derivative B_t has the corresponding actual L² bound. -/
theorem velocityDerivative_norm :
    ‖s.velocityDerivative‖ ≤ ‖F₁‖*‖s.velocityLp‖+‖F‖*‖s.acceleration‖ := by
  apply (fieldProductDerivative_norm_le T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    s.velocityLp s.acceleration).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_right (solenoidalFrame_norm_le T F₁) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (solenoidalFrame_norm_le T F) (norm_nonneg _))

/-- The actual pressure-gradient residual is controlled without differentiating H. -/
theorem pressureResidual_norm :
    ‖s.pressureResidual‖ ≤ ‖f‖+‖F‖*‖s.acceleration‖+2*‖F₁‖*‖s.velocityLp‖ := by
  have hfa : ‖timeMultiplier T hT (solenoidalFrame T F) s.acceleration‖ ≤ ‖F‖*‖s.acceleration‖ :=
    (timeApply_bound T hT (solenoidalFrame T F) _).trans
      (mul_le_mul_of_nonneg_right (solenoidalFrame_norm_le T F) (norm_nonneg _))
  have hfv : ‖timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp‖ ≤ ‖F₁‖*‖s.velocityLp‖ :=
    (timeApply_bound T hT (solenoidalFrame T F₁) _).trans
      (mul_le_mul_of_nonneg_right (solenoidalFrame_norm_le T F₁) (norm_nonneg _))
  calc
    ‖s.pressureResidual‖ ≤ ‖f‖+
        ‖timeMultiplier T hT (solenoidalFrame T F) s.acceleration‖+
        2*‖timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp‖ :=
      norm_sub_sub_two_smul f
        (timeMultiplier T hT (solenoidalFrame T F) s.acceleration)
        (timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp)
    _ ≤ ‖f‖+‖F‖*‖s.acceleration‖+2*(‖F₁‖*‖s.velocityLp‖) :=
      add_le_add (add_le_add le_rfl hfa) (mul_le_mul_of_nonneg_left hfv (by norm_num))
    _ = _ := by ring

/-- The derived compact-initial-data law has an actual quantitative trace bound. -/
theorem initialPhysicalVelocity_norm
    (hFInv₀ : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hF₀ : F ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2) :
    ‖s.physicalPath 0‖ ≤ |L| * ‖A‖*Real.sqrt T*‖u‖ := by
  have hz : (s.label 0 : L2) = realPrimitive T u 0 := by
    simpa only [hFInv₀, id_apply] using s.label_eq ⟨0, le_rfl, hT⟩
  have hzbound : ‖(s.label 0 : L2)‖ ≤ Real.sqrt T*‖u‖ := by
    have h := realPrimitive_norm_le T u 0 ⟨le_rfl, hT⟩
    simp only [sub_zero] at h
    exact (congrArg norm hz).trans_le h
  calc
    ‖s.physicalPath 0‖ = |L| * ‖A (s.label 0 : L2)‖ := by
      rw [s.physicalPath_initial hF₀, norm_smul, Real.norm_eq_abs]
    _ ≤ |L| * (‖A‖*‖(s.label 0 : L2)‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (abs_nonneg L)
    _ ≤ |L| * (‖A‖*(Real.sqrt T*‖u‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzbound (norm_nonneg A)) (abs_nonneg L)
    _ = _ := by ring

/-- The actual continuous velocity is uniformly controlled in time by its
initial trace and the proved L² derivative bound. -/
theorem physicalPath_norm_uniform
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hFInv₀ : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hF₀ : F ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖s.physicalPath t‖ ≤ |L| * ‖A‖*Real.sqrt T*‖u‖+Real.sqrt T*‖s.velocityDerivative‖ := by
  have hV := s.physical_h1 hF
  apply (norm_le_initial_add_uniform T hT s.velocityDerivative s.physicalPath hV.1 hV.2.2 t
      ht).trans
  exact add_le_add (s.initialPhysicalVelocity_norm hFInv₀ hF₀) le_rfl

end StrongMeanEvolution
end EulerMeanVariationalInverse
