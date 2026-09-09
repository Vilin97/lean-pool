/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalTimePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
public import LeanPool.NavierStokesAndEuler.Euler.MeanVariationalOperator

@[expose] public section

/-!
# A genuine mean time-variational inverse on ordinary spatial L²

The Hilbert variable is the time derivative of the physical displacement η.
Terminal integration constructs η, and the closed constraints require
`FInv(t) η(t)` to be an actual ordinary-space solenoidal field at every time.
The exact initial form is `M0 + L A`, not a replacement boundary condition.

The lower bound for this given boundary operator on solenoidal fields remains
an explicit input.  In the source it must be proved from the concrete cutoff
operator and harmonic localization.  This file does not claim that step, the
strong interior equation, or the initial derivative boundary identity.  The
recovered `z=FInv η` is continuous here; its H¹ regularity additionally uses the
source's C¹-in-time inverse deformation.
-/

noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerTransverseVariationalInverse

/-- Derivatives whose actual terminal primitives obey the solenoidal label constraint. -/
def meanDerivatives (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) : Submodule ℝ (TimeLp T L2) where
  carrier := {u | ∀ t, FInv t (terminalPrimitive T hT u t) ∈ solenoidalSpace}
  zero_mem' := by
    intro t
    simp only [map_zero, ContinuousMap.zero_apply, Submodule.zero_mem]
  add_mem' := by
    intro u v hu hv t
    simpa only [map_add, ContinuousMap.add_apply] using solenoidalSpace.add_mem (hu t) (hv t)
  smul_mem' := by
    intro a u hu t
    simpa only [map_smul, ContinuousMap.smul_apply] using solenoidalSpace.smul_mem a (hu t)

/-- Every genuine absolutely continuous terminal-zero path with an L² derivative
and the label-solenoidal constraint is represented in this Hilbert space. -/
theorem derivative_mem_of_ac (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T L2) (η : ℝ → L2)
    (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (u t) t) (hterminal : η T = 0)
    (hsolenoidal : ∀ t : Icc (0 : ℝ) T, FInv t (η t) ∈ solenoidalSpace) :
    u ∈ meanDerivatives T hT FInv := by
  intro t
  change FInv t (realPrimitive T u t) ∈ solenoidalSpace
  rw [← eq_realPrimitive_of_ac_hasDerivAt_ae T hT u η hη hder hterminal t t.property]
  exact hsolenoidal t

/-- Every time constraint is the preimage of the actual closed solenoidal subspace. -/
theorem meanDerivatives_closed (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    IsClosed (meanDerivatives T hT FInv : Set (TimeLp T L2)) := by
  change IsClosed {u : TimeLp T L2 | ∀ t, FInv t (terminalPrimitive T hT u t) ∈ solenoidalSpace}
  rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro t
  exact gradientSpace.isClosed_orthogonal.preimage
    ((FInv t).continuous.comp (evaluation T hT t).continuous)

/-- The genuine closed constraint space is a complete Hilbert space. -/
instance meanDerivatives_complete (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    CompleteSpace (meanDerivatives T hT FInv) :=
  (meanDerivatives_closed T hT FInv).completeSpace_coe

/-- The actual displacement primitive, restricted to the mean constraint space. -/
def meanPrimitive (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    meanDerivatives T hT FInv →L[ℝ] TimeLp T L2 :=
  (primitiveTimeLp T hT).comp (meanDerivatives T hT FInv).subtypeL

/-- The actual initial trace on that same constraint space. -/
def meanTrace (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    meanDerivatives T hT FInv →L[ℝ] L2 :=
  (initialTrace T hT).comp (meanDerivatives T hT FInv).subtypeL

/-- The sharp source Poincaré estimate survives restriction to the constraint space. -/
theorem meanPrimitive_norm_sq (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : meanDerivatives T hT FInv) :
    ‖meanPrimitive T hT FInv u‖^2 ≤ T^2/2*‖u‖^2 :=
  primitiveTimeLp_norm_sq_le T hT (u : TimeLp T L2)

/-- The source initial trace estimate is an estimate of this literal trace. -/
theorem meanTrace_norm_sq (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : meanDerivatives T hT FInv) :
    ‖meanTrace T hT FInv u‖^2 ≤ T*‖u‖^2 :=
  initialTrace_norm_sq_le T hT (u : TimeLp T L2)

/-- The normalization of the deformation makes the initial physical trace solenoidal. -/
theorem meanTrace_mem (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (u : meanDerivatives T hT FInv) : meanTrace T hT FInv u ∈ solenoidalSpace := by
  have hu := u.property ⟨0, le_rfl, hT⟩
  rw [hF0, id_apply] at hu
  exact hu

/-- Only the boundary lower bound on actual solenoidal traces is needed. -/
theorem meanTrace_boundary (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (M0 A : L2 →L[ℝ] L2) (L B : ℝ)
    (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
      -B*‖z‖^2 ≤ ⟪M0 z, z⟫_ℝ+L*⟪A z, z⟫_ℝ)
    (u : meanDerivatives T hT FInv) :
    -B*‖meanTrace T hT FInv u‖^2 ≤
      ⟪(M0+L • A) (meanTrace T hT FInv u), meanTrace T hT FInv u⟫_ℝ := by
  simpa only [add_apply, smul_apply, inner_add_left, real_inner_smul_left] using
    hboundary (meanTrace T hT FInv u) (meanTrace_mem T hT FInv hF0 u)

/-- A polynomial operator bound for the actual terminal primitive. -/
theorem meanPrimitive_norm_le (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) : ‖meanPrimitive T hT FInv‖ ≤ T := by
  apply ContinuousLinearMap.opNorm_le_bound _ hT
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (norm_nonneg u))).1
  calc
    _ ≤ T^2/2*‖u‖^2 := meanPrimitive_norm_sq T hT FInv u
    _ ≤ T^2*‖u‖^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u‖)
      nlinarith only [sq_nonneg T]
    _ = (T*‖u‖)^2 := by ring

/-- The mean-space primitive has the same genuine integral representative. -/
theorem meanPrimitive_ae (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : meanDerivatives T hT FInv) :
    (meanPrimitive T hT FInv u : ℝ → L2) =ᵐ[timeMeasure T] realPrimitive T (u : TimeLp T L2) :=
  primitiveTimeLp_ae T hT (u : TimeLp T L2)

/-- The potential pairing is the literal time integral on the actual displacement paths. -/
theorem meanPotential_inner_eq_integral (T : ℝ) (hT : 0 ≤ T)
    (FInv H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u v : meanDerivatives T hT FInv) :
    ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ =
      ∫ t, ⟪H (projIcc 0 T hT t) (realPrimitive T (u : TimeLp T L2) t),
        realPrimitive T (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [timeMultiplier_ae T hT H (meanPrimitive T hT FInv u),
    meanPrimitive_ae T hT FInv u, meanPrimitive_ae T hT FInv v] with t ht hu hv
  change ⟪(timeMultiplier T hT H (meanPrimitive T hT FInv u) : ℝ → L2) t,
    (meanPrimitive T hT FInv v : ℝ → L2) t⟫_ℝ = _
  exact congrArg₂ (fun x y : L2 => ⟪x, y⟫_ℝ)
    (ht.trans (congrArg (H (projIcc 0 T hT t)) hu)) hv

/-- The forcing pairing is the literal time integral against the actual test displacement. -/
theorem meanForcing_inner_eq_integral (T : ℝ) (hT : 0 ≤ T)
    (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (f : TimeLp T L2)
    (v : meanDerivatives T hT FInv) :
    ⟪f, meanPrimitive T hT FInv v⟫_ℝ =
      ∫ t, ⟪f t, realPrimitive T (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [meanPrimitive_ae T hT FInv v] with t ht
  exact congrArg (fun z : L2 => ⟪f t, z⟫_ℝ) ht

/-- Rewriting the form as actual time integrals is independent of how its
argument was constructed. This also keeps the integral interface lightweight. -/
theorem weak_integral_of_weak (T : ℝ) (hT : 0 ≤ T)
    (FInv H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)
    (u v : meanDerivatives T hT FInv) (f : TimeLp T L2)
    (h : ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ-
      ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ+
      ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ+
      L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ =
      -⟪f, meanPrimitive T hT FInv v⟫_ℝ) :
    (∫ t, ⟪(u : TimeLp T L2) t, (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T)-
      (∫ t, ⟪H (projIcc 0 T hT t) (realPrimitive T (u : TimeLp T L2) t),
        realPrimitive T (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T)+
      ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ+
      L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ =
      -(∫ t, ⟪f t, realPrimitive T (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T) := by
  have hi : ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ =
      ∫ t, ⟪(u : TimeLp T L2) t, (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T :=
    MeasureTheory.L2.inner_def (u : TimeLp T L2) (v : TimeLp T L2)
  have hp := meanPotential_inner_eq_integral T hT FInv H u v
  have hf := meanForcing_inner_eq_integral T hT FInv f v
  have hleft := congrArg
    (fun r : ℝ => r + ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ +
      L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ)
    (congrArg₂ (fun x y : ℝ => x-y) hi hp)
  exact hleft.symm.trans (h.trans (congrArg (fun r : ℝ => -r) hf))

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2)
  (L K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K*‖z‖^2)
  (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
    -B*‖z‖^2 ≤ ⟪M0 z, z⟫_ℝ+L*⟪A z, z⟫_ℝ)
  (hsmall : K*(T^2/2)+B*T ≤ 1/2)

/-- The mean forcing-to-displacement-derivative map is constructed by Lax--Milgram. -/
def meanSolver : TimeLp T L2 →L[ℝ] meanDerivatives T hT FInv :=
  EulerMeanVariationalOperator.meanSolver (meanPrimitive T hT FInv) (meanTrace T hT FInv)
    (timeMultiplier T hT H) (M0+L • A) (T^2/2) T K B hK hB
    (meanPrimitive_norm_sq T hT FInv) (meanTrace_norm_sq T hT FInv)
    (timeMultiplier_quadratic_upper T hT H K hH)
    (meanTrace_boundary T hT FInv M0 A L B hF0 hboundary) hsmall

/-- The physical displacement is the actual terminal primitive of the solved derivative. -/
def meanEta : TimeLp T L2 →L[ℝ] C(Icc (0 : ℝ) T, L2) :=
  (terminalPrimitive T hT).comp ((meanDerivatives T hT FInv).subtypeL.comp
    (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall))

/-- Recover the actual continuous solenoidal label displacement `z=FInv η`. -/
def meanDisplacement (f : TimeLp T L2) : C(Icc (0 : ℝ) T, L2) :=
  ⟨fun t => FInv t (meanEta T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f t),
    FInv.continuous.clm_apply
      (meanEta T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f).continuous⟩

/-- The recovered label displacement is genuinely solenoidal at every time. -/
theorem meanDisplacement_solenoidal (f : TimeLp T L2) (t : Icc (0 : ℝ) T) :
    meanDisplacement T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f t ∈
      solenoidalSpace :=
  (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f).property t

/-- The actual physical displacement has zero terminal trace. -/
theorem meanEta_terminal (f : TimeLp T L2) :
    meanEta T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f ⟨T, hT, le_rfl⟩ = 0 :=
  terminalPrimitive_terminal T hT
    (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f : TimeLp T L2)

/-- The recovered label displacement also has zero terminal trace. -/
theorem meanDisplacement_terminal (f : TimeLp T L2) :
    meanDisplacement T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f
      ⟨T, hT, le_rfl⟩ = 0 := by
  change FInv _ (meanEta T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f _) = 0
  rw [meanEta_terminal T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f, map_zero]

/-- The solved derivative is the actual a.e. derivative of the physical displacement. -/
theorem meanEta_hasDerivAt_ae (f : TimeLp T L2) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (realPrimitive T
        (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f : TimeLp T L2))
        ((meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f : TimeLp T L2) t) t :=
  realPrimitive_hasDerivAt_ae T
    (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f : TimeLp T L2)

/-- The physical displacement is a genuine absolutely continuous time path. -/
theorem meanEta_absolutelyContinuous (f : TimeLp T L2) :
    AbsolutelyContinuousOnInterval (realPrimitive T
      (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f : TimeLp T L2)) 0 T :=
  realPrimitive_absolutelyContinuous T
    (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f : TimeLp T L2)

/-- The exact mean form with the two original initial boundary terms. -/
theorem meanSolver_weak (f : TimeLp T L2) (v : meanDerivatives T hT FInv) :
    let u := meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f
    ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ-
      ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ+
      ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ+
      L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ =
      -⟪f, meanPrimitive T hT FInv v⟫_ℝ := by
  simpa only [meanSolver, Submodule.coe_inner, add_apply, smul_apply, inner_add_left,
    real_inner_smul_left, add_assoc] using
    EulerMeanVariationalOperator.meanSolver_weak (meanPrimitive T hT FInv) (meanTrace T hT FInv)
      (timeMultiplier T hT H) (M0+L • A) (T^2/2) T K B hK hB
      (meanPrimitive_norm_sq T hT FInv) (meanTrace_norm_sq T hT FInv)
      (timeMultiplier_quadratic_upper T hT H K hH)
      (meanTrace_boundary T hT FInv M0 A L B hF0 hboundary) hsmall f v

/-- The solved mean derivative obeys a polynomial finite-time norm bound. -/
theorem meanSolver_norm (f : TimeLp T L2) :
    ‖meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f‖ ≤ 2*T*‖f‖ := by
  apply (EulerMeanVariationalOperator.meanSolver_norm
    (meanPrimitive T hT FInv) (meanTrace T hT FInv)
    (timeMultiplier T hT H) (M0+L • A) (T^2/2) T K B hK hB
    (meanPrimitive_norm_sq T hT FInv) (meanTrace_norm_sq T hT FInv)
    (timeMultiplier_quadratic_upper T hT H K hH)
    (meanTrace_boundary T hT FInv M0 A L B hF0 hboundary) hsmall f).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (meanPrimitive_norm_le T hT FInv) (by norm_num)) (norm_nonneg f)

/-- The weak equation is an equality of genuine time integrals, including the
two actual initial boundary terms from the source. -/
theorem meanSolver_weak_integral (f : TimeLp T L2) (v : meanDerivatives T hT FInv) :
    let u := meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f
    (∫ t, ⟪(u : TimeLp T L2) t, (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T)-
      (∫ t, ⟪H (projIcc 0 T hT t) (realPrimitive T (u : TimeLp T L2) t),
        realPrimitive T (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T)+
      ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ+
      L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ =
      -(∫ t, ⟪f t, realPrimitive T (v : TimeLp T L2) t⟫_ℝ ∂timeMeasure T) := by
  exact weak_integral_of_weak T hT FInv H M0 A L
    (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f) v f
    (meanSolver_weak T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f v)

/-- No other admissible derivative solves this same genuine mean form. -/
theorem meanSolver_unique (f : TimeLp T L2) (u : meanDerivatives T hT FInv)
    (hu : ∀ v : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ-
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ+
        ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ+
        L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ =
        -⟪f, meanPrimitive T hT FInv v⟫_ℝ) :
    u = meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f := by
  apply EulerMeanVariationalOperator.meanSolver_unique
    (meanPrimitive T hT FInv) (meanTrace T hT FInv)
    (timeMultiplier T hT H) (M0+L • A) (T^2/2) T K B hK hB
    (meanPrimitive_norm_sq T hT FInv) (meanTrace_norm_sq T hT FInv)
    (timeMultiplier_quadratic_upper T hT H K hH)
    (meanTrace_boundary T hT FInv M0 A L B hF0 hboundary) hsmall f u
  intro v
  simpa only [Submodule.coe_inner, add_apply, smul_apply, inner_add_left,
    real_inner_smul_left, add_assoc] using hu v

include hK hB hF0 hH hboundary hsmall in
/-- Existence and uniqueness for the source's mean form, conditional on the
explicit coefficient and solenoidal boundary lower bounds. -/
theorem existsUnique_mean_weak_solution (f : TimeLp T L2) :
    ∃! u : meanDerivatives T hT FInv, ∀ v : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ-
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ+
        ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ+
        L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ =
        -⟪f, meanPrimitive T hT FInv v⟫_ℝ :=
  ⟨meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f,
    meanSolver_weak T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f,
    fun u hu => meanSolver_unique T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f u hu⟩

end EulerMeanVariationalInverse
