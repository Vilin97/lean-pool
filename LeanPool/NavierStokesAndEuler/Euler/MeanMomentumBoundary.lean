/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanDisplacementRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseMomentumRegularity
import LeanPool.NavierStokesAndEuler.Euler.TimeWeakBoundary

/-!
# The mean variational solve determines its actual initial momentum trace

All solenoidal terminal-H¹ tests, including those nonzero initially, identify
an explicit AC momentum representative. Its initial value is the adjoint
frame applied to the original `M0 + L A` boundary force.
-/

@[expose] public section


noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive EulerMeanSolenoidal EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTransverseMomentumRegularity EulerTimeWeakBoundary

-- Cache the nested Hilbert-space instances used throughout the operator identities.
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanMomentumBoundary1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanMomentumBoundary2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanMomentumBoundary3 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanMomentumBoundary4 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanMomentumBoundary5 (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanMomentumBoundary6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace)
    := inferInstance

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- The original initial boundary force, expressed in the actual solenoidal coordinate space. -/
def meanBoundaryFlux (M0 A : L2 →L[ℝ] L2) (L : ℝ) (u : meanDerivatives T hT FInv) :
    solenoidalSpace :=
  (solenoidalFrame T F ⟨0, le_rfl, hT⟩).adjoint
    ((M0+L • A) (meanTrace T hT FInv u))

/-- The full mean weak equation, in actual momentum variables, retains the
original boundary force for every genuine solenoidal terminal-H¹ test. -/
theorem meanMomentum_full_weak
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)
    (u : meanDerivatives T hT FInv) (f : TimeLp T L2)
    (hu : ∀ w : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (w : TimeLp T L2)⟫_ℝ -
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv w⟫_ℝ +
        ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ +
        L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ =
        -⟪f, meanPrimitive T hT FInv w⟫_ℝ)
    (v : TimeLp T solenoidalSpace) :
    ⟪momentum T hT (solenoidalFrame T F) (u : TimeLp T L2), v⟫_ℝ +
      ⟪momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F') H
        (u : TimeLp T L2) f, primitiveTimeLp T hT v⟫_ℝ +
      ⟪meanBoundaryFlux T hT FInv F M0 A L u, initialTrace T hT v⟫_ℝ = 0 := by
  have h := hu (meanTestMap T hT FInv F F' hF hInv v)
  have htrace := meanTestMap_trace T hT FInv F F' hF hInv v
  change meanTrace T hT FInv (meanTestMap T hT FInv F F' hF hInv v) =
    solenoidalFrame T F ⟨0, le_rfl, hT⟩ (initialTrace T hT v) at htrace
  have hp := meanTestMap_primitive T hT FInv F F' hF hInv v
  have hk := congrArg (fun w : TimeLp T L2 => ⟪(u : TimeLp T L2), w⟫_ℝ)
    (meanTestMap_coe T hT FInv F F' hF hInv v)
  have hpot := congrArg
    (fun w : TimeLp T L2 => ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), w⟫_ℝ) hp
  have hforce := congrArg (fun w : TimeLp T L2 => ⟪f, w⟫_ℝ) hp
  have hm := congrArg (fun x : L2 => ⟪M0 (meanTrace T hT FInv u), x⟫_ℝ) htrace
  have ha := congrArg (fun x : L2 => L*⟪A (meanTrace T hT FInv u), x⟫_ℝ) htrace
  have htest :
      ⟪(u : TimeLp T L2), productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F') v⟫_ℝ -
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u),
          timeMultiplier T hT (solenoidalFrame T F) (primitiveTimeLp T hT v)⟫_ℝ +
        ⟪M0 (meanTrace T hT FInv u),
          solenoidalFrame T F ⟨0, le_rfl, hT⟩ (initialTrace T hT v)⟫_ℝ +
        L*⟪A (meanTrace T hT FInv u),
          solenoidalFrame T F ⟨0, le_rfl, hT⟩ (initialTrace T hT v)⟫_ℝ =
        -⟪f, timeMultiplier T hT (solenoidalFrame T F) (primitiveTimeLp T hT v)⟫_ℝ := by
    linarith only [h, hk, hpot, hforce, hm, ha]
  simp only [meanPrimitive, comp_apply, Submodule.subtypeL_apply,
    productDerivative, add_apply, inner_add_right] at htest
  simp only [momentum, momentumForcing, meanBoundaryFlux, inner_add_left,
    inner_sub_left, adjoint_inner_left, add_apply, smul_apply, real_inner_smul_left]
  linarith only [htest]

/-- The weak mean solution has a genuine AC momentum representative whose initial
value is derived from the original boundary form. -/
theorem meanMomentum_with_initial
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)
    (u : meanDerivatives T hT FInv) (f : TimeLp T L2)
    (hu : ∀ w : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (w : TimeLp T L2)⟫_ℝ -
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv w⟫_ℝ +
        ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ +
        L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ =
        -⟪f, meanPrimitive T hT FInv w⟫_ℝ) :
    ∃ p : ℝ → solenoidalSpace, AbsolutelyContinuousOnInterval p 0 T ∧
      p 0 = meanBoundaryFlux T hT FInv F M0 A L u ∧
      (momentum T hT (solenoidalFrame T F) (u : TimeLp T L2) : ℝ → solenoidalSpace)
        =ᵐ[timeMeasure T] p ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt p (momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F')
          H (u : TimeLp T L2) f t) t :=
  exists_ac_representative_with_initial T hT
    (momentum T hT (solenoidalFrame T F) (u : TimeLp T L2))
    (momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F') H (u : TimeLp T L2) f)
    (meanBoundaryFlux T hT FInv F M0 A L u)
    (meanMomentum_full_weak T hT FInv F F' hF hInv H M0 A L u f hu)

/-- The constructed mean inverse therefore has the genuine derived initial
momentum trace, before cancellation with the initial deformation derivative. -/
theorem meanSolver_momentum_with_initial
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2)
    (L K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K*‖z‖^2)
    (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
      -B*‖z‖^2 ≤ ⟪M0 z, z⟫_ℝ+L*⟪A z, z⟫_ℝ)
    (hsmall : K*(T^2/2)+B*T ≤ 1/2) (f : TimeLp T L2) :
    let u := meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f
    ∃ p : ℝ → solenoidalSpace, AbsolutelyContinuousOnInterval p 0 T ∧
      p 0 = meanBoundaryFlux T hT FInv F M0 A L u ∧
      (momentum T hT (solenoidalFrame T F) (u : TimeLp T L2) : ℝ → solenoidalSpace)
        =ᵐ[timeMeasure T] p ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt p (momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F')
          H (u : TimeLp T L2) f t) t :=
  meanMomentum_with_initial T hT FInv F F' hF hInv H M0 A L
    (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f) f
    (meanSolver_weak T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f)

end EulerMeanVariationalInverse
