/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanDisplacementRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseMomentumRegularity
import LeanPool.NavierStokesAndEuler.Euler.TimeWeakDerivative

/-!
# Genuine mean momentum regularity from the variational solve

Zero-initial-trace solenoidal test primitives are mapped by F into the actual
mean test space. The two original boundary terms then vanish, and the weak
identity constructs an AC representative of `Pσ F* η_t`. This is a regularity
conclusion, not an assumed momentum equation or an assumed second derivative.
-/

@[expose] public section


noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution EulerMeanSolenoidal
  EulerTimeH1OperatorProduct EulerTimeWeakDerivative EulerTransverseMomentumRegularity

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- The frame adjoint is the actual ordinary solenoidal projection of `F*`. -/
theorem solenoidalFrame_adjoint (t : Icc (0 : ℝ) T) :
    (solenoidalFrame T F t).adjoint =
      solenoidalSpace.orthogonalProjectionOnto.comp (F t).adjoint := by
  change ((F t).comp solenoidalSpace.subtypeL).adjoint = _
  calc
    _ = solenoidalSpace.subtypeL.adjoint.comp (F t).adjoint :=
      adjoint_comp _ _
    _ = _ := congrArg (fun A : L2 →L[ℝ] solenoidalSpace => A.comp (F t).adjoint)
      (Submodule.adjoint_subtypeL solenoidalSpace)

/-- Thus the momentum's actual representative is `Pσ F* u`, with ordinary
spatial L² projection and no abstract replacement of the solenoidal space. -/
theorem meanMomentum_ae (u : TimeLp T L2) :
    (fun t => ((momentum T hT (solenoidalFrame T F) u t : solenoidalSpace) : L2))
      =ᵐ[timeMeasure T]
      fun t => solenoidalProjection ((extendPath T hT F t).adjoint (u t)) := by
  filter_upwards [momentum_ae T hT (solenoidalFrame T F) u] with t ht
  rw [ht]
  change (((solenoidalFrame T F (projIcc 0 T hT t)).adjoint (u t) : solenoidalSpace) : L2) = _
  exact congrArg (fun A : L2 →L[ℝ] solenoidalSpace => (A (u t) : L2))
    (solenoidalFrame_adjoint T F (projIcc 0 T hT t))

/-- The exact mean variational identity determines the weak derivative of its
actual projected momentum after the trace-zero test restriction. -/
theorem meanMomentum_weak
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
    (v : TimeLp T solenoidalSpace) (hv : initialTrace T hT v = 0) :
    ⟪momentum T hT (solenoidalFrame T F) (u : TimeLp T L2), v⟫_ℝ =
      -⟪momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F') H
        (u : TimeLp T L2) f, primitiveTimeLp T hT v⟫_ℝ := by
  apply momentum_weak_of_product_tests T hT (solenoidalFrame T F) (solenoidalFrame T F')
    (solenoidalFrame_hasDerivWithinAt T hT F F' hF) H (u : TimeLp T L2) f v
  have h := hu (meanTestMap T hT FInv F F' hF hInv v)
  simpa only [meanTestMap_trace_zero T hT FInv F F' hF hInv v hv,
    inner_zero_right, mul_zero, add_zero, meanPrimitive, comp_apply,
    Submodule.subtypeL_apply, meanTestMap_coe] using h

/-- An actual weak mean solution has an AC momentum representative with the
explicit Bochner L² derivative forced by the variational identity. -/
theorem meanMomentum_ac (hTpos : 0 < T)
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
    ∃ p : ℝ → solenoidalSpace,
      AbsolutelyContinuousOnInterval p 0 T ∧
      (momentum T hT (solenoidalFrame T F) (u : TimeLp T L2) : ℝ → solenoidalSpace)
        =ᵐ[timeMeasure T] p ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt p (momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F')
          H (u : TimeLp T L2) f t) t := by
  apply exists_ac_representative_of_weak T hTpos
  intro v hv
  exact meanMomentum_weak T hT FInv F F' hF hInv H M0 A L u f hu v hv

/-- In particular the already constructed mean variational inverse has genuine
projected momentum regularity. The coefficient/boundary lower bounds are used
only by that solve; no regularity of the answer is assumed. -/
theorem meanSolver_momentum_ac (hTpos : 0 < T)
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
    let u : TimeLp T L2 :=
      meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f
    ∃ p : ℝ → solenoidalSpace,
      AbsolutelyContinuousOnInterval p 0 T ∧
      (momentum T hT (solenoidalFrame T F) u : ℝ → solenoidalSpace) =ᵐ[timeMeasure T] p ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt p (momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F') H u f t) t
            :=
  meanMomentum_ac T hT FInv F F' hTpos hF hInv H M0 A L
    (meanSolver T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f) f
    (meanSolver_weak T hT FInv H M0 A L K B hK hB hF0 hH hboundary hsmall f)

end EulerMeanVariationalInverse
