/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEquation
public import LeanPool.NavierStokesAndEuler.Euler.MeanVariationalInverse
import LeanPool.NavierStokesAndEuler.Euler.MeanFrameCoefficients
import LeanPool.NavierStokesAndEuler.Euler.MeanMomentumBoundary

/-!
# The actual mean strong equation and initial velocity condition

The time variational solution is upgraded to genuine H² solenoidal coordinates
using its derived AC momentum and the constructed coercive Gram inverse. The
initial momentum trace then cancels the original M0 boundary term. The final
fields contain the actual projected equation (9) and `z_t(0)=L A z(0)`.
-/

@[expose] public section


noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive EulerMeanSolenoidal EulerVolterraConvolution
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseCoordinateRegularity
  EulerTransverseMomentumRegularity EulerTransverseStrongAlgebra EulerTransverseStrongEquation

/-- The source's strong mean evolution, with actual time functions and actual
Bochner L² acceleration. Every derivative assertion concerns these functions. -/
structure StrongMeanEvolution (T : ℝ) (hT : 0 ≤ T)
    (FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (A : L2 →L[ℝ] L2) (L : ℝ) (u f : TimeLp T L2) where
  /-- Label of `StrongMeanEvolution`, of type `ℝ → solenoidalSpace`. -/
  label : ℝ → solenoidalSpace
  /-- Velocity field of `StrongMeanEvolution`, of type `ℝ → solenoidalSpace`. -/
  velocity : ℝ → solenoidalSpace
  /-- Velocity Lᵖ of `StrongMeanEvolution`, of type `TimeLp T solenoidalSpace`. -/
  velocityLp : TimeLp T solenoidalSpace
  velocity_ae : (velocityLp : ℝ → solenoidalSpace) =ᵐ[timeMeasure T] velocity
  /-- Acceleration of `StrongMeanEvolution`, of type `TimeLp T solenoidalSpace`. -/
  acceleration : TimeLp T solenoidalSpace
  label_eq : ∀ t : Icc (0 : ℝ) T,
    (label t : L2) = FInv t (realPrimitive T u t)
  label_ac : AbsolutelyContinuousOnInterval label 0 T
  velocity_ac : AbsolutelyContinuousOnInterval velocity 0 T
  terminal : label T = 0
  initial_velocity : (velocity 0 : L2) = L • A (label 0 : L2)
  label_derivative : ∀ᵐ t ∂timeMeasure T, HasDerivAt label (velocity t) t
  velocity_derivative : ∀ᵐ t ∂timeMeasure T, HasDerivAt velocity (acceleration t) t
  equation : ∀ᵐ t ∂timeMeasure T,
    solenoidalProjection ((extendPath T hT F t).adjoint
      (extendPath T hT F t (acceleration t : L2))) =
    solenoidalProjection ((extendPath T hT F t).adjoint
      (f t - (2 : ℝ) • extendPath T hT F₁ t (velocity t : L2)))

/-- At the initial identity frame, the derived momentum condition cancels M0.
The range assumption here is only the genuine solenoidal range of A. -/
theorem initial_momentum_cancellation (F₀ F₁ M0 A : L2 →L[ℝ] L2) (L : ℝ)
    (hF₀ : F₀ = ContinuousLinearMap.id ℝ L2) (hF₁ : F₁ = M0)
    (z v : solenoidalSpace) (hAz : A (z : L2) ∈ solenoidalSpace)
    (hm : gram (F₀.comp solenoidalSpace.subtypeL) v +
      (F₀.comp solenoidalSpace.subtypeL).adjoint (F₁ (z : L2)) =
      (F₀.comp solenoidalSpace.subtypeL).adjoint ((M0 + L • A) (z : L2))) :
    (v : L2) = L • A (z : L2) := by
  subst F₀ F₁
  have hm' : v + solenoidalSpace.orthogonalProjectionOnto (M0 (z : L2)) =
      solenoidalSpace.orthogonalProjectionOnto ((M0+L • A) (z : L2)) := by
    simpa only [id_comp, gram, Submodule.adjoint_subtypeL, comp_apply,
      Submodule.subtypeL_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hm
  simp only [add_apply, smul_apply, map_add, map_smul] at hm'
  have hv : v = L • solenoidalSpace.orthogonalProjectionOnto (A (z : L2)) := by
    apply add_left_cancel (a := solenoidalSpace.orthogonalProjectionOnto (M0 (z : L2)))
    exact (add_comm _ _).trans hm'
  have hproj : (solenoidalSpace.orthogonalProjectionOnto (A (z : L2)) : L2) = A (z : L2) :=
    congrArg (fun w : solenoidalSpace => (w : L2))
      (solenoidalSpace.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A (z : L2), hAz⟩)
  have he := congrArg (fun w : solenoidalSpace => (w : L2)) hv
  change (v : L2) = L • (solenoidalSpace.orthogonalProjectionOnto (A (z : L2)) : L2) at he
  exact he.trans (congrArg (fun x : L2 => L • x) hproj)

/-- A frame Gram equation on L²σ is exactly the ordinary projected spatial equation. -/
theorem ordinary_projected_equation (F F₁ : L2 →L[ℝ] L2) (f : L2)
    (a v : solenoidalSpace)
    (h : gram (F.comp solenoidalSpace.subtypeL) a =
      (F.comp solenoidalSpace.subtypeL).adjoint (f - (2 : ℝ) • F₁ (v : L2))) :
    solenoidalProjection (F.adjoint (F (a : L2))) =
      solenoidalProjection (F.adjoint (f-(2 : ℝ) • F₁ (v : L2))) := by
  have he := congrArg (fun w : solenoidalSpace => (w : L2)) h
  simpa only [gram, adjoint_comp, Submodule.adjoint_subtypeL, comp_apply,
    Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply,
    solenoidalProjection] using he

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F₁ F₂ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (M0 A : L2 →L[ℝ] L2) (L : ℝ)

/-- A genuine mean weak solution has actual H² label coordinates, the literal
projected equation, and the original initial velocity condition. -/
theorem meanWeakSolution_strong
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hF₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F₁) (F₂ t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x)
    (hFInv₀ : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
    (hF₁₀ : F₁ ⟨0, le_rfl, hT⟩ = M0)
    (hODE : ∀ t, F₂ t = -(H t).comp (F t))
    (hAσ : ∀ z : L2, z ∈ solenoidalSpace → A z ∈ solenoidalSpace)
    (u : meanDerivatives T hT FInv) (f : TimeLp T L2)
    (hu : ∀ w : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (w : TimeLp T L2)⟫_ℝ -
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv w⟫_ℝ +
        ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ +
        L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ =
        -⟪f, meanPrimitive T hT FInv w⟫_ℝ) :
    Nonempty (StrongMeanEvolution T hT FInv F F₁ A L (u : TimeLp T L2) f) := by
  let Q := solenoidalFrame T F
  let Q₁ := solenoidalFrame T F₁
  let Q₂ := solenoidalFrame T F₂
  let c := meanFrameCoercivity T FInv
  have hc : 0 < c := meanFrameCoercivity_pos T FInv
  have hQ : ∀ t x, c*‖x‖^2 ≤ ‖Q t x‖^2 := solenoidalFrame_lower T FInv F hInv
  have hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t :=
    solenoidalFrame_hasDerivWithinAt T hT F F₁ hF
  have hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t :=
    solenoidalFrame_hasDerivWithinAt T hT F₁ F₂ hF₁
  have hRange : ∀ t : Icc (0 : ℝ) T, ∃ x : solenoidalSpace, Q t x = realPrimitive T (u : TimeLp T
      L2) t :=
    meanPrimitive_in_frame_range T hT FInv F hRight u
  have hframe : ∀ t, Q₂ t = -(H t).comp (Q t) := solenoidalFrame_ode T F F₂ H hODE
  obtain ⟨p, hpAC, hp₀, hp, hpder⟩ :=
    meanMomentum_with_initial T hT FInv F F₁ hF hInv H M0 A L u f hu
  let z := coordinatePrimitive T hT Q c hc hQ (u : TimeLp T L2)
  let v := velocityRepresentative T hT Q Q₁ c hc hQ (u : TimeLp T L2) p
  let a := coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H (u : TimeLp T L2) f
  have hV := velocityRepresentative_h1 T hT Q Q₁ Q₂ c hc hQ hd hd₁
    H (u : TimeLp T L2) f hRange p hpAC hp hpder
  have hz : ∀ t : Icc (0 : ℝ) T, (z t : L2) = FInv t (realPrimitive T (u : TimeLp T L2) t) := by
    intro t
    have hrec := coordinatePrimitive_reconstruct_of_range T hT Q c hc hQ
      (u : TimeLp T L2) hRange t
    have hi := congrArg (fun x : L2 => FInv t x) hrec
    change FInv t (F t (z t : L2)) = _ at hi
    exact (hInv t (z t : L2)).symm.trans hi
  have hF₀ : F ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2 := by
    apply ContinuousLinearMap.ext
    intro x
    simpa only [hFInv₀, id_apply] using hInv ⟨0, le_rfl, hT⟩ x
  have hz₀ : (z 0 : L2) = meanTrace T hT FInv u := by
    have h := hz ⟨0, le_rfl, hT⟩
    exact h.trans (congrArg (fun G : L2 →L[ℝ] L2 =>
      G (realPrimitive T (u : TimeLp T L2) 0)) hFInv₀)
  refine ⟨{
    label := z
    velocity := v
    velocityLp := coordinateDerivative T hT Q Q₁ c hc hQ (u : TimeLp T L2)
    velocity_ae := hV.2.1
    acceleration := a
    label_eq := hz
    label_ac := coordinatePrimitive_absolutelyContinuous T hT Q Q₁ c hc hQ hd (u : TimeLp T L2)
    velocity_ac := hV.1
    terminal := coordinatePrimitive_terminal T hT Q c hc hQ (u : TimeLp T L2)
    initial_velocity := ?_
    label_derivative := ?_
    velocity_derivative := hV.2.2
    equation := ?_
  }⟩
  · have hm := velocityRepresentative_momentum T hT Q Q₁ c hc hQ (u : TimeLp T L2) p 0
    simp only [extendPath, projIcc_of_mem hT ⟨le_rfl, hT⟩,
      gramPath, mixedPath] at hm
    have hm := hm.trans hp₀
    change gram ((F ⟨0, le_rfl, hT⟩).comp solenoidalSpace.subtypeL) (v 0) +
      ((F ⟨0, le_rfl, hT⟩).comp solenoidalSpace.subtypeL).adjoint
        (F₁ ⟨0, le_rfl, hT⟩ (z 0 : L2)) =
      ((F ⟨0, le_rfl, hT⟩).comp solenoidalSpace.subtypeL).adjoint
        ((M0+L • A) (meanTrace T hT FInv u)) at hm
    have hb := congrArg (fun x : L2 =>
      ((F ⟨0, le_rfl, hT⟩).comp solenoidalSpace.subtypeL).adjoint ((M0+L • A) x)) hz₀.symm
    exact initial_momentum_cancellation _ _ M0 A L hF₀ hF₁₀ (z 0) (v 0)
      (hAσ (z 0 : L2) (z 0).property) (hm.trans hb)
  · filter_upwards [coordinatePrimitive_hasDerivAt_ae T hT Q Q₁ c hc hQ hd
      (u : TimeLp T L2), hV.2.1] with t hdt hvt
    exact hdt.congr_deriv hvt
  · filter_upwards [velocityRepresentative_projected_equation T hT Q Q₁ Q₂ c hc hQ hd hd₁
      H (u : TimeLp T L2) f hRange hframe p hpAC hp hpder, hV.2.1] with t he hvt
    have hr := congrArg (fun w : solenoidalSpace =>
      (Q (projIcc 0 T hT t)).adjoint (f t - (2 : ℝ) • Q₁ (projIcc 0 T hT t) w)) hvt
    exact ordinary_projected_equation (F (projIcc 0 T hT t)) (F₁ (projIcc 0 T hT t))
      (f t) (a t) (v t) (he.trans hr)

end EulerMeanVariationalInverse
