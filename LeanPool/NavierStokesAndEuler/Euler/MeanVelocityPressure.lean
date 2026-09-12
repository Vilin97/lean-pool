/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanDisplacementRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongEquation

/-!
# The actual mean velocity and pressure-gradient residual

From a genuine strong mean evolution, construct B=F z_t in Bochner L², its
actual time derivative, and the residual f-B_t-MB. Its F-adjoint transform is
in the ordinary L² gradient space by the proved strong projected equation.
-/

@[expose] public section


noncomputable section


namespace EulerMeanVariationalInverse.StrongMeanEvolution

open MeasureTheory Set EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerVolterraConvolution EulerTimeH1FieldProduct

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The actual physical velocity B=F z_t as a Bochner L² field. -/
def velocityField : TimeLp T L2 :=
  timeMultiplier T hT (solenoidalFrame T F) s.velocityLp

/-- The actual continuous physical-velocity representative. -/
def physicalPath : ℝ → L2 := fun t => extendPath T hT F t (s.velocity t : L2)

/-- The product-rule candidate for B_t, constructed in actual Bochner L². -/
def velocityDerivative : TimeLp T L2 :=
  fieldProductDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    s.velocityLp s.acceleration

/-- This field really is B_t, and B has an actual absolutely continuous representative. -/
theorem physical_h1
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t) :
    AbsolutelyContinuousOnInterval s.physicalPath 0 T ∧
      (s.velocityField : ℝ → L2) =ᵐ[timeMeasure T] s.physicalPath ∧
      ∀ᵐ t ∂timeMeasure T, HasDerivAt s.physicalPath (s.velocityDerivative t) t :=
  fieldProduct_h1 T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    (solenoidalFrame_hasDerivWithinAt T hT F F₁ hF) s.velocityLp s.acceleration
    s.velocity s.velocity_ac s.velocity_ae s.velocity_derivative

/-- In label coordinates the actual physical velocity is solenoidal at every time. -/
theorem inversePhysicalPath_solenoidal
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x) (t : ℝ) :
    extendPath T hT FInv t (s.physicalPath t) ∈ solenoidalSpace := by
  change FInv (projIcc 0 T hT t) (F (projIcc 0 T hT t) (s.velocity t : L2)) ∈ solenoidalSpace
  rw [hInv]
  exact (s.velocity t).property

/-- The pressure residual in the strong equation, before using F_t=MF. -/
def pressureResidual : TimeLp T L2 :=
  f - timeMultiplier T hT (solenoidalFrame T F) s.acceleration -
    (2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp

/-- The residual has its literal pointwise strong-equation representative. -/
theorem pressureResidual_ae :
    (s.pressureResidual : ℝ → L2) =ᵐ[timeMeasure T] fun t =>
      f t - extendPath T hT F t (s.acceleration t : L2) -
        (2 : ℝ) • extendPath T hT F₁ t (s.velocity t : L2) := by
  filter_upwards [Lp.coeFn_sub (f-timeMultiplier T hT (solenoidalFrame T F) s.acceleration)
      ((2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp),
    Lp.coeFn_sub f (timeMultiplier T hT (solenoidalFrame T F) s.acceleration),
    Lp.coeFn_smul (2 : ℝ) (timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp),
    timeMultiplier_ae T hT (solenoidalFrame T F) s.acceleration,
    timeMultiplier_ae T hT (solenoidalFrame T F₁) s.velocityLp, s.velocity_ae]
    with t hs₂ hs₁ hsmul ha hv hvrep
  simp only [Pi.sub_apply, Pi.smul_apply] at hs₂ hs₁ hsmul
  change (f-timeMultiplier T hT (solenoidalFrame T F) s.acceleration -
    (2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp) t = _
  have hv' := hv.trans (congrArg
    (fun w : solenoidalSpace => F₁ (projIcc 0 T hT t) (w : L2)) hvrep)
  exact hs₂.trans (congrArg₂ (fun x y : L2 => x-y)
    (hs₁.trans (congrArg (fun x : L2 => f t-x) ha))
    (hsmul.trans (congrArg (fun x : L2 => (2 : ℝ) • x) hv')))

/-- The actual pressure residual has an ordinary weak L² gradient after F-adjoint
transformation. This follows from the proved projected equation. -/
theorem pressureResidual_gradient_ae :
    ∀ᵐ t ∂timeMeasure T,
      (extendPath T hT F t).adjoint (s.pressureResidual t) ∈ gradientSpace := by
  filter_upwards [s.pressureResidual_ae, s.equation] with t hp he
  apply (solenoidalProjection_eq_zero_iff _).1
  have hb : f t - extendPath T hT F t (s.acceleration t : L2) -
      (2 : ℝ) • extendPath T hT F₁ t (s.velocity t : L2) =
      (f t - (2 : ℝ) • extendPath T hT F₁ t (s.velocity t : L2)) -
        extendPath T hT F t (s.acceleration t : L2) := by abel
  have hh := congrArg (fun x : L2 => solenoidalProjection ((F (projIcc 0 T hT t)).adjoint x))
    (hp.trans hb)
  have hl := (solenoidalProjection.comp (F (projIcc 0 T hT t)).adjoint).map_sub
    (f t - (2 : ℝ) • extendPath T hT F₁ t (s.velocity t : L2))
    (extendPath T hT F t (s.acceleration t : L2))
  exact hh.trans (hl.trans (sub_eq_zero.mpr he.symm))

/-- The prescribed coefficient identity F_t=MF holds for the actual velocity field. -/
theorem movingVelocityField_eq (M : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (hM : ∀ (t : Icc (0 : ℝ) T) (x : L2), F₁ t x = M t (F t x)) :
    timeMultiplier T hT M s.velocityField =
      timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT M s.velocityField,
    timeMultiplier_ae T hT (solenoidalFrame T F) s.velocityLp,
    timeMultiplier_ae T hT (solenoidalFrame T F₁) s.velocityLp] with t hmul hv hv₁
  exact hmul.trans ((congrArg (fun x : L2 => M (projIcc 0 T hT t) x) hv).trans
    ((hM (projIcc 0 T hT t) (s.velocityLp t : L2)).symm.trans hv₁.symm))

/-- The reconstructed fields satisfy the actual evolution B_t+MB+dq=f in L². -/
theorem velocity_evolution (M : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (hM : ∀ (t : Icc (0 : ℝ) T) (x : L2), F₁ t x = M t (F t x)) :
    s.velocityDerivative + timeMultiplier T hT M s.velocityField + s.pressureResidual = f := by
  calc
    _ = s.velocityDerivative + timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp +
        s.pressureResidual := congrArg
      (fun x : TimeLp T L2 => s.velocityDerivative+x+s.pressureResidual)
      (s.movingVelocityField_eq M hM)
    _ = f := by
      simp only [velocityDerivative, fieldProductDerivative, pressureResidual, two_smul]
      abel

/-- The initial physical velocity is exactly the source's localized boundary value. -/
theorem physicalPath_initial
    (hF₀ : F ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2) :
    s.physicalPath 0 = L • A (s.label 0 : L2) := by
  change F (projIcc 0 T hT 0) (s.velocity 0 : L2) = _
  rw [projIcc_of_mem hT ⟨le_rfl, hT⟩, hF₀, ContinuousLinearMap.id_apply]
  exact s.initial_velocity

end EulerMeanVariationalInverse.StrongMeanEvolution
