/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Energy
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordTime
public import LeanPool.NavierStokesAndEuler.Euler.SmoothEulerEvolution

@[expose] public section

/-! Actual Euler evolutions and their genuine H³ difference-energy law.
The record contains only the fields, their classical Euler equation,
the Helmholtz constraints, and continuity of their ordinary L² jets. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerVolterraConvolution Finset
open scoped ContDiff

private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance

structure Evolution (T : ℝ) (hT : 0 ≤ T) where
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  pressureForce : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t => (velocity t).jetLp n)
  pressure_continuous : ∀ n, Continuous (fun t => (pressureForce t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  gradient : ∀ t, (pressureForce t).toLp ∈ gradientSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r => (velocity (projIcc 0 T hT r)).field x)
      (-fderiv ℝ (velocity ⟨t,ht.1.le,ht.2.le⟩).field x
        ((velocity ⟨t,ht.1.le,ht.2.le⟩).field x)-
          (pressureForce ⟨t,ht.1.le,ht.2.le⟩).field x) t

def evolutionOfClassical (T : ℝ) (hT : 0 ≤ T)
    (U G : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n))
    (hG : ∀ n, Continuous (fun t => (G t).jetLp n))
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (hu : ∀ (t : Icc (0 : ℝ) T) x, u (t,x)=(U t).field x)
    (hp : ∀ (t : Icc (0 : ℝ) T), Differentiable ℝ (fun x => p (t,x)))
    (hg : ∀ (t : Icc (0 : ℝ) T) x, gradient (fun y => p (t,y)) x=(G t).field x)
    (hdiv : ∀ t x, divergence (U t).field x=0)
    (hdiff : ∀ t ∈ Ioo 0 T, ∀ x, DifferentiableAt ℝ u (t,x))
    (heuler : ∀ t ∈ Ioo 0 T, ∀ x, EulerLagrangian.momentumResidual u p (t,x)=0) :
    Evolution T hT where
  velocity := U
  pressureForce := G
  velocity_continuous := hU
  pressure_continuous := hG
  solenoidal t := smooth_mem_solenoidal (U t).field (U t).smooth (U t).memLp (hdiv t)
  gradient t := gradient_mem (G t) (fun x => p (t,x))
    (potential_smooth (G t) _ (hp t) (fun x => (hg t x).symm)) (fun x => (hg t x).symm)
  time_law := EulerSmoothEulerEvolution.pointwise_time_derivative_of_classical T hT U G
    u p hu hg hdiff heuler

theorem continuous_jet_fieldSub {K : Type*} [TopologicalSpace K]
    (A B : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (fieldSub (A t) (B t)).jetLp n) :=
  continuous_jetLp_addField A (fun t => fieldNeg (B t)) hA
    (continuous_jetLp_mapField _ B hB) n

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

def derivative (U : Evolution T hT) : Icc (0 : ℝ) T → SmoothL2Field Space :=
  EulerSmoothEulerEvolution.rhs U.velocity U.velocity_continuous U.pressureForce

theorem derivative_field (U : Evolution T hT) (t : Icc (0 : ℝ) T) (x : Space) :
    (U.derivative t).field x = -fderiv ℝ (U.velocity t).field x ((U.velocity t).field x)-
      (U.pressureForce t).field x :=
  EulerSmoothEulerEvolution.rhs_field U.velocity U.velocity_continuous U.pressureForce t x

theorem derivative_continuous (U : Evolution T hT) (n : ℕ) :
    Continuous (fun t => (U.derivative t).jetLp n) :=
  EulerSmoothEulerEvolution.rhs_jet_continuous U.velocity U.velocity_continuous
    U.pressureForce U.pressure_continuous n

def difference (U V : Evolution T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  fieldSub (V.velocity t) (U.velocity t)

def pressureDifference (U V : Evolution T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  fieldSub (V.pressureForce t) (U.pressureForce t)

def differenceDerivative (U V : Evolution T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  fieldSub (V.derivative t) (U.derivative t)

theorem difference_continuous (U V : Evolution T hT) (n : ℕ) :
    Continuous (fun t => (U.difference V t).jetLp n) :=
  continuous_jet_fieldSub V.velocity U.velocity V.velocity_continuous U.velocity_continuous n

theorem differenceDerivative_continuous (U V : Evolution T hT) (n : ℕ) :
    Continuous (fun t => (U.differenceDerivative V t).jetLp n) :=
  continuous_jet_fieldSub V.derivative U.derivative V.derivative_continuous U.derivative_continuous
    n

theorem differenceDerivative_eq (U V : Evolution T hT) (t : Icc (0 : ℝ) T) :
    U.differenceDerivative V t =
      differenceRhs (U.velocity t) (U.difference V t) (U.pressureDifference V t) := by
  apply field_ext
  funext x
  have he : (U.difference V t).field=(V.velocity t).field-(U.velocity t).field :=
    funext (fieldSub_field (V.velocity t) (U.velocity t))
  rw [differenceRhs_field,he,fderiv_sub ((V.velocity t).smooth.differentiable (by simp) x)
    ((U.velocity t).smooth.differentiable (by simp) x)]
  simp only [differenceDerivative,pressureDifference,fieldSub_field,
    derivative_field,Pi.sub_apply,sub_apply,map_sub]
  abel_nf

theorem difference_time_law (U V : Evolution T hT) :
    ∀ t (ht : t ∈ Ioo 0 T) x,
      HasDerivAt (fun r => (U.difference V (projIcc 0 T hT r)).field x)
        ((U.differenceDerivative V ⟨t,ht.1.le,ht.2.le⟩).field x) t := by
  intro t ht x
  have h := (V.time_law t ht x).sub (U.time_law t ht x)
  convert! h using 1
  simp only [differenceDerivative,fieldSub_field,derivative_field]

def energyPath (U V : Evolution T hT) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => wordEnergy 3 (U.difference V t),wordEnergy_continuous _ (U.difference_continuous V) 3⟩

def energyDerivative (U V : Evolution T hT) (t : Icc (0 : ℝ) T) : ℝ :=
  energyProduction (U.difference V t) (U.differenceDerivative V t)

theorem energy_hasDerivWithinAt (U V : Evolution T hT) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.energyPath V)) (U.energyDerivative V t)
      (Icc (0 : ℝ) T) t :=
  wordEnergy_hasDerivWithinAt T hT (U.difference V) (U.differenceDerivative V)
    (U.difference_continuous V) (U.differenceDerivative_continuous V) (U.difference_time_law V) 3 t

theorem energyDerivative_bound (U V : Evolution T hT) (M : ℝ)
    (hM : ∀ t, WordBound 4 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    U.energyDerivative V t ≤ 3600*h3ProductConstant*(M+Real.sqrt (U.energyPath V t))*U.energyPath V
      t := by
  rw [energyDerivative,differenceDerivative_eq]
  apply difference_energy_bound _ _ _ M (hM t)
  · have he : (addField (U.velocity t) (U.difference V t)).field=(V.velocity t).field := by
      funext x
      simp only [addField_field,difference,fieldSub_field]
      abel
    rw [he]
    exact solenoidal_representative_divergence _ (V.solenoidal t) _ (V.velocity t).smooth
      (V.velocity t).toLp_ae
  · rw [difference,toLp_fieldSub]
    exact solenoidalSpace.sub_mem (V.solenoidal t) (U.solenoidal t)
  · rw [pressureDifference,toLp_fieldSub]
    exact gradientSpace.sub_mem (V.gradient t) (U.gradient t)

end Evolution
end EulerOrdinarySobolev
