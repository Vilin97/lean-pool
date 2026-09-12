/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Energy
public import LeanPool.NavierStokesAndEuler.Euler.SmoothEulerEvolution
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordTime
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
import LeanPool.NavierStokesAndEuler.Euler.MeanOrbitSmoothL2Field
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
import LeanPool.NavierStokesAndEuler.Euler.MeanWeakCurl
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryL2Integration
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! Actual Euler evolutions and their genuine H³ difference-energy law.
The record contains only the fields, their classical Euler equation,
the Helmholtz constraints, and continuity of their ordinary L² jets. -/

section

/-! A genuine smooth L² gradient belongs to the closed ordinary gradient
space, even when its scalar potential is not square-integrable. The
solenoidal remainder is both curl-free and harmonic, hence zero by the
actual L² integration-by-parts identity. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanVectorIdentities
  EulerMeanSolenoidal EulerMeanSmoothRepresentative EulerMeanPressure EulerMeanClassical
  EulerMeanCutoffCurl EulerVectorCalculus Laplacian
open scoped ContDiff ENNReal

theorem solenoidal_orbit (A : SmoothL2Field Space) :
    SmoothOrbit (solenoidalProjection A.toLp) := by
  have he : (fun a : Space => EulerMeanSolenoidal.translation a (solenoidalProjection A.toLp)) =
      solenoidalProjection ∘ (fun a : Space => EulerMeanSolenoidal.translation a A.toLp) :=
    funext (fun a => solenoidalProjection_translation a A.toLp)
  change ContDiff ℝ ∞ _
  rw [he]
  exact solenoidalProjection.contDiff.comp A.translation_contDiff

theorem curl_zero_of_symmetric (A : SmoothL2Field Space)
    (hA : ∀ x i j, (fderiv ℝ A.field x (EuclideanSpace.single i 1)) j =
      (fderiv ℝ A.field x (EuclideanSpace.single j 1)) i) :
    vectorCurl A.field=0 := by
  funext x
  ext i
  change partialDerivative (fun y => A.field y (i+2)) (i+1) x -
    partialDerivative (fun y => A.field y (i+1)) (i+2) x=0
  simp only [partialDerivative,fderiv_coordinate A.field x
    (A.smooth.differentiable (by simp) x)]
  exact sub_eq_zero.mpr (hA x (i+1) (i+2))

theorem gradient_mem_of_symmetric (A : SmoothL2Field Space)
    (hA : ∀ x i j, (fderiv ℝ A.field x (EuclideanSpace.single i 1)) j =
      (fderiv ℝ A.field x (EuclideanSpace.single j 1)) i) :
    A.toLp ∈ gradientSpace := by
  let B := smoothL2Field (solenoidalProjection A.toLp) (solenoidal_orbit A)
  have hB : B.toLp=solenoidalProjection A.toLp := smoothL2Field_toLp _ _
  have hrep : (solenoidalProjection A.toLp : Space → Space)=ᵐ[volume] B.field := by
    rw [← hB]
    exact B.toLp_ae
  have hres : ((A.toLp-solenoidalProjection A.toLp : L2) : Space → Space)=ᵐ[volume] A.field-B.field
      := by
    filter_upwards [Lp.coeFn_sub A.toLp (solenoidalProjection A.toLp),A.toLp_ae,hrep]
      with x hs ha hb
    simp only [hs,ha,hb,Pi.sub_apply]
  have hsym := gradientSpace_classical_curl_zero _ (sub_solenoidalProjection_mem_gradient A.toLp)
    (A.field-B.field) hres (A.smooth.sub B.smooth)
  have hBc : ∀ x i j, (fderiv ℝ B.field x (EuclideanSpace.single i 1)) j =
      (fderiv ℝ B.field x (EuclideanSpace.single j 1)) i := by
    intro x i j
    have hd := hsym x i j
    rw [fderiv_sub (A.smooth.differentiable (by
        simp) x) (B.smooth.differentiable (by simp) x)] at hd
    simp only [sub_apply,PiLp.sub_apply] at hd
    linarith [hA x i j]
  have hcurl := curl_zero_of_symmetric B hBc
  have hdiv : divergence B.field=0 := funext
    (solenoidal_representative_divergence _ (solenoidalProjection_mem A.toLp) B.field B.smooth hrep)
  have hΔ : ∀ x, Δ B.field x=0 := by
    intro x
    have h := congrFun (vectorCurl_vectorCurl B.field B.smooth) x
    rw [hcurl,hdiv] at h
    have hc : vectorCurl (0 : Space → Space) x=0 := by
      ext i
      simp [vectorCurl,curl,partialDerivative]
    have hg : gradient (0 : Space → ℝ) x=0 := by simp [gradient]
    simp only [hc,hg,Pi.sub_apply,zero_sub] at h
    exact neg_eq_zero.mp h.symm
  have hz := field_zero_of_laplacian_zero B hΔ
  apply (solenoidalProjection_eq_zero_iff A.toLp).mp
  rw [← hB]
  apply Lp.ext
  filter_upwards [B.toLp_ae,Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hb hzero
  rw [hb,hz,Pi.zero_apply,hzero]
  rfl

theorem gradient_mem (A : SmoothL2Field Space) (p : Space → ℝ)
    (hp : ContDiff ℝ ∞ p) (hgrad : ∀ x, A.field x = gradient p x) :
    A.toLp ∈ gradientSpace := by
  apply gradient_mem_of_symmetric A
  intro x i j
  have hi : (fun y => A.field y i)=partialDerivative p i :=
    funext (fun y => by rw [hgrad,gradient_coordinate])
  have hj : (fun y => A.field y j)=partialDerivative p j :=
    funext (fun y => by rw [hgrad,gradient_coordinate])
  have h := partialDerivative_comm p (hp.of_le (by simp)) j i x
  rw [← hi,← hj] at h
  simpa only [partialDerivative,fderiv_coordinate A.field x
    (A.smooth.differentiable (by simp) x)] using h

theorem gradient_pairing_zero (A U : SmoothL2Field Space) (p : Space → ℝ)
    (hp : ContDiff ℝ ∞ p) (hgrad : ∀ x, A.field x = gradient p x)
    (hdiv : ∀ x, divergence U.field x = 0) : ⟪A.toLp,U.toLp⟫_ℝ=0 :=
  pressure_pairing_zero (gradient_mem A p hp hgrad)
    (smooth_mem_solenoidal U.field U.smooth U.memLp hdiv)

theorem potential_smooth (A : SmoothL2Field Space) (p : Space → ℝ)
    (hp : Differentiable ℝ p) (hgrad : ∀ x, A.field x = gradient p x) :
    ContDiff ℝ ∞ p := by
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨hp,?_⟩
  have he : fderiv ℝ p=(toDual ℝ Space) ∘ A.field := by
    funext x
    rw [Function.comp_apply,hgrad,toDual_gradient]
  rw [he]
  exact (toDual ℝ Space).contDiff.comp A.smooth

theorem gradient_pairing_zero_of_differentiable (A U : SmoothL2Field Space) (p : Space → ℝ)
    (hp : Differentiable ℝ p) (hgrad : ∀ x, A.field x = gradient p x)
    (hdiv : ∀ x, divergence U.field x = 0) : ⟪A.toLp,U.toLp⟫_ℝ=0 :=
  gradient_pairing_zero A U p (potential_smooth A p hp hgrad) hgrad hdiv

end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerVolterraConvolution Finset
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instOrdinaryEulerDifference1 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instOrdinaryEulerDifference2 : NormedSpace ℝ Space := inferInstance

/-- Evolution data, collecting `velocity`, `pressureForce`, `velocity_continuous`,
`pressure_continuous`, `solenoidal`, `gradient` and their compatibility conditions. -/
structure Evolution (T : ℝ) (hT : 0 ≤ T) where
  /-- Velocity field of `Evolution`, of type `Icc (0 : ℝ) T → SmoothL2Field Space`. -/
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  /-- Pressure force of `Evolution`, of type `Icc (0 : ℝ) T → SmoothL2Field Space`. -/
  pressureForce : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t => (velocity t).jetLp n)
  pressure_continuous : ∀ n, Continuous (fun t => (pressureForce t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  gradient : ∀ t, (pressureForce t).toLp ∈ gradientSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r => (velocity (projIcc 0 T hT r)).field x)
      (-fderiv ℝ (velocity ⟨t,ht.1.le,ht.2.le⟩).field x
        ((velocity ⟨t,ht.1.le,ht.2.le⟩).field x) -
          (pressureForce ⟨t,ht.1.le,ht.2.le⟩).field x) t

/-- Evolution of classical, bundling `velocity`, `pressureForce`, `velocity_continuous`,
`pressure_continuous` and the required compatibility proofs. -/
def evolutionOfClassical (T : ℝ) (hT : 0 ≤ T)
    (U G : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n))
    (hG : ∀ n, Continuous (fun t => (G t).jetLp n))
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (hu : ∀ (t : Icc (0 : ℝ) T) x, u (t, x) = (U t).field x)
    (hp : ∀ (t : Icc (0 : ℝ) T), Differentiable ℝ (fun x => p (t, x)))
    (hg : ∀ (t : Icc (0 : ℝ) T) x, gradient (fun y => p (t, y)) x = (G t).field x)
    (hdiv : ∀ t x, divergence (U t).field x = 0)
    (hdiff : ∀ t ∈ Ioo 0 T, ∀ x, DifferentiableAt ℝ u (t, x))
    (heuler : ∀ t ∈ Ioo 0 T, ∀ x, EulerLagrangian.momentumResidual u p (t, x) = 0) :
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

/-- Derivative, given by `EulerSmoothEulerEvolution.rhs U.velocity U.velocity_continuous
U.pressureForce`. -/
def derivative (U : Evolution T hT) : Icc (0 : ℝ) T → SmoothL2Field Space :=
  EulerSmoothEulerEvolution.rhs U.velocity U.velocity_continuous U.pressureForce

theorem derivative_field (U : Evolution T hT) (t : Icc (0 : ℝ) T) (x : Space) :
    (U.derivative t).field x = -fderiv ℝ (U.velocity t).field x ((U.velocity t).field x) -
      (U.pressureForce t).field x :=
  EulerSmoothEulerEvolution.rhs_field U.velocity U.velocity_continuous U.pressureForce t x

theorem derivative_continuous (U : Evolution T hT) (n : ℕ) :
    Continuous (fun t => (U.derivative t).jetLp n) :=
  EulerSmoothEulerEvolution.rhs_jet_continuous U.velocity U.velocity_continuous
    U.pressureForce U.pressure_continuous n

/-- Difference, given by `fieldSub (V.velocity t) (U.velocity t)`. -/
def difference (U V : Evolution T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  fieldSub (V.velocity t) (U.velocity t)

/-- Pressure difference, given by `fieldSub (V.pressureForce t) (U.pressureForce t)`. -/
def pressureDifference (U V : Evolution T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  fieldSub (V.pressureForce t) (U.pressureForce t)

/-- Difference derivative, given by `fieldSub (V.derivative t) (U.derivative t)`. -/
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

/-- Energy path, given by `⟨fun t => wordEnergy 3 (U.difference V t),wordEnergy_continuous _
(U.difference_continuous V) 3⟩`. -/
def energyPath (U V : Evolution T hT) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => wordEnergy 3 (U.difference V t),wordEnergy_continuous _ (U.difference_continuous V) 3⟩

/-- Energy derivative, given by `energyProduction (U.difference V t) (U.differenceDerivative V
t)`. -/
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
