/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLimit
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryStrongTime
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerConcatenation

/-! The reverse bridge from ordinary scalar-pressure Euler to the
projected equation. The only regularity inputs are the velocity and its
actual strong time derivative in all spatial Sobolev orders. Neither a
pressure-force regularity hypothesis nor a projected equation is assumed.
The scalar pressure may be changed by an arbitrary function of time. -/

section

/-! Characterization of the ordinary smooth Euler class by its actual
velocity alone. Pressure regularity follows from the projected equation.
Every solution has one continuous strong time derivative in every
spatial Sobolev order. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal EulerVolterraConvolution EulerSmoothFieldSobolevTime

variable {T : ℝ} {hT : 0 ≤ T}

/-- Is smooth projected euler as an element of `Prop`. -/
def IsSmoothProjectedEuler (A : Icc (0 : ℝ) T → SmoothL2Field Space) : Prop :=
  (∀ n, Continuous (fun t => (A t).jetLp n)) ∧
  (∀ t, (A t).toLp ∈ solenoidalSpace) ∧
  (∀ t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
      (projectedRhs (A ⟨t,ht.1.le,ht.2.le⟩)).toLp t)

/-- Evolution of projected equation, bundling `velocity`, `pressureForce`,
`velocity_continuous`, `pressure_continuous` and the required compatibility proofs. -/
def evolutionOfProjectedEquation (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : IsSmoothProjectedEuler (hT := hT) A) : Evolution T hT where
  velocity := A
  pressureForce t := pressureField (A t)
  velocity_continuous := hA.1
  pressure_continuous := pressureField_continuous A hA.1
  solenoidal := hA.2.1
  gradient t := pressureField_mem_gradient (A t)
  time_law t ht x := by
    have h := pointwise_derivative_of_l2 T hT A (fun s => projectedRhs (A s)) hA.1
      (projectedRhs_continuous A hA.1) hA.2.2 ⟨t,ht.1.le,ht.2.le⟩ x
    simpa only [projectedRhs_field] using h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem Evolution.isSmoothProjectedEuler (U : Evolution T hT) (hpos : 0 < T) :
    IsSmoothProjectedEuler (hT := hT) U.velocity := by
  refine ⟨U.velocity_continuous,U.solenoidal,?_⟩
  intro t ht
  exact (U.velocity_toLp_hasDerivWithinAt_projected hpos ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

theorem exists_evolution_iff_projected (hpos : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space) :
    (∃ U : Evolution T hT, U.velocity=A) ↔ IsSmoothProjectedEuler (hT := hT) A := by
  constructor
  · rintro ⟨U,rfl⟩
    exact U.isSmoothProjectedEuler hpos
  · intro hA
    exact ⟨evolutionOfProjectedEquation A hA,rfl⟩

theorem Evolution.sobolevTimeDerivative (U : Evolution T hT) (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath U.velocity U.velocity_continuous q))
      (sobolevPath U.derivative U.derivative_continuous q t) (Icc (0 : ℝ) T) t := by
  apply sobolev_derivative_of_l2 T hT U.velocity U.derivative U.velocity_continuous
    U.derivative_continuous _ q t
  intro r hr
  have h := U.velocityPath_hasDerivWithinAt ⟨r,hr.1.le,hr.2.le⟩
  rw [U.velocityPath_extend] at h
  exact h.hasDerivAt (Icc_mem_nhds hr.1 hr.2)

theorem Evolution.sobolevSolutionClass (U : Evolution T hT) (q : ℕ) :
    Continuous (sobolevPath U.velocity U.velocity_continuous q) ∧
      Continuous (sobolevPath U.derivative U.derivative_continuous q) ∧
      ∀ t : Icc (0 : ℝ) T,
        HasDerivWithinAt (extendPath T hT (sobolevPath U.velocity U.velocity_continuous q))
          (sobolevPath U.derivative U.derivative_continuous q t) (Icc (0 : ℝ) T) t :=
  ⟨(sobolevPath U.velocity U.velocity_continuous q).continuous,
    (sobolevPath U.derivative U.derivative_continuous q).continuous,
    U.sobolevTimeDerivative q⟩

end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerMeanOrdinaryLift EulerMeanSmoothRepresentative EulerSmoothFieldSobolevTime
  EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerVolterraConvolution
open scoped ContDiff

local instance instOrdinaryEulerClassicalClass1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {T : ℝ} {hT : 0 ≤ T}

/-- The force obtained from the actual velocity and its actual time derivative. -/
def scalarEulerForce (A B : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldNeg (addField B (advectionField A A))

theorem scalarEulerForce_field (A B : SmoothL2Field Space) (x : Space) :
    (scalarEulerForce A B).field x = -((B.field x)+fderiv ℝ A.field x (A.field x)) := by
  simp only [scalarEulerForce,fieldNeg_field,addField_field,advectionField_field]

theorem scalarEulerForce_continuous
    (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (scalarEulerForce (A t) (B t)).jetLp n) :=
  continuous_jetLp_mapField _ _
    (continuous_jetLp_addField B _ hB (advectionField_continuous A hA)) n

/-- An ordinary scalar Euler equation implies the actual projected L² equation.
Spatial differentiability of pressure is used only at interior times. -/
theorem isSmoothProjectedEuler_of_scalarEuler
    (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hd : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
        (B ⟨t, ht.1.le, ht.2.le⟩).toLp t)
    (p : ℝ → Space → ℝ)
    (hdiv : ∀ t x, divergence (A t).field x = 0)
    (hp : ∀ t ∈ Ioo 0 T, Differentiable ℝ (p t))
    (he : ∀ t (ht : t ∈ Ioo 0 T) x,
      (B ⟨t, ht.1.le, ht.2.le⟩).field x +
        fderiv ℝ (A ⟨t, ht.1.le, ht.2.le⟩).field x
          ((A ⟨t, ht.1.le, ht.2.le⟩).field x) +
 gradient (p t) x =
 0) :
    IsSmoothProjectedEuler (hT := hT) A := by
  have hs (t : Icc (0 : ℝ) T) : (A t).toLp ∈ solenoidalSpace :=
    smooth_mem_solenoidal (A t).field (A t).smooth (A t).memLp (hdiv t)
  refine ⟨hA,hs,?_⟩
  intro t ht
  let s : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
  let G := scalarEulerForce (A s) (B s)
  have hg (x : Space) : G.field x=gradient (p t) x := by
    rw [scalarEulerForce_field]
    exact (eq_neg_of_add_eq_zero_right (he t ht x)).symm
  have hG : G.toLp ∈ EulerMeanSolenoidal.gradientSpace :=
    gradient_mem G (p t) (potential_smooth G (p t) (hp t ht) hg) hg
  have hproj := solenoidalProjection.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hfix : (fun r => solenoidalProjection (A (projIcc 0 T hT r)).toLp) =
      (fun r => (A (projIcc 0 T hT r)).toLp) := by
    funext r
    exact solenoidalSpace.starProjection_eq_self_iff.mpr (hs _)
  simp only [Function.comp_def] at hproj
  rw [hfix] at hproj
  have hB : solenoidalProjection (B s).toLp=(B s).toLp := hproj.unique (hd t ht)
  have hzero := (solenoidalProjection_eq_zero_iff G.toLp).mpr hG
  change solenoidalProjection (fieldNeg (addField (B s) (advectionField (A s) (A s)))).toLp=0
      at hzero
  rw [toLp_fieldNeg,toLp_addField,map_neg,map_add,hB] at hzero
  have hR : (B s).toLp=(projectedRhs (A s)).toLp := by
    rw [projectedRhs_toLp]
    exact eq_neg_of_add_eq_zero_left (neg_eq_zero.mp hzero)
  exact hR ▸ hd t ht

/-- Evolution of scalar euler, given by `evolutionOfProjectedEquation A
(isSmoothProjectedEuler_of_scalarEuler A B hA hd p hdiv hp he)`. -/
def evolutionOfScalarEuler
    (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hd : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
        (B ⟨t, ht.1.le, ht.2.le⟩).toLp t)
    (p : ℝ → Space → ℝ)
    (hdiv : ∀ t x, divergence (A t).field x = 0)
    (hp : ∀ t ∈ Ioo 0 T, Differentiable ℝ (p t))
    (he : ∀ t (ht : t ∈ Ioo 0 T) x,
      (B ⟨t, ht.1.le, ht.2.le⟩).field x +
        fderiv ℝ (A ⟨t, ht.1.le, ht.2.le⟩).field x
          ((A ⟨t, ht.1.le, ht.2.le⟩).field x) +
 gradient (p t) x =
 0) : Evolution T hT :=
  evolutionOfProjectedEquation A (isSmoothProjectedEuler_of_scalarEuler A B hA hd p hdiv hp he)

section Identification

variable (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (hB : ∀ n, Continuous (fun t => (B t).jetLp n))
  (hd : ∀ t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
      (B ⟨t, ht.1.le, ht.2.le⟩).toLp t)
  (p : ℝ → Space → ℝ)
  (hdiv : ∀ t x, divergence (A t).field x = 0)
  (hp : ∀ t ∈ Ioo 0 T, Differentiable ℝ (p t))
  (he : ∀ t (ht : t ∈ Ioo 0 T) x,
    (B ⟨t, ht.1.le, ht.2.le⟩).field x +
      fderiv ℝ (A ⟨t, ht.1.le, ht.2.le⟩).field x
        ((A ⟨t, ht.1.le, ht.2.le⟩).field x) +
 gradient (p t) x =
 0)

theorem evolutionOfScalarEuler_velocity :
    (evolutionOfScalarEuler A B hA hd p hdiv hp he).velocity=A := rfl

include hB in
theorem evolutionOfScalarEuler_derivative (hpos : 0 < T) (t : Icc (0 : ℝ) T) :
    (evolutionOfScalarEuler A B hA hd p hdiv hp he).derivative t=B t := by
  let U := evolutionOfScalarEuler A B hA hd p hdiv hp he
  have h₁ := U.sobolevTimeDerivative 3 t
  have h₂ := sobolev_derivative_of_l2 T hT A B hA hB hd 3 t
  change HasDerivWithinAt (extendPath T hT (sobolevPath A hA 3))
    (sobolevPath U.derivative U.derivative_continuous 3 t) (Icc (0 : ℝ) T) t at h₁
  have hh := (h₁.derivWithin (uniqueDiffOn_Icc hpos t t.property)).symm.trans
    (h₂.derivWithin (uniqueDiffOn_Icc hpos t t.property))
  apply field_ext
  funext x
  have h := congrArg (observation 3 (le_refl 3) (x,(0 : AddCircle (1 : ℝ)))) hh
  simpa only [sobolevPath,ContinuousMap.coe_mk,observation_apply] using h

include hB in
theorem evolutionOfScalarEuler_pressureForce (hpos : 0 < T) (t : Icc (0 : ℝ) T) :
    (evolutionOfScalarEuler A B hA hd p hdiv hp he).pressureForce t =
      scalarEulerForce (A t) (B t) := by
  let U := evolutionOfScalarEuler A B hA hd p hdiv hp he
  have hd' := evolutionOfScalarEuler_derivative A B hA hB hd p hdiv hp he hpos t
  apply field_ext
  funext x
  have hv := congrArg (fun C : SmoothL2Field Space => C.field x) hd'
  rw [Evolution.derivative_field] at hv
  change -fderiv ℝ (A t).field x ((A t).field x)-(U.pressureForce t).field x=(B t).field x at hv
  rw [scalarEulerForce_field]
  apply add_left_cancel (a := (B t).field x)
  calc
    (B t).field x+(U.pressureForce t).field x = -fderiv ℝ (A t).field x ((A t).field x) :=
      ((sub_eq_iff_eq_add).mp hv).symm
    _ = (B t).field x+-((B t).field x+fderiv ℝ (A t).field x ((A t).field x)) := by abel

include hB in
theorem evolutionOfScalarEuler_scalarPressure (hpos : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    (evolutionOfScalarEuler A B hA hd p hdiv hp he).scalarPressure ⟨t,ht.1.le,ht.2.le⟩ x =
      p t x-p t 0 := by
  let U := evolutionOfScalarEuler A B hA hd p hdiv hp he
  let s : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
  have hg (y : Space) : (U.pressureForce s).field y=gradient (p t) y := by
    rw [evolutionOfScalarEuler_pressureForce A B hA hB hd p hdiv hp he hpos s,
      scalarEulerForce_field]
    exact (eq_neg_of_add_eq_zero_right (he t ht y)).symm
  exact EulerCanonicalGraphPotential.radialPotential_eq_sub (U.pressureForce s).field
    (U.pressureForce s).smooth.continuous (p t)
    (potential_smooth (U.pressureForce s) (p t) (hp t ht) hg) (fun y => (hg y).symm) x

end Identification

/-- A strong time derivative in any genuine spatial Sobolev order gives
the L² derivative used above. In the source class one can take order two. -/
theorem l2_timeDerivative_of_sobolev
    (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (q : ℕ)
    (hd : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (extendPath T hT (sobolevPath A hA q))
        (sobolevPath B hB q ⟨t, ht.1.le, ht.2.le⟩) t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
      (B ⟨t,ht.1.le,ht.2.le⟩).toLp t := by
  let L : SobolevSpace 1 q →L[ℝ] L2 :=
    ordinaryLift.toContinuousLinearMap.adjoint.comp (valueOperator 1 q)
  have hL (C : SmoothL2Field Space) :
      L (ordinarySobolev q C.toLp C.translation_contDiff)=C.toLp := by
    change ordinaryLift.toContinuousLinearMap.adjoint
      (value 1 (ordinarySobolev q C.toLp C.translation_contDiff))=C.toLp
    erw [ordinarySobolev_value]
    exact congrArg (fun M : L2 →L[ℝ] L2 => M C.toLp) ordinaryLift.adjoint_comp_self
  have h := L.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  simpa only [Function.comp_def,extendPath,sobolevPath,ContinuousMap.coe_mk,hL] using h

/-- The scalar-pressure form of the smooth ordinary Euler class. The
all-order spatial paths represent `C H^m` for every finite `m`. A single
strong L² time law and the continuous all-order derivative paths imply
the strong time law in every Sobolev order by `sobolev_derivative_of_l2`.
No norm, time regularity, or normalization is imposed on the scalar pressure. -/
def IsSmoothScalarEuler (A : Icc (0 : ℝ) T → SmoothL2Field Space) : Prop :=
  (∀ n, Continuous (fun t => (A t).jetLp n)) ∧
    ∃ (B : Icc (0 : ℝ) T → SmoothL2Field Space) (p : ℝ → Space → ℝ),
      (∀ n, Continuous (fun t => (B t).jetLp n)) ∧
      (∀ t (ht : t ∈ Ioo 0 T),
        HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
          (B ⟨t,ht.1.le,ht.2.le⟩).toLp t) ∧
      (∀ t x, divergence (A t).field x=0) ∧
      (∀ t ∈ Ioo 0 T, Differentiable ℝ (p t)) ∧
      (∀ t (ht : t ∈ Ioo 0 T) x,
        (B ⟨t,ht.1.le,ht.2.le⟩).field x +
          fderiv ℝ (A ⟨t,ht.1.le,ht.2.le⟩).field x
            ((A ⟨t,ht.1.le,ht.2.le⟩).field x)+gradient (p t) x=0)

theorem isSmoothScalarEuler_of_sobolev
    (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (q : ℕ)
    (hd : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (extendPath T hT (sobolevPath A hA q))
        (sobolevPath B hB q ⟨t, ht.1.le, ht.2.le⟩) t)
    (p : ℝ → Space → ℝ)
    (hdiv : ∀ t x, divergence (A t).field x = 0)
    (hp : ∀ t ∈ Ioo 0 T, Differentiable ℝ (p t))
    (he : ∀ t (ht : t ∈ Ioo 0 T) x,
      (B ⟨t, ht.1.le, ht.2.le⟩).field x +
        fderiv ℝ (A ⟨t, ht.1.le, ht.2.le⟩).field x
          ((A ⟨t, ht.1.le, ht.2.le⟩).field x) +
 gradient (p t) x =
 0) :
    IsSmoothScalarEuler (hT := hT) A :=
  ⟨hA,B,p,hB,l2_timeDerivative_of_sobolev A B hA hB q hd,hdiv,hp,he⟩

/-- Starting from genuine continuous Sobolev realizations requires no
preselected smooth representative or pressure-force path. The order-two
time law is part of the source's `C¹ H^(m-1)` condition at `m=3`;
the continuous realizations of the derivative come from its higher orders. -/
theorem SobolevTower.isSmoothScalarEuler (A B : SobolevTower T)
    (hd : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (extendPath T hT (A.realization 2))
        (B.realization 2 ⟨t, ht.1.le, ht.2.le⟩) t)
    (p : ℝ → Space → ℝ)
    (hdiv : ∀ t x, divergence (A.smoothField t).field x = 0)
    (hp : ∀ t ∈ Ioo 0 T, Differentiable ℝ (p t))
    (he : ∀ t (ht : t ∈ Ioo 0 T) x,
      (B.smoothField ⟨t, ht.1.le, ht.2.le⟩).field x +
        fderiv ℝ (A.smoothField ⟨t, ht.1.le, ht.2.le⟩).field x
          ((A.smoothField ⟨t, ht.1.le, ht.2.le⟩).field x) +
 gradient (p t) x =
 0) :
    IsSmoothScalarEuler (hT := hT) A.smoothField := by
  apply isSmoothScalarEuler_of_sobolev A.smoothField B.smoothField
    A.smoothField_jet_continuous B.smoothField_jet_continuous 2 _ p hdiv hp he
  simpa only [A.smoothField_path 2,B.smoothField_path 2] using hd

theorem scalarEuler_iff_projected (A : Icc (0 : ℝ) T → SmoothL2Field Space) :
    IsSmoothScalarEuler (hT := hT) A ↔ IsSmoothProjectedEuler (hT := hT) A := by
  constructor
  · rintro ⟨hA,B,p,_hB,hd,hdiv,hp,he⟩
    exact isSmoothProjectedEuler_of_scalarEuler A B hA hd p hdiv hp he
  · intro hA
    let U := evolutionOfProjectedEquation A hA
    refine ⟨hA.1,U.derivative,(fun r => U.scalarPressure (projIcc 0 T hT r)),
      U.derivative_continuous,?_,?_,?_,?_⟩
    · intro t ht
      have h := U.velocityPath_hasDerivWithinAt ⟨t,ht.1.le,ht.2.le⟩
      rw [U.velocityPath_extend] at h
      exact h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · intro t x
      exact solenoidal_representative_divergence _ (hA.2.1 t) _ (A t).smooth (A t).toLp_ae x
    · intro t ht
      exact (U.scalarPressure_spec (projIcc 0 T hT t)).1.differentiable (by simp)
    · intro t ht x
      dsimp only
      rw [projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩,
        (U.scalarPressure_spec ⟨t,ht.1.le,ht.2.le⟩).2.2 x,U.derivative_field]
      change (-fderiv ℝ (A ⟨t,ht.1.le,ht.2.le⟩).field x
        ((A ⟨t,ht.1.le,ht.2.le⟩).field x) -
        (U.pressureForce ⟨t,ht.1.le,ht.2.le⟩).field x)+_+_=0
      abel

theorem exists_evolution_iff_scalar (hpos : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space) :
    (∃ U : Evolution T hT, U.velocity=A) ↔ IsSmoothScalarEuler (hT := hT) A :=
  (exists_evolution_iff_projected hpos A).trans (scalarEuler_iff_projected A).symm

end EulerOrdinarySobolev
