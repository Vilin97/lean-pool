/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySobolevTower
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral

@[expose] public section

/-! The genuine Helmholtz projection preserves ordinary smooth L²
fields and continuous paths of all their jets. Euler pressure and time
derivatives are recovered from velocity, not supplied as estimates. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanOrdinaryLift EulerSmoothFieldSobolevTime
  EulerVolterraConvolution EulerLpFiniteTensor
open scoped ContDiff Topology

def solenoidalField (A : SmoothL2Field Space) : SmoothL2Field Space :=
  smoothL2Field (solenoidalProjection A.toLp) (solenoidal_orbit A)

@[simp] theorem solenoidalField_toLp (A : SmoothL2Field Space) :
    (solenoidalField A).toLp=solenoidalProjection A.toLp := smoothL2Field_toLp _ _

theorem solenoidalField_word (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    (wordField (solenoidalField A) w).toLp=solenoidalProjection (wordField A w).toLp := by
  rw [word_toLp_eq_orbit,solenoidalField_toLp]
  exact (projection_word A w).symm

theorem jetLp_eq_word_reassembly (A : SmoothL2Field Space) (n : ℕ) :
    A.jetLp n=tensorLpReassembly (volume : Measure Space) n
      (fun w : Fin n → Fin 3 => (wordField A w).toLp) := by
  rw [← ordinaryTensorOperator_apply A n]
  unfold ordinaryTensorOperator
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  funext w
  exact ordinaryWordOperator_apply A w

theorem solenoidalField_continuous {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (solenoidalField (A t)).jetLp n) := by
  simp_rw [jetLp_eq_word_reassembly,solenoidalField_word]
  apply (tensorLpReassembly (V := Space) (volume : Measure Space) n).continuous.comp
  apply continuous_pi
  intro w
  apply solenoidalProjection.continuous.comp
  have h := (ordinaryWordPath A hA w).continuous
  exact h.congr (ordinaryWordPath_apply A hA w)

theorem advectionField_continuous {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (advectionField (A t) (A t)).jetLp n) := by
  have he (t : K) : advectionField (A t) (A t)=EulerSmoothEulerEvolution.advection A hA t := by
    apply field_ext
    funext x
    rw [advectionField_field,EulerSmoothEulerEvolution.advection_field]
  simp only [he]
  exact EulerSmoothEulerEvolution.advection_jet_continuous A hA n

def pressureField (A : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldSub (solenoidalField (advectionField A A)) (advectionField A A)

def projectedRhs (A : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldNeg (solenoidalField (advectionField A A))

@[simp] theorem projectedRhs_toLp (A : SmoothL2Field Space) :
    (projectedRhs A).toLp = -solenoidalProjection (advectionField A A).toLp := by
  rw [projectedRhs,toLp_fieldNeg,solenoidalField_toLp]

@[simp] theorem pressureField_toLp (A : SmoothL2Field Space) :
    (pressureField A).toLp = solenoidalProjection (advectionField A A).toLp-(advectionField A
      A).toLp := by
  rw [pressureField,toLp_fieldSub,solenoidalField_toLp]

theorem pressureField_mem_gradient (A : SmoothL2Field Space) : (pressureField A).toLp ∈
  gradientSpace := by
  rw [pressureField_toLp,← neg_sub]
  exact gradientSpace.neg_mem (sub_solenoidalProjection_mem_gradient _)

theorem projectedRhs_field (A : SmoothL2Field Space) (x : Space) :
    (projectedRhs A).field x = -fderiv ℝ A.field x (A.field x)-(pressureField A).field x := by
  simp only [projectedRhs,pressureField,fieldNeg_field,fieldSub_field,advectionField_field]
  abel

theorem pressureField_continuous {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (pressureField (A t)).jetLp n) :=
  continuous_jet_fieldSub _ _ (solenoidalField_continuous _ (advectionField_continuous A hA))
    (advectionField_continuous A hA) n

theorem projectedRhs_continuous {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (projectedRhs (A t)).jetLp n) :=
  continuous_jetLp_mapField _ _ (solenoidalField_continuous _ (advectionField_continuous A hA)) n

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

theorem velocityPath_extend (U : Evolution T hT) :
    extendPath T hT U.velocityPath = fun r => (U.velocity (projIcc 0 T hT r)).toLp :=
  funext (fun r => U.velocityPath_apply (projIcc 0 T hT r))

theorem velocityPath_hasDerivWithinAt (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT U.velocityPath) (U.derivative t).toLp (Icc (0 : ℝ) T) t := by
  have h := ordinaryWord_hasDerivWithinAt T hT U.velocity U.derivative U.velocity_continuous
    U.derivative_continuous (fun r hr x => by simpa only [derivative_field] using U.time_law r hr x)
    (Fin.elim0 : Fin 0 → Fin 3) t
  rw [U.velocityPath_extend]
  simpa only [wordField_zero] using h

theorem derivative_mem_solenoidal (U : Evolution T hT) (hpos : 0 < T) (t : Icc (0 : ℝ) T) :
    (U.derivative t).toLp ∈ solenoidalSpace := by
  have hu := U.velocityPath_hasDerivWithinAt t
  have hp := solenoidalProjection.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hu
  have he : (fun r => solenoidalProjection (extendPath T hT U.velocityPath r))=
      extendPath T hT U.velocityPath := by
    funext r
    rw [U.velocityPath_extend]
    exact solenoidalSpace.starProjection_eq_self_iff.mpr (U.solenoidal (projIcc 0 T hT r))
  simp only [Function.comp_def] at hp
  rw [he] at hp
  have hd := (hp.derivWithin (uniqueDiffOn_Icc hpos t t.property)).symm.trans
    (hu.derivWithin (uniqueDiffOn_Icc hpos t t.property))
  exact solenoidalSpace.starProjection_eq_self_iff.mp hd

theorem derivative_toLp_projected (U : Evolution T hT) (hpos : 0 < T) (t : Icc (0 : ℝ) T) :
    (U.derivative t).toLp = (projectedRhs (U.velocity t)).toLp := by
  have hd : solenoidalProjection (U.derivative t).toLp=(U.derivative t).toLp :=
    solenoidalSpace.starProjection_eq_self_iff.mpr (U.derivative_mem_solenoidal hpos t)
  have he : (U.derivative t).toLp = -((advectionField (U.velocity t) (U.velocity t)).toLp+
      (U.pressureForce t).toLp) := by
    rw [U.derivative_eq_eulerRhs,eulerRhs,toLp_fieldNeg,toLp_addField]
  rw [he,map_neg,map_add,(solenoidalProjection_eq_zero_iff _).mpr (U.gradient t),add_zero] at hd
  rw [projectedRhs_toLp]
  exact he.trans hd.symm

def projectedPath (U : Evolution T hT) : C(Icc (0 : ℝ) T,L2) :=
  fieldPath (fun t => projectedRhs (U.velocity t)) (projectedRhs_continuous U.velocity
    U.velocity_continuous)

theorem velocity_integral_equation (U : Evolution T hT) (hpos : 0 < T) :
    U.velocityPath = ContinuousMap.const (Icc (0 : ℝ) T) (U.velocityPath ⟨0,le_rfl,hT⟩)+
      EulerContinuousTimeIntegral.integral T hT U.projectedPath := by
  apply ContinuousMap.ext
  intro t
  have hd (s : Icc (0 : ℝ) T) : HasDerivWithinAt (extendPath T hT U.velocityPath)
      (U.projectedPath s) (Icc (0 : ℝ) T) s := by
    rw [show U.projectedPath s=(projectedRhs (U.velocity s)).toLp from rfl,
      ← U.derivative_toLp_projected hpos s]
    exact U.velocityPath_hasDerivWithinAt s
  have h := EulerContinuousTimeIntegral.eq_initial_add_integral T hT U.projectedPath
    (extendPath T hT U.velocityPath) hd t
  simpa only [extendPath,projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    ContinuousMap.add_apply,ContinuousMap.const_apply] using h

end Evolution
end EulerOrdinarySobolev
