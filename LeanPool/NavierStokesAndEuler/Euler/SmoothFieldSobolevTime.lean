/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2CoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.SeparatingTimeDerivative
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction

@[expose] public section

/-! Pointwise evolution of smooth L² fields upgrades to genuine strong
Sobolev evolution when all spatial L² jets of the field and its prescribed
time derivative are continuous. The ordinary field is represented by its
isometric, angle-independent lift to the unit cylinder. -/

noncomputable section

namespace EulerSmoothFieldSobolevTime

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerLiftedGradientSpace
  EulerVolterraConvolution
open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {K : Type*} [TopologicalSpace K]

theorem continuous_sobolev (A : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (q : ℕ) :
    Continuous (fun t => ordinarySobolev q (A t).toLp (A t).translation_contDiff) := by
  apply ordinarySobolev_continuous q (fun t => (A t).toLp) (fun t => (A t).translation_contDiff)
  intro n _
  have he : (fun t => iteratedFDeriv ℝ n
      (fun a : Space => EulerMeanSolenoidal.translation a (A t).toLp) 0) =
      fun t => EulerLpDerivative.multilinearBundling (P := Space) (V := Space) volume n
        ((A t).jetLp n) := by
    funext t
    have h := (A t).iteratedFDeriv_translation_eq n 0
    rw [EulerLpTranslation.translation_zero] at h
    simpa only [EulerLpTranslation.translation,EulerMeanSolenoidal.translation] using h
  rw [he]
  exact (EulerLpDerivative.multilinearBundling (P := Space) (V := Space) volume n).continuous.comp
    (hA n)

def sobolevPath (A : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (q : ℕ) : C(K,SobolevSpace 1 q) :=
  ⟨fun t => ordinarySobolev q (A t).toLp (A t).translation_contDiff,continuous_sobolev A hA q⟩

theorem restrict_sobolev {p q : ℕ} (h : q ≤ p) (A : SmoothL2Field Space) :
    restrictOperator 1 h (ordinarySobolev p A.toLp A.translation_contDiff) =
      ordinarySobolev q A.toLp A.translation_contDiff := by
  apply value_injective 1
  exact (value_restrictOperator 1 h _).trans
    ((ordinarySobolev_value p A.toLp A.translation_contDiff).trans
      (ordinarySobolev_value q A.toLp A.translation_contDiff).symm)

def observation (q : ℕ) (hq : 3 ≤ q) (x : LiftDomain 1) : SobolevSpace 1 q →L[ℝ] Space :=
  (pointEvaluation 1 x).comp (restrictOperator 1 hq)

theorem observation_apply (q : ℕ) (hq : 3 ≤ q) (x : LiftDomain 1) (A : SmoothL2Field Space) :
    observation q hq x (ordinarySobolev q A.toLp A.translation_contDiff) = A.field x.1 := by
  change pointEvaluation 1 x
    (restrictOperator 1 hq (ordinarySobolev q A.toLp A.translation_contDiff)) = _
  rw [restrict_sobolev]
  apply pointEvaluation_eq 1 x _ (fun z : LiftDomain 1 => A.field z.1)
    (A.smooth.continuous.comp continuous_fst)
  exact Filter.EventuallyEq.trans
    (Filter.Eventually.of_forall (fun z =>
      congrArg (fun u : LiftL2 1 => u z) (ordinarySobolev_value 3 A.toLp A.translation_contDiff)))
    ((ordinaryLift_ae A.toLp).trans
      (ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae A.toLp_ae))

theorem observation_injective (q : ℕ) (hq : 3 ≤ q) :
    Function.Injective (fun u : SobolevSpace 1 q => fun x : LiftDomain 1 => observation q hq x u)
      := by
  intro u v h
  apply value_injective 1
  apply Lp.ext
  filter_upwards [EulerSobolevPointEvaluation.representative_ae 1 (restrictOperator 1 hq u),
    EulerSobolevPointEvaluation.representative_ae 1 (restrictOperator 1 hq v)] with x hu hv
  exact hu.trans ((congrFun h x).trans hv.symm)

variable (T : ℝ) (hT : 0 ≤ T)
  (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (hB : ∀ n, Continuous (fun t => (B t).jetLp n))
  (hd : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).field x)
      ((B ⟨t,ht.1.le,ht.2.le⟩).field x) t)

include hd in
theorem sobolevPath_hasDerivWithinAt_of_three_le (q : ℕ) (hq : 3 ≤ q)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath A hA q))
      (sobolevPath B hB q t) (Icc (0 : ℝ) T) t := by
  apply EulerSeparatingTimeDerivative.hasDerivWithinAt T hT (sobolevPath A hA q)
    (sobolevPath B hB q) (observation q hq) (observation_injective q hq)
  intro x r hr
  simpa only [extendPath,sobolevPath,ContinuousMap.coe_mk,observation_apply] using hd r hr x.1

include hd in
theorem sobolevPath_hasDerivWithinAt (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath A hA q))
      (sobolevPath B hB q t) (Icc (0 : ℝ) T) t := by
  have hb := sobolevPath_hasDerivWithinAt_of_three_le T hT A B hA hB hd (q+3) (by omega) t
  have hs := (restrictOperator 1 (by omega : q ≤ q+3)).hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) hb
  convert! hs using 1 <;>
    simp only [extendPath,sobolevPath,ContinuousMap.coe_mk,Function.comp_def,restrict_sobolev]
  rfl

include hd in
theorem sobolevPath_hasDerivAt (q : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT (sobolevPath A hA q))
      (sobolevPath B hB q ⟨t,ht.1.le,ht.2.le⟩) t :=
  (sobolevPath_hasDerivWithinAt T hT A B hA hB hd q ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end EulerSmoothFieldSobolevTime
