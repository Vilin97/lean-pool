/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordConstraints
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFieldSobolevTime
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Strong time differentiation of every actual ordinary L² word,
derived from the pointwise evolution and continuous L² spatial jets. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerVolterraConvolution Finset
open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def ordinaryWordOperator {n : ℕ} (w : Fin n → Fin 3) :
    SobolevSpace 1 n →L[ℝ] EulerMeanSolenoidal.L2 :=
  ordinaryLift.toContinuousLinearMap.adjoint.comp
    (wordOperator 1 ⟨⟨n, Nat.lt_succ_self n⟩,fun i => (w i).succ⟩)

theorem ordinaryWordOperator_apply (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    ordinaryWordOperator w (ordinarySobolev n A.toLp A.translation_contDiff)=
      (wordField A w).toLp := by
  change ordinaryLift.toContinuousLinearMap.adjoint
    ((ordinarySobolev n A.toLp A.translation_contDiff).val
      ⟨⟨n,Nat.lt_succ_self n⟩,fun i => (w i).succ⟩)=_
  erw [ordinarySobolev_coordinate]
  have he (u : EulerMeanSolenoidal.L2) : ordinaryLift.toContinuousLinearMap.adjoint (ordinaryLift
    u)=u :=
    congrArg (fun L : EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2 => L u)
      ordinaryLift.adjoint_comp_self
  rw [he,word_toLp_eq_orbit]
  have hc : coordinateTuple (fun i => (w i).succ)=(fun i => axis (w i)) := by
    funext i
    simp only [coordinateTuple,EulerCylinderSobolev.standardDirection_succ,axis]
  change iteratedFDeriv ℝ n (fun a => EulerMeanSolenoidal.translation a A.toLp) 0
    (coordinateTuple (fun i => (w i).succ)) = _
  rw [hc]
  rfl

variable {K : Type*} [TopologicalSpace K]

def ordinaryWordPath (A : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) {n : ℕ} (w : Fin n → Fin 3) :
    C(K,EulerMeanSolenoidal.L2) :=
  ⟨fun t => ordinaryWordOperator w (sobolevPath A hA n t),
    (ordinaryWordOperator w).continuous.comp (sobolevPath A hA n).continuous⟩

@[simp] theorem ordinaryWordPath_apply (A : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) {n : ℕ} (w : Fin n → Fin 3) (t : K) :
    ordinaryWordPath A hA w t=(wordField (A t) w).toLp :=
  ordinaryWordOperator_apply (A t) w

theorem wordEnergy_continuous (A : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (s : ℕ) :
    Continuous (fun t => wordEnergy s (A t)) := by
  apply continuous_finsetSum
  intro n _
  apply continuous_finsetSum
  intro w _
  have hc : Continuous (fun t => (wordField (A t) w).toLp) := by
    exact (ordinaryWordPath A hA w).continuous.congr (ordinaryWordPath_apply A hA w)
  exact hc.norm.pow 2

variable (T : ℝ) (hT : 0 ≤ T)
  (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (hB : ∀ n, Continuous (fun t => (B t).jetLp n))
  (hd : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).field x)
      ((B ⟨t,ht.1.le,ht.2.le⟩).field x) t)

include hA hB hd in
theorem ordinaryWord_hasDerivWithinAt {n : ℕ} (w : Fin n → Fin 3) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => (wordField (A (projIcc 0 T hT r)) w).toLp)
      (wordField (B t) w).toLp (Icc (0 : ℝ) T) t := by
  have h := (ordinaryWordOperator w).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (sobolevPath_hasDerivWithinAt T hT A B hA hB hd n t)
  simpa only [Function.comp_def,extendPath,sobolevPath,ContinuousMap.coe_mk,
    ordinaryWordOperator_apply] using h

include hA hB hd in
theorem wordEnergy_hasDerivWithinAt (s : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => wordEnergy s (A (projIcc 0 T hT r)))
      (2*(∑ n ∈ range (s+1), ∑ w : Fin n → Fin 3,
        ⟪(wordField (A t) w).toLp,(wordField (B t) w).toLp⟫_ℝ)) (Icc (0 : ℝ) T) t := by
  have hw (n : ℕ) (w : Fin n → Fin 3) :=
    (ordinaryWord_hasDerivWithinAt T hT A B hA hB hd w t).norm_sq
  have hp : projIcc 0 T hT (t : ℝ)=t := projIcc_of_mem hT t.property
  simp only [hp] at hw
  have hs := HasDerivWithinAt.fun_sum (u := range (s+1))
    (fun n _ => HasDerivWithinAt.fun_sum (u := univ) (fun w _ => hw n w))
  simpa only [wordEnergy,← Finset.mul_sum] using hs

end EulerOrdinarySobolev
