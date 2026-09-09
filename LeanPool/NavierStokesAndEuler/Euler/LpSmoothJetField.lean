/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra

@[expose] public section

/-! Every actual spatial derivative tensor remains a smooth L² field. -/

noncomputable section

namespace EulerLpTranslation.SmoothL2Field

open MeasureTheory ContinuousLinearMap EulerSmoothLimit
open scoped ContDiff

universe u v

private def jetFieldAux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V],
      SmoothL2Field V → SmoothL2Field (Space [×n]→L[ℝ] V) :=
  Nat.rec (motive := fun n => ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V],
      SmoothL2Field V → SmoothL2Field (Space [×n]→L[ℝ] V))
    (fun V _ _ A => mapField (V := V) (W := Space [×0]→L[ℝ] V)
      (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
        A)
    (fun n ih V _ _ A => mapField
      (V := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (W := Space [×(n+1)]→L[ℝ] V)
      (continuousMultilinearCurryRightEquiv' ℝ n Space
        V).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (ih (Space →L[ℝ] V) A.derivative)) n

def jetField (n : ℕ) {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) : SmoothL2Field (Space [×n]→L[ℝ] V) := jetFieldAux n V A

@[simp] theorem jetField_zero {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) :
    jetField 0 A = mapField (V := V) (W := Space [×0]→L[ℝ] V)
      (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
        A := rfl

@[simp] theorem jetField_succ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) (n : ℕ) :
    jetField (n+1) A = mapField
      (V := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (W := Space [×(n+1)]→L[ℝ] V)
      (continuousMultilinearCurryRightEquiv' ℝ n Space
        V).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (jetField n A.derivative) := rfl

private theorem jetField_field_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V) (x : Space),
      (jetField n A).field x = iteratedFDeriv ℝ n A.field x := by
  induction n with
  | zero =>
    intro V _ _ A x
    change (continuousMultilinearCurryFin0 ℝ Space V).symm (A.field x) = _
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  | succ n ih =>
    intro V _ _ A x
    change (continuousMultilinearCurryRightEquiv' ℝ n Space V).symm
      ((jetField n A.derivative).field x) = _
    rw [ih (Space →L[ℝ] V) A.derivative x, iteratedFDeriv_succ_eq_comp_right]
    rfl

@[simp] theorem jetField_field {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) (n : ℕ) (x : Space) :
    (jetField n A).field x = iteratedFDeriv ℝ n A.field x :=
  jetField_field_aux n V A x

theorem jetField_toLp {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) (n : ℕ) : (jetField n A).toLp = A.jetLp n := by
  apply Lp.ext
  filter_upwards [(jetField n A).toLp_ae, A.jetLp_ae n] with x h₁ h₂
  exact h₁.trans ((jetField_field A n x).trans h₂.symm)

variable {K : Type v} [TopologicalSpace K]

private theorem continuous_jetField_jet_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : K → SmoothL2Field V),
      (∀ k, Continuous (fun t => (A t).jetLp k)) →
      ∀ k, Continuous (fun t => (jetField n (A t)).jetLp k) := by
  induction n with
  | zero =>
    intro V _ _ A hA k
    have he : (fun t => (jetField 0 (A t)).jetLp k) =
        (fun t => (mapField (V := V) (W := Space [×0]→L[ℝ] V)
          (continuousMultilinearCurryFin0 ℝ Space
            V).symm.toContinuousLinearEquiv.toContinuousLinearMap
          (A t)).jetLp k) :=
      funext fun t => congrArg (fun F => F.jetLp k) (jetField_zero (A t))
    rw [he]
    exact continuous_jetLp_mapField (V := V) (W := Space [×0]→L[ℝ] V)
      (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
        A hA k
  | succ n ih =>
    intro V _ _ A hA k
    have hd : ∀ j, Continuous (fun t => (A t).derivative.jetLp j) :=
      continuous_jetLp_derivative A hA
    have hr : ∀ j, Continuous (fun t => (jetField n (A t).derivative).jetLp j) :=
      ih (Space →L[ℝ] V) (fun t => (A t).derivative) hd
    have he : (fun t => (jetField (n+1) (A t)).jetLp k) =
        (fun t => (mapField
          (V := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (W := Space [×(n+1)]→L[ℝ] V)
          (continuousMultilinearCurryRightEquiv' ℝ n Space
            V).symm.toContinuousLinearEquiv.toContinuousLinearMap
          (jetField n (A t).derivative)).jetLp k) :=
      funext fun t => congrArg (fun F => F.jetLp k) (jetField_succ (A t) n)
    rw [he]
    apply continuous_jetLp_mapField
      (V := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (W := Space [×(n+1)]→L[ℝ] V)
      (continuousMultilinearCurryRightEquiv' ℝ n Space
        V).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (fun t => jetField n (A t).derivative) hr

theorem continuous_jetField_jet {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : K → SmoothL2Field V) (hA : ∀ k, Continuous (fun t => (A t).jetLp k)) (n k : ℕ) :
    Continuous (fun t => (jetField n (A t)).jetLp k) :=
  continuous_jetField_jet_aux n V A hA k

end EulerLpTranslation.SmoothL2Field
