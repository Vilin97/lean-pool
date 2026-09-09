/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelOperator
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Genuine parameter regularity of the forced initial value problem

The homogeneous evolutions need not have assumed parameter derivatives. The
constructed solution is the actual inverse of a smooth Volterra operator on a
fixed continuous-path Banach space. Operator inversion therefore proves its
parameter smoothness from coefficient and data smoothness alone.
-/

noncomputable section


namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T,E →L[ℝ] E)}

namespace Evolution

variable (U : Evolution T hT B)

/-- The constructed Volterra inverse is the canonical continuous-linear-map inverse. -/
theorem volterraInverse_eq_mapInverse : U.volterraInverse = (volterraOperator T hT B).inverse := by
  calc
    U.volterraInverse = (U.volterraEquiv.symm :
      C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E)) := rfl
    _ = (U.volterraEquiv : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E)).inverse :=
      (ContinuousLinearMap.inverse_equiv U.volterraEquiv).symm
    _ = _ := rfl

/-- The actual forced solution is obtained by this genuine Volterra inverse. -/
theorem solution_eq_volterraInverse (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) :
    U.solution f a₀ = U.volterraInverse
      ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) a₀ + integral T hT f) := by
  have he : volterraOperator T hT B (U.solution f a₀) =
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) a₀ + integral T hT f := by
    change U.solution f a₀ - integral T hT (multiplier B (U.solution f a₀)) = _
    calc
      _ = ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) a₀ +
          integral T hT (multiplier B (U.solution f a₀) + f)) -
          integral T hT (multiplier B (U.solution f a₀)) :=
        congrArg (fun v => v - integral T hT (multiplier B (U.solution f a₀)))
          (U.solution_integral f a₀)
      _ = _ := by rw [map_add]; abel
  calc
    U.solution f a₀ = U.volterraInverse (volterraOperator T hT B (U.solution f a₀)) :=
      (U.volterra_inverse_operator _).symm
    _ = _ := congrArg U.volterraInverse he

end Evolution

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable (T : ℝ) (hT : 0 ≤ T) (B : P → C(Icc (0 : ℝ) T,E →L[ℝ] E))

/-- Smooth coefficients give a genuinely smooth Volterra operator family. -/
theorem volterraOperator_contDiff {n : ℕ∞ω} (hB : ContDiff ℝ n B) :
    ContDiff ℝ n (fun x => volterraOperator T hT (B x)) := by
  exact contDiff_const.sub (contDiff_const.clm_comp (contDiff_multiplier B hB))

/-- Parameter smoothness of the actual inverse requires no parameter regularity
assumption on the chosen homogeneous fundamental evolutions. -/
theorem volterraInverse_contDiff (U : ∀ x, Evolution T hT (B x)) {n : ℕ∞ω}
    (hB : ContDiff ℝ n B) : ContDiff ℝ n (fun x => (U x).volterraInverse) := by
  have he : (fun x => (U x).volterraInverse) = fun x => (volterraOperator T hT (B x)).inverse := by
    funext x
    exact (U x).volterraInverse_eq_mapInverse
  rw [he, contDiff_iff_contDiffAt]
  intro x
  have hi : ContDiffAt ℝ n ContinuousLinearMap.inverse (volterraOperator T hT (B x)) := by
    change ContDiffAt ℝ n ContinuousLinearMap.inverse
      ((U x).volterraEquiv : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))
    exact contDiffAt_map_inverse (U x).volterraEquiv
  exact hi.comp x (volterraOperator_contDiff T hT B hB).contDiffAt

/-- The integral construction is genuinely smooth in parameters whenever the
coefficient, initial data and forcing are smooth in their actual Banach norms. -/
theorem solution_contDiff (U : ∀ x, Evolution T hT (B x))
    (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → E) {n : ℕ∞ω}
    (hB : ContDiff ℝ n B) (hf : ContDiff ℝ n f) (ha₀ : ContDiff ℝ n a₀) :
    ContDiff ℝ n (fun x => (U x).solution (f x) (a₀ x)) := by
  have he : (fun x => (U x).solution (f x) (a₀ x)) = fun x => (U x).volterraInverse
      ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) (a₀ x) + integral T hT (f x)) := by
    funext x
    exact (U x).solution_eq_volterraInverse (f x) (a₀ x)
  rw [he]
  exact (volterraInverse_contDiff T hT B U hB).clm_apply
    (((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)).contDiff.comp ha₀).add
      ((integral T hT).contDiff.comp hf))

end EulerLinearDuhamel
