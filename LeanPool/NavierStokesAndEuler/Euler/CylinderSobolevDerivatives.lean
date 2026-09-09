/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators

@[expose] public section

/-! Actual coordinate derivatives and truncations between the complete cylinder Sobolev spaces. -/

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open scoped Topology

/-- An old word viewed in the next Sobolev order. -/
def truncateIndex {q : ℕ} (w : SobolevWord q) : SobolevWord (q + 1) :=
  ⟨⟨w.1.val, Nat.lt_succ_of_lt w.1.isLt⟩, w.2⟩

/-- Appending a direction indexes a derivative of the corresponding underlying derivative field. -/
def derivativeIndex {q : ℕ} (i : Fin 4) (w : SobolevWord q) : SobolevWord (q + 1) :=
  ⟨⟨w.1.val + 1, Nat.succ_lt_succ w.1.isLt⟩, Fin.snoc w.2 i⟩

variable (period : ℝ) [Fact (0 < period)]

/-- Continuous truncation forgets the highest derivative level. -/
def truncateOperator (q : ℕ) : SobolevSpace period (q + 1) →L[ℝ] SobolevSpace period q :=
  ((ContinuousLinearMap.pi (fun w : SobolevWord q =>
    ContinuousLinearMap.proj (truncateIndex w))).comp (arrayOperator period (q + 1))).codRestrict
    (sobolevSubspace period q).toSubmodule (by
      intro u
      apply ClosedSubmodule.mem_iInf.mpr
      intro e
      exact word_hasDerivAt period u (Nat.lt_succ_of_lt e.1.isLt) e.2.1 e.2.2)

/-- A coordinate derivative is a bounded map from H^(q+1) to H^q. -/
def derivativeOperator (q : ℕ) (i : Fin 4) :
    SobolevSpace period (q + 1) →L[ℝ] SobolevSpace period q :=
  ((ContinuousLinearMap.pi (fun w : SobolevWord q =>
    ContinuousLinearMap.proj (derivativeIndex i w))).comp (arrayOperator period (q +
      1))).codRestrict
    (sobolevSubspace period q).toSubmodule (by
      intro u
      apply ClosedSubmodule.mem_iInf.mpr
      intro e
      have hd := word_hasDerivAt period u (Nat.succ_lt_succ e.1.isLt) (Fin.snoc e.2.1 i) e.2.2
      change HasDerivAt (fun t => translation period
        (translationPath period (standardDirection e.2.2) t)
        (u.val (derivativeIndex i (edgeParent e))))
        (u.val (derivativeIndex i (edgeChild e))) 0
      simpa only [word, derivativeIndex, edgeParent, edgeChild, Fin.cons_snoc_eq_snoc_cons] using
        hd)

/-- Truncation acts by the literal inclusion of derivative-word coordinates. -/
@[simp]
theorem truncateOperator_apply {q : ℕ} (u : SobolevSpace period (q + 1)) (w : SobolevWord q) :
    (truncateOperator period q u).val w = u.val (truncateIndex w) := rfl

/-- A derivative acts by appending its direction to each word. -/
@[simp]
theorem derivativeOperator_apply {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q + 1))
    (w : SobolevWord q) :
    (derivativeOperator period q i u).val w = u.val (derivativeIndex i w) := rfl

/-- Truncation is contractive in the complete derivative-array norm. -/
theorem truncateOperator_bound {q : ℕ} (u : SobolevSpace period (q + 1)) :
    ‖truncateOperator period q u‖ ≤ ‖u‖ := by
  change ‖(truncateOperator period q u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro w
  exact word_norm_le period u (truncateIndex w)

/-- One coordinate derivative has operator bound one between successive Sobolev levels. -/
theorem derivativeOperator_bound {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q + 1)) :
    ‖derivativeOperator period q i u‖ ≤ ‖u‖ := by
  change ‖(derivativeOperator period q i u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro w
  exact word_norm_le period u (derivativeIndex i w)

/-- Truncation leaves the underlying L² field unchanged. -/
@[simp]
theorem value_truncateOperator {q : ℕ} (u : SobolevSpace period (q + 1)) :
    value period (truncateOperator period q u) = value period u := rfl

/-- The derivative operator really differentiates the underlying L² translation orbit. -/
theorem derivativeOperator_hasDerivAt {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q + 1)) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t)
      (value period u)) (value period (derivativeOperator period q i u)) 0 := by
  have hd := word_hasDerivAt period u (Nat.zero_lt_succ q) Fin.elim0 i
  have hw : Fin.cons i (Fin.elim0 : Fin 0 → Fin 4) =
      Fin.snoc (α := fun _ : Fin 1 => Fin 4) (Fin.elim0 : Fin 0 → Fin 4) i := by
    funext j
    fin_cases j
    rfl
  change HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t)
    (u.val (emptyWord (q + 1)))) (u.val (derivativeIndex i (emptyWord q))) 0
  simpa only [word, emptyWord, derivativeIndex, hw] using hd

/-- Coordinate differentiation commutes with actual Sobolev translation. -/
theorem derivativeOperator_translation {q : ℕ} (i : Fin 4) (a : LiftDomain period)
    (u : SobolevSpace period (q + 1)) :
    derivativeOperator period q i (sobolevTranslation period (q + 1) a u) =
      sobolevTranslation period q a (derivativeOperator period q i u) := by
  apply Subtype.ext
  funext w
  rfl

end EulerCylinderSobolevSpace
