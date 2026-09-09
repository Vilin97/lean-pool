/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevTranslationDifferentiation

@[expose] public section

/-! Genuine restrictions between any two finite cylinder Sobolev orders. -/

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open scoped Topology

/-- The same derivative word at a larger Sobolev order. -/
def restrictIndex {p q : ℕ} (h : q ≤ p) (w : SobolevWord q) : SobolevWord p :=
  ⟨⟨w.1.val, Nat.lt_of_lt_of_le w.1.isLt (Nat.succ_le_succ h)⟩, w.2⟩

variable (period : ℝ) [Fact (0 < period)]

/-- Restriction is a bounded linear map between the actual complete Sobolev spaces. -/
def restrictOperator {p q : ℕ} (h : q ≤ p) : SobolevSpace period p →L[ℝ] SobolevSpace period q :=
  ((ContinuousLinearMap.pi (fun w : SobolevWord q =>
    ContinuousLinearMap.proj (restrictIndex h w))).comp (arrayOperator period p)).codRestrict
    (sobolevSubspace period q).toSubmodule (by
      intro u
      apply ClosedSubmodule.mem_iInf.mpr
      intro e
      exact word_hasDerivAt period u (Nat.lt_of_lt_of_le e.1.isLt h) e.2.1 e.2.2)

@[simp] theorem restrictOperator_apply {p q : ℕ} (h : q ≤ p) (u : SobolevSpace period p) (w :
  SobolevWord q) :
    (restrictOperator period h u).val w = u.val (restrictIndex h w) := rfl

@[simp] theorem value_restrictOperator {p q : ℕ} (h : q ≤ p) (u : SobolevSpace period p) :
    value period (restrictOperator period h u) = value period u := rfl

theorem restrictOperator_bound {p q : ℕ} (h : q ≤ p) (u : SobolevSpace period p) :
    ‖restrictOperator period h u‖ ≤ ‖u‖ := by
  change ‖(restrictOperator period h u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro w
  exact word_norm_le period u (restrictIndex h w)

@[simp] theorem restrictOperator_self {q : ℕ} (u : SobolevSpace period q) :
    restrictOperator period (le_refl q) u = u := by
  apply value_injective period
  rfl

@[simp] theorem restrictOperator_comp {p q r : ℕ} (hqp : q ≤ p) (hrq : r ≤ q) (u : SobolevSpace
  period p) :
    restrictOperator period hrq (restrictOperator period hqp u) = restrictOperator period
      (hrq.trans hqp) u := by
  apply value_injective period
  rfl

@[simp] theorem restrictOperator_truncate {p q : ℕ} (h : q ≤ p) (u : SobolevSpace period (p+1)) :
    restrictOperator period h (truncateOperator period p u) = restrictOperator period (by omega : q
      ≤ p+1) u := by
  apply value_injective period
  rfl

@[simp] theorem truncate_restrictOperator {p q : ℕ} (h : q+1 ≤ p) (u : SobolevSpace period p) :
    truncateOperator period q (restrictOperator period h u) = restrictOperator period (by omega : q
      ≤ p) u := by
  apply value_injective period
  rfl

/-- Actual restriction and spatial differentiation commute. -/
theorem restrictOperator_derivative {p q : ℕ} (h : q ≤ p) (i : Fin 4) (u : SobolevSpace period
  (p+1)) :
    restrictOperator period h (derivativeOperator period p i u) =
      derivativeOperator period q i (restrictOperator period (Nat.succ_le_succ h) u) := by
  apply value_injective period
  rfl

/-- Restriction commutes with every genuine cylinder translation. -/
theorem restrictOperator_translation {p q : ℕ} (h : q ≤ p) (a : LiftDomain period) (u :
  SobolevSpace period p) :
    restrictOperator period h (sobolevTranslation period p a u) =
      sobolevTranslation period q a (restrictOperator period h u) := by
  apply value_injective period
  rfl

end EulerCylinderSobolevSpace
