/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderMollifier

/-! Continuous operators and exact norm comparisons on the actual complete cylinder Sobolev spaces.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderMollifier
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The continuous inclusion of the Sobolev space into its finite derivative array. -/
def arrayOperator (q : ℕ) : SobolevSpace period q →L[ℝ] (SobolevWord q → LiftL2 period) :=
  (sobolevSubspace period q).toSubmodule.subtypeL

/-- Continuous evaluation of the underlying L² field. -/
def valueOperator (q : ℕ) : SobolevSpace period q →L[ℝ] LiftL2 period :=
  (ContinuousLinearMap.proj (emptyWord q)).comp (arrayOperator period q)

/-- Continuous evaluation of one actual derivative coordinate. -/
def wordOperator {q : ℕ} (w : SobolevWord q) : SobolevSpace period q →L[ℝ] LiftL2 period :=
  (ContinuousLinearMap.proj w).comp (arrayOperator period q)

/-- The L² norm of each genuine derivative is bounded by the complete Sobolev norm. -/
theorem word_norm_le {q : ℕ} (u : SobolevSpace period q) (w : SobolevWord q) : ‖u.val w‖ ≤ ‖u‖ :=
  norm_le_pi_norm u.val w

/-- The underlying L² evaluation is contractive. -/
theorem value_norm_le {q : ℕ} (u : SobolevSpace period q) : ‖value period u‖ ≤ ‖u‖ :=
  word_norm_le period u (emptyWord q)

/-- The sum of actual derivative norms, in the source's Sobolev convention. -/
def sumNorm {q : ℕ} (u : SobolevSpace period q) : ℝ := ∑ w : SobolevWord q, ‖u.val w‖

/-- The complete-array norm is bounded by the source's derivative sum. -/
theorem norm_le_sumNorm {q : ℕ} (u : SobolevSpace period q) : ‖u‖ ≤ sumNorm period u := by
  change ‖u.val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
  intro w
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ w)

/-- The source's derivative sum is bounded by a fixed Sobolev-order multiple of the complete norm.
-/
theorem sumNorm_le_card_norm {q : ℕ} (u : SobolevSpace period q) :
    sumNorm period u ≤ (Fintype.card (SobolevWord q) : ℝ) * ‖u‖ := by
  change (∑ w : SobolevWord q, ‖u.val w‖) ≤
    (Fintype.card (SobolevWord q) : ℝ) * ‖u.val‖
  simpa only [nsmul_eq_mul] using Pi.sum_norm_apply_le_norm u.val

/-- The derivative sum is exactly the norm of the reconstructed genuine strong jet. -/
theorem sumNorm_eq_jet {q : ℕ} (u : SobolevSpace period q) :
    sumNorm period u = (toJet period u).sobolevNorm := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  unfold sumNorm
  simp only [Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range
    (fun n => ∑ w : Fin n → Fin 4, ‖(toJet period u).word w‖) (q + 1)]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro w _
  rw [toJet_word period u (Nat.le_of_lt_succ n.isLt)]
  rfl

/-- A translation-commuting L² operator acts on every actual derivative coordinate. -/
def liftOperator (q : ℕ) (A : LiftL2 period →L[ℝ] LiftL2 period)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f)) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  ((ContinuousLinearMap.pi (fun w : SobolevWord q => A.comp (ContinuousLinearMap.proj w))).comp
    (arrayOperator period q)).codRestrict (sobolevSubspace period q).toSubmodule (by
      intro u
      apply ClosedSubmodule.mem_iInf.mpr
      intro e
      have hd := A.hasFDerivAt.comp_hasDerivAt 0
        (word_hasDerivAt period u e.1.isLt e.2.1 e.2.2)
      change HasDerivAt (fun t => translation period
        (translationPath period (standardDirection e.2.2) t) (A (u.val (edgeParent e))))
        (A (u.val (edgeChild e))) 0
      simpa only [Function.comp_def, hA, word, edgeParent, edgeChild] using hd)

/-- A lifted operator applies the same L² operator to each derivative coordinate. -/
@[simp]
theorem liftOperator_apply {q : ℕ} (A : LiftL2 period →L[ℝ] LiftL2 period)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) (w : SobolevWord q) :
    (liftOperator period q A hA u).val w = A (u.val w) := rfl

/-- The lifted Sobolev operator has the same uniform bound as its L² action. -/
theorem liftOperator_bound {q : ℕ} (A : LiftL2 period →L[ℝ] LiftL2 period)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : ‖liftOperator period q A hA u‖ ≤ ‖A‖ * ‖u‖ := by
  change ‖(liftOperator period q A hA u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro w
  exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (word_norm_le period u w) (norm_nonneg A))

/-- The operator norm bound for an operator lifted to the complete Sobolev space. -/
theorem norm_liftOperator_le (q : ℕ) (A : LiftL2 period →L[ℝ] LiftL2 period)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f)) :
    ‖liftOperator period q A hA‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (liftOperator_bound period A hA)

/-- The action on the underlying field is exactly the original L² operator. -/
@[simp]
theorem value_liftOperator {q : ℕ} (A : LiftL2 period →L[ℝ] LiftL2 period)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : value period (liftOperator period q A hA u) = A (value period u)
        := rfl

/-- Translations commute in the cylinder's additive group. -/
theorem translations_commute (a b : LiftDomain period) (f : LiftL2 period) :
    translation period a (translation period b f) = translation period b (translation period a f)
        := by
  rw [translation_add, translation_add, add_comm a b]

/-- Actual cylinder translation as a bounded operator on the complete Sobolev space. -/
def sobolevTranslation (q : ℕ) (a : LiftDomain period) : SobolevSpace period q →L[ℝ] SobolevSpace
    period q :=
  liftOperator period q (translation period a).toContinuousLinearMap (translations_commute period a)

/-- Cylinder translation preserves the complete Sobolev norm exactly. -/
theorem sobolevTranslation_norm {q : ℕ} (a : LiftDomain period) (u : SobolevSpace period q) :
    ‖sobolevTranslation period q a u‖ = ‖u‖ := by
  apply le_antisymm
  · change ‖(sobolevTranslation period q a u).val‖ ≤ ‖u.val‖
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u.val)).mpr
    intro w
    change ‖translation period a (u.val w)‖ ≤ ‖u.val‖
    rw [(translation period a).norm_map]
    exact norm_le_pi_norm u.val w
  · change ‖u.val‖ ≤ ‖(sobolevTranslation period q a u).val‖
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro w
    have h := norm_le_pi_norm (sobolevTranslation period q a u).val w
    change ‖translation period a (u.val w)‖ ≤ _ at h
    simpa only [(translation period a).norm_map] using h

/-- The translation action is strongly continuous in the complete Sobolev topology. -/
theorem sobolevTranslation_continuous {q : ℕ} (u : SobolevSpace period q) :
    Continuous (fun a => sobolevTranslation period q a u) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  exact translation_continuous period (u.val w)

end EulerCylinderSobolevSpace
