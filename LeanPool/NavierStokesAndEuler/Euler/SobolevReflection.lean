/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderReflection
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDerivatives
import LeanPool.NavierStokesAndEuler.Euler.GradientReflection

/-! Joint reflection on the actual complete cylinder Sobolev spaces. -/

@[expose] public section


noncomputable section

namespace EulerSobolevReflection

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolevSpace
  EulerCylinderReflection EulerGradientReflection EulerCylinderSobolev
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Reflection of a derivative array includes the sign of each derivative word. -/
def reflectionArrayOperator (q : ℕ) :
    SobolevSpace period q →L[ℝ] (SobolevWord q → LiftL2 period) :=
  ContinuousLinearMap.pi fun w => ((-1 : ℝ) ^ w.1.val) •
    ((reflection period).toContinuousLinearMap.comp (wordOperator period w))

/-- The signed derivative array satisfies the actual strong-derivative compatibility. -/
theorem reflectionArray_mem (q : ℕ) (u : SobolevSpace period q) :
    reflectionArrayOperator period q u ∈ (sobolevSubspace period q).toSubmodule := by
  apply ClosedSubmodule.mem_iInf.mpr
  intro e
  have hd := word_hasDerivAt period u e.1.isLt e.2.1 e.2.2
  have hr := (reflection_hasDerivAt period (standardDirection e.2.2) hd).const_smul ((-1 : ℝ) ^
      e.1.val)
  change HasDerivAt (fun t => translation period (translationPath period (standardDirection e.2.2)
      t)
    (((-1 : ℝ) ^ e.1.val) • reflection period (u.val (edgeParent e))))
    (((-1 : ℝ) ^ (e.1.val + 1)) • reflection period (u.val (edgeChild e))) 0
  convert! hr using 1
  · funext t
    rw [map_smul]
    rfl
  · simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]
    rfl

/-- Joint pullback reflection as a genuine bounded map of the complete Sobolev space. -/
def sobolevReflection (q : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  (reflectionArrayOperator period q).codRestrict (sobolevSubspace period q).toSubmodule
    (reflectionArray_mem period q)

/-- The derivative coordinates of reflection have exactly the alternating signs. -/
@[simp] theorem sobolevReflection_apply {q : ℕ} (u : SobolevSpace period q) (w : SobolevWord q) :
    (sobolevReflection period q u).val w = (-1 : ℝ) ^ w.1.val • reflection period (u.val w) := rfl

/-- The underlying field is the actual L² pullback by joint negation. -/
@[simp] theorem value_sobolevReflection {q : ℕ} (u : SobolevSpace period q) :
    value period (sobolevReflection period q u) = reflection period (value period u) := by
  change (-1 : ℝ) ^ 0 • reflection period (value period u) = _
  simp

/-- Joint reflection is involutive on the complete Sobolev space. -/
@[simp] theorem sobolevReflection_involutive {q : ℕ} (u : SobolevSpace period q) :
    sobolevReflection period q (sobolevReflection period q u) = u := by
  apply value_injective period
  rw [value_sobolevReflection, value_sobolevReflection, reflection_involutive]

/-- Every genuine derivative coordinate keeps its L² norm under reflection. -/
theorem sobolevReflection_word_norm {q : ℕ} (u : SobolevSpace period q) (w : SobolevWord q) :
    ‖(sobolevReflection period q u).val w‖ = ‖u.val w‖ := by
  rw [sobolevReflection_apply, norm_smul, reflection_norm, norm_pow]
  norm_num

/-- Reflection preserves the actual finite Sobolev norm. -/
theorem sobolevReflection_norm {q : ℕ} (u : SobolevSpace period q) :
    ‖sobolevReflection period q u‖ = ‖u‖ := by
  apply le_antisymm
  · change ‖(sobolevReflection period q u).val‖ ≤ ‖u.val‖
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u.val)).mpr
    intro w
    rw [sobolevReflection_word_norm]
    exact norm_le_pi_norm u.val w
  · change ‖u.val‖ ≤ ‖(sobolevReflection period q u).val‖
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro w
    have hh := norm_le_pi_norm (sobolevReflection period q u).val w
    rwa [sobolevReflection_word_norm] at hh

/-- Reflection also preserves the source's sum-over-derivatives Sobolev norm. -/
theorem sobolevReflection_sumNorm {q : ℕ} (u : SobolevSpace period q) :
    sumNorm period (sobolevReflection period q u) = sumNorm period u := by
  unfold sumNorm
  exact Finset.sum_congr rfl fun w _ => sobolevReflection_word_norm period u w

/-- Truncating the Sobolev order commutes with actual reflection. -/
theorem truncate_reflection {q : ℕ} (u : SobolevSpace period (q + 1)) :
    truncateOperator period q (sobolevReflection period (q + 1) u) =
      sobolevReflection period q (truncateOperator period q u) := by
  apply value_injective period
  simp only [value_truncateOperator, value_sobolevReflection]

/-- Every actual coordinate derivative reverses sign under joint reflection. -/
theorem derivative_reflection {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q + 1)) :
    derivativeOperator period q i (sobolevReflection period (q + 1) u) =
      -sobolevReflection period q (derivativeOperator period q i u) := by
  apply Subtype.ext
  funext w
  change (-1 : ℝ) ^ (w.1.val + 1) • reflection period (u.val (derivativeIndex i w)) =
    -((-1 : ℝ) ^ w.1.val • reflection period (u.val (derivativeIndex i w)))
  simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]

/-- The symmetry whose fixed points are odd velocity fields. -/
def oddReflection (q : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  -sobolevReflection period q

/-- Odd reflection is represented by minus the field at the reflected point. -/
@[simp] theorem oddReflection_apply {q : ℕ} (u : SobolevSpace period q) :
    oddReflection period q u = -sobolevReflection period q u := rfl

/-- The signed reflection is involutive. -/
theorem oddReflection_involutive {q : ℕ} (u : SobolevSpace period q) :
    oddReflection period q (oddReflection period q u) = u := by
  simp only [oddReflection_apply, map_neg, neg_neg, sobolevReflection_involutive]

/-- The signed reflection preserves the Sobolev norm. -/
theorem oddReflection_norm {q : ℕ} (u : SobolevSpace period q) :
    ‖oddReflection period q u‖ = ‖u‖ := by
        rw [oddReflection_apply, norm_neg, sobolevReflection_norm]

/-- Signed reflection preserves the genuine weak divergence constraint. -/
theorem oddReflection_divergenceFree {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q)
    (hu : value period u ∈ divergenceFreeSpace period κ m) :
    value period (oddReflection period q u) ∈ divergenceFreeSpace period κ m := by
  change -value period (sobolevReflection period q u) ∈ divergenceFreeSpace period κ m
  rw [value_sobolevReflection]
  exact (divergenceFreeSpace period κ m).neg_mem (divergenceFreeSpace_reflection_mem period κ m hu)

end EulerSobolevReflection
