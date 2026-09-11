/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoerciveProjection
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Inverse Regularity
-/

@[expose] public section

noncomputable section

namespace EulerInverseRegularity

open EulerCoerciveProjection InnerProductSpace ContinuousLinearMap
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The bounded translation difference quotient with increment h. -/
def differenceQuotient (τ : E →L[ℝ] E) (h : ℝ) : E →L[ℝ] E :=
  h⁻¹ • (τ - ContinuousLinearMap.id ℝ E)

/-- The operator commutator D T minus T D. -/
def commutator (D T : E →L[ℝ] E) : E →L[ℝ] E := D.comp T - T.comp D

/-- Repeated commutation with an operator, defined by its actual algebraic formula. -/
def iteratedRingCommutator {R : Type*} [Ring R] (D T : R) : ℕ → R
  | 0 => T
  | n + 1 => D * iteratedRingCommutator D T n - iteratedRingCommutator D T n * D

theorem mul_iteratedRingCommutator {R : Type*} [Ring R] (D T : R) (n : ℕ) :
    D * iteratedRingCommutator D T n =
      iteratedRingCommutator D T n * D + iteratedRingCommutator D T (n + 1) := by
  simp only [iteratedRingCommutator]
  abel

/-- The complete noncommutative Leibniz formula, proved from the commutator definition. -/
theorem iterated_operator_leibniz {R : Type*} [Ring R] (D T : R) (n : ℕ) :
    D ^ n * T = ∑ l ∈ Finset.range (n + 1),
      n.choose l • (iteratedRingCommutator D T l * D ^ (n - l)) := by
  induction n with
  | zero => simp [iteratedRingCommutator]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum,
      Finset.sum_choose_succ_nsmul (fun l r => iteratedRingCommutator D T l * D ^ r) n,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    have hln : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hsub : n + 1 - l = (n - l) + 1 := by omega
    calc
      D * (n.choose l • (iteratedRingCommutator D T l * D ^ (n - l))) =
          n.choose l • ((D * iteratedRingCommutator D T l) * D ^ (n - l)) := by
        rw [mul_smul_comm, mul_assoc]
      _ = n.choose l • ((iteratedRingCommutator D T l * D +
          iteratedRingCommutator D T (l + 1)) * D ^ (n - l)) := by
        rw [mul_iteratedRingCommutator]
      _ = n.choose l • (iteratedRingCommutator D T l * D ^ (n + 1 - l)) +
          n.choose l • (iteratedRingCommutator D T (l + 1) * D ^ (n - l)) := by
        rw [add_mul, nsmul_add, hsub, pow_succ', mul_assoc]

theorem inverse_commutator_apply (T D : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) :
    D (coerciveInverse T c hc hT f) =
      coerciveInverse T c hc hT
        (D f - commutator D T (coerciveInverse T c hc hT f)) := by
  apply (coerciveEquiv T c hc hT).injective
  simp only [coerciveEquiv_apply, operator_inverse_apply, commutator,
    sub_apply, ContinuousLinearMap.comp_apply]
  abel

theorem inverse_commutator_norm_le (T D : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) :
    ‖D (coerciveInverse T c hc hT f)‖ ≤
      c⁻¹ * (‖D f‖ + ‖commutator D T (coerciveInverse T c hc hT f)‖) := by
  rw [inverse_commutator_apply T D c hc hT f]
  exact (coerciveInverse_apply_norm_le T c hc hT _).trans
    (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.2 hc.le))

/-- The full differentiated inverse recurrence, derived from the operator equation. -/
theorem inverse_iterated_commutator_apply (T D : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) (n : ℕ) :
    (D ^ (n + 1)) (coerciveInverse T c hc hT f) =
      coerciveInverse T c hc hT
        ((D ^ (n + 1)) f - ∑ l ∈ Finset.range (n + 1),
          (n + 1).choose (l + 1) •
            (iteratedRingCommutator D T (l + 1)
              ((D ^ (n - l)) (coerciveInverse T c hc hT f)))) := by
  have hprod := congrArg (fun A : E →L[ℝ] E => A (coerciveInverse T c hc hT f))
    (iterated_operator_leibniz D T (n + 1))
  simp only [mul_apply_eq_comp, operator_inverse_apply, sum_apply, smul_apply] at hprod
  rw [Finset.sum_range_succ'] at hprod
  simp only [Nat.choose_zero_right, iteratedRingCommutator, Nat.sub_zero,
    one_smul, Nat.add_sub_add_right] at hprod
  apply (coerciveEquiv T c hc hT).injective
  simp only [coerciveEquiv_apply, operator_inverse_apply]
  apply eq_sub_of_add_eq
  exact (add_comm _ _).trans hprod.symm

/-- The quantitative all-order recurrence follows from the exact commutator identity. -/
theorem inverse_iterated_commutator_norm_le (T D : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) (n : ℕ) :
    ‖(D ^ (n + 1)) (coerciveInverse T c hc hT f)‖ ≤ c⁻¹ *
      (‖(D ^ (n + 1)) f‖ + ∑ l ∈ Finset.range (n + 1),
        ((n + 1).choose (l + 1) : ℝ) * ‖iteratedRingCommutator D T (l + 1)‖ *
          ‖(D ^ (n - l)) (coerciveInverse T c hc hT f)‖) := by
  have hs : ‖∑ l ∈ Finset.range (n + 1), (n + 1).choose (l + 1) •
        (iteratedRingCommutator D T (l + 1)
          ((D ^ (n - l)) (coerciveInverse T c hc hT f)))‖ ≤
      ∑ l ∈ Finset.range (n + 1),
        ((n + 1).choose (l + 1) : ℝ) * ‖iteratedRingCommutator D T (l + 1)‖ *
          ‖(D ^ (n - l)) (coerciveInverse T c hc hT f)‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro l _
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      ((iteratedRingCommutator D T (l + 1)).le_opNorm
        ((D ^ (n - l)) (coerciveInverse T c hc hT f)))
      (Nat.cast_nonneg ((n + 1).choose (l + 1)))
  rw [inverse_iterated_commutator_apply T D c hc hT f n]
  refine (coerciveInverse_apply_norm_le T c hc hT _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hc.le)
  exact (norm_sub_le _ _).trans (add_le_add_right hs _)

omit [CompleteSpace E] in
theorem differenceQuotient_commutator (τ T : E →L[ℝ] E) (h : ℝ) :
    commutator (differenceQuotient τ h) T = h⁻¹ • commutator τ T := by
  ext x
  simp only [commutator, differenceQuotient, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul]
  simp only [smul_sub]
  abel

/-- The spatial difference-quotient estimate, before any passage to weak derivatives. -/
theorem inverse_differenceQuotient_norm_le (T τ : E →L[ℝ] E) (h c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) :
    ‖differenceQuotient τ h (coerciveInverse T c hc hT f)‖ ≤
      c⁻¹ * (‖differenceQuotient τ h f‖ +
        ‖h⁻¹ • commutator τ T (coerciveInverse T c hc hT f)‖) := by
  simpa only [differenceQuotient_commutator, smul_apply] using
    inverse_commutator_norm_le T (differenceQuotient τ h) c hc hT f

theorem coerciveInverse_eq_mapInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    coerciveInverse T c hc hT = T.inverse := by
  have he : (coerciveEquiv T c hc hT : E →L[ℝ] E) = T := by
    ext x
    exact coerciveEquiv_apply T c hc hT x
  calc
    coerciveInverse T c hc hT =
        (coerciveEquiv T c hc hT).symm.toContinuousLinearMap := rfl
    _ = (coerciveEquiv T c hc hT : E →L[ℝ] E).inverse :=
      (ContinuousLinearMap.inverse_equiv (coerciveEquiv T c hc hT)).symm
    _ = T.inverse := congrArg ContinuousLinearMap.inverse he

theorem coerciveInverse_eq_ringInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    coerciveInverse T c hc hT = Ring.inverse T := by
  rw [ContinuousLinearMap.ringInverse_eq_inverse]
  exact coerciveInverse_eq_mapInverse T c hc hT

/-- A `Cⁿ` family of coercive operators has a `Cⁿ` family of the constructed inverses. -/
theorem contDiff_coerciveInverse (T : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪T t x, x⟫_ℝ) {n : ℕ∞ω}
    (hreg : ContDiff ℝ n T) :
    ContDiff ℝ n (fun t => coerciveInverse (T t) c hc (hT t)) := by
  have he : ∀ t, (coerciveEquiv (T t) c hc (hT t) : E →L[ℝ] E) = T t := by
    intro t
    ext x
    exact coerciveEquiv_apply (T t) c hc (hT t) x
  have hfun : (fun t => coerciveInverse (T t) c hc (hT t)) =
      fun t => (T t).inverse := by
    funext t
    exact coerciveInverse_eq_mapInverse (T t) c hc (hT t)
  rw [hfun, contDiff_iff_contDiffAt]
  intro t
  have hinv : ContDiffAt ℝ n ContinuousLinearMap.inverse (T t) := by
    rw [← he t]
    exact contDiffAt_map_inverse (coerciveEquiv (T t) c hc (hT t))
  exact hinv.comp t hreg.contDiffAt

/-- The time derivative of the constructed inverse is `-I T' I`. -/
theorem hasDerivAt_coerciveInverse (T : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪T t x, x⟫_ℝ)
    (t : ℝ) (T₁ : E →L[ℝ] E) (hder : HasDerivAt T T₁ t) :
    HasDerivAt (fun s => coerciveInverse (T s) c hc (hT s))
      (-(coerciveInverse (T t) c hc (hT t)).comp
        (T₁.comp (coerciveInverse (T t) c hc (hT t)))) t := by
  let u : (E →L[ℝ] E)ˣ := (coerciveEquiv (T t) c hc (hT t)).toUnit
  have hu : (u : E →L[ℝ] E) = T t := by
    ext x
    exact coerciveEquiv_apply (T t) c hc (hT t) x
  have hui : (↑u⁻¹ : E →L[ℝ] E) = coerciveInverse (T t) c hc (hT t) := rfl
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hi
  have hcomp := hi.comp_hasDerivAt t hder
  have hfun : (fun s => coerciveInverse (T s) c hc (hT s)) = Ring.inverse ∘ T := by
    funext s
    exact coerciveInverse_eq_ringInverse (T s) c hc (hT s)
  rw [hfun]
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply, hui,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hcomp

theorem hasDerivAt_coerciveSolution (T : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪T t x, x⟫_ℝ)
    (f : ℝ → E) (t : ℝ) (T₁ : E →L[ℝ] E) (f₁ : E)
    (hder : HasDerivAt T T₁ t) (hf : HasDerivAt f f₁ t) :
    HasDerivAt (fun s => coerciveInverse (T s) c hc (hT s) (f s))
      (coerciveInverse (T t) c hc (hT t)
        (f₁ - T₁ (coerciveInverse (T t) c hc (hT t) (f t)))) t := by
  convert (hasDerivAt_coerciveInverse T c hc hT t T₁ hder).clm_apply hf using 1
  simp only [neg_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

section Projected

variable (S : Submodule ℝ E) [CompleteSpace S]

omit [CompleteSpace E] in
theorem contDiff_projectedOperator (G : ℝ → E →L[ℝ] E) {n : ℕ∞ω}
    (hreg : ContDiff ℝ n G) :
    ContDiff ℝ n (fun t => projectedOperator S (G t)) := by
  exact contDiff_const.clm_comp (hreg.clm_comp contDiff_const)

omit [CompleteSpace E] in
theorem hasDerivAt_projectedOperator (G : ℝ → E →L[ℝ] E) (t : ℝ)
    (G₁ : E →L[ℝ] E) (hder : HasDerivAt G G₁ t) :
    HasDerivAt (fun s => projectedOperator S (G s)) (projectedOperator S G₁) t := by
  simpa only [zero_comp, comp_zero, zero_add, add_zero, projectedOperator, comp_assoc] using
    (hasDerivAt_const t S.orthogonalProjectionOnto).clm_comp
      (hder.clm_comp (hasDerivAt_const t S.subtypeL))

omit [CompleteSpace E] in
theorem contDiff_projectedInverse (G : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪G t x, x⟫_ℝ) {n : ℕ∞ω}
    (hreg : ContDiff ℝ n G) :
    ContDiff ℝ n (fun t => projectedInverse S (G t) c hc (hG t)) :=
  contDiff_coerciveInverse (fun t => projectedOperator S (G t)) c hc
    (fun t => projectedOperator_coercive S (G t) c (hG t))
    (contDiff_projectedOperator S G hreg)

omit [CompleteSpace E] in
theorem hasDerivAt_projectedInverse (G : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪G t x, x⟫_ℝ)
    (t : ℝ) (G₁ : E →L[ℝ] E) (hder : HasDerivAt G G₁ t) :
    HasDerivAt (fun s => projectedInverse S (G s) c hc (hG s))
      (-(projectedInverse S (G t) c hc (hG t)).comp
        ((projectedOperator S G₁).comp (projectedInverse S (G t) c hc (hG t)))) t :=
  hasDerivAt_coerciveInverse (fun t => projectedOperator S (G t)) c hc
    (fun t => projectedOperator_coercive S (G t) c (hG t)) t
    (projectedOperator S G₁) (hasDerivAt_projectedOperator S G t G₁ hder)

end Projected

end EulerInverseRegularity
