/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.OrthogonalIdempotentExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# Finite spectral-block Sylvester reconstruction

This is the purely algebraic and scalar-Fourier core of the separated
Sylvester theorem.  It is parameterized by a scalar kernel and its reciprocal
identity, so it is independent of the particular Haagerup--Zsido construction.

**Promoted 2026-07-30 under lane `EXP-PROMOTE-MISC`**, in the same cascade: it became
promotable only after the modules it imported were promoted earlier in this lane.  Nothing is
restated; names and namespace are unchanged.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.Sylvester

open TauCeti.DavisKahanExt

open DavisKahan

open MeasureTheory Set
open scoped InnerProductSpace BigOperators

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Finite diagonal operator with respect to a projection family. -/
noncomputable def finiteDiagonalOperator {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (P : Fin n → H →L[ℂ] H) (a : Fin n → ℝ) : H →L[ℂ] H :=
  ∑ i, (a i : ℂ) • P i

/-- The unitary exponential of a finite real diagonal operator acts
coefficientwise. -/
theorem unitaryGroup_finiteDiagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} (P : Fin n → H →L[ℂ] H) (a : Fin n → ℝ)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hsum : ∑ i, P i = (1 : H →L[ℂ] H)) (t : ℝ) :
    NormedSpace.exp (((t : ℂ) * Complex.I) • finiteDiagonalOperator P a) =
      ∑ i, Complex.exp (((t * a i : ℝ) : ℂ) * Complex.I) • P i := by
  unfold finiteDiagonalOperator
  have hscale : (((t : ℂ) * Complex.I) • ∑ i, (a i : ℂ) • P i) =
      ((t : ℂ) • ∑ i, ((a i : ℂ) * Complex.I) • P i) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, smul_smul]
    congr 1
    ring
  rw [hscale]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    exp_finset_orthogonal_idempotents P
      (fun i => (a i : ℂ) * Complex.I) hidem horth hsum t

omit [CompleteSpace F] in
/-- A diagonal block selects the corresponding coefficient on the left. -/
theorem finiteDiagonal_select_left
    {m : ℕ} (P : Fin m → F →L[ℂ] F) (a : Fin m → ℝ)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (i : Fin m) :
    P i ∘L finiteDiagonalOperator P a = (a i : ℂ) • P i := by
  unfold finiteDiagonalOperator
  rw [ContinuousLinearMap.comp_finsetSum,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [ContinuousLinearMap.comp_smul]
    change (a i : ℂ) • (P i * P i) = _
    rw [hidem i]
  · intro j _ hji
    rw [ContinuousLinearMap.comp_smul]
    change (a j : ℂ) • (P i * P j) = 0
    rw [horth i j hji.symm, smul_zero]

omit [CompleteSpace E] in
/-- A diagonal block selects the corresponding coefficient on the right. -/
theorem finiteDiagonal_select_right
    {m : ℕ} (P : Fin m → E →L[ℂ] E) (a : Fin m → ℝ)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (i : Fin m) :
    finiteDiagonalOperator P a ∘L P i = (a i : ℂ) • P i := by
  unfold finiteDiagonalOperator
  rw [ContinuousLinearMap.finsetSum_comp,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [ContinuousLinearMap.smul_comp]
    change (a i : ℂ) • (P i * P i) = _
    rw [hidem i]
  · intro j _ hji
    rw [ContinuousLinearMap.smul_comp]
    change (a j : ℂ) • (P j * P i) = 0
    rw [horth j i hji, smul_zero]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Sylvester defect restricted to one spectral rectangle is scalar. -/
theorem finiteDiagonal_sylvester_block
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (X : E →L[ℂ] F) (i : Fin m) (j : Fin n) :
    P i ∘L (finiteDiagonalOperator P a ∘L X -
      X ∘L finiteDiagonalOperator Q b) ∘L Q j =
      (((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j) := by
  apply ContinuousLinearMap.ext
  intro v
  have hL := ContinuousLinearMap.ext_iff.mp
    (finiteDiagonal_select_left P a hPid hPorth i) (X (Q j v))
  have hR := ContinuousLinearMap.ext_iff.mp
    (finiteDiagonal_select_right Q b hQid hQorth j) v
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    map_sub, smul_apply] at hL hR ⊢
  rw [hL, hR, map_smul, map_smul, Complex.ofReal_sub, sub_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The full operator is the sum of all rectangular blocks. -/
theorem eq_sum_rectangular_blocks
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQsum : ∑ j, Q j = (1 : E →L[ℂ] E))
    (X : E →L[ℂ] F) :
    X = ∑ i, ∑ j, P i ∘L X ∘L Q j := by
  calc
    X = (∑ i, P i) ∘L X ∘L (∑ j, Q j) := by
      rw [hPsum, hQsum]
      ext v
      simp
    _ = ∑ i, ∑ j, P i ∘L X ∘L Q j := by
      simp only [ContinuousLinearMap.finsetSum_comp,
        ContinuousLinearMap.comp_finsetSum]
      rw [Finset.sum_comm]

/-- Expansion of the conjugated Sylvester defect into scalar spectral blocks. -/
theorem finiteDiagonal_orbit_expansion
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (hQsum : ∑ i, Q i = (1 : E →L[ℂ] E))
    (X : E →L[ℂ] F) (t : ℝ) :
    NormedSpace.exp ((((t : ℂ) * Complex.I) • finiteDiagonalOperator P a)) ∘L
        (finiteDiagonalOperator P a ∘L X - X ∘L finiteDiagonalOperator Q b) ∘L
        NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • finiteDiagonalOperator Q b) =
      ∑ i, ∑ j,
        Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
          ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j)) := by
  rw [unitaryGroup_finiteDiagonal P a hPid hPorth hPsum t,
    unitaryGroup_finiteDiagonal Q b hQid hQorth hQsum (-t)]
  simp only [ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [finiteDiagonal_sylvester_block P Q a b hPid hPorth hQid hQorth X i j, smul_smul]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [CompleteSpace E] [CompleteSpace F] in
/-- The separated finite diagonal Sylvester equation has an explicit
blockwise solution. -/
theorem finiteDiagonal_sylvester_solution
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (hQsum : ∑ i, Q i = (1 : E →L[ℂ] E))
    (hne : ∀ i j, a i - b j ≠ 0)
    (C : E →L[ℂ] F) :
    finiteDiagonalOperator P a ∘L
        (∑ i, ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) • (P i ∘L C ∘L Q j)) -
      (∑ i, ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) • (P i ∘L C ∘L Q j)) ∘L
        finiteDiagonalOperator Q b = C := by
  have hL : finiteDiagonalOperator P a ∘L
      (∑ i, ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) • (P i ∘L C ∘L Q j)) =
      ∑ i, ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) •
        ((a i : ℂ) • (P i ∘L C ∘L Q j)) := by
    rw [ContinuousLinearMap.comp_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.comp_smul]
    congr 1
    calc
      finiteDiagonalOperator P a ∘L (P i ∘L C ∘L Q j)
          = (finiteDiagonalOperator P a ∘L P i) ∘L C ∘L Q j := by
            rw [ContinuousLinearMap.comp_assoc]
      _ = (a i : ℂ) • (P i ∘L C ∘L Q j) := by
            rw [finiteDiagonal_select_right P a hPid hPorth i,
              ContinuousLinearMap.smul_comp]
  have hR : (∑ i, ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) • (P i ∘L C ∘L Q j)) ∘L
      finiteDiagonalOperator Q b =
      ∑ i, ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) •
        ((b j : ℂ) • (P i ∘L C ∘L Q j)) := by
    rw [ContinuousLinearMap.finsetSum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.finsetSum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.smul_comp]
    congr 1
    calc
      (P i ∘L C ∘L Q j) ∘L finiteDiagonalOperator Q b
          = P i ∘L C ∘L (Q j ∘L finiteDiagonalOperator Q b) := by
            rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
      _ = (b j : ℂ) • (P i ∘L C ∘L Q j) := by
            rw [finiteDiagonal_select_left Q b hQid hQorth j,
              ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]
  rw [hL, hR, ← Finset.sum_sub_distrib]
  calc
    (∑ i, ((∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) •
          ((a i : ℂ) • (P i ∘L C ∘L Q j))) -
        ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) •
          ((b j : ℂ) • (P i ∘L C ∘L Q j))))
        = ∑ i, ∑ j, P i ∘L C ∘L Q j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, smul_smul, ← sub_smul, ← mul_sub]
      have hone : ((((a i - b j)⁻¹ : ℝ) : ℂ)) *
          ((a i : ℂ) - (b j : ℂ)) = 1 := by
        norm_cast
        exact inv_mul_cancel₀ (hne i j)
      rw [hone, one_smul]
    _ = C := (eq_sum_rectangular_blocks P Q hPsum hQsum C).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- Integrability of one scalar oscillatory block against an `L1` kernel. -/
theorem integrable_scalar_oscillatory_block
    (μ : ℝ → ℂ) (hμ : Integrable μ)
    (r : ℝ) (T : E →L[ℂ] F) :
    Integrable fun t : ℝ =>
      (μ t * Complex.exp ((((t * r : ℝ) : ℂ) * Complex.I))) • T := by
  have hf : Integrable fun t : ℝ =>
      μ t * Complex.exp ((((t * r : ℝ) : ℂ) * Complex.I)) := by
    apply Integrable.mono' hμ.norm
    · exact hμ.aestronglyMeasurable.mul
        (Complex.continuous_exp.comp
          (Complex.continuous_ofReal.comp
            (continuous_id.mul continuous_const) |>.mul continuous_const)).aestronglyMeasurable
    · filter_upwards [] with t
      apply le_of_eq
      rw [norm_mul, Complex.norm_exp]
      have hre : ((((t * r : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one]
  exact hf.smul_const T

/-- Finite blockwise reconstruction from the scalar reciprocal identity. -/
theorem finiteDiagonal_sylvester_reconstruction
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (hQsum : ∑ i, Q i = (1 : E →L[ℂ] E))
    (μ : ℝ → ℂ) (hμ : Integrable μ)
    (hscalar : ∀ i j,
      ∫ t : ℝ, μ t *
        Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) =
          (((a i - b j)⁻¹ : ℝ) : ℂ))
    (hne : ∀ i j, a i - b j ≠ 0)
    (X : E →L[ℂ] F) :
    X = ∫ t : ℝ, μ t •
      (NormedSpace.exp ((((t : ℂ) * Complex.I) • finiteDiagonalOperator P a)) ∘L
        (finiteDiagonalOperator P a ∘L X - X ∘L finiteDiagonalOperator Q b) ∘L
        NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • finiteDiagonalOperator Q b)) := by
  have horbit := finiteDiagonal_orbit_expansion P Q a b
    hPid hPorth hPsum hQid hQorth hQsum X
  have hintegrable : ∀ i j, Integrable fun t : ℝ =>
      μ t •
        (Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
          ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j))) := by
    intro i j
    simpa [smul_smul, mul_assoc] using
      integrable_scalar_oscillatory_block μ hμ (a i - b j)
        ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j))
  calc
    X = ∑ i, ∑ j, P i ∘L X ∘L Q j :=
      eq_sum_rectangular_blocks P Q hPsum hQsum X
    _ = ∑ i, ∑ j,
        ∫ t : ℝ, μ t •
          (Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
            ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hrw : (fun t : ℝ => μ t •
            (Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
              ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j)))) =
          fun t : ℝ =>
            (μ t * Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I))) •
              ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j)) := by
        funext t
        rw [smul_smul]
      rw [hrw, integral_smul_const, hscalar i j, smul_smul]
      have hc : (((a i - b j)⁻¹ : ℝ) : ℂ) *
          (((a i - b j : ℝ) : ℂ)) = 1 := by
        norm_cast
        exact inv_mul_cancel₀ (hne i j)
      rw [hc, one_smul]
    _ = ∫ t : ℝ, ∑ i, ∑ j,
        μ t •
          (Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
            ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j))) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        exact fun j hj => hintegrable i j
      · intro i hi
        exact (integrable_finsetSum _ fun j hj => hintegrable i j)
    _ = ∫ t : ℝ, μ t •
      (NormedSpace.exp ((((t : ℂ) * Complex.I) • finiteDiagonalOperator P a)) ∘L
        (finiteDiagonalOperator P a ∘L X - X ∘L finiteDiagonalOperator Q b) ∘L
        NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • finiteDiagonalOperator Q b)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [horbit t, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.smul_sum]

end
end DavisKahan.Sylvester
end TauCeti
