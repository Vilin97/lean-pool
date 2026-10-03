/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.FiniteStepCalculus


/-!
# Exponentials of finite orthogonal projection decompositions

The proof is algebraic.  Powers of an orthogonal idempotent decomposition act
coefficientwise, and the exponential power series may then be interchanged with
the finite sum.

**Promoted 2026-07-30 under lane `EXP-PROMOTE-MISC`**, from
`DavisKahan/Experimental/InfiniteDimensional/Sylvester/`.  It became promotable *because*
`Sylvester/FiniteStepCalculus.lean` was promoted an hour earlier under `EXP-PROMOTE-SYL`:
that was its only Experimental import, so clearing one module cleared this one.  Nothing is
restated; names and namespace (`TauCeti.DavisKahanExt`) are unchanged.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.Sylvester

open TauCeti.DavisKahanExt

open DavisKahan

open scoped InnerProductSpace BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- Powers of a scalar multiple of an idempotent. -/
theorem smul_idempotent_pow
    (P : H →L[ℂ] H) (hP : P * P = P) (c : ℂ) :
    ∀ n : ℕ, n ≠ 0 → (c • P) ^ n = c ^ n • P := by
  intro n hn
  induction n with
  | zero => exact False.elim (hn rfl)
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp
      · rw [pow_succ, ih hn0, smul_mul_smul, hP]
        simp [pow_succ]

/-- Exponential of one scalar multiple of an idempotent. -/
theorem exp_smul_idempotent
    (P : H →L[ℂ] H) (hP : P * P = P) (c : ℂ) :
    NormedSpace.exp (c • P) =
      (1 : H →L[ℂ] H) + (Complex.exp c - 1) • P := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  simp only [← one_div]
  have hseries : Summable fun n : ℕ =>
      (1 / n.factorial : ℂ) • (c • P) ^ n := by
    simpa only [← one_div] using NormedSpace.expSeries_summable' (𝕂 := ℂ) (c • P)
  rw [hseries.tsum_eq_zero_add]
  have hzero : (1 / Nat.factorial 0 : ℂ) • (c • P) ^ 0 = 1 := by simp
  rw [hzero]
  congr 1
  calc
    ∑' n : ℕ, (1 / (n + 1).factorial : ℂ) • (c • P) ^ (n + 1)
        = ∑' n : ℕ,
            ((1 / (n + 1).factorial : ℂ) * c ^ (n + 1)) • P := by
          apply tsum_congr
          intro n
          rw [smul_idempotent_pow P hP c (n + 1) (Nat.succ_ne_zero n), smul_smul]
    _ = (∑' n : ℕ, (1 / (n + 1).factorial : ℂ) * c ^ (n + 1)) • P := by
          have hf : Summable fun n : ℕ => (1 / (n + 1).factorial : ℂ) * c ^ (n + 1) :=
            ((NormedSpace.expSeries_div_summable c).comp_injective Nat.succ_injective).congr
              (fun n => by
                simp only [Function.comp_apply, Nat.succ_eq_add_one]; rw [div_eq_mul_inv,
                  one_div, mul_comm])
          rw [hf.tsum_smul_const]
    _ = (Complex.exp c - 1) • P := by
          congr 1
          have hexp : Complex.exp c = ∑' n : ℕ, c ^ n / n.factorial := by
            rw [Complex.exp_eq_exp_ℂ]
            exact congr_fun NormedSpace.exp_eq_tsum_div c
          rw [hexp]
          have hcexp : Summable fun n : ℕ => c ^ n / n.factorial :=
            NormedSpace.expSeries_div_summable c
          rw [hcexp.tsum_eq_zero_add]
          simp [div_eq_mul_inv, mul_comm]

omit [CompleteSpace H] in
/-- Powers of a finite sum of pairwise orthogonal idempotents are taken
coefficientwise. -/
theorem finset_orthogonal_idempotents_pow
    {n : ℕ} (P : Fin n → H →L[ℂ] H) (c : Fin n → ℂ)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    ∀ m : ℕ, m ≠ 0 →
      (∑ i, c i • P i) ^ m = ∑ i, c i ^ m • P i := by
  intro m hm
  induction m with
  | zero => exact False.elim (hm rfl)
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp
      · rw [pow_succ, ih hm0, Finset.sum_mul]
        simp only [Finset.mul_sum]
        calc
          ∑ i, ∑ j, (c i ^ m • P i) * (c j • P j)
              = ∑ i, c i ^ m • P i * (c i • P i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
                · intro j _ hji
                  rw [smul_mul_smul, horth i j hji.symm, smul_zero]
          _ = ∑ i, c i ^ (m + 1) • P i := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [smul_mul_smul, hidem i]
                simp [pow_succ]

/-- Exponential of a finite pairwise orthogonal idempotent decomposition. -/
theorem exp_finset_orthogonal_idempotents
    {n : ℕ} (P : Fin n → H →L[ℂ] H) (c : Fin n → ℂ)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hsum : ∑ i, P i = (1 : H →L[ℂ] H)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • ∑ i, c i • P i) =
      ∑ i, Complex.exp ((t : ℂ) * c i) • P i := by
  have hscale : (t : ℂ) • ∑ i, c i • P i =
      ∑ i, ((t : ℂ) * c i) • P i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul]
  rw [hscale, NormedSpace.exp_eq_tsum ℂ]
  simp only [← one_div]
  have hsumexp : ∀ m : ℕ, m ≠ 0 →
      (∑ i, ((t : ℂ) * c i) • P i) ^ m =
        ∑ i, (((t : ℂ) * c i) ^ m) • P i :=
    finset_orthogonal_idempotents_pow P (fun i => (t : ℂ) * c i) hidem horth
  have hseries : Summable fun m : ℕ =>
      (1 / m.factorial : ℂ) •
        (∑ i, ((t : ℂ) * c i) • P i) ^ m := by
    simpa only [← one_div] using
      NormedSpace.expSeries_summable' (𝕂 := ℂ) (∑ i, ((t : ℂ) * c i) • P i)
  rw [hseries.tsum_eq_zero_add]
  have hzero : (1 / Nat.factorial 0 : ℂ) •
      (∑ i, ((t : ℂ) * c i) • P i) ^ 0 =
      ∑ i, P i := by
    simp [hsum]
  rw [hzero, hsum]
  calc
    (1 : H →L[ℂ] H) +
        ∑' m : ℕ, (1 / (m + 1).factorial : ℂ) •
          (∑ i, ((t : ℂ) * c i) • P i) ^ (m + 1)
        = (∑ i, P i) +
          ∑' m : ℕ, ∑ i,
            ((1 / (m + 1).factorial : ℂ) *
              (((t : ℂ) * c i) ^ (m + 1))) • P i := by
            rw [hsum]
            congr 1
            apply tsum_congr
            intro m
            rw [hsumexp (m + 1) (Nat.succ_ne_zero m), Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [smul_smul]
    _ = ∑ i, (P i + ∑' m : ℕ,
          ((1 / (m + 1).factorial : ℂ) *
            (((t : ℂ) * c i) ^ (m + 1))) • P i) := by
          rw [Finset.sum_add_distrib]
          congr 1
          have hsum_i : ∀ i : Fin n, Summable
              (fun m : ℕ => ((1 / (m + 1).factorial : ℂ) *
                (((t : ℂ) * c i) ^ (m + 1))) • P i) := by
            intro i
            refine Summable.smul_const ?_ (P i)
            exact ((NormedSpace.expSeries_div_summable ((t : ℂ) * c i)).comp_injective
              Nat.succ_injective).congr (fun m => by
                simp only [Function.comp_apply, Nat.succ_eq_add_one]; rw [div_eq_mul_inv,
                  one_div, mul_comm])
          rw [Summable.tsum_finsetSum (fun i _ => hsum_i i)]
    _ = ∑ i, Complex.exp ((t : ℂ) * c i) • P i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hf : Summable fun m : ℕ =>
              (1 / (m + 1).factorial : ℂ) * (((t : ℂ) * c i) ^ (m + 1)) :=
            ((NormedSpace.expSeries_div_summable ((t : ℂ) * c i)).comp_injective
              Nat.succ_injective).congr (fun m => by
                simp only [Function.comp_apply, Nat.succ_eq_add_one]; rw [div_eq_mul_inv,
                  one_div, mul_comm])
          have hscalar : (1 : ℂ) +
              ∑' m : ℕ, (1 / (m + 1).factorial : ℂ) * (((t : ℂ) * c i) ^ (m + 1)) =
              Complex.exp ((t : ℂ) * c i) := by
            have hexp : Complex.exp ((t : ℂ) * c i) =
                ∑' m : ℕ, ((t : ℂ) * c i) ^ m / m.factorial := by
              rw [Complex.exp_eq_exp_ℂ]
              exact congr_fun NormedSpace.exp_eq_tsum_div ((t : ℂ) * c i)
            rw [hexp]
            have hcexp : Summable fun m : ℕ =>
                (((t : ℂ) * c i) ^ m) / m.factorial :=
              NormedSpace.expSeries_div_summable ((t : ℂ) * c i)
            rw [hcexp.tsum_eq_zero_add]
            simp [div_eq_mul_inv, mul_comm]
          rw [hf.tsum_smul_const, ← hscalar, add_smul, one_smul]

end
end DavisKahan.Sylvester
end TauCeti
