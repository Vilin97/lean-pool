/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Defs

/-!
# The kernel as an inner product

The identity that turns the kernel into a Gram matrix on `L²((-lam, lam))`, and its two immediate
consequences.

Every integral here is taken over `Set.Ioo (-lam) lam` rather than over `ℝ`, so that it is
literally the inner product of the ambient Hilbert space; `fourierC` integrates over the line, and
the two agree because an admissible test function vanishes off the interval.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

/-- An admissible test function vanishes off `Ioo (-lam) lam`. -/
private lemma eta_eq_zero_of_notMem (h : IsAdmissible lam eta) {u : ℝ}
    (hu : u ∉ Set.Ioo (-lam) lam) : eta u = 0 := by
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hu
  rcases hu with h1 | h2
  · exact h.support u (le_trans (by linarith) (neg_le_abs u))
  · exact h.support u (le_trans h2 (le_abs_self u))

/-- The twisted function vanishes off `Ioo (-lam) lam`. -/
private lemma fz_eq_zero_of_notMem (h : IsAdmissible lam eta) {z : ℂ} {u : ℝ}
    (hu : u ∉ Set.Ioo (-lam) lam) : fz eta z u = 0 := by
  simp [fz, eta_eq_zero_of_notMem h hu]

/-- **The kernel is a Gram matrix.** `K_eta (z - conj s)` is the inner product of the twisted
functions attached to `z` and `s`. -/
@[zz_tag "lem_kernel_factorization"]
theorem testKernel_sub_conj (h : IsAdmissible lam eta) (z s : ℂ) :
    testKernel eta (z - (starRingEnd ℂ) s)
      = ∫ u in Set.Ioo (-lam) lam, fz eta z u * (starRingEnd ℂ) (fz eta s u) := by
  have hpt : ∀ u : ℝ,
      ((eta u : ℂ) ^ 2) *
          Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (z - (starRingEnd ℂ) s) * (u : ℂ))
        = fz eta z u * (starRingEnd ℂ) (fz eta s u) := by
    intro u
    simp only [fz, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_mul,
      Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    have hexp : -(2 * (Real.pi : ℂ)) * Complex.I * (u : ℂ) * z
          + -(2 * (Real.pi : ℂ)) * -Complex.I * (u : ℂ) * (starRingEnd ℂ) s
        = -(2 * (Real.pi : ℂ)) * Complex.I * (z - (starRingEnd ℂ) s) * (u : ℂ) := by
      ring
    rw [mul_mul_mul_comm, ← Complex.exp_add, hexp, sq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
        simp [fz_eq_zero_of_notMem h hu]]
  simp only [testKernel, fourierC, Pi.pow_apply, Complex.ofReal_pow]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- At a real point the twisted function has unit `L²` norm. -/
@[zz_tag "lem_f_real_norm"]
theorem integral_norm_fz_sq (h : IsAdmissible lam eta) {x : ℂ} (hx : x.im = 0) :
    ∫ u in Set.Ioo (-lam) lam, ‖fz eta x u‖ ^ 2 = 1 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, x = (r : ℂ) := ⟨x.re, by apply Complex.ext <;> simp [hx]⟩
  have hnorm : ∀ u : ℝ, ‖fz eta x u‖ ^ 2 = eta u ^ 2 := by
    intro u
    have hexp : -(2 * (Real.pi : ℂ)) * Complex.I * (u : ℂ) * x
        = ((-(2 * Real.pi) * u * r : ℝ) : ℂ) * Complex.I := by
      rw [hr]; push_cast; ring
    rw [fz, norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, mul_one]
    simp [sq_abs]
  simp only [hnorm]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
        simp [eta_eq_zero_of_notMem h hu]]
  have hk := h.fourier_sq_zero
  simp only [fourierC, Pi.pow_apply, mul_zero, zero_mul, Complex.exp_zero, mul_one] at hk
  have hcast : ((∫ u : ℝ, eta u ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    exact hk
  exact_mod_cast hcast

/-- Conjugating the second argument of the kernel does not change the second moment: conjugation
permutes the support and preserves multiplicity. -/
@[zz_tag "lem_sum_shift_conj"]
theorem sum_testKernel_sq_eq_sum_conj {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsConjInvariant Z m) :
    ∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2
      = ∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - (starRingEnd ℂ) s) ^ 2 := by
  refine Finset.sum_congr rfl fun z _ => ?_
  refine (Finset.sum_nbij' (fun s => (starRingEnd ℂ) s) (fun s => (starRingEnd ℂ) s)
    (fun s hs => h.conj_mem s hs) (fun s hs => h.conj_mem s hs)
    (fun s _ => Complex.conj_conj s) (fun s _ => Complex.conj_conj s) ?_).symm
  intro s hs
  rw [h.mult_conj s hs]

end ZetaZeros
