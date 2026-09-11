/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Actual ordered parameter derivatives and their factorial word sums

The parameter estimates are stated for the genuine iterated Fréchet
derivative. Evaluation on an ordered family of directions gives the mixed
word derivative. Summing all words changes the radius by one fixed alphabet
factor, independent of the derivative order and factorial shift.
-/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open Finset EulerGevrey

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- The actual mixed differential evaluated on an ordered word of directions. -/
def wordDerivative (directions : ι → P) (f : P → E) {n : ℕ} (w : Fin n → ι) (x : P) : E :=
  iteratedFDeriv ℝ n f x (fun j => directions (w j))

/-- The sum of the actual norms over all ordered words. -/
def wordSum (directions : ι → P) (f : P → E) (n : ℕ) (x : P) : ℝ :=
  ∑ w : Fin n → ι, ‖wordDerivative directions f w x‖

omit [Fintype ι] in
/-- Unit directions do not enlarge the norm of the actual differential. -/
theorem wordDerivative_norm (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1)
    (f : P → E) {n : ℕ} (w : Fin n → ι) (x : P) :
    ‖wordDerivative directions f w x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  have hp : (∏ j : Fin n, ‖directions (w j)‖) ≤ 1 :=
    prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hd (w j))
  exact ((iteratedFDeriv ℝ n f x).le_opNorm (fun j => directions (w j))).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg _))

/-- Summing the actual word norms costs precisely the number of words. -/
theorem wordSum_le (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1)
    (f : P → E) (n : ℕ) (x : P) :
    wordSum directions f n x ≤ (Fintype.card ι : ℝ)^n * ‖iteratedFDeriv ℝ n f x‖ := by
  have h := sum_le_sum (fun (w : Fin n → ι) (_ : w ∈ univ) => wordDerivative_norm directions hd f w
      x)
  simpa only [wordSum, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow] using h

/-- The actual word sum has a factorial bound with one dimension-dependent radius enlargement. -/
theorem wordSum_gevrey (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1)
    (f : P → E) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * majorant R d n)
    (n : ℕ) (x : P) :
    wordSum directions f n x ≤
      C * majorant (max 1 (Fintype.card ι : ℝ) * R) d n := by
  let m : ℝ := max 1 (Fintype.card ι : ℝ)
  have hm : 1 ≤ m := le_max_left _ _
  have hcard : (Fintype.card ι : ℝ) ≤ m := le_max_right _ _
  have hpow : (Fintype.card ι : ℝ)^n ≤ m^(n+d) :=
    (pow_le_pow_left₀ (by positivity) hcard n).trans
      (pow_le_pow_right₀ hm (Nat.le_add_right n d))
  have hM : 0 ≤ majorant R d n := majorant_nonneg R hR d n
  calc
    wordSum directions f n x ≤ (Fintype.card ι : ℝ)^n * ‖iteratedFDeriv ℝ n f x‖ :=
      wordSum_le directions hd f n x
    _ ≤ (Fintype.card ι : ℝ)^n * (C*majorant R d n) :=
      mul_le_mul_of_nonneg_left (hb n x) (by positivity)
    _ ≤ m^(n+d) * (C*majorant R d n) :=
      mul_le_mul_of_nonneg_right hpow (mul_nonneg hC hM)
    _ = C*majorant (m*R) d n := by simp only [majorant, mul_pow]; ring

end EulerParameterWordGevrey
