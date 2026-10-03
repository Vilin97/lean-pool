/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Dist.Basic

/-! The multiplication theorem for `Lbp` (the proof notes, §1 (i)):
`∑_{b<p} Lbp (Q(p X - b)) = p · Lbp Q`, proved by shift invariance and the binomial basis
(a shift-invariant linear functional on `ℚ[X]` vanishes). Consequence for `locPoly`:
`∑_{b<p} locPoly (r p) (Q(p X - b)) = p² · locPoly r Q`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

noncomputable section

lemma Lbp_C_mul (c : ℚ) (Q : ℚ[X]) : Lbp (C c * Q) = c * Lbp Q := by
  rw [Lbp_eq, Lbp_eq, Lb_C_mul, coeff_C_mul]; ring

/-- Shift rule for `Lbp`: `Lbp (Q(X+1)) - Lbp Q = Q'(1)`. -/
lemma Lbp_shift (Q : ℚ[X]) : Lbp (Q.comp (X + 1)) - Lbp Q = (derivative Q).eval 1 := by
  rw [Lbp_eq, Lbp_eq]
  have h := Lb_shift Q
  have h1 : (Q.comp (X + 1)).coeff 1 = (derivative Q).eval 1 := by
    have : (derivative (Q.comp (X + 1))).coeff 0 = (Q.comp (X + 1)).coeff 1 := by
      rw [coeff_derivative]; simp
    rw [← this, coeff_zero_eq_eval_zero, derivative_comp]
    simp [eval_comp]
  have h0 : Q.coeff 1 = (derivative Q).eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]; simp
  linarith

/-- `Ψ_p(Q) = ∑_{b<p} Lbp (Q(p X - b))`. -/
def Psi (p : ℕ) (Q : ℚ[X]) : ℚ := ∑ b ∈ Finset.range p, Lbp (Q.comp (C (p : ℚ) * X - C (b : ℚ)))

lemma Psi_add (p : ℕ) (P Q : ℚ[X]) : Psi p (P + Q) = Psi p P + Psi p Q := by
  unfold Psi
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [add_comp, Lbp_add]

lemma Psi_C_mul (p : ℕ) (c : ℚ) (Q : ℚ[X]) : Psi p (C c * Q) = c * Psi p Q := by
  unfold Psi
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [mul_comp, C_comp, Lbp_C_mul]

lemma Psi_shift {p : ℕ} (hp : 0 < p) (Q : ℚ[X]) :
    Psi p (Q.comp (X + 1)) - Psi p Q = (p : ℚ) * (derivative Q).eval 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  unfold Psi
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have h1 : ∀ b ∈ Finset.range k,
      Lbp ((Q.comp (X + 1)).comp (C ((k + 1 : ℕ) : ℚ) * X - C ((b + 1 : ℕ) : ℚ))) =
        Lbp (Q.comp (C ((k + 1 : ℕ) : ℚ) * X - C (b : ℚ))) := by
    intro b _
    rw [comp_assoc]
    congr 2
    simp only [add_comp, X_comp, one_comp]
    push_cast
    simp only [C_add, C_1]; ring
  rw [Finset.sum_congr rfl h1]
  set R := Q.comp (C ((k + 1 : ℕ) : ℚ) * X - C (k : ℚ)) with hR
  have h2 : (Q.comp (X + 1)).comp (C ((k + 1 : ℕ) : ℚ) * X - C ((0 : ℕ) : ℚ)) = R.comp (X + 1) := by
    rw [comp_assoc, hR, comp_assoc]
    congr 1
    simp only [add_comp, X_comp, one_comp, sub_comp, mul_comp, C_comp]
    push_cast
    simp only [C_add, C_1, C_0]; ring
  rw [h2]
  have h3 := Lbp_shift R
  have h4 : (derivative R).eval 1 = ((k + 1 : ℕ) : ℚ) * (derivative Q).eval 1 := by
    rw [hR, derivative_comp]
    simp [eval_comp]
  linarith

/-- A shift-invariant linear functional on `ℚ[X]` vanishes. -/
lemma shift_invariant_eq_zero (Φ : ℚ[X] → ℚ) (hadd : ∀ P Q, Φ (P + Q) = Φ P + Φ Q)
    (hsmul : ∀ (c : ℚ) Q, Φ (C c * Q) = c * Φ Q) (hshift : ∀ Q, Φ (Q.comp (X + 1)) = Φ Q)
    (Q : ℚ[X]) : Φ Q = 0 := by
  have hbin : ∀ k, Φ (bin k) = 0 := by
    intro k
    have := hshift (bin (k + 1))
    rw [bin_comp_add_one, hadd] at this
    linarith
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → ℚ[X]), Φ (∑ i ∈ s, f i) = ∑ i ∈ s, Φ (f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      have := hsmul 0 0
      simp only [C_0, zero_mul] at this
      simpa using this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  rw [newton Q le_rfl, hsum]
  exact Finset.sum_eq_zero fun k _ => by rw [hsmul, hbin, mul_zero]

/-- **Multiplication theorem**: `∑_{b<p} Lbp (Q(p X - b)) = p · Lbp Q`. -/
theorem Psi_eq {p : ℕ} (hp : 0 < p) (Q : ℚ[X]) : Psi p Q = (p : ℚ) * Lbp Q := by
  have := shift_invariant_eq_zero (fun Q => Psi p Q - (p : ℚ) * Lbp Q)
    (fun P Q => by simp only [Psi_add, Lbp_add]; ring)
    (fun c Q => by simp only [Psi_C_mul, Lbp_C_mul]; ring)
    (fun Q => by
      have h1 := Psi_shift hp Q
      have h2 := Lbp_shift Q
      linear_combination h1 - (p : ℚ) * h2) Q
  linarith

/-- `∑_{b<p} locPoly (r p) (Q(p X - b)) = p² · locPoly r Q`. -/
theorem sum_locPoly_comp {p : ℕ} (hp : 0 < p) (r : ℚ) (Q : ℚ[X]) :
    ∑ b ∈ Finset.range p, locPoly (r * p) (Q.comp (C (p : ℚ) * X - C (b : ℚ))) =
      (p : ℚ) ^ 2 * locPoly r Q := by
  have h : ∀ b ∈ Finset.range p, locPoly (r * p) (Q.comp (C (p : ℚ) * X - C (b : ℚ))) =
      (p : ℚ) * Lbp ((derivative Q).comp (C (p : ℚ) * X - C (b : ℚ))) +
        2 * (r * p) * Lbp (Q.comp (C (p : ℚ) * X - C (b : ℚ))) := by
    intro b _
    rw [locPoly_eq, derivative_comp]
    simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, derivative_X, mul_one,
      zero_add, sub_zero]
    rw [Lbp_C_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change (p : ℚ) * Psi p (derivative Q) + 2 * (r * p) * Psi p Q = _
  rw [Psi_eq hp, Psi_eq hp, locPoly_eq]
  ring

end

end Zeta32.PrimeEdge

end
