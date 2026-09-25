/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.SuperPowerSums

/-!
# Rationality from recurrence

If the complete homogeneous sequence `newtonH t` satisfies a linear
recurrence with constant coefficients from some index onward, then `t`
decomposes as a difference of power sums of two disjoint multisets of
nonzero complex numbers (Lemma A.9 of the accompanying paper).

The proof passes through the generating series `H = newtonHSeries t`,
builds a polynomial `Q` from the recurrence whose product with `H`
truncates to a polynomial `P`, divides by the GCD to get a coprime
pair, factors both over ℂ, and reads off the power-sum identity
from the logarithmic derivative of `H = P₀/Q₀`.
-/

namespace RS

-- Only scoped notation is opened globally (`ℂ[X]` and `ℂ⟦X⟧`);
-- full `open PowerSeries` would break `ℂ[X]` notation via a GetElem
-- conflict, and `open Polynomial in private theorem` does not parse.
open scoped Polynomial PowerSeries

/-- Shorthand for the linear factor `(1 - C γ * X)` as a polynomial. -/
private noncomputable abbrev oneSub (γ : ℂ) : ℂ[X] :=
  (1 : ℂ[X]) - Polynomial.C γ * Polynomial.X

/-! ### Tail-sum series -/

/-- The tail-sum power series attached to a multiset of complex numbers:
coefficient `m` is `(M.map (· ^ m)).sum` for `m ≥ 1`, and `0` for `m = 0`. -/
noncomputable def tailSumSeries (M : Multiset ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun m => if m = 0 then 0 else (M.map (· ^ m)).sum

@[simp]
private theorem tailSumSeries_zero : tailSumSeries (0 : Multiset ℂ) = 0 := by
  ext m; simp [tailSumSeries, PowerSeries.coeff_mk]

private theorem tailSumSeries_cons (γ : ℂ) (M : Multiset ℂ) :
    tailSumSeries (γ ::ₘ M) =
      tailSumSeries M +
        PowerSeries.mk (fun m => if m = 0 then 0 else γ ^ m) := by
  ext m
  simp only [tailSumSeries, map_add, PowerSeries.coeff_mk]
  split
  · simp
  · simp [Multiset.map_cons, Multiset.sum_cons, add_comm]

/-! ### Geometric tail identity -/

/-- The geometric tail identity:
`↑(oneSub γ) * mk(γ^m for m ≥ 1) = ↑(C γ * X)` in `ℂ⟦X⟧`. -/
private theorem one_sub_mul_geometric_tail (γ : ℂ) :
    (↑(oneSub γ) : ℂ⟦X⟧) *
      PowerSeries.mk (fun m => if m = 0 then 0 else γ ^ m) =
      ↑(Polynomial.C γ * Polynomial.X : ℂ[X]) := by
  have hcoe : (↑(oneSub γ) : ℂ⟦X⟧) = 1 - PowerSeries.C γ * PowerSeries.X := by
    simp [oneSub, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X]
  have hdecomp : PowerSeries.mk (fun m => if m = 0 then 0 else γ ^ m) =
      PowerSeries.mk (fun m => γ ^ m) - 1 := by
    ext m; simp only [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    cases m with
    | zero => simp
    | succ n => simp
  have hRHS : (↑(Polynomial.C γ * Polynomial.X : ℂ[X]) : ℂ⟦X⟧) =
      PowerSeries.C γ * PowerSeries.X := by
    simp [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
  rw [hcoe, hdecomp, hRHS]
  suffices h : (1 - PowerSeries.C γ * PowerSeries.X) *
      PowerSeries.mk (fun m => γ ^ m) = 1 by
    have : (1 - PowerSeries.C γ * PowerSeries.X) *
        (PowerSeries.mk (fun m => γ ^ m) - 1) =
        (1 - PowerSeries.C γ * PowerSeries.X) *
          PowerSeries.mk (fun m => γ ^ m) -
        (1 - PowerSeries.C γ * PowerSeries.X) := by ring
    rw [this, h]; ring
  rw [sub_mul, one_mul]
  ext n
  simp only [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  cases n with
  | zero =>
    simp [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul]
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, pow_succ]
    ring

/-! ### Log-derivative identity for products -/

/-- For `F_M := (M.map oneSub).prod`,
`↑X * ↑(derivative F_M) = -↑F_M * tailSumSeries M` in `ℂ⟦X⟧`. -/
private theorem X_mul_coe_derivative_prod (M : Multiset ℂ) :
    (↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) *
      (↑(Polynomial.derivative ((M.map oneSub).prod)) : ℂ⟦X⟧) =
      -(↑((M.map oneSub).prod) : ℂ⟦X⟧) * tailSumSeries M := by
  induction M using Multiset.induction with
  | empty =>
    have h0 : tailSumSeries (0 : Multiset ℂ) = 0 := tailSumSeries_zero
    simp [Multiset.map_zero, Multiset.prod_zero, Polynomial.derivative_one,
      Polynomial.coe_zero, h0]
  | cons γ M' ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [Polynomial.derivative_mul]
    have hder : Polynomial.derivative (oneSub γ) = -Polynomial.C γ := by
      simp [oneSub, Polynomial.derivative_sub, Polynomial.derivative_one,
            Polynomial.derivative_X]
    rw [hder]
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_neg]
    rw [mul_add]
    have hrearr : (↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) * ((↑(oneSub γ) : ℂ⟦X⟧) *
        (↑(Polynomial.derivative ((Multiset.map oneSub M').prod)) : ℂ⟦X⟧)) =
        (↑(oneSub γ) : ℂ⟦X⟧) * ((↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) *
        (↑(Polynomial.derivative ((Multiset.map oneSub M').prod)) :
          ℂ⟦X⟧)) := by ring
    rw [hrearr, ih, tailSumSeries_cons]
    have h_geom := one_sub_mul_geometric_tail γ
    rw [Polynomial.coe_mul] at h_geom
    linear_combination (↑(Multiset.map oneSub M').prod : ℂ⟦X⟧) * h_geom

/-! ### Factorisation into `(1 - γX)` factors -/

section Factorisation
open Polynomial

/-- Over ℂ, a nonzero polynomial `F` with `F.coeff 0 ≠ 0` factors as
`F = C (F.coeff 0) * (M.map oneSub).prod` where
`M = F.roots.map (· ⁻¹)`, with `M.card = F.natDegree` and every
element of `M` nonzero. -/
private theorem eq_prod_one_sub_of_coeff_zero_ne_zero (F : ℂ[X]) (_hF : F ≠ 0)
    (hF0 : F.coeff 0 ≠ 0) :
    F = Polynomial.C (F.coeff 0) *
      ((F.roots.map (· ⁻¹)).map oneSub).prod ∧
    (F.roots.map (· ⁻¹)).card = F.natDegree ∧
    ∀ x ∈ F.roots.map (· ⁻¹), x ≠ (0 : ℂ) := by
  have hno_zero : ∀ r ∈ F.roots, r ≠ (0 : ℂ) := by
    intro r hr heq
    subst heq
    exact hF0 ((coeff_zero_eq_eval_zero F).trans (isRoot_of_mem_roots hr))
  have hsplit := (IsAlgClosed.splits F).eq_prod_roots
  have factor_eq : ∀ r ∈ F.roots,
      (Polynomial.X : ℂ[X]) - Polynomial.C r =
        -Polynomial.C r * oneSub (r⁻¹) := by
    intro r hr
    have hr0 := hno_zero r hr
    have key : (Polynomial.C r : ℂ[X]) * (Polynomial.C r⁻¹ * Polynomial.X) =
        Polynomial.X := by
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hr0, map_one,
        one_mul]
    unfold oneSub
    linear_combination -key
  have prod_transform :
      (F.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod =
      (F.roots.map (fun r => -(Polynomial.C r : ℂ[X]))).prod *
        ((F.roots.map (· ⁻¹)).map oneSub).prod := by
    conv_lhs =>
      rw [show F.roots.map (fun r => Polynomial.X - Polynomial.C r) =
          F.roots.map (fun r => -(Polynomial.C r : ℂ[X]) * oneSub (r⁻¹)) from
        Multiset.map_congr rfl factor_eq]
    rw [Multiset.prod_map_mul]
    congr 1
    simp only [Multiset.map_map, Function.comp_def]
  have coeff_prod :
      Polynomial.C F.leadingCoeff *
        (F.roots.map (fun r => -(Polynomial.C r : ℂ[X]))).prod =
        Polynomial.C (F.coeff 0) := by
    have h1 : (F.roots.map (fun r => -(Polynomial.C r : ℂ[X]))).prod =
        Polynomial.C ((F.roots.map (- ·)).prod) := by
      conv_lhs =>
        rw [show F.roots.map (fun r => -(Polynomial.C r : ℂ[X])) =
            (F.roots.map (- ·)).map (Polynomial.C : ℂ →+* ℂ[X]) from by
          simp only [Multiset.map_map, Function.comp_def, Polynomial.C_neg]]
      exact (map_multiset_prod (Polynomial.C : ℂ →+* ℂ[X]) _).symm
    rw [h1, ← Polynomial.C_mul]
    apply congr_arg
    rw [coeff_zero_eq_eval_zero, (IsAlgClosed.splits F).eval_eq_prod_roots 0]
    congr 1; congr 1
    exact Multiset.map_congr rfl fun (r : ℂ) _ => (zero_sub r).symm
  refine ⟨?_, ?_, ?_⟩
  · calc F
        = Polynomial.C F.leadingCoeff *
            (F.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod :=
          hsplit
      _ = Polynomial.C F.leadingCoeff *
            ((F.roots.map (fun r => -(Polynomial.C r : ℂ[X]))).prod *
             ((F.roots.map (· ⁻¹)).map oneSub).prod) := by
          rw [prod_transform]
      _ = (Polynomial.C F.leadingCoeff *
            (F.roots.map (fun r => -(Polynomial.C r : ℂ[X]))).prod) *
            ((F.roots.map (· ⁻¹)).map oneSub).prod := by
          rw [mul_assoc]
      _ = Polynomial.C (F.coeff 0) *
            ((F.roots.map (· ⁻¹)).map oneSub).prod := by
          rw [coeff_prod]
  · rw [Multiset.card_map]; exact IsAlgClosed.card_roots_eq_natDegree
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    exact inv_ne_zero (hno_zero r hr)

end Factorisation

/-! ### Coprime pair from recurrence

The construction is split across two lemmas to keep proof terms small
enough for the kernel's `whnf` check.
-/

/-- Build the recurrence polynomial `Q` and its truncated product `P`
with the Newton generating series. -/
theorem truncated_product_from_recurrence {t : ℕ → ℂ} {a b : ℕ}
    (c : Fin (a + 1) → ℂ) (hc : c ≠ 0)
    (hrec : ∀ ρ : ℤ, (b : ℤ) - a ≤ ρ →
      ∑ k : Fin (a + 1), c k * newtonHZ t (ρ + 1 + (k : ℤ)) = 0) :
    ∃ Q P : ℂ[X],
      Q ≠ 0 ∧ P ≠ 0 ∧
      (↑Q : ℂ⟦X⟧) * newtonHSeries t = ↑P ∧
      Q.natDegree ≤ a ∧ P.natDegree ≤ b := by
  classical
  let Q : ℂ[X] := ∑ i ∈ Finset.range (a + 1),
    Polynomial.C (c ⟨a - i, by omega⟩) * Polynomial.X ^ i
  have hQ_def : Q = ∑ i ∈ Finset.range (a + 1),
    Polynomial.C (c ⟨a - i, by omega⟩) * Polynomial.X ^ i := rfl
  have hQ_ne : Q ≠ 0 := by
    intro hQ; apply hc; ext ⟨k, hk⟩
    have h : Q.coeff (a - k) = 0 := by rw [hQ]; simp
    simp only [hQ_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow] at h
    rw [Finset.sum_eq_single_of_mem (a - k)
      (Finset.mem_range.mpr (by omega))] at h
    · simpa [show a - (a - k) = k from by omega] using h
    · intro j _ hji
      have hne : ¬(a - k = j) := fun h => hji h.symm
      simp [hne]
  let H := newtonHSeries t
  have hH_def : H = newtonHSeries t := rfl
  have hQH_ev : ∀ n, b + 1 ≤ n → PowerSeries.coeff n ((↑Q : ℂ⟦X⟧) * H) = 0 := by
    intro n hn
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Polynomial.coeff_coe, hH_def, newtonHSeries,
      PowerSeries.coeff_mk]
    have hQ_van : ∀ k, ¬(k < a + 1) → Q.coeff k = 0 := by
      intro k hk
      simp only [hQ_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow]
      apply Finset.sum_eq_zero
      intro j hj; rw [Finset.mem_range] at hj
      simp [show k ≠ j by omega]
    have hQ_val : ∀ k, k < a + 1 → Q.coeff k = c ⟨a - k, by omega⟩ := by
      intro k hk
      simp only [hQ_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk)]
      · simp
      · intro j _ hji; simp [Ne.symm hji]
    have hnat (k : ℕ) (hk : k < n + 1) :
        newtonH t (n - k) = newtonHZ t ((n : ℤ) - k) := by
      rw [show (n : ℤ) - k = ((n - k : ℕ) : ℤ) by omega,
        newtonHZ_natCast]
    have hstep1 :
        ∑ k ∈ Finset.range (n + 1), Q.coeff k * newtonH t (n - k) =
        ∑ k ∈ Finset.range (a + 1),
          c ⟨a - k, by omega⟩ * newtonHZ t ((n : ℤ) - k) := by
      calc
        _ = ∑ k ∈ Finset.range (n + 1),
            Q.coeff k * newtonHZ t ((n : ℤ) - k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hnat k (Finset.mem_range.mp hk)]
        _ = ∑ k ∈ Finset.range (a + 1),
            Q.coeff k * newtonHZ t ((n : ℤ) - k) := by
          by_cases han : a ≤ n
          · symm
            apply Finset.sum_subset (Finset.range_mono (by omega))
            intro k _ hk
            rw [hQ_van k (by simpa only [Finset.mem_range] using hk),
              zero_mul]
          · apply Finset.sum_subset (Finset.range_mono (by omega))
            intro k _ hk
            rw [newtonHZ_neg t _ (by
              simp only [Finset.mem_range] at hk
              omega), mul_zero]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hQ_val k (Finset.mem_range.mp hk)]
    rw [hstep1]
    let f : ℕ → ℂ := fun j =>
      if h : j < a + 1 then
        c ⟨j, h⟩ * newtonHZ t ((n : ℤ) - a + j) else 0
    suffices hsuff : ∑ k ∈ Finset.range (a + 1),
        f ((a + 1) - 1 - k) = 0 by
      convert hsuff using 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      change c ⟨a - k, _⟩ * newtonHZ t ((n : ℤ) - k) =
        if h : a - k < a + 1 then
          c ⟨a - k, h⟩ * newtonHZ t ((n : ℤ) - a + (a - k : ℕ)) else 0
      rw [dite_eq_left (show a - k < a + 1 by omega)]
      congr 2
      omega
    rw [Finset.sum_range_reflect f (a + 1),
      ← Fin.sum_univ_eq_sum_range f (a + 1)]
    have hf_eq : ∑ i : Fin (a + 1), f ↑i =
        ∑ i : Fin (a + 1),
          c i * newtonHZ t (((n : ℤ) - a - 1) + 1 + (i : ℤ)) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [f]
      rw [dite_eq_left i.isLt]
      congr 2
      omega
    rw [hf_eq]
    exact hrec ((n : ℤ) - a - 1) (by omega)
  let P := PowerSeries.trunc (b + 1) ((↑Q : ℂ⟦X⟧) * H)
  have hQH_eq : (↑Q : ℂ⟦X⟧) * H = ↑P :=
    powerSeries_eq_coe_trunc_of_eventually_zero _ (b + 1) hQH_ev
  have hH_ne : H ≠ 0 := by
    intro hH
    have : PowerSeries.coeff 0 H = 0 := by rw [hH]; simp
    simp [hH_def, newtonHSeries, PowerSeries.coeff_mk] at this
  have hP_ne : P ≠ 0 := by
    intro hP
    have : (↑Q : ℂ⟦X⟧) * H ≠ 0 :=
      mul_ne_zero (Polynomial.coe_eq_zero_iff.not.mpr hQ_ne) hH_ne
    rw [hQH_eq, hP, Polynomial.coe_zero] at this
    exact this rfl
  have hQ_deg : Q.natDegree ≤ a := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    calc (Polynomial.C (c ⟨a - i, _⟩) * Polynomial.X ^ i).natDegree
        ≤ i := Polynomial.natDegree_C_mul_X_pow_le _ _
      _ ≤ a := by rw [Finset.mem_range] at hi; omega
  have hP_deg : P.natDegree ≤ b := by
    change (PowerSeries.trunc (b + 1) ((↑Q : ℂ⟦X⟧) * H)).natDegree ≤ b
    have := PowerSeries.natDegree_trunc_lt ((↑Q : ℂ⟦X⟧) * H) b
    omega
  exact ⟨Q, P, hQ_ne, hP_ne, hQH_eq, hQ_deg, hP_deg⟩

/-- A coprime pair `(Q₀, P₀)` with `↑Q₀ * H = ↑P₀` must have nonzero
constant coefficients, since `X` would otherwise divide a coprime pair. -/
private theorem nonzero_coeff_of_coprime_product {t : ℕ → ℂ}
    (Q₀ P₀ : ℂ[X]) (_hQ0_ne : Q₀ ≠ 0) (_hP0_ne : P₀ ≠ 0)
    (hcop : IsCoprime P₀ Q₀)
    (hQ0H : (↑Q₀ : ℂ⟦X⟧) * newtonHSeries t = ↑P₀) :
    Q₀.coeff 0 ≠ 0 ∧ P₀.coeff 0 ≠ 0 := by
  have hQ0_coeff0 : Q₀.coeff 0 ≠ 0 := by
    intro hQ0c
    have hP0c : P₀.coeff 0 = 0 := by
      have := congr_arg PowerSeries.constantCoeff hQ0H
      simp only [map_mul, Polynomial.constantCoeff_coe] at this
      rw [hQ0c, zero_mul] at this
      exact this.symm
    exact Polynomial.not_isUnit_X
      (hcop.isUnit_of_dvd' (Polynomial.X_dvd_iff.mpr hP0c)
        (Polynomial.X_dvd_iff.mpr hQ0c))
  exact ⟨hQ0_coeff0, by
    intro hP0c
    have := congr_arg PowerSeries.constantCoeff hQ0H
    simp only [map_mul, Polynomial.constantCoeff_coe] at this
    rw [hP0c] at this
    rcases mul_eq_zero.mp this with h | h
    · exact hQ0_coeff0 h
    · simp [newtonHSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_mk] at h⟩

/-- From two nonzero polynomials with `↑Q * H = ↑P`, produce a coprime
pair `(Q₀, P₀)` with `↑Q₀ * H = ↑P₀` via division by the GCD,
with nonzero constant coefficients and the original degree bounds. -/
theorem coprime_pair_from_product {t : ℕ → ℂ}
    (Q P : ℂ[X]) (hQ_ne : Q ≠ 0) (hP_ne : P ≠ 0)
    (hQH : (↑Q : ℂ⟦X⟧) * newtonHSeries t = ↑P) :
    ∃ Q₀ P₀ : ℂ[X],
      Q₀ ≠ 0 ∧ P₀ ≠ 0 ∧ IsCoprime P₀ Q₀ ∧
      (↑Q₀ : ℂ⟦X⟧) * newtonHSeries t = ↑P₀ ∧
      Q₀.coeff 0 ≠ 0 ∧ P₀.coeff 0 ≠ 0 ∧
      Q₀.natDegree ≤ Q.natDegree ∧ P₀.natDegree ≤ P.natDegree := by
  -- The Euclidean-domain GCD is not a typeclass `GCDMonoid` instance for
  -- `ℂ[X]` by default; introduce it explicitly so the coprimality API
  -- (`right_div_gcd_ne_zero`, `isCoprime_div_gcd_div_gcd`, etc.) resolves.
  let := EuclideanDomain.gcdMonoid ℂ[X]
  have hd_ne : EuclideanDomain.gcd P Q ≠ 0 := gcd_ne_zero_of_right hQ_ne
  have hd_coe_ne : (↑(EuclideanDomain.gcd P Q) : ℂ⟦X⟧) ≠ 0 :=
    Polynomial.coe_eq_zero_iff.not.mpr hd_ne
  have hQ_eq : Q = EuclideanDomain.gcd P Q * (Q / EuclideanDomain.gcd P Q) :=
    (EuclideanDomain.mul_div_cancel' hd_ne (gcd_dvd_right P Q)).symm
  have hP_eq : P = EuclideanDomain.gcd P Q * (P / EuclideanDomain.gcd P Q) :=
    (EuclideanDomain.mul_div_cancel' hd_ne (gcd_dvd_left P Q)).symm
  have hid : (↑(Q / EuclideanDomain.gcd P Q) : ℂ⟦X⟧) * newtonHSeries t =
      ↑(P / EuclideanDomain.gcd P Q) := by
    have h : (↑(EuclideanDomain.gcd P Q) : ℂ⟦X⟧) *
        ((↑(Q / EuclideanDomain.gcd P Q) : ℂ⟦X⟧) * newtonHSeries t -
         ↑(P / EuclideanDomain.gcd P Q)) = 0 := by
      rw [mul_sub, ← mul_assoc, ← Polynomial.coe_mul, ← hQ_eq,
        ← Polynomial.coe_mul, ← hP_eq, hQH, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hd_coe_ne)
  obtain ⟨hc0Q, hc0P⟩ := nonzero_coeff_of_coprime_product _ _
    (right_div_gcd_ne_zero hQ_ne) (left_div_gcd_ne_zero hP_ne)
    (isCoprime_div_gcd_div_gcd hQ_ne) hid
  exact ⟨Q / EuclideanDomain.gcd P Q, P / EuclideanDomain.gcd P Q,
    right_div_gcd_ne_zero hQ_ne, left_div_gcd_ne_zero hP_ne,
    isCoprime_div_gcd_div_gcd hQ_ne, hid, hc0Q, hc0P,
    Polynomial.natDegree_le_of_dvd ⟨_, by rw [mul_comm]; exact hQ_eq⟩ hQ_ne,
    Polynomial.natDegree_le_of_dvd ⟨_, by rw [mul_comm]; exact hP_eq⟩ hP_ne⟩

/-! ### Main theorem -/

/-- **Lemma A.9 of the accompanying paper.**
If the complete homogeneous sequence `newtonH t` satisfies a nontrivial
linear recurrence with constant coefficients from some index onward,
then `t` decomposes as a difference of power sums of two disjoint
multisets of nonzero complex numbers. -/
theorem superPowerSums_of_recurrence {t : ℕ → ℂ} {a b : ℕ}
    (c : Fin (a + 1) → ℂ) (hc : c ≠ 0)
    (hrec : ∀ ρ : ℤ, (b : ℤ) - a ≤ ρ →
      ∑ k : Fin (a + 1), c k * newtonHZ t (ρ + 1 + (k : ℤ)) = 0) :
    ∃ α β : Multiset ℂ,
      α.card ≤ a ∧ β.card ≤ b ∧
      (∀ x ∈ α, x ≠ 0) ∧ (∀ x ∈ β, x ≠ 0) ∧ (∀ x ∈ α, x ∉ β) ∧
      ∀ m : ℕ, 1 ≤ m →
        t m = (α.map (· ^ m)).sum - (β.map (· ^ m)).sum := by
  -- ═══════ STAGE A: Get the truncated pair ═══════
  obtain ⟨Q, P, hQ_ne, hP_ne, hQH, hQ_deg, hP_deg⟩ :=
    truncated_product_from_recurrence c hc hrec
  -- ═══════ STAGE B: Get the coprime pair ═══════
  obtain ⟨Q₀, P₀, hQ0_ne, hP0_ne, hcop, hQ0H, hQ0_coeff0, hP0_coeff0,
    hQ0_deg_le, hP0_deg_le⟩ := coprime_pair_from_product Q P hQ_ne hP_ne hQH
  -- ═══════ STAGE C: Factor P₀ and Q₀ ═══════
  obtain ⟨hQ0_fac, hQ0_card, hQ0_nz⟩ :=
    eq_prod_one_sub_of_coeff_zero_ne_zero Q₀ hQ0_ne hQ0_coeff0
  obtain ⟨hP0_fac, hP0_card, hP0_nz⟩ :=
    eq_prod_one_sub_of_coeff_zero_ne_zero P₀ hP0_ne hP0_coeff0
  -- ═══════ STAGE D: Define multisets α and β ═══════
  set α := Q₀.roots.map (· ⁻¹) with hα_def
  set β := P₀.roots.map (· ⁻¹) with hβ_def
  refine ⟨α, β, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQ0_card]; exact hQ0_deg_le.trans hQ_deg
  · rw [hP0_card]; exact hP0_deg_le.trans hP_deg
  · exact hQ0_nz
  · exact hP0_nz
  -- ═══════ STAGE E: Disjointness ═══════
  · intro x hx hxβ
    rw [hα_def, Multiset.mem_map] at hx
    rw [hβ_def, Multiset.mem_map] at hxβ
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, hrs⟩ := hxβ
    have hrs' : r = s := inv_injective hrs.symm
    subst hrs'
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : P₀.eval r = 0 := Polynomial.isRoot_of_mem_roots hs
    have h2 : Q₀.eval r = 0 := Polynomial.isRoot_of_mem_roots hr
    apply_fun Polynomial.eval r at huv
    simp [h1, h2] at huv
  -- ═══════ STAGE F: Power-sum identity ═══════
  · intro m hm
    -- Log-derivative identities for the C-scaled products
    have hXdQ : (↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) *
        (↑(Polynomial.derivative Q₀) : ℂ⟦X⟧) =
        -(↑Q₀ : ℂ⟦X⟧) * tailSumSeries α := by
      rw [hQ0_fac]
      simp only [Polynomial.derivative_C_mul, Polynomial.coe_mul,
        Polynomial.coe_C]
      linear_combination
        (PowerSeries.C (Q₀.coeff 0)) * X_mul_coe_derivative_prod α
    have hXdP : (↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) *
        (↑(Polynomial.derivative P₀) : ℂ⟦X⟧) =
        -(↑P₀ : ℂ⟦X⟧) * tailSumSeries β := by
      rw [hP0_fac]
      simp only [Polynomial.derivative_C_mul, Polynomial.coe_mul,
        Polynomial.coe_C]
      linear_combination
        (PowerSeries.C (P₀.coeff 0)) * X_mul_coe_derivative_prod β
    -- Leibniz rule applied to ↑Q₀ * H, then rewritten
    have hleib := ((PowerSeries.derivative (R := ℂ))).leibniz (a := (↑Q₀ : ℂ⟦X⟧)) (b :=
        newtonHSeries t)
    simp only [smul_eq_mul] at hleib
    rw [hQ0H, PowerSeries.derivative_coe, PowerSeries.derivative_coe,
        newtonH_derivative] at hleib
    -- Multiply the Leibniz identity by ↑X with strategic parenthesisation
    have hmul : (↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) *
        (↑(Polynomial.derivative P₀) : ℂ⟦X⟧) =
        (↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) * powerSumSeries t *
          ((↑Q₀ : ℂ⟦X⟧) * newtonHSeries t) +
        newtonHSeries t *
          ((↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) *
            (↑(Polynomial.derivative Q₀) : ℂ⟦X⟧)) := by
      linear_combination (↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) * hleib
    rw [hQ0H, hXdQ, hXdP] at hmul
    -- Cancel the unit ↑P₀
    have hP0_unit : IsUnit (↑P₀ : ℂ⟦X⟧) := by
      rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe]
      exact isUnit_iff_ne_zero.mpr hP0_coeff0
    have hkey : (↑(Polynomial.X : ℂ[X]) : ℂ⟦X⟧) * powerSumSeries t =
        tailSumSeries α - tailSumSeries β :=
      hP0_unit.mul_left_cancel
        (by linear_combination -hmul + tailSumSeries α * hQ0H)
    -- Extract coefficient m (where m ≥ 1)
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hcoeff := congr_arg (PowerSeries.coeff (n + 1)) hkey
    simp only [Polynomial.coe_X, PowerSeries.coeff_succ_X_mul, map_sub,
      tailSumSeries, powerSumSeries, PowerSeries.coeff_mk,
      Nat.succ_ne_zero, ↓reduceIte] at hcoeff
    exact hcoeff

end RS
