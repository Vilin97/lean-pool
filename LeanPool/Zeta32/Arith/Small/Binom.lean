/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Family
public import LeanPool.Zeta32.Arith.Local.ValExtra
public import LeanPool.Zeta32.Arith.Local.Binom
public import LeanPool.Zeta5Irrational.Arith.BinomBasis
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Binomial polynomials `binom(t,a)`, their integer values at all integers, Newton expansion at an
arbitrary centre, derivatives at integers (`v_p ≥ β - ⌊log_p e⌋`), `D_m = m!·binom(t+m,m)`, and the
residue scale `K!/∏_{l≠j}(l-j) ∈ ℤ`. -/

public section

open Zeta32.Arith.Local

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/DecayNormalization.lean
-- (binomPoly), .../Base/DecayBinomial.lean (integer values, Newton expansion, derivative at 0),
-- .../Base/DecayMu.lean (`derivative_eval_VG`), .../Base/DecayQuotient.lean (D, shiftBinom, the
-- shifted binomial ratio, `inv_choose_VG`), .../Base/DecayResidue.lean (`eraseProd`,
-- `residueScale_VG`).
-- namespace changed; `D` is `Zeta32.D` (same definition as Li₂'s `D`).

open Polynomial fwdDiff
open scoped BigOperators
namespace Zeta32.Arith.Small
open Zeta32
noncomputable section

/-- binom(t,a)=descPochhammer a/a!. -/
abbrev binomPoly (a : ℕ) : ℚ[X] := Zeta5Irrational.bin a

lemma binomPoly_eval_nat (a m : ℕ) : (binomPoly a).eval (m : ℚ) = (m.choose a : ℚ) :=
  Zeta5Irrational.bin_eval_nat a m

lemma binomPoly_natDegree (a : ℕ) : (binomPoly a).natDegree = a := by
  unfold binomPoly Zeta5Irrational.bin
  rw [natDegree_C_mul (inv_ne_zero (by positivity)), descPochhammer_natDegree]

lemma binomPoly_coeff_self (a : ℕ) : (binomPoly a).coeff a = (a.factorial : ℚ)⁻¹ := by
  have h := (monic_descPochhammer ℚ a).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  rw [binomPoly, Zeta5Irrational.bin, coeff_C_mul, h, mul_one]

/-- Two rational polynomials agreeing on c+m for every natural m are equal. -/
lemma eq_of_eval_shift_nat {p q : ℚ[X]} (c : ℚ)
    (h : ∀ m : ℕ, p.eval (c + m) = q.eval (c + m)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun m : ℕ => c + (m : ℚ)) := fun a b hab => by
    simpa using hab
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro _ ⟨m, rfl⟩
    exact h m)

lemma binomPoly_zero : binomPoly 0 = 1 := Zeta5Irrational.bin_zero

lemma binomPoly_succ_comp_add_one (k : ℕ) :
    (binomPoly (k+1)).comp (X+1) = binomPoly (k+1) + binomPoly k :=
  Zeta5Irrational.bin_comp_add_one k

lemma binomPoly_eval_add_one (k : ℕ) (x : ℚ) :
    (binomPoly (k+1)).eval (x+1) = (binomPoly (k+1)).eval x + (binomPoly k).eval x := by
  have h := congrArg (eval x) (binomPoly_succ_comp_add_one k)
  simpa [eval_comp] using h

/-- binom(m,k) is an integer for every integer m, including negative m. -/
lemma binomPoly_eval_int (k : ℕ) (m : ℤ) : ∃ z : ℤ, (binomPoly k).eval (m : ℚ) = z := by
  induction k generalizing m with
  | zero => exact ⟨1, by simp [binomPoly_zero]⟩
  | succ k ih =>
    have h0 : (binomPoly (k+1)).eval ((0 : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by
      have := binomPoly_eval_nat (k+1) 0
      simpa using this
    induction m using Int.induction_on with
    | zero => exact ⟨0, h0⟩
    | succ i hi =>
      obtain ⟨a, ha⟩ := hi
      obtain ⟨b, hb⟩ := ih (i : ℤ)
      refine ⟨a + b, ?_⟩
      push_cast
      rw [binomPoly_eval_add_one, ← Int.cast_natCast, ha, hb]
    | pred i hi =>
      obtain ⟨a, ha⟩ := hi
      obtain ⟨b, hb⟩ := ih (-(i : ℤ) - 1)
      refine ⟨a - b, ?_⟩
      have h := binomPoly_eval_add_one k ((-(i:ℤ) - 1 : ℤ) : ℚ)
      have e : ((-(i:ℤ) - 1 : ℤ) : ℚ) + 1 = ((-(i:ℤ) : ℤ) : ℚ) := by push_cast; ring
      rw [e, ha, hb] at h
      push_cast at h ⊢
      linarith

lemma binomPoly_eval_int_VG (p : ℕ) (k : ℕ) (m : ℤ) :
    VG p ((binomPoly k).eval (m : ℚ)) 0 := by
  obtain ⟨z, hz⟩ := binomPoly_eval_int k m
  rw [hz]
  exact VG.intCast z

/-- The k-th forward difference of the values of f, at step 1. -/
def newtonCoeff (f : ℚ[X]) (c : ℚ) (k : ℕ) : ℚ := (Δ_[(1:ℚ)])^[k] (fun x => f.eval x) c

lemma newtonCoeff_eq_sum (f : ℚ[X]) (c : ℚ) (k : ℕ) :
    newtonCoeff f c k = ∑ i ∈ Finset.range (k+1),
      ((-1 : ℚ)^(k-i) * (k.choose i : ℚ)) * f.eval (c + i) := by
  rw [newtonCoeff, fwdDiff_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro i _
  simp [zsmul_eq_mul]

lemma newtonCoeff_eq_zero {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d) (c : ℚ) {k : ℕ}
    (hk : d < k) : newtonCoeff f c k = 0 := by
  rw [newtonCoeff]
  have := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := f) (n := k) (by omega)
  exact congrFun this c

/-- **Newton expansion** at an arbitrary rational centre c, degree window d. -/
theorem newton_expansion {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d) (c : ℚ) :
    f = ∑ k ∈ Finset.range (d+1), C (newtonCoeff f c k) * (binomPoly k).comp (X - C c) := by
  apply eq_of_eval_shift_nat c
  intro m
  have hG := shift_eq_sum_fwdDiff_iter (1 : ℚ) (fun x => f.eval x) m c
  simp only [nsmul_eq_mul, mul_one] at hG
  rw [hG, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, add_sub_cancel_left,
    binomPoly_eval_nat]
  have hext : ∀ N, m ≤ N → d ≤ N →
      ∑ k ∈ Finset.range (N+1), (m.choose k : ℚ) * newtonCoeff f c k =
      ∑ k ∈ Finset.range (d+1), newtonCoeff f c k * (m.choose k : ℚ) ∧
      ∑ k ∈ Finset.range (N+1), (m.choose k : ℚ) * newtonCoeff f c k =
      ∑ k ∈ Finset.range (m+1), (m.choose k : ℚ) * newtonCoeff f c k := by
    intro N hm hd
    constructor
    · rw [← Finset.sum_range_add_sum_Ico _ (by omega : d+1 ≤ N+1)]
      rw [Finset.sum_eq_zero (s := Finset.Ico (d+1) (N+1)) (fun k hk => by
        rw [newtonCoeff_eq_zero hf c (by simp at hk; omega), mul_zero]), add_zero]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · rw [← Finset.sum_range_add_sum_Ico _ (by omega : m+1 ≤ N+1)]
      rw [Finset.sum_eq_zero (s := Finset.Ico (m+1) (N+1)) (fun k hk => by
        rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega), Nat.cast_zero, zero_mul]), add_zero]
  obtain ⟨h1, h2⟩ := hext (max m d) (le_max_left _ _) (le_max_right _ _)
  change ∑ k ∈ Finset.range (m+1), (m.choose k : ℚ) * newtonCoeff f c k = _
  rw [← h2, h1]

/-- VG bound on Newton coefficients from a window of consecutive values. -/
lemma newtonCoeff_VG (p : ℕ) [Fact p.Prime] {f : ℚ[X]} (c r : ℚ) (k : ℕ)
    (hv : ∀ i ≤ k, VG p (f.eval (c + i)) r) : VG p (newtonCoeff f c k) r := by
  rw [newtonCoeff_eq_sum]
  apply VG.sum
  intro i hi
  have hcoef : VG p ((-1 : ℚ)^(k-i) * (k.choose i : ℚ)) 0 := by
    have : ((-1 : ℚ)^(k-i) * (k.choose i : ℚ)) = (((-1 : ℤ)^(k-i) * (k.choose i : ℤ) : ℤ) : ℚ) := by
      push_cast; ring
    rw [this]; exact VG.intCast _
  simpa using hcoef.mul (hv i (by simp at hi; omega))

lemma descPochhammer_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ k).eval (-1) = (-1 : ℚ)^k * (k.factorial : ℚ) :=
  Zeta32.Arith.Local.descPochhammer_eval_neg_one k

/-- d/dx binom(x,k+1) at x=0 equals (-1)^k/(k+1). -/
lemma binomPoly_derivative_eval_zero (k : ℕ) :
    (derivative (binomPoly (k+1))).eval 0 = (-1 : ℚ)^k / ((k:ℚ)+1) :=
  Zeta5Irrational.bin_derivative_eval_zero k

lemma binomPoly_derivative_eval_zero_zero : (derivative (binomPoly 0)).eval 0 = 0 := by
  simp [binomPoly_zero]

/-- The derivative at a Newton centre: f'(c)=sum_{k=1}^d Delta^k f(c) (-1)^(k-1)/k. -/
theorem derivative_eval_newton {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d) (c : ℚ) :
    (derivative f).eval c = ∑ k ∈ Finset.range d,
      newtonCoeff f c (k+1) * ((-1 : ℚ)^k / ((k:ℚ)+1)) := by
  conv_lhs => rw [newton_expansion hf c]
  rw [derivative_sum, eval_finsetSum, Finset.sum_range_succ']
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp,
    derivative_sub, derivative_X, derivative_C, sub_zero, eval_mul, eval_C,
    eval_comp, eval_sub, eval_X, sub_self]
  simp only [eval_one, one_mul, binomPoly_derivative_eval_zero_zero, mul_zero, add_zero]
  exact Finset.sum_congr rfl fun k _ => by rw [binomPoly_derivative_eval_zero]

/-- Derivative values at integers from values at all integers. -/
theorem derivative_eval_VG (p : ℕ) [Fact p.Prime] {f : ℚ[X]} {e : ℕ} (hf : f.natDegree ≤ e)
    (r : ℚ) (hv : ∀ m : ℤ, VG p (f.eval (m:ℚ)) r) (m : ℤ) :
    VG p ((derivative f).eval (m:ℚ)) (r - (Nat.log p e : ℚ)) := by
  rw [derivative_eval_newton hf]
  apply VG.sum
  intro k hk
  have hk' : k + 1 ≤ e := by simp at hk; omega
  have hc : VG p (newtonCoeff f (m:ℚ) (k+1)) r :=
    newtonCoeff_VG p _ r _ fun i _ => by
      have := hv (m + i)
      push_cast at this
      exact this
  have hinv : VG p ((-1:ℚ)^k / ((k:ℚ)+1)) (-(Nat.log p e : ℚ)) := by
    rw [div_eq_mul_inv]
    have h1 : VG p ((-1:ℚ)^k) 0 := by
      have : ((-1:ℚ)^k) = (((-1:ℤ)^k : ℤ) : ℚ) := by push_cast; ring
      rw [this]; exact VG.intCast _
    have h2 := VG.inv_nat (p := p) (j := k+1) (n := e) (by omega) hk'
    push_cast at h2
    simpa using h1.mul h2
  simpa [sub_eq_add_neg] using hc.mul hinv

/-! ### `D_m` and the shifted binomial -/

lemma D_succ (m : ℕ) : D (m+1) = D m * (X + C ((m:ℚ)+1)) := by
  rw [D, Finset.prod_Icc_succ_top (by omega)]
  push_cast
  rfl

lemma D_eq_desc (m : ℕ) : D m = (descPochhammer ℚ m).comp (X + C (m:ℚ)) := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    rw [D_succ, ih, descPochhammer_succ_left, mul_comp, X_comp, comp_assoc]
    have h : (X - 1 : ℚ[X]).comp (X + C ((m+1 : ℕ) : ℚ)) = X + C (m:ℚ) := by
      rw [sub_comp, X_comp, one_comp]
      push_cast
      rw [map_add, map_one]
      ring
    rw [h, mul_comm]
    push_cast
    rfl

lemma D_natDegree (m : ℕ) : (D m).natDegree = m := by
  rw [D_eq_desc, natDegree_comp, descPochhammer_natDegree, natDegree_X_add_C, mul_one]

lemma D_monic (m : ℕ) : (D m).Monic := by
  unfold D
  exact monic_prod_of_monic _ _ fun j _ => monic_X_add_C _

lemma desc_eq_C_mul_binomPoly (m : ℕ) :
    descPochhammer ℚ m = C (m.factorial : ℚ) * binomPoly m := by
  rw [binomPoly, Zeta5Irrational.bin, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (by positivity), C_1, one_mul]

/-- binom(t+n,n). -/
def shiftBinom (n : ℕ) : ℚ[X] := (binomPoly n).comp (X + C (n:ℚ))

lemma D_eq_shiftBinom (n : ℕ) : D n = C (n.factorial : ℚ) * shiftBinom n := by
  rw [D_eq_desc, desc_eq_C_mul_binomPoly, mul_comp, C_comp, shiftBinom]

lemma shiftBinom_eval_int (p n : ℕ) (m : ℤ) : VG p ((shiftBinom n).eval (m:ℚ)) 0 := by
  rw [shiftBinom, eval_comp, eval_add, eval_X, eval_C]
  have := binomPoly_eval_int_VG p n (m + n)
  push_cast at this
  exact this

lemma shiftBinom_natDegree (n : ℕ) : (shiftBinom n).natDegree = n := by
  rw [shiftBinom, natDegree_comp, binomPoly_natDegree, natDegree_X_add_C, mul_one]

lemma D_eval_nat (K m : ℕ) :
    (D K).eval (m:ℚ) = (K.factorial : ℚ) * ((m+K).choose K : ℚ) := by
  rw [D_eq_desc, eval_comp, eval_add, eval_X, eval_C,
    show (m:ℚ) + K = ((m+K : ℕ) : ℚ) by push_cast; ring,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- K! binom(t+K,k) = D_K binom(t,k-K)/binom(k,K) for K <= k. -/
lemma shifted_binom_ratio {K k : ℕ} (hk : K ≤ k) :
    C (K.factorial : ℚ) * (binomPoly k).comp (X + C (K:ℚ)) =
      D K * (C ((k.choose K : ℚ)⁻¹) * binomPoly (k - K)) := by
  apply eq_of_eval_shift_nat 0
  intro m
  simp only [zero_add, eval_mul, eval_C, eval_comp, eval_add, eval_X]
  rw [D_eval_nat, show (m:ℚ) + K = ((m+K : ℕ) : ℚ) by push_cast; ring,
    binomPoly_eval_nat, binomPoly_eval_nat]
  have hc : (k.choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have key : (m+K).choose k * k.choose K = (m+K).choose K * m.choose (k-K) := by
    have := Nat.choose_mul (n := m+K) (k := k) (s := K) hk
    rwa [Nat.add_sub_cancel] at this
  have key' : ((m+K).choose k : ℚ) * (k.choose K : ℚ) = ((m+K).choose K : ℚ) * (m.choose (k-K) :
    ℚ) := by
    exact_mod_cast key
  field_simp
  linear_combination key'

lemma inv_choose_VG (p : ℕ) [hp : Fact p.Prime] {k K N : ℕ} (hk : K ≤ k) (hkN : k ≤ N) :
    VG p (((k.choose K : ℚ))⁻¹) (-(Nat.log p N : ℚ)) := by
  have hc : k.choose K ≠ 0 := (Nat.choose_pos hk).ne'
  apply VG.inv
  rw [padicValRat.of_nat, ← Nat.factorization_def _ hp.out]
  exact_mod_cast (Nat.factorization_choose_le_log).trans (Nat.log_mono_right hkN)

/-! ### Residue denominators -/

/-- Product of the differences from `j` to all other indices in `1`, …, `K`. -/
@[expose]
def eraseProd (K j : ℕ) : ℚ := ∏ l ∈ (Finset.Icc 1 K).erase j, ((l:ℚ) - (j:ℚ))

lemma D_eval_eq_prod (m : ℕ) (x : ℚ) : (D m).eval x = ∏ l ∈ Finset.Icc 1 m, (x + l) := by
  rw [D, eval_prod]
  simp

lemma eraseProd_base {j : ℕ} (hj : 1 ≤ j) :
    eraseProd j j = (-1:ℚ)^(j-1) * ((j-1).factorial : ℚ) := by
  have hs : (Finset.Icc 1 j).erase j = Finset.Icc 1 (j-1) := by
    ext l; simp; omega
  rw [eraseProd, hs]
  have h := D_eval_eq_prod (j-1) (-(j:ℚ))
  rw [D_eq_desc, eval_comp, eval_add, eval_X, eval_C] at h
  have hc : -(j:ℚ) + ((j-1 : ℕ) : ℚ) = -1 := by
    rw [Nat.cast_sub hj]; push_cast; ring
  rw [hc, descPochhammer_eval_neg_one] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro l _
  ring

lemma eraseProd_succ {K j : ℕ} (hjK : j ≤ K) :
    eraseProd (K+1) j = eraseProd K j * (((K+1 : ℕ) : ℚ) - j) := by
  have hs : (Finset.Icc 1 (K+1)).erase j = insert (K+1) ((Finset.Icc 1 K).erase j) := by
    ext l; simp; omega
  rw [eraseProd, hs, Finset.prod_insert (by simp), eraseProd, mul_comm]

lemma eraseProd_eq {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    eraseProd K j = (-1:ℚ)^(j-1) * ((j-1).factorial : ℚ) * ((K-j).factorial : ℚ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjK
  induction t with
  | zero => simp [eraseProd_base hj]
  | succ t ih =>
    rw [← add_assoc, eraseProd_succ (by omega), ih (by omega)]
    rw [show j + t + 1 - j = t + 1 by omega, show j + t - j = t by omega, Nat.factorial_succ]
    push_cast
    ring

lemma residueScale_eq {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    (K.factorial : ℚ) / eraseProd K j =
      (-1:ℚ)^(j-1) * (K:ℚ) * ((K-1).choose (j-1) : ℚ) := by
  rw [eraseProd_eq hj hjK]
  have hc := Nat.choose_mul_factorial_mul_factorial (n := K-1) (k := j-1) (by omega)
  rw [show K - 1 - (j - 1) = K - j by omega] at hc
  have hK : K.factorial = K * (K-1).factorial := by
    obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ K)
    rw [show 1 + K' - 1 = K' by omega, add_comm, Nat.factorial_succ]
  have hc' : ((K-1).choose (j-1) : ℚ) * ((j-1).factorial : ℚ) * ((K-j).factorial : ℚ) =
      ((K-1).factorial : ℚ) := by exact_mod_cast hc
  have h1 : ((j-1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((K-j).factorial : ℚ) ≠ 0 := by positivity
  rw [hK]
  push_cast
  rw [← hc']
  have hs : ((-1:ℚ)^(j-1))^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  field_simp
  linear_combination (-(K:ℚ) * ((K-1).choose (j-1) : ℚ)) * hs

lemma residueScale_VG (p : ℕ) {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    VG p ((K.factorial : ℚ) / eraseProd K j) 0 := by
  rw [residueScale_eq hj hjK]
  have : (-1:ℚ)^(j-1) * (K:ℚ) * ((K-1).choose (j-1) : ℚ) =
      (((-1:ℤ)^(j-1) * K * ((K-1).choose (j-1)) : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  exact VG.intCast _

end
end Zeta32.Arith.Small

end
