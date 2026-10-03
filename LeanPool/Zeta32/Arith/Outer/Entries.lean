/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Small.Binom
public import LeanPool.Zeta32.Arith.Outer.Moments
public import LeanPool.Zeta32.Arith.Outer.RankOne
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-! the proof notes section 4, Lemma 5, first step (partial fractions).
With `ρ_j = Res_{t=-j} R_n = rs n j`, the Hankel entry is
  `U_r(t^{a+b} R_n) = U_r(q_{a+b}) + Σ_j ρ_j (2jX + β_j) (-j)^a (-j)^b`,
where `q_m = polynomialPart n m` has integer coefficients and degree `m - n`.
The exact valuation of `ρ_j` for `n < j ≤ 5n < p²` is `3v((j-1)!) - 4v((j-n-1)!) - v((5n-j)!)`.

Several lemmas are adapted from the Li₂ formalization
dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/
(DecayQuotient: `D_succ`, `D_eq_desc`; DecayBinomial: `descPochhammer_eval_neg_one`;
DecayResidue: `eraseProd_*`;
DecayMediumNodes: `D_eval_neg_of_lt`, `padicValRat_factorial_small`, `rscale_val`;
IntegerFamily: the integer quotient),
with the layout `(s, K) = (3, 4)` there replaced by `(4, 5)` here. -/

public section

open Zeta32.Arith.Local

open Polynomial
open scoped BigOperators
namespace Zeta32.Outer
noncomputable section

/-! ## The polynomials `D m` -/

export Zeta32.Arith.Small (D_succ D_eq_desc D_monic D_natDegree
  descPochhammer_eval_neg_one D_eval_eq_prod)

/-! ## The integer polynomial part -/

-- adapted from Li2Unified/Modular/Base/IntegerFamily.lean
/-- The integral polynomial with roots `-1`, …, `-m`. -/
def integerD (m : ℕ) : ℤ[X] := ∏ j ∈ Finset.Icc 1 m, (X + C (j:ℤ))

lemma integerD_monic (m : ℕ) : (integerD m).Monic := by
  apply monic_prod_of_monic
  intro j _
  exact monic_X_add_C _

lemma integerD_map (m : ℕ) : (integerD m).map (Int.castRingHom ℚ) = D m := by
  simp only [integerD, D, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, Int.coe_castRingHom, Int.cast_natCast]

/-- Integral polynomial quotient of the rational-function numerator by its denominator. -/
def integerPolynomialPart (n k : ℕ) : ℤ[X] :=
  (X^k * (integerD n)^4) /ₘ integerD (5 * n)

theorem integerPolynomialPart_map (n k : ℕ) :
    (integerPolynomialPart n k).map (Int.castRingHom ℚ) = polynomialPart n k := by
  unfold integerPolynomialPart polynomialPart numerator
  rw [map_divByMonic _ (integerD_monic _)]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, integerD_map]

theorem polynomialPart_GV (p : ℕ) (n k : ℕ) : GV p (polynomialPart n k) 0 := by
  rw [← integerPolynomialPart_map]
  intro j
  rw [coeff_map]
  exact VG.intCast _

theorem polynomialPart_natDegree_le (n k : ℕ) :
    (polynomialPart n k).natDegree ≤ k + 4*n - 5 * n := by
  rw [polynomialPart, natDegree_divByMonic _ (D_monic _), D_natDegree]
  have h : (numerator n k).natDegree ≤ k + 4*n := by
    unfold numerator
    refine natDegree_mul_le.trans ?_
    refine add_le_add (natDegree_X_pow_le k) ?_
    refine natDegree_pow_le.trans ?_
    rw [D_natDegree, mul_comm]
  omega

/-! ## Moments of integral polynomials -/

lemma polynomialMoment_eq (r : ℚ) (q : ℚ[X]) :
    polynomialMoment r q = ∑ e ∈ q.support, q.coeff e * moment r e := by
  unfold polynomialMoment
  rw [Polynomial.sum_def]

section Val
variable {p : ℕ} [hp : Fact p.Prime]

lemma polynomialMoment_VG {r : ℚ} (hr : VG p r 0) {q : ℚ[X]} (hq : GV p q 0) :
    VG p (polynomialMoment r q) (-1) := by
  rw [polynomialMoment_eq]
  apply VG.sum
  intro e _
  simpa using (hq e).mul (moment_VG hr e)

lemma polynomialMoment_VG_small (hp2 : p ≠ 2) {r : ℚ} (hr : VG p r 0) {q : ℚ[X]}
    (hq : GV p q 0) (hdeg : q.natDegree + 3 ≤ p) : VG p (polynomialMoment r q) 0 := by
  rw [polynomialMoment_eq]
  apply VG.sum
  intro e he
  have := le_natDegree_of_mem_supp e he
  simpa using (hq e).mul (moment_VG_small hp2 hr (e := e) (by omega))

end Val

/-! ## Residues -/

-- adapted from Li2Unified/Modular/Base/DecayResidue.lean
/-- Product of the differences from `j` to all other indices in `1`, …, `K`. -/
abbrev eraseProd (K j : ℕ) : ℚ := Zeta32.Arith.Small.eraseProd K j

lemma eraseProd_base {j : ℕ} (hj : 1 ≤ j) :
    eraseProd j j = (-1:ℚ)^(j-1) * ((j-1).factorial : ℚ) :=
  Zeta32.Arith.Small.eraseProd_base hj

lemma eraseProd_succ {K j : ℕ} (hjK : j ≤ K) :
    eraseProd (K+1) j = eraseProd K j * (((K+1 : ℕ) : ℚ) - j) :=
  Zeta32.Arith.Small.eraseProd_succ hjK

lemma eraseProd_eq {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    eraseProd K j = (-1:ℚ)^(j-1) * ((j-1).factorial : ℚ) * ((K-j).factorial : ℚ) :=
  Zeta32.Arith.Small.eraseProd_eq hj hjK

lemma eraseProd_ne_zero {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) : eraseProd K j ≠ 0 := by
  rw [eraseProd_eq hj hjK]
  have : ((j-1).factorial : ℚ) ≠ 0 := by positivity
  have : ((K-j).factorial : ℚ) ≠ 0 := by positivity
  simp_all

/-- `ρ_j = Res_{t=-j} D_n^4/D_{5n}`. -/
def rs (n j : ℕ) : ℚ := (D n).eval (-(j:ℚ)) ^ 4 / eraseProd (5 * n) j

lemma residue_eq (n k j : ℕ) : residue n k j = (-(j:ℚ))^k * rs n j := by
  unfold residue rs eraseProd Zeta32.Arith.Small.eraseProd numerator
  rw [eval_mul, eval_pow, eval_pow, eval_X]
  ring

-- adapted from Li2Unified/Modular/Base/DecayMediumNodes.lean
lemma D_eval_neg_of_lt (n j : ℕ) (hnj : n < j) :
    (D n).eval (-(j:ℚ)) = (-1:ℚ)^n * (((j-1).factorial : ℚ) / ((j-1-n).factorial : ℚ)) := by
  induction n with
  | zero =>
    have : ((j-1).factorial : ℚ) ≠ 0 := by positivity
    simp [D, div_self this]
  | succ n ih =>
    rw [D_succ, eval_mul, ih (by omega), eval_add, eval_X, eval_C]
    have e : j - 1 - n = (j - 1 - (n+1)) + 1 := by omega
    rw [e, Nat.factorial_succ]
    have h1 : ((j - 1 - (n+1)).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((j - 1 - (n+1) + 1 : ℕ) : ℚ) = (j:ℚ) - n - 1 := by
      rw [show j - 1 - (n+1) + 1 = j - (n+1) by omega, Nat.cast_sub (by omega)]; push_cast; ring
    push_cast at h2 ⊢
    rw [h2]
    have h3 : (j:ℚ) - n - 1 ≠ 0 := by
      have : ((n:ℚ) + 1) < j := by exact_mod_cast hnj
      linarith
    field_simp
    ring

lemma D_eval_neg_of_le {n j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) : (D n).eval (-(j:ℚ)) = 0 := by
  rw [D_eval_eq_prod]
  exact Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨h1, h2⟩) (by ring)

lemma rs_eq_zero {n j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) : rs n j = 0 := by
  simp [rs, D_eval_neg_of_le h1 h2]

section Val
variable {p : ℕ} [hp : Fact p.Prime]

-- adapted from Li2Unified/Modular/Base/DecayMediumNodes.lean
lemma padicValRat_factorial_small {m : ℕ} (hm : m < p ^ 2) :
    padicValRat p (m.factorial : ℚ) = ((m / p : ℕ) : ℤ) := by
  rw [padicValRat.of_nat]
  have hlog : Nat.log p m < 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · exact Nat.log_lt_of_lt_pow (by omega) hm
  rw [padicValNat_factorial hlog]
  simp

lemma padicValRat_neg_one_pow (m : ℕ) : padicValRat p ((-1:ℚ)^m) = 0 := by
  rw [padicValRat.pow, padicValRat.neg]; simp

-- adapted from Li2Unified/Modular/Base/DecayMediumNodes.lean (`rscale_val`)
theorem rs_val {n j : ℕ} (hnj : n < j) (hjK : j ≤ 5 * n) (hK : 5 * n < p ^ 2) :
    padicValRat p (rs n j) =
      3 * (((j-1)/p : ℕ) : ℤ) - 4 * (((j-1-n)/p : ℕ) : ℤ) - (((5 * n-j)/p : ℕ) : ℤ) := by
  have h1 : ((j-1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((j-1-n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((5 * n-j).factorial : ℚ) ≠ 0 := by positivity
  have hs1 : (-1:ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs2 : (-1:ℚ)^(j-1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hD : (D n).eval (-(j:ℚ)) ≠ 0 := by
    rw [D_eval_neg_of_lt n j hnj]; exact mul_ne_zero hs1 (div_ne_zero h1 h2)
  have hE : eraseProd (5 * n) j ≠ 0 := eraseProd_ne_zero (by omega) hjK
  rw [rs, padicValRat.div (pow_ne_zero _ hD) hE, padicValRat.pow,
    D_eval_neg_of_lt n j hnj, eraseProd_eq (by omega) hjK,
    padicValRat.mul hs1 (div_ne_zero h1 h2), padicValRat.div h1 h2,
    padicValRat.mul (mul_ne_zero hs2 h1) h3, padicValRat.mul hs2 h1,
    padicValRat_neg_one_pow, padicValRat_neg_one_pow,
    padicValRat_factorial_small (by omega : j - 1 < p^2),
    padicValRat_factorial_small (by omega : j - 1 - n < p^2),
    padicValRat_factorial_small (by omega : 5 * n - j < p^2)]
  push_cast
  ring

end Val

/-! ## The rank-one scalars and the entry decomposition -/

/-- The pole scalar `ρ_j (2jX + β_j)`. -/
def gam (r : ℚ) (n j : ℕ) : ℚ[X] := C (rs n j) * (C (2 * (j:ℚ)) * X + C (beta r j))

theorem entry_eq (r : ℚ) (n : ℕ) (a b : Fin (3 * n)) :
    ((X : ℚ[X]) • (B n).map C + (A r n).map C) a b =
      C (polynomialMoment r (polynomialPart n (a.val + b.val))) +
      ∑ j ∈ Finset.Icc 1 (5 * n), gam r n j * C ((-(j:ℚ))^(a:ℕ) * (-(j:ℚ))^(b:ℕ)) := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, A, B, slope, intercept,
    smul_eq_mul, map_add, map_sum, Finset.mul_sum]
  rw [add_comm (C _) _, ← add_assoc, ← Finset.sum_add_distrib, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [residue_eq, pow_add, gam]
  simp only [map_mul, map_pow, map_neg, map_natCast, map_ofNat]
  ring

/-- Node weight of the proof notes, Lemma 5: `w_j = v_p(ρ_j) + betaWt`, and a large dummy value
for the
cancelled nodes `j ≤ n` (where `ρ_j = 0`). -/
@[expose]
def wv (n p j : ℕ) : ℚ :=
  if j ≤ n then 15 * (n:ℚ) + 1 else
    (3 * ((j-1)/p : ℕ) - 4 * ((j-1-n)/p : ℕ) - ((5 * n-j)/p : ℕ) : ℚ) + betaWt p j

section Val
variable {p : ℕ} [hp : Fact p.Prime]

theorem gam_GV {r : ℚ} (hr : VG p r 0) {n j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ 5 * n)
    (hK : 5 * n < p ^ 2) : GV p (gam r n j) (wv n p j) := by
  by_cases hjn : j ≤ n
  · rw [gam, rs_eq_zero hj1 hjn, map_zero, zero_mul]
    exact GV.zero _
  · have hnj : n < j := by omega
    have hrs : VG p (rs n j)
        (3 * ((j-1)/p : ℕ) - 4 * ((j-1-n)/p : ℕ) - ((5 * n-j)/p : ℕ) : ℚ) :=
      VG.of_eq _ fun _ => by
        rw [rs_val hnj hjK hK]
        push_cast
        exact le_rfl
    have h := GV.C_mul hrs (poleValue_GV (p := p) hr (j := j) (by omega) (by omega))
    unfold wv
    rw [ite_eq_right hjn]
    exact h

omit hp in
lemma wv_le_big {n j : ℕ} (hj : j ≤ 5 * n) : wv n p j ≤ 15 * (n:ℚ) + 1 := by
  unfold wv
  split_ifs
  · exact le_rfl
  · have h1 : (((j-1)/p : ℕ) : ℚ) ≤ 5 * n := by
      exact_mod_cast (Nat.div_le_self _ _).trans (by omega)
    have h2 : (0:ℚ) ≤ ((j-1-n)/p : ℕ) := Nat.cast_nonneg _
    have h3 : (0:ℚ) ≤ ((5 * n-j)/p : ℕ) := Nat.cast_nonneg _
    have h4 : betaWt p j ≤ 0 := by unfold betaWt; split_ifs <;> norm_num
    linarith

end Val

end
end Zeta32.Outer

end
