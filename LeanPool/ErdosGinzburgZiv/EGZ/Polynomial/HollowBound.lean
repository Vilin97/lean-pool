/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Constants
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# A polynomial bound for hollow families

This file formalizes Proposition `thw` from the paper.  For every positive
dimension `d` and prime `p`, it proves

`𝔴(𝔽_p^d) ≤ choose (2 * d - 1) d + 1`.

The right-hand side is independent of `p`, which is the fact needed when the
elementary lower bound for the Erdős--Ginzburg--Ziv constant is converted into
an asymptotic statement.

The proof follows the paper's polynomial method.  Stars and bars counts the
low-degree monomials.  A kernel-dimension argument produces a nonzero weight
annihilating them and vanishing at one prescribed point.  Contracting the
zero-sum detector polynomial in all but its last vector block is constant in
that last block, while hollowness identifies it with `h(t)^q`; these two facts
contradict the choice of `h`.
-/

open scoped BigOperators

noncomputable section

namespace EGZ
namespace Polynomial

/-! ## Low-degree monomials and the annihilator -/

/-- Stars-and-bars indices for monomials in `d` variables of total degree at
most `d - 1`.  The final coordinate is a slack exponent. -/
abbrev LowExponent (d : ℕ) := Sym (Fin (d + 1)) (d - 1)

/-- The exponent tuple, including its final slack coordinate. -/
def lowExponentTuple (d : ℕ) (a : LowExponent d) : Fin (d + 1) → ℕ :=
  (Sym.equivNatSumOfFintype (Fin (d + 1)) (d - 1) a : Fin (d + 1) → ℕ)

/-- The actual exponent tuple in the first `d` coordinates. -/
def lowExponentMonomial (d : ℕ) (a : LowExponent d) : Fin d → ℕ :=
  fun j => lowExponentTuple d a j.castSucc

theorem lowExponentTuple_sum (d : ℕ) (a : LowExponent d) :
    ∑ j, lowExponentTuple d a j = d - 1 :=
  (Sym.equivNatSumOfFintype (Fin (d + 1)) (d - 1) a).property

/-- Pad an exponent tuple of total degree at most `d - 1` with a slack
coordinate. -/
def lowExponentOfFun (d : ℕ) (e : Fin d → ℕ) (he : ∑ j, e j ≤ d - 1) :
    LowExponent d :=
  (Sym.equivNatSumOfFintype (Fin (d + 1)) (d - 1)).symm
    ⟨Fin.snoc e (d - 1 - ∑ j, e j), by
      rw [Fin.sum_univ_castSucc, Fin.snoc_last]
      simpa only [Fin.snoc_castSucc] using Nat.add_sub_of_le he⟩

@[simp]
theorem lowExponentMonomial_lowExponentOfFun (d : ℕ) (e : Fin d → ℕ)
    (he : ∑ j, e j ≤ d - 1) :
    lowExponentMonomial d (lowExponentOfFun d e he) = e := by
  funext j
  simp [lowExponentMonomial, lowExponentTuple, lowExponentOfFun]

/-- The number of monomials in `d` variables of degree at most `d - 1`. -/
theorem card_lowExponent (d : ℕ) (hd : 1 ≤ d) :
    Fintype.card (LowExponent d) = (2 * d - 1).choose d := by
  rw [Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have hsum : d + 1 + (d - 1) - 1 = 2 * d - 1 := by omega
  rw [hsum]
  exact Nat.choose_symm_of_eq_add (by omega)

variable {K : Type*} [Field K]

/-- Value of a coordinate monomial. -/
def monomialValue {d : ℕ} (e : Fin d → ℕ) (x : Fin d → K) : K :=
  ∏ j, x j ^ e j

/-- The linear system consisting of every low-monomial moment and one
prescribed zero coordinate. -/
def equationMap {d n : ℕ} (v : Fin n → Fin d → K) (t₀ : Fin n) :
    (Fin n → K) →ₗ[K] (Option (LowExponent d) → K) where
  toFun h
    | none => h t₀
    | some e => ∑ i, h i * monomialValue (lowExponentMonomial d e) (v i)
  map_add' h k := by
    funext e
    cases e with
    | none => simp
    | some e => simp [Finset.sum_add_distrib, add_mul, monomialValue]
  map_smul' c h := by
    funext e
    cases e with
    | none => simp
    | some e => simp [Finset.mul_sum, mul_assoc, monomialValue]

/-- More variables than equations give a nonzero annihilating weight. -/
theorem exists_annihilator {d n : ℕ} (hd : 1 ≤ d)
    (hn : (2 * d - 1).choose d + 2 ≤ n)
    (v : Fin n → Fin d → K) (t₀ : Fin n) :
    ∃ h : Fin n → K, h ≠ 0 ∧ h t₀ = 0 ∧
      ∀ e : LowExponent d,
        ∑ i, h i * monomialValue (lowExponentMonomial d e) (v i) = 0 := by
  let L := equationMap v t₀
  have hdim :
      Module.finrank K (Option (LowExponent d) → K) <
        Module.finrank K (Fin n → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun,
      Fintype.card_option, card_lowExponent d hd]
    omega
  have hker : LinearMap.ker L ≠ ⊥ := L.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨h, hhker, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨h, hh0, ?_, ?_⟩
  · have hrow := congrFun hhker none
    simpa [L, equationMap] using hrow
  · intro e
    have hrow := congrFun hhker (some e)
    simpa [L, equationMap] using hrow

/-- A weight annihilates every ordinary exponent tuple of total degree at
most `d - 1`. -/
def AnnihilatesLow {d n : ℕ} (h : Fin n → K) (v : Fin n → Fin d → K) : Prop :=
  ∀ e : Fin d → ℕ, (∑ j, e j) ≤ d - 1 →
    ∑ i, h i * monomialValue e (v i) = 0

theorem exists_annihilator' {d n : ℕ} (hd : 1 ≤ d)
    (hn : (2 * d - 1).choose d + 2 ≤ n)
    (v : Fin n → Fin d → K) (t₀ : Fin n) :
    ∃ h : Fin n → K, h ≠ 0 ∧ h t₀ = 0 ∧ AnnihilatesLow h v := by
  obtain ⟨h, hh, ht, ha⟩ := exists_annihilator hd hn v t₀
  refine ⟨h, hh, ht, ?_⟩
  intro e he
  simpa [AnnihilatesLow] using ha (lowExponentOfFun d e he)

/-! ## The detector polynomial -/

open MvPolynomial

/-- The polynomial detecting whether `q + 1` vector blocks sum to zero over
`ZMod (q + 1)`. -/
def zeroSumDetector (q d : ℕ) :
    MvPolynomial (Fin (q + 1) × Fin d) (ZMod (q + 1)) :=
  ∏ j : Fin d, (1 - (∑ i : Fin (q + 1), X (i, j)) ^ q)

/-- Total-degree bound for the detector. -/
theorem totalDegree_zeroSumDetector_le (q d : ℕ) [Fact (q + 1).Prime] :
    (zeroSumDetector q d).totalDegree ≤ d * q := by
  calc
    (zeroSumDetector q d).totalDegree ≤
        ∑ j : Fin d, (1 - (∑ i : Fin (q + 1), X (i, j)) ^ q :
          MvPolynomial (Fin (q + 1) × Fin d) (ZMod (q + 1))).totalDegree :=
      totalDegree_finsetProd Finset.univ _
    _ ≤ ∑ _j : Fin d, q := by
      gcongr with j
      refine (totalDegree_sub _ _).trans ?_
      simp only [totalDegree_one, zero_max]
      refine (totalDegree_pow _ _).trans ?_
      have hs : (∑ i : Fin (q + 1), (X (i, j) :
          MvPolynomial (Fin (q + 1) × Fin d) (ZMod (q + 1)))).totalDegree ≤ 1 :=
        totalDegree_finsetSum_le fun i _ => by
          exact (totalDegree_X (R := ZMod (q + 1)) (i, j)).le
      simpa using Nat.mul_le_mul_left q hs
    _ = d * q := by simp

theorem eval_zeroSumDetector (q d : ℕ)
    (y : Fin (q + 1) → FpVec (q + 1) d) :
    eval (fun ij => y ij.1 ij.2) (zeroSumDetector q d) =
      ∏ j : Fin d, (1 - (∑ i : Fin (q + 1), y i j) ^ q) := by
  simp [zeroSumDetector]

/-- The detector is `1` exactly on tuples whose vector sum is zero. -/
theorem eval_zeroSumDetector_eq_one_iff (q d : ℕ) [Fact (q + 1).Prime]
    (y : Fin (q + 1) → FpVec (q + 1) d) :
    eval (fun ij => y ij.1 ij.2) (zeroSumDetector q d) = 1 ↔
      ∑ i, y i = 0 := by
  rw [eval_zeroSumDetector]
  have hq : 0 < q := by
    have hp := (Fact.out : (q + 1).Prime).two_le
    omega
  constructor
  · contrapose!
    intro hsum
    have : ∃ j, ∑ i, y i j ≠ 0 := by
      simpa only [Ne, funext_iff, Pi.zero_apply, not_forall, Finset.sum_apply] using hsum
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ j)]
    · exact zero_ne_one
    · have hpw : (∑ i, y i j) ^ q = 1 := by
        simpa using ZMod.pow_card_sub_one_eq_one hj
      rw [hpw, sub_self]
  · intro hsum
    apply Finset.prod_eq_one
    intro j _
    have hj : ∑ i, y i j = 0 := by
      simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun hsum j
    rw [hj, zero_pow hq.ne']
    simp

/-! ## Monomial contraction -/

/-- Degree contributed by one vector block. -/
def blockDegree {q d : ℕ} (e : (Fin (q + 1) × Fin d) →₀ ℕ)
    (i : Fin (q + 1)) : ℕ :=
  ∑ j, e (i, j)

/-- Value of the part of a monomial belonging to one vector block. -/
def blockValue {q d : ℕ} (e : (Fin (q + 1) × Fin d) →₀ ℕ)
    (i : Fin (q + 1)) (x : Fin d → K) : K :=
  ∏ j, x j ^ e (i, j)

theorem sum_blockDegree {q d : ℕ} (e : (Fin (q + 1) × Fin d) →₀ ℕ) :
    ∑ i, blockDegree e i = e.sum fun _ n => n := by
  simp [blockDegree, Fintype.sum_prod_type, Finsupp.sum_fintype]

theorem fullMonomialValue_eq_blocks {q d : ℕ}
    (e : (Fin (q + 1) × Fin d) →₀ ℕ)
    (y : Fin (q + 1) → Fin d → K) :
    ∏ ij, y ij.1 ij.2 ^ e ij = ∏ i, blockValue e i (y i) := by
  rw [Fintype.prod_prod_type]
  rfl

/-- Every supported detector monomial either has low degree in one of the
first `q` blocks, or degree zero in the last block. -/
theorem low_block_or_last_zero {q d : ℕ} [Fact (q + 1).Prime]
    {e : (Fin (q + 1) × Fin d) →₀ ℕ}
    (he : e ∈ (zeroSumDetector q d).support) :
    (∃ k : Fin q, blockDegree e k.castSucc ≤ d - 1) ∨
      blockDegree e (Fin.last q) = 0 := by
  by_cases hlow : ∃ k : Fin q, blockDegree e k.castSucc ≤ d - 1
  · exact Or.inl hlow
  · right
    push Not at hlow
    have hfirst : d * q ≤ ∑ k : Fin q, blockDegree e k.castSucc := by
      simpa [mul_comm] using
        (Finset.sum_le_sum fun k (_hk : k ∈ Finset.univ) =>
          Order.le_of_sub_one_lt (hlow k))
    have htotal :
        (∑ k : Fin q, blockDegree e k.castSucc) +
            blockDegree e (Fin.last q) ≤ d * q := by
      rw [← Fin.sum_univ_castSucc, sum_blockDegree]
      exact (le_totalDegree he).trans (totalDegree_zeroSumDetector_le q d)
    omega

theorem blockValue_last_eq_one_of_degree_zero {q d : ℕ}
    (e : (Fin (q + 1) × Fin d) →₀ ℕ) (x : Fin d → K)
    (he : blockDegree e (Fin.last q) = 0) :
    blockValue e (Fin.last q) x = 1 := by
  apply Finset.prod_eq_one
  intro j _
  have hej : e (Fin.last q, j) = 0 := by
    exact Finset.sum_eq_zero_iff.mp he j (Finset.mem_univ j)
  simp [hej]

/-- Contribution of one detector monomial after contracting its first `q`
blocks. -/
def weightedMonomialSum {q d n : ℕ} (h : Fin n → K)
    (v : Fin n → Fin d → K) (e : (Fin (q + 1) × Fin d) →₀ ℕ)
    (t : Fin n) : K :=
  ∑ a : Fin q → Fin n,
    ((∏ k, h (a k)) * ∏ k, blockValue e k.castSucc (v (a k))) *
      blockValue e (Fin.last q) (v t)

theorem sum_weighted_blockValues_eq_prod_sums {q d n : ℕ}
    (h : Fin n → K) (v : Fin n → Fin d → K)
    (e : (Fin (q + 1) × Fin d) →₀ ℕ) :
    (∑ a : Fin q → Fin n,
        (∏ k, h (a k)) * ∏ k, blockValue e k.castSucc (v (a k))) =
      ∏ k : Fin q, ∑ i, h i * blockValue e k.castSucc (v i) := by
  simpa only [Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun k : Fin q => fun i : Fin n =>
      h i * blockValue e k.castSucc (v i))).symm

theorem weightedMonomialSum_eq_of_support {q d n : ℕ} [Fact (q + 1).Prime]
    {h : Fin n → ZMod (q + 1)} {v : Fin n → FpVec (q + 1) d}
    (ha : AnnihilatesLow h v) {e : (Fin (q + 1) × Fin d) →₀ ℕ}
    (he : e ∈ (zeroSumDetector q d).support) (t u : Fin n) :
    weightedMonomialSum h v e t = weightedMonomialSum h v e u := by
  rcases low_block_or_last_zero he with ⟨k, hk⟩ | hlast
  · have hzero : ∑ i, h i * blockValue e k.castSucc (v i) = 0 := by
      exact ha (fun j => e (k.castSucc, j)) hk
    have hpzero :
        (∏ k : Fin q, ∑ i, h i * blockValue e k.castSucc (v i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) hzero
    simp only [weightedMonomialSum]
    rw [← Finset.sum_mul, ← Finset.sum_mul,
      sum_weighted_blockValues_eq_prod_sums, hpzero]
    simp
  · have ht := blockValue_last_eq_one_of_degree_zero e (v t) hlast
    have hu := blockValue_last_eq_one_of_degree_zero e (v u) hlast
    simp only [weightedMonomialSum, ht, hu]

/-! ## The contracted detector -/

/-- Append the final vector block to the `q` contracted blocks. -/
def tupleWithLast {q d n : ℕ} (v : Fin n → FpVec (q + 1) d)
    (a : Fin q → Fin n) (t : Fin n) : Fin (q + 1) → FpVec (q + 1) d :=
  Fin.snoc (fun k : Fin q => v (a k)) (v t)

/-- The corresponding tuple of indices. -/
def indexTuple {q n : ℕ} (a : Fin q → Fin n) (t : Fin n) :
    Fin (q + 1) → Fin n :=
  Fin.snoc a t

/-- Contract the detector against `h` in its first `q` blocks. -/
def phi {q d n : ℕ} (h : Fin n → ZMod (q + 1))
    (v : Fin n → FpVec (q + 1) d) (t : Fin n) : ZMod (q + 1) :=
  ∑ a : Fin q → Fin n, (∏ k, h (a k)) *
    eval (fun ij => tupleWithLast v a t ij.1 ij.2) (zeroSumDetector q d)

theorem phi_eq_support_sum {q d n : ℕ} [Fact (q + 1).Prime]
    (h : Fin n → ZMod (q + 1)) (v : Fin n → FpVec (q + 1) d)
    (t : Fin n) :
    phi h v t = ∑ e ∈ (zeroSumDetector q d).support,
      (zeroSumDetector q d).coeff e * weightedMonomialSum h v e t := by
  classical
  simp only [phi, eval_eq']
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp only [weightedMonomialSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [fullMonomialValue_eq_blocks, Fin.prod_univ_castSucc]
  simp only [tupleWithLast, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The low-moment conditions make `phi` independent of its final argument. -/
theorem phi_eq_of_annihilatesLow {q d n : ℕ} [Fact (q + 1).Prime]
    {h : Fin n → ZMod (q + 1)} {v : Fin n → FpVec (q + 1) d}
    (ha : AnnihilatesLow h v) (t u : Fin n) : phi h v t = phi h v u := by
  rw [phi_eq_support_sum, phi_eq_support_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [weightedMonomialSum_eq_of_support ha he]

/-- Operational hollowness specialized to a `Fin (q + 1)` tuple. -/
theorem isPHollow_sum_zero_iff_constant {q d n : ℕ}
    {v : Fin n → FpVec (q + 1) d} (hv : IsPHollow (q + 1) v)
    (a : Fin (q + 1) → Fin n) :
    (∑ k, v (a k) = 0) ↔ ∃ i, ∀ k, a k = i :=
  hv.sum_fin_eq_zero_iff_constant a

/-- On a hollow family, the detector is supported exactly on constant index
tuples. -/
theorem isPHollow_detector_on_tuple {q d n : ℕ} [Fact (q + 1).Prime]
    {v : Fin n → FpVec (q + 1) d} (hv : IsPHollow (q + 1) v)
    (a : Fin (q + 1) → Fin n) :
    eval (fun ij => v (a ij.1) ij.2) (zeroSumDetector q d) =
      if ∃ i, ∀ k, a k = i then 1 else 0 := by
  by_cases hc : ∃ i, ∀ k, a k = i
  · rw [ite_eq_left hc]
    exact (eval_zeroSumDetector_eq_one_iff q d (fun i => v (a i))).mpr
      ((isPHollow_sum_zero_iff_constant hv a).mpr hc)
  · rw [ite_eq_right hc]
    have hsum : ∑ k, v (a k) ≠ 0 :=
      fun h => hc ((isPHollow_sum_zero_iff_constant hv a).mp h)
    rw [eval_zeroSumDetector q d (fun i => v (a i))]
    obtain ⟨j, hj⟩ : ∃ j, ∑ i, v (a i) j ≠ 0 := by
      simpa only [Ne, funext_iff, Pi.zero_apply, not_forall, Finset.sum_apply] using hsum
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hpw : (∑ i, v (a i) j) ^ q = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one hj
    rw [hpw, sub_self]

theorem isPHollow_detector_tupleWithLast {q d n : ℕ} [Fact (q + 1).Prime]
    {v : Fin n → FpVec (q + 1) d} (hv : IsPHollow (q + 1) v)
    (a : Fin q → Fin n) (t : Fin n) :
    eval (fun ij => tupleWithLast v a t ij.1 ij.2) (zeroSumDetector q d) =
      if a = fun _ => t then 1 else 0 := by
  have htuple : tupleWithLast v a t = fun i => v (indexTuple a t i) := by
    funext i j
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [tupleWithLast, indexTuple]
  rw [htuple]
  rw [isPHollow_detector_on_tuple hv (indexTuple a t)]
  congr 1
  apply propext
  constructor
  · rintro ⟨i, hi⟩
    funext k
    have hk := hi k.castSucc
    have ht := hi (Fin.last q)
    simpa only [indexTuple, Fin.snoc_castSucc, Fin.snoc_last] using hk.trans ht.symm
  · rintro rfl
    refine ⟨t, ?_⟩
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k <;> simp [indexTuple]

/-- Hollowness gives the first computation of the contraction:
`phi(t) = h(t)^q`. -/
theorem phi_eq_pow_of_isPHollow {q d n : ℕ} [Fact (q + 1).Prime]
    {v : Fin n → FpVec (q + 1) d} (hv : IsPHollow (q + 1) v)
    (h : Fin n → ZMod (q + 1)) (t : Fin n) : phi h v t = h t ^ q := by
  classical
  simp [phi, isPHollow_detector_tupleWithLast hv]

/-- Pointwise polynomial bound for a modulus written as the prime `q + 1`. -/
theorem phollow_length_le_succ_choose {q d n : ℕ} [Fact (q + 1).Prime]
    (hd : 1 ≤ d) {v : Fin n → FpVec (q + 1) d}
    (hv : IsPHollow (q + 1) v) :
    n ≤ (2 * d - 1).choose d + 1 := by
  by_contra hnle
  have hn : (2 * d - 1).choose d + 2 ≤ n := by omega
  let t₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨h, hh, ht₀, ha⟩ := exists_annihilator' hd hn v t₀
  have hnonzero : ∃ t, h t ≠ 0 := by
    simpa only [Ne, funext_iff, Pi.zero_apply, not_forall] using hh
  obtain ⟨t, ht⟩ := hnonzero
  have hconst := phi_eq_of_annihilatesLow ha t₀ t
  rw [phi_eq_pow_of_isPHollow hv, phi_eq_pow_of_isPHollow hv, ht₀] at hconst
  have hq : 0 < q := by
    have hp := (Fact.out : (q + 1).Prime).two_le
    omega
  rw [zero_pow hq.ne'] at hconst
  exact (pow_ne_zero q ht) hconst.symm

end Polynomial

/-! ## Proposition `thw` and the bound on `𝔴` -/

namespace IsPHollow

/-- **Proposition `thw`.** Every `p`-hollow family in positive dimension has
at most `choose (2d - 1) d + 1` members. -/
theorem card_le_choose_add_one {p d s : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    {v : Fin s → FpVec p d} (hv : IsPHollow p v) :
    s ≤ (2 * d - 1).choose d + 1 := by
  cases p with
  | zero => exact (hp.ne_zero rfl).elim
  | succ q =>
      letI : Fact (q + 1).Prime := ⟨by simpa using hp⟩
      exact Polynomial.phollow_length_le_succ_choose hd hv

end IsPHollow

/-- The polynomial upper bound on the extremal hollow number. -/
theorem hollowConstant_le_choose_add_one {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d) :
    hollowConstant p d ≤ (2 * d - 1).choose d + 1 := by
  obtain ⟨v, hv⟩ := hollowConstant_spec hp
  exact hv.card_le_choose_add_one hp hd

/-- For fixed positive `d`, `𝔴(𝔽_p^d)` is bounded independently of the
prime.  This is the form used by the asymptotic bridge. -/
theorem exists_uniform_hollowConstant_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℕ, ∀ p : ℕ, p.Prime → hollowConstant p d ≤ C :=
  ⟨(2 * d - 1).choose d + 1,
    fun _p hp => hollowConstant_le_choose_add_one hp hd⟩

end EGZ
