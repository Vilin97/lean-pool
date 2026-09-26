/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFraction
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.LeadingGrade
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.CoefficientMap
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.FieldTheory.Minpoly.Basic

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# Degrees in a homogenized algebraic relation

An element of the fraction field of `P̂` that is algebraic over the
coefficient field satisfies a monic relation which, after clearing denominators, becomes a sum of
terms `B ^ e * C ^ f` with `e + f` constant. Because the degree is a multiplicative valuation, the
degree of such a term is `e` copies of `deg B` plus `f` copies of `deg C`, the sum taken in the
Hessenberg (natural) arithmetic of `NatOrdinal`.

This file records the arithmetic that forces the two degrees to agree. Natural addition is
cancellative and strictly monotone and natural multiplication by a positive factor is strictly
monotone, so if the two degrees differed, the degrees of the individual terms would be pairwise
distinct and the term of largest degree could not be cancelled by the others. The consequence
recorded here is the contrapositive: distinct terms of equal degree force `deg B = deg C`.

Where the source argument passes from a relation among leading homogeneous components back to a
degree bound on a combination of representatives, it cites LM24, Lemma 4.2.5. That appeal is
discharged here by the quotient presentation of `P_α` instead: `principalComponentMk_eq_zero_iff`
identifies the vanishing of a class with a degree drop of any representative, and additivity of
the class map turns the homogeneous relation into the required bound. No separate formalization of
the printed lemma is used.
-/

universe v

open scoped HahnSeries NatOrdinal

namespace Berarducci

open HahnSeries.Nonpositive

public noncomputable section

/-- Along a homogenized relation the term degrees are strictly antitone in the exponent of the
smaller of the two degrees. -/
theorem natOrdinal_termDegree_lt_of_lt {beta gamma : NatOrdinal} (h : beta < gamma)
    {e f e' f' : ℕ} (hsum : e + f = e' + f') (hlt : e < e') :
    (e' : NatOrdinal) * beta + (f' : NatOrdinal) * gamma <
      (e : NatOrdinal) * beta + (f : NatOrdinal) * gamma := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
  have hm0 : 0 < m + 1 := Nat.succ_pos m
  have hf : f = f' + (m + 1) := by omega
  have hmul : ((m + 1 : ℕ) : NatOrdinal) * beta < ((m + 1 : ℕ) : NatOrdinal) * gamma := by
    refine mul_lt_mul_of_pos_left h ?_
    exact_mod_cast hm0
  have hleft : (e' : NatOrdinal) * beta + (f' : NatOrdinal) * gamma =
      ((e : NatOrdinal) * beta + (f' : NatOrdinal) * gamma) +
        ((m + 1 : ℕ) : NatOrdinal) * beta := by
    rw [hm]
    push_cast
    ring
  have hright : (e : NatOrdinal) * beta + (f : NatOrdinal) * gamma =
      ((e : NatOrdinal) * beta + (f' : NatOrdinal) * gamma) +
        ((m + 1 : ℕ) : NatOrdinal) * gamma := by
    rw [hf]
    push_cast
    ring
  rw [hleft, hright]
  exact add_lt_add_of_le_of_lt le_rfl hmul

/-- If `β ≠ γ`, two distinct exponent pairs with the same total exponent have distinct
`β, γ`-weighted degrees. -/
theorem natOrdinal_termDegree_ne {beta gamma : NatOrdinal} (h : beta ≠ gamma)
    {e f e' f' : ℕ} (hsum : e + f = e' + f') (hne : e ≠ e') :
    (e : NatOrdinal) * beta + (f : NatOrdinal) * gamma ≠
      (e' : NatOrdinal) * beta + (f' : NatOrdinal) * gamma := by
  have hswap : ∀ a b : ℕ, (a : NatOrdinal) * beta + (b : NatOrdinal) * gamma =
      (b : NatOrdinal) * gamma + (a : NatOrdinal) * beta := fun a b ↦ add_comm _ _
  rcases lt_or_gt_of_ne h with hbg | hbg
  · rcases lt_or_gt_of_ne hne with hee | hee
    · exact (natOrdinal_termDegree_lt_of_lt hbg hsum hee).ne'
    · exact (natOrdinal_termDegree_lt_of_lt hbg hsum.symm hee).ne
  · have hfne : f ≠ f' := by omega
    rw [hswap e f, hswap e' f']
    rcases lt_or_gt_of_ne hfne with hff | hff
    · exact (natOrdinal_termDegree_lt_of_lt hbg (by omega : f + e = f' + e') hff).ne'
    · exact (natOrdinal_termDegree_lt_of_lt hbg (by omega : f' + e' = f + e) hff).ne

/-! ### Multiplicativity of the leading grade on `P̂` -/

variable {K : Type v} [Field K] [CharZero K]

/-- Nonzero homogeneous classes have nonzero product: `P̂` is a domain, and
the product of the homogeneous inclusions is the inclusion of the graded product. -/
theorem principalComponent_gMul_ne_zero {i j : NatOrdinal}
    (a : PrincipalComponent K i) (b : PrincipalComponent K j) (ha : a ≠ 0) (hb : b ≠ 0) :
    GradedMonoid.GMul.mul a b ≠ 0 := by
  intro hzero
  have hprod :
      (DirectSum.of (PrincipalComponent K) i a) *
        (DirectSum.of (PrincipalComponent K) j b) = 0 := by
    rw [DirectSum.of_mul_of, hzero, map_zero]
  rcases mul_eq_zero.mp hprod with h | h
  · exact ha (DirectSum.of_injective i (by rw [h, map_zero]))
  · exact hb (DirectSum.of_injective j (by rw [h, map_zero]))

/-- On `P̂` the leading grade is additive on products. -/
theorem leadingGrade_mul_principalGraded (x y : PrincipalSubring K) :
    DirectSum.leadingGrade (PrincipalComponent K) (x * y) =
      DirectSum.leadingGrade (PrincipalComponent K) x +
        DirectSum.leadingGrade (PrincipalComponent K) y :=
  DirectSum.leadingGrade_mul (PrincipalComponent K)
    (fun a b ha hb ↦ principalComponent_gMul_ne_zero a b ha hb) x y

omit [CharZero K] in
variable (K) in
/-- The unit has leading grade zero. -/
theorem leadingGrade_one_principalGraded :
    DirectSum.leadingGrade (PrincipalComponent K) (1 : PrincipalSubring K) =
      ((0 : NatOrdinal) : WithBot NatOrdinal) := by
  have hone : (GradedMonoid.GOne.one : PrincipalComponent K 0) ≠ 0 := by
    intro hzero
    have : (1 : PrincipalSubring K) = 0 := by
      rw [DirectSum.one_def, hzero, map_zero]
    exact one_ne_zero this
  rw [DirectSum.one_def]
  exact DirectSum.leadingGrade_of (PrincipalComponent K) hone

/-- The leading grade of a power multiplies the leading grade by the exponent. -/
theorem leadingGrade_pow_principalGraded {x : PrincipalSubring K} {beta : NatOrdinal}
    (hx : DirectSum.leadingGrade (PrincipalComponent K) x = (beta : WithBot NatOrdinal))
    (n : ℕ) :
    DirectSum.leadingGrade (PrincipalComponent K) (x ^ n) =
      (((n : NatOrdinal) * beta : NatOrdinal) : WithBot NatOrdinal) := by
  induction n with
  | zero => simpa using leadingGrade_one_principalGraded K
  | succ n ih =>
    rw [pow_succ, leadingGrade_mul_principalGraded, ih, hx, ← WithBot.coe_add]
    congr 1
    push_cast
    ring

omit [CharZero K] in
/-- Adding an element of strictly smaller leading grade leaves the leading grade unchanged. This
is the step that makes a uniquely maximal term impossible to cancel. -/
theorem leadingGrade_add_eq_of_lt {x y : PrincipalSubring K}
    (h : DirectSum.leadingGrade (PrincipalComponent K) y <
      DirectSum.leadingGrade (PrincipalComponent K) x) :
    DirectSum.leadingGrade (PrincipalComponent K) (x + y) =
      DirectSum.leadingGrade (PrincipalComponent K) x := by
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, DirectSum.leadingGrade_zero] at h
    exact (not_lt_bot h).elim
  obtain ⟨m, hm, hxm⟩ := DirectSum.exists_grade_eq_leadingGrade (PrincipalComponent K) hx
  have hym : y m = 0 := by
    by_contra hne
    exact absurd (DirectSum.grade_le_leadingGrade (PrincipalComponent K) hne)
      (not_le.mpr (by rw [hm] at h; exact h))
  refine le_antisymm ?_ ?_
  · refine (DirectSum.leadingGrade_add_le_max (PrincipalComponent K) x y).trans ?_
    exact max_le le_rfl h.le
  · rw [hm]
    refine DirectSum.grade_le_leadingGrade (PrincipalComponent K) ?_
    rw [DirectSum.add_apply, hym, add_zero]
    exact hxm

/-! ### A uniquely maximal term cannot cancel -/

omit [CharZero K] in
/-- The leading grade of a finite sum is at most the supremum of the leading grades. -/
theorem leadingGrade_finsetSum_le {iota : Type*}
    (s : Finset iota) (g : iota → PrincipalSubring K) :
    DirectSum.leadingGrade (PrincipalComponent K) (∑ i ∈ s, g i) ≤
      s.sup fun i ↦ DirectSum.leadingGrade (PrincipalComponent K) (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [DirectSum.leadingGrade_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact (DirectSum.leadingGrade_add_le_max (PrincipalComponent K) _ _).trans
      (max_le_max le_rfl ih)

omit [CharZero K] in
/-- A finite sum in which one nonzero term has strictly largest leading grade has that leading
grade. In particular such a sum cannot vanish, which is what forbids the degrees of two distinct
terms of the homogenized relation from being separated. -/
theorem leadingGrade_finsetSum_eq_of_unique_max
    {iota : Type*} (s : Finset iota) (g : iota → PrincipalSubring K)
    {i₀ : iota} (hi₀ : i₀ ∈ s) (hg₀ : g i₀ ≠ 0)
    (hmax : ∀ i ∈ s, i ≠ i₀ →
      DirectSum.leadingGrade (PrincipalComponent K) (g i) <
        DirectSum.leadingGrade (PrincipalComponent K) (g i₀)) :
    DirectSum.leadingGrade (PrincipalComponent K) (∑ i ∈ s, g i) =
      DirectSum.leadingGrade (PrincipalComponent K) (g i₀) := by
  classical
  have hbot : (⊥ : WithBot NatOrdinal) <
      DirectSum.leadingGrade (PrincipalComponent K) (g i₀) :=
    bot_lt_iff_ne_bot.mpr fun hb ↦
      hg₀ ((DirectSum.leadingGrade_eq_bot_iff (PrincipalComponent K) _).mp hb)
  rw [← Finset.add_sum_erase s g hi₀]
  refine leadingGrade_add_eq_of_lt ?_
  refine lt_of_le_of_lt (leadingGrade_finsetSum_le _ g) ?_
  exact (Finset.sup_lt_iff hbot).mpr fun i hi ↦
    hmax i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

/-! ### The two degrees of a homogenized relation agree -/

omit [CharZero K] in
/-- A nonzero scalar has leading grade zero. -/
theorem leadingGrade_algebraMap_of_ne_zero {a : K}
    (ha : a ≠ 0) :
    DirectSum.leadingGrade (PrincipalComponent K) (algebraMap K (PrincipalSubring K) a) =
      ((0 : NatOrdinal) : WithBot NatOrdinal) := by
  rw [principalSubring_algebraMap_apply]
  refine DirectSum.leadingGrade_of (PrincipalComponent K) ?_
  intro hzero
  exact ha (principalComponentScalarHom_injective K (by rw [hzero, map_zero]))

/-- The leading grade of a term of a homogenized relation. -/
theorem leadingGrade_relationTerm {a : K} (ha : a ≠ 0)
    {B C : PrincipalSubring K} {beta gamma : NatOrdinal}
    (hB : DirectSum.leadingGrade (PrincipalComponent K) B = (beta : WithBot NatOrdinal))
    (hC : DirectSum.leadingGrade (PrincipalComponent K) C = (gamma : WithBot NatOrdinal))
    (i f : ℕ) :
    DirectSum.leadingGrade (PrincipalComponent K)
        (algebraMap K (PrincipalSubring K) a * B ^ i * C ^ f) =
      (((i : NatOrdinal) * beta + (f : NatOrdinal) * gamma : NatOrdinal) :
        WithBot NatOrdinal) := by
  rw [leadingGrade_mul_principalGraded, leadingGrade_mul_principalGraded,
    leadingGrade_algebraMap_of_ne_zero ha,
    leadingGrade_pow_principalGraded hB, leadingGrade_pow_principalGraded hC,
    ← WithBot.coe_add, ← WithBot.coe_add, zero_add]

/-- The two degrees of a homogenized relation agree. If `∑ i, k i * B ^ i * C ^ (d - i) = 0` with
top coefficient nonzero and `B`, `C` nonzero, then `B` and `C` have the same leading grade:
otherwise the term degrees would be pairwise distinct, so the term of largest degree could not be
cancelled and the sum could not vanish. -/
theorem leadingGrade_eq_of_relation {B C : PrincipalSubring K} (hB : B ≠ 0) (hC : C ≠ 0)
    {d : ℕ} (k : ℕ → K) (hkd : k d ≠ 0)
    (hrel : ∑ i ∈ Finset.range (d + 1),
      algebraMap K (PrincipalSubring K) (k i) * B ^ i * C ^ (d - i) = 0) :
    DirectSum.leadingGrade (PrincipalComponent K) B =
      DirectSum.leadingGrade (PrincipalComponent K) C := by
  classical
  obtain ⟨beta, hbeta⟩ := WithBot.ne_bot_iff_exists.mp
    (fun hb ↦ hB ((DirectSum.leadingGrade_eq_bot_iff (PrincipalComponent K) B).mp hb))
  obtain ⟨gamma, hgamma⟩ := WithBot.ne_bot_iff_exists.mp
    (fun hb ↦ hC ((DirectSum.leadingGrade_eq_bot_iff (PrincipalComponent K) C).mp hb))
  rw [← hbeta, ← hgamma]
  by_contra hne
  have hbg : beta ≠ gamma := fun h ↦ hne (by rw [h])
  obtain ⟨i₀, hi₀S, hi₀max⟩ :=
    ((Finset.range (d + 1)).filter fun i ↦ k i ≠ 0).exists_max_image
      (fun i ↦ (i : NatOrdinal) * beta + ((d - i : ℕ) : NatOrdinal) * gamma)
      ⟨d, Finset.mem_filter.mpr ⟨Finset.self_mem_range_succ d, hkd⟩⟩
  have hi₀range : i₀ ∈ Finset.range (d + 1) := (Finset.mem_filter.mp hi₀S).1
  have hk₀ : k i₀ ≠ 0 := (Finset.mem_filter.mp hi₀S).2
  have hgrade₀ := leadingGrade_relationTerm hk₀ hbeta.symm hgamma.symm i₀ (d - i₀)
  have hg₀ : algebraMap K (PrincipalSubring K) (k i₀) * B ^ i₀ * C ^ (d - i₀) ≠ 0 := by
    intro hzero
    rw [hzero, DirectSum.leadingGrade_zero] at hgrade₀
    exact WithBot.coe_ne_bot hgrade₀.symm
  have hsum := leadingGrade_finsetSum_eq_of_unique_max (Finset.range (d + 1))
    (fun i ↦ algebraMap K (PrincipalSubring K) (k i) * B ^ i * C ^ (d - i))
    hi₀range hg₀ (fun i hi hine ↦ ?_)
  · rw [hrel, DirectSum.leadingGrade_zero, hgrade₀] at hsum
    exact WithBot.coe_ne_bot hsum.symm
  · by_cases hki : k i = 0
    · have hzero : algebraMap K (PrincipalSubring K) (k i) * B ^ i * C ^ (d - i) = 0 := by
        rw [hki, map_zero, zero_mul, zero_mul]
      rw [hzero, DirectSum.leadingGrade_zero, hgrade₀]
      exact bot_lt_iff_ne_bot.mpr WithBot.coe_ne_bot
    · rw [leadingGrade_relationTerm hki hbeta.symm hgamma.symm i (d - i), hgrade₀,
        WithBot.coe_lt_coe]
      refine lt_of_le_of_ne (hi₀max i (Finset.mem_filter.mpr ⟨hi, hki⟩)) ?_
      have hile : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hi₀le : i₀ ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi₀range)
      exact natOrdinal_termDegree_ne hbg (by omega) hine

/-! ### Homogenizing a split polynomial -/

/-- Scaling the roots of a product of monic linear factors and evaluating produces the
homogenized linear factors. This is the identity that turns the cleared relation into a product
over the roots of the minimal polynomial. -/
theorem eval_scaleRoots_prod_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] (s : Multiset R)
    (b c : R) :
    Polynomial.eval b
        ((s.map fun z ↦ Polynomial.X - Polynomial.C z).prod.scaleRoots c) =
      (s.map fun z ↦ b - z * c).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons z t ih =>
    have hmonic : (t.map fun z ↦ Polynomial.X - Polynomial.C z).prod.Monic :=
      Polynomial.monic_multiset_prod_of_monic t _ fun w _ ↦ Polynomial.monic_X_sub_C w
    have hlead : (Polynomial.X - Polynomial.C z).leadingCoeff *
        (t.map fun z ↦ Polynomial.X - Polynomial.C z).prod.leadingCoeff ≠ 0 := by
      rw [(Polynomial.monic_X_sub_C z).leadingCoeff, hmonic.leadingCoeff, one_mul]
      exact one_ne_zero
    have hlin : (Polynomial.X - Polynomial.C z).scaleRoots c =
        Polynomial.X - Polynomial.C (z * c) := by
      have := Polynomial.X_add_C_scaleRoots (-z) c
      rwa [map_neg, ← sub_eq_add_neg, neg_mul, map_neg, ← sub_eq_add_neg] at this
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_scaleRoots' _ _ _ hlead, hlin,
      Polynomial.eval_mul, ih, Multiset.map_cons, Multiset.prod_cons]
    simp

/-! ### Passing to leading terms -/

omit [CharZero K] in
/-- The leading term of a product is the product of the leading terms. Stated in the graded ring
itself rather than in its homogeneous components, so no grade casts appear. -/
theorem of_apply_add_mul {x y : PrincipalSubring K}
    {m n : NatOrdinal}
    (hx : DirectSum.leadingGrade (PrincipalComponent K) x = (m : WithBot NatOrdinal))
    (hy : DirectSum.leadingGrade (PrincipalComponent K) y = (n : WithBot NatOrdinal)) :
    DirectSum.of (PrincipalComponent K) (m + n) ((x * y) (m + n)) =
      DirectSum.of (PrincipalComponent K) m (x m) *
        DirectSum.of (PrincipalComponent K) n (y n) := by
  rw [DirectSum.of_mul_of, DirectSum.mul_apply_add_eq_of_leadingGrade_eq _ hx hy]

/-- The leading term of a power is the power of the leading term. -/
theorem of_apply_pow {x : PrincipalSubring K}
    {m : NatOrdinal}
    (hx : DirectSum.leadingGrade (PrincipalComponent K) x = (m : WithBot NatOrdinal)) (i : ℕ) :
    DirectSum.of (PrincipalComponent K) ((i : NatOrdinal) * m)
        ((x ^ i) ((i : NatOrdinal) * m)) =
      (DirectSum.of (PrincipalComponent K) m (x m)) ^ i := by
  induction i with
  | zero =>
    have h1 : (1 : PrincipalSubring K) 0 = GradedMonoid.GOne.one := by
      rw [DirectSum.one_def, DirectSum.of_eq_same]
    rw [pow_zero, pow_zero, Nat.cast_zero, zero_mul, h1]
    exact (DirectSum.one_def (PrincipalComponent K)).symm
  | succ i ih =>
    have hgrade : ((i + 1 : ℕ) : NatOrdinal) * m = (i : NatOrdinal) * m + m := by
      push_cast; ring
    have hshift : DirectSum.of (PrincipalComponent K) (((i + 1 : ℕ) : NatOrdinal) * m)
          ((x ^ (i + 1)) (((i + 1 : ℕ) : NatOrdinal) * m)) =
        DirectSum.of (PrincipalComponent K) ((i : NatOrdinal) * m + m)
          ((x ^ (i + 1)) ((i : NatOrdinal) * m + m)) :=
      DirectSum.of_eq_of_gradedMonoid_eq (by rw [hgrade])
    rw [hshift, pow_succ, pow_succ, ← ih,
      of_apply_add_mul (leadingGrade_pow_principalGraded hx i) hx]

/-- The homogenized relation passes to the leading terms. Every term of the relation has leading
grade `d * beta`, so taking that component turns the relation into the same relation among the
homogeneous leading terms of `B` and `C`. -/
theorem sum_leadingTerm_eq_zero
    {B C : PrincipalSubring K} {beta : NatOrdinal} {d : ℕ} (k : ℕ → K)
    (hB : DirectSum.leadingGrade (PrincipalComponent K) B = (beta : WithBot NatOrdinal))
    (hC : DirectSum.leadingGrade (PrincipalComponent K) C = (beta : WithBot NatOrdinal))
    (hrel : ∑ i ∈ Finset.range (d + 1),
      algebraMap K (PrincipalSubring K) (k i) * B ^ i * C ^ (d - i) = 0) :
    ∑ i ∈ Finset.range (d + 1), algebraMap K (PrincipalSubring K) (k i) *
        (DirectSum.of (PrincipalComponent K) beta (B beta)) ^ i *
        (DirectSum.of (PrincipalComponent K) beta (C beta)) ^ (d - i) = 0 := by
  classical
  have hterm : ∀ i ∈ Finset.range (d + 1),
      DirectSum.of (PrincipalComponent K) ((d : NatOrdinal) * beta)
          ((algebraMap K (PrincipalSubring K) (k i) * B ^ i * C ^ (d - i))
            ((d : NatOrdinal) * beta)) =
        algebraMap K (PrincipalSubring K) (k i) *
          (DirectSum.of (PrincipalComponent K) beta (B beta)) ^ i *
          (DirectSum.of (PrincipalComponent K) beta (C beta)) ^ (d - i) := by
    intro i hi
    have hile : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hgr : (d : NatOrdinal) * beta =
        (i : NatOrdinal) * beta + ((d - i : ℕ) : NatOrdinal) * beta := by
      have : ((d : ℕ) : NatOrdinal) = ((i : ℕ) : NatOrdinal) + ((d - i : ℕ) : NatOrdinal) := by
        rw [← Nat.cast_add]
        congr 1
        omega
      rw [this, add_mul]
    have hshift : DirectSum.of (PrincipalComponent K) ((d : NatOrdinal) * beta)
          ((B ^ i * C ^ (d - i)) ((d : NatOrdinal) * beta)) =
        DirectSum.of (PrincipalComponent K)
            ((i : NatOrdinal) * beta + ((d - i : ℕ) : NatOrdinal) * beta)
          ((B ^ i * C ^ (d - i))
            ((i : NatOrdinal) * beta + ((d - i : ℕ) : NatOrdinal) * beta)) :=
      DirectSum.of_eq_of_gradedMonoid_eq (by rw [hgr])
    have hsmul : (algebraMap K (PrincipalSubring K) (k i) * (B ^ i * C ^ (d - i)))
        ((d : NatOrdinal) * beta) = k i • ((B ^ i * C ^ (d - i)) ((d : NatOrdinal) * beta)) := by
      rw [← Algebra.smul_def]
      rfl
    rw [mul_assoc, hsmul, DirectSum.of_smul, Algebra.smul_def, hshift,
      of_apply_add_mul (leadingGrade_pow_principalGraded hB i)
        (leadingGrade_pow_principalGraded hC (d - i)),
      of_apply_pow hB, of_apply_pow hC, mul_assoc]
  have hfinal : DirectSum.of (PrincipalComponent K) ((d : NatOrdinal) * beta)
      ((∑ i ∈ Finset.range (d + 1),
        algebraMap K (PrincipalSubring K) (k i) * B ^ i * C ^ (d - i))
          ((d : NatOrdinal) * beta)) = 0 := by
    rw [hrel]
    simp
  rw [← Finset.sum_congr rfl hterm, ← map_sum, ← DFinsupp.finsetSum_apply]
  exact hfinal

/-! ### Descending to representatives -/

omit [CharZero K] in
/-- A power of a homogeneous class is the class of the power of a representative. The grade is
written with `nsmul`, for which the successor identity is definitional, so no grade cast
intervenes. -/
theorem of_principalComponentMk_pow {beta : NatOrdinal}
    (b : Series K) (hb : ordinalValue b < ω^ (beta + 1)) (i : ℕ) :
    ∃ h : ordinalValue (b ^ i) < ω^ (i • beta + 1),
      (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta b hb)) ^ i =
        DirectSum.of (PrincipalComponent K) (i • beta)
          (principalComponentMk (i • beta) (b ^ i) h) := by
  induction i with
  | zero =>
    have h0 : ordinalValue ((b : Series K) ^ 0) < ω^ ((0 : ℕ) • beta + 1) := by
      rw [pow_zero, ordinalValue_one, zero_nsmul, zero_add]
      simpa using NatOrdinal.wpow_lt_wpow.mpr (zero_lt_one : (0 : NatOrdinal) < 1)
    refine ⟨h0, ?_⟩
    rw [pow_zero, DirectSum.one_def]
    congr 1
    have hone : (GradedMonoid.GOne.one : PrincipalComponent K 0) =
        (ordinalValueDegreeValuation K).componentOne := rfl
    rw [hone, MaxAddDegree.componentOne_eq_componentMk]
    simp only [pow_zero]
    rw [principalComponentMk_eq_componentMk]
    rfl
  | succ i ih =>
    obtain ⟨hi, hstep⟩ := ih
    have hbound : ordinalValue (b ^ (i + 1)) < ω^ ((i + 1) • beta + 1) := by
      have h := ordinalValue_mul_lt_wpow_add_one hi hb
      rwa [← pow_succ] at h
    refine ⟨hbound, ?_⟩
    rw [pow_succ, hstep, DirectSum.of_mul_of]
    congr 1
    rw [show (GradedMonoid.GMul.mul
          (principalComponentMk (i • beta) (b ^ i) hi)
          (principalComponentMk beta b hb)) =
        principalComponentMul _ _ from
      (principalComponentMul_eq_componentMul _ _).symm,
      principalComponentMul_mk]
    congr 1

omit [CharZero K] in
/-- A product of powers of two homogeneous classes is the class of the corresponding product of
representatives. -/
theorem of_principalComponentMk_pow_mul_pow {beta : NatOrdinal}
    (b c : Series K) (hb : ordinalValue b < ω^ (beta + 1)) (hc : ordinalValue c < ω^ (beta + 1))
    (i j : ℕ) :
    ∃ h : ordinalValue (b ^ i * c ^ j) < ω^ (i • beta + j • beta + 1),
      (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta b hb)) ^ i *
          (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta c hc)) ^ j =
        DirectSum.of (PrincipalComponent K) (i • beta + j • beta)
          (principalComponentMk (i • beta + j • beta) (b ^ i * c ^ j) h) := by
  obtain ⟨hi, hpi⟩ := of_principalComponentMk_pow b hb i
  obtain ⟨hj, hpj⟩ := of_principalComponentMk_pow c hc j
  refine ⟨ordinalValue_mul_lt_wpow_add_one hi hj, ?_⟩
  rw [hpi, hpj, DirectSum.of_mul_of]
  congr 1
  rw [show (GradedMonoid.GMul.mul
        (principalComponentMk (i • beta) (b ^ i) hi)
        (principalComponentMk (j • beta) (c ^ j) hj)) =
      principalComponentMul _ _ from
    (principalComponentMul_eq_componentMul _ _).symm,
    principalComponentMul_mk]

omit [CharZero K] in
/-- The same statement with the grade presented in normalized form. -/
theorem of_principalComponentMk_pow_mul_pow' {beta : NatOrdinal}
    (b c : Series K) (hb : ordinalValue b < ω^ (beta + 1)) (hc : ordinalValue c < ω^ (beta + 1))
    (i j : ℕ) {p : NatOrdinal} (hp : i • beta + j • beta = p) :
    ∃ h : ordinalValue (b ^ i * c ^ j) < ω^ (p + 1),
      (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta b hb)) ^ i *
          (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta c hc)) ^ j =
        DirectSum.of (PrincipalComponent K) p
          (principalComponentMk p (b ^ i * c ^ j) h) := by
  subst hp
  exact of_principalComponentMk_pow_mul_pow b c hb hc i j

omit [CharZero K] in
/-- The class of a finite sum of representatives is the sum of the classes. -/
theorem principalComponentMk_finsetSum {iota : Type*}
    (s : Finset iota) (alpha : NatOrdinal) (u : iota → Series K)
    (hu : ∀ i, ordinalValue (u i) < ω^ (alpha + 1))
    (hsum : ordinalValue (∑ i ∈ s, u i) < ω^ (alpha + 1)) :
    ∑ i ∈ s, principalComponentMk alpha (u i) (hu i) =
      principalComponentMk alpha (∑ i ∈ s, u i) hsum := by
  classical
  simp only [principalComponentMk_eq_componentMk]
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]

omit [CharZero K] in
/-- A finite sum of series each of ordinal value below a positive bound stays below that bound. -/
theorem ordinalValue_finsetSum_lt {iota : Type*} (s : Finset iota) (u : iota → Series K)
    {X : NatOrdinal} (hX : 0 < X) (hu : ∀ i ∈ s, ordinalValue (u i) < X) :
    ordinalValue (∑ i ∈ s, u i) < X := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hX
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (ordinalValue_add_le_max _ _) ?_
    exact max_lt (hu a (Finset.mem_insert_self a t))
      (ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))

omit [CharZero K] in
/-- The relation among leading terms descends to a degree bound on the corresponding combination
of representatives. This is where the source argument's appeal to LM24, Lemma 4.2.5 is replaced
by the intrinsic homogeneous-component interface. -/
theorem ordinalValue_relationSum_lt {beta : NatOrdinal}
    {d : ℕ} (k : ℕ → K) (b c : Series K)
    (hb : ordinalValue b < ω^ (beta + 1)) (hc : ordinalValue c < ω^ (beta + 1))
    (hrel : ∑ i ∈ Finset.range (d + 1),
      algebraMap K (PrincipalSubring K) (k i) *
        (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta b hb)) ^ i *
        (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta c hc)) ^ (d - i)
        = 0) :
    ordinalValue (∑ i ∈ Finset.range (d + 1),
      (HahnSeries.Nonpositive.C : K →+* Series K) (k i) * (b ^ i * c ^ (d - i))) <
      ω^ (d • beta) := by
  classical
  have hterm : ∀ i ∈ Finset.range (d + 1),
      ∃ h : ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) (k i) *
          (b ^ i * c ^ (d - i))) < ω^ (d • beta + 1),
        algebraMap K (PrincipalSubring K) (k i) *
            (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta b hb)) ^ i *
            (DirectSum.of (PrincipalComponent K) beta (principalComponentMk beta c hc)) ^ (d - i) =
          DirectSum.of (PrincipalComponent K) (d • beta)
            (principalComponentMk (d • beta)
              ((HahnSeries.Nonpositive.C : K →+* Series K) (k i) * (b ^ i * c ^ (d - i))) h) := by
    intro i hi
    have hile : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hp : i • beta + (d - i) • beta = d • beta := by
      rw [← add_nsmul]
      congr 1
      omega
    obtain ⟨h1, e1⟩ := of_principalComponentMk_pow_mul_pow' b c hb hc i (d - i) hp
    refine ⟨?_, ?_⟩
    · simpa only [zero_add] using
        ordinalValue_mul_lt_wpow_add_one (ordinalValue_C_lt_wpow_one (k i)) h1
    · rw [mul_assoc, ← Algebra.smul_def, e1, ← DirectSum.of_smul K, smul_principalComponentMk]
  have hupos : (0 : NatOrdinal) < ω^ (d • beta + 1) :=
    lt_of_lt_of_le zero_lt_one
      (by rw [← NatOrdinal.wpow_zero]; exact NatOrdinal.wpow_le_wpow.mpr zero_le)
  classical
  set u : ℕ → Series K := fun i ↦
    if i ∈ Finset.range (d + 1) then
      (HahnSeries.Nonpositive.C : K →+* Series K) (k i) * (b ^ i * c ^ (d - i)) else 0 with hu_def
  have hu : ∀ i : ℕ, ordinalValue (u i) < ω^ (d • beta + 1) := by
    intro i
    by_cases hi : i ∈ Finset.range (d + 1)
    · rw [hu_def]
      simp only [hi, ite_true]
      exact (hterm i hi).choose
    · rw [hu_def]
      simp only [hi, ite_false]
      simp
  have hu_eq : ∀ j ∈ Finset.range (d + 1), u j =
      (HahnSeries.Nonpositive.C : K →+* Series K) (k j) * (b ^ j * c ^ (d - j)) := by
    intro j hj
    rw [hu_def]
    simp only [hj, ite_true]
  have hcongr : ∑ i ∈ Finset.range (d + 1),
      (HahnSeries.Nonpositive.C : K →+* Series K) (k i) * (b ^ i * c ^ (d - i)) =
      ∑ i ∈ Finset.range (d + 1), u i :=
    Finset.sum_congr rfl fun i hi ↦ (hu_eq i hi).symm
  have hsum : ordinalValue (∑ i ∈ Finset.range (d + 1), u i) < ω^ (d • beta + 1) :=
    ordinalValue_finsetSum_lt _ _ hupos fun i _ ↦ hu i
  rw [hcongr, ← principalComponentMk_eq_zero_iff (d • beta) _ hsum,
    ← principalComponentMk_finsetSum (Finset.range (d + 1)) (d • beta) u hu hsum]
  apply DirectSum.of_injective (d • beta)
  rw [map_zero, map_sum, ← hrel]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  obtain ⟨h, e⟩ := hterm i hi
  rw [e]
  congr 1
  rw [principalComponentMk_eq_iff, hu_eq i hi, sub_self]
  simp

omit [CharZero K] in
/-- The homogenized relation sum is the scaled-roots evaluation of the polynomial pushed along a
ring homomorphism out of the coefficient field. -/
theorem eval_scaleRoots_map {R : Type*} [CommRing R] [Nontrivial R] (g : K →+* R)
    (p : Polynomial K) (b c : R) :
    Polynomial.eval b ((p.map g).scaleRoots c) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        g (p.coeff i) * (b ^ i * c ^ (p.natDegree - i)) := by
  have hdeg : (p.map g).natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective g.injective p
  rw [Polynomial.eval_eq_sum_range' (by
    rw [Polynomial.natDegree_scaleRoots, hdeg]
    exact Nat.lt_succ_self _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hdeg]
  ring

omit [CharZero K] in
/-- Coefficient extension carries the homogenized relation sum of a polynomial to that of the
extended polynomial. -/
theorem map_relationSum {E : Type v} [Field E] (f : K →+* E) (p : Polynomial K) (b c : Series K)
    (n : ℕ) :
    nonpositiveCoefficientMap f
        (∑ i ∈ Finset.range (n + 1),
          (HahnSeries.Nonpositive.C : K →+* Series K) (p.coeff i) * (b ^ i * c ^ (n - i))) =
      ∑ i ∈ Finset.range (n + 1),
        (HahnSeries.Nonpositive.C : E →+* Series E) ((p.map f).coeff i) *
          ((nonpositiveCoefficientMap f b) ^ i * (nonpositiveCoefficientMap f c) ^ (n - i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_mul, map_pow, map_pow, nonpositiveCoefficientMap_C, Polynomial.coeff_map]

/-! ### Pigeonhole on the factor degrees -/

/-- If a product of ordinal-value-multiplicative factors has ordinal value below `ω ^ (n * beta)`,
where `n` is the number of factors, then some factor has ordinal value below `ω ^ beta`. -/
theorem exists_ordinalValue_lt_of_prod_lt {E : Type v} [Field E] [CharZero E]
    (s : Multiset (Series E)) (beta : NatOrdinal)
    (h : ordinalValue s.prod < ω^ ((s.card : NatOrdinal) * beta)) :
    ∃ u ∈ s, ordinalValue u < ω^ beta := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have key : ∀ t : Multiset (Series E), (∀ u ∈ t, ω^ beta ≤ ordinalValue u) →
      ω^ ((t.card : NatOrdinal) * beta) ≤ ordinalValue t.prod := by
    intro t
    induction t using Multiset.induction with
    | empty => intro _; simp [ordinalValue_one]
    | cons a u ih =>
      intro hall
      rw [Multiset.prod_cons, ordinalValueMultiplicative.ordinalValue_mul, Multiset.card_cons]
      push_cast
      rw [add_mul, one_mul, NatOrdinal.wpow_add, mul_comm]
      exact mul_le_mul' (hall a (Multiset.mem_cons_self a u))
        (ih fun v hv ↦ hall v (Multiset.mem_cons_of_mem hv))
  exact absurd (key s hcon) (not_le.mpr h)

/-! ### Rationality of a root read off a single exponent -/

/-- The single-exponent rationality step. If, after extending the coefficients along `f`,
subtracting `zeta` times `c` from `b` strictly lowers the ordinal value below that of `b`, then some
exponent must cancel, and at that exponent `zeta` is the ratio of a coefficient of `b` by a
coefficient of `c`. Hence `zeta` lies in the range of `f`.

This is the step of the source argument that returns a root of the minimal polynomial from the
algebraic closure of the coefficient field to the coefficient field itself. -/
theorem mem_range_of_ordinalValue_sub_C_mul_lt {K E : Type v} [Field K] [Field E] (f : K →+* E)
    (b c : HahnSeries.Nonpositive ℝ K) (zeta : E)
    (h : ordinalValue (nonpositiveCoefficientMap f b -
        HahnSeries.Nonpositive.C zeta * nonpositiveCoefficientMap f c) <
      ordinalValue (nonpositiveCoefficientMap f b)) :
    zeta ∈ f.range := by
  by_contra hzeta
  refine absurd (ordinalValue_le_of_support_subset _ _ ?_) (not_le.mpr h)
  intro x hx
  rw [HahnSeries.mem_support] at hx ⊢
  rw [coe_nonpositiveCoefficientMap] at hx
  intro hzero
  apply hzeta
  rw [AddSubgroupClass.coe_sub, HahnSeries.coeff_sub, Subring.coe_mul,
    HahnSeries.Nonpositive.coe_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    coe_nonpositiveCoefficientMap, coe_nonpositiveCoefficientMap, smul_eq_mul,
    sub_eq_zero] at hzero
  have hcx : f ((c : K⟦ℝ⟧).coeff x) ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hzero
    exact hx hzero
  rw [RingHom.mem_range]
  refine ⟨(b : K⟦ℝ⟧).coeff x / (c : K⟦ℝ⟧).coeff x, ?_⟩
  rw [map_div₀, hzero, mul_div_assoc, div_self hcx, mul_one]

/-! ### A root in the coefficient field -/

/-- If the homogenized relation sum of a monic polynomial at two representatives has strictly
smaller degree than the product of the degrees, the polynomial already has a root in the
coefficient field. The source argument factors over the algebraic closure; the ordinal value is
multiplicative there because the multiplicativity theorem is field-polymorphic. -/
theorem exists_isRoot_of_ordinalValue_relationSum_lt {beta : NatOrdinal} {d : ℕ}
    (Q : Polynomial K) (hQ : Q.Monic) (hdeg : Q.natDegree = d) (b c : Series K)
    (hbdeg : ω^ beta ≤ ordinalValue b)
    (hlt : ordinalValue (∑ i ∈ Finset.range (d + 1),
      (HahnSeries.Nonpositive.C : K →+* Series K) (Q.coeff i) * (b ^ i * c ^ (d - i))) <
      ω^ (d • beta)) :
    ∃ z : K, Q.IsRoot z := by
  classical
  set f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hf
  have hQLmonic : (Q.map f).Monic := hQ.map f
  have hQLdeg : (Q.map f).natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective f.injective, hdeg]
  have hsplits : Polynomial.Splits (Q.map f) := IsAlgClosed.splits _
  have hprod : Q.map f = ((Q.map f).roots.map fun z ↦ Polynomial.X - Polynomial.C z).prod :=
    hsplits.eq_prod_roots_of_monic hQLmonic
  have hcard : (Q.map f).roots.card = d := by
    rw [← hQLdeg]
    exact Polynomial.splits_iff_card_roots.mp hsplits
  have hsum_eq : nonpositiveCoefficientMap f
      (∑ i ∈ Finset.range (d + 1),
        (HahnSeries.Nonpositive.C : K →+* Series K) (Q.coeff i) * (b ^ i * c ^ (d - i))) =
      ((Q.map f).roots.map fun z ↦
        nonpositiveCoefficientMap f b -
          (HahnSeries.Nonpositive.C : AlgebraicClosure K →+* Series (AlgebraicClosure K)) z *
            nonpositiveCoefficientMap f c).prod := by
    rw [map_relationSum, ← hQLdeg, ← eval_scaleRoots_map]
    conv_lhs => rw [hprod]
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    have hlin : ∀ z : AlgebraicClosure K,
        ((fun q : Polynomial (AlgebraicClosure K) ↦
            q.map (HahnSeries.Nonpositive.C : AlgebraicClosure K →+* Series (AlgebraicClosure K)))
          ∘ fun z ↦ Polynomial.X - Polynomial.C z) z =
          Polynomial.X - Polynomial.C ((HahnSeries.Nonpositive.C :
            AlgebraicClosure K →+* Series (AlgebraicClosure K)) z) := by
      intro z
      simp
    rw [Multiset.map_congr rfl fun z _ ↦ hlin z]
    rw [show (Multiset.map (fun z ↦ Polynomial.X - Polynomial.C
          ((HahnSeries.Nonpositive.C : AlgebraicClosure K →+* Series (AlgebraicClosure K)) z))
            (Q.map f).roots) =
        Multiset.map (fun w ↦ Polynomial.X - Polynomial.C w)
          (Multiset.map (HahnSeries.Nonpositive.C :
            AlgebraicClosure K →+* Series (AlgebraicClosure K)) (Q.map f).roots) from
      by rw [Multiset.map_map]; rfl,
      eval_scaleRoots_prod_X_sub_C, Multiset.map_map]
    rfl
  have hprodlt : ordinalValue (((Q.map f).roots.map fun z ↦
      nonpositiveCoefficientMap f b -
        (HahnSeries.Nonpositive.C : AlgebraicClosure K →+* Series (AlgebraicClosure K)) z *
          nonpositiveCoefficientMap f c).prod) <
      ω^ ((((Q.map f).roots.map fun z ↦
        nonpositiveCoefficientMap f b -
          (HahnSeries.Nonpositive.C : AlgebraicClosure K →+* Series (AlgebraicClosure K)) z *
            nonpositiveCoefficientMap f c).card : NatOrdinal) * beta) := by
    rw [← hsum_eq, ordinalValue_nonpositiveCoefficientMap, Multiset.card_map, hcard,
      ← nsmul_eq_mul]
    exact hlt
  obtain ⟨w, hw_mem, hw_lt⟩ := exists_ordinalValue_lt_of_prod_lt _ beta hprodlt
  obtain ⟨z, hz_mem, rfl⟩ := Multiset.mem_map.mp hw_mem
  have hzrange : z ∈ f.range := by
    refine mem_range_of_ordinalValue_sub_C_mul_lt f b c z (lt_of_lt_of_le hw_lt ?_)
    rw [ordinalValue_nonpositiveCoefficientMap]
    exact hbdeg
  obtain ⟨z₀, hz₀⟩ := hzrange
  refine ⟨z₀, ?_⟩
  have hroot : (Q.map f).IsRoot z := Polynomial.isRoot_of_mem_roots hz_mem
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← hz₀, Polynomial.eval₂_at_apply] at hroot
  exact f.injective (by rw [hroot, map_zero])

/-! ### Clearing denominators -/

/-- The principal-subring algebra structure used locally when clearing denominators. -/
local instance principalSubringFractionSelfAlgebraLocal :
    Algebra (PrincipalSubring K) (PrincipalSubringFractionField K) :=
  principalSubringFractionSelfAlgebra K

local instance principalSubringFractionIsFractionRingLocal :
    IsFractionRing (PrincipalSubring K) (PrincipalSubringFractionField K) :=
  IsFractionRing.of_algEquiv (principalSubringFractionAlgEquiv K)

/-- The coefficient-field algebra structure used locally when clearing denominators. -/
local instance principalSubringFractionAlgebraLocal :
    Algebra K (PrincipalSubringFractionField K) :=
  principalSubringFractionAlgebra K

/-- Clearing denominators in an algebraic relation satisfied by a nonzero fraction. -/
theorem exists_relation_of_aeval_eq_zero (Q : Polynomial K)
    {x : PrincipalSubringFractionField K} (hQ : Polynomial.aeval x Q = 0) (hx0 : x ≠ 0) :
    ∃ B C : PrincipalSubring K, B ≠ 0 ∧ C ≠ 0 ∧
      ∑ i ∈ Finset.range (Q.natDegree + 1),
        algebraMap K (PrincipalSubring K) (Q.coeff i) * B ^ i *
          C ^ (Q.natDegree - i) = 0 := by
  have : IsScalarTower K (PrincipalSubring K) (PrincipalSubringFractionField K) :=
    principalSubringFraction_isScalarTower K
  have hinj : Function.Injective
      (algebraMap (PrincipalSubring K) (PrincipalSubringFractionField K)) :=
    IsFractionRing.injective _ _
  obtain ⟨⟨B, C⟩, hBC⟩ :=
    IsLocalization.surj (nonZeroDivisors (PrincipalSubring K)) x
  have hCne : (C : PrincipalSubring K) ≠ 0 := nonZeroDivisors.coe_ne_zero C
  have hmapC : algebraMap (PrincipalSubring K) (PrincipalSubringFractionField K)
      (C : PrincipalSubring K) ≠ 0 := fun h ↦ hCne (hinj (by rw [h, map_zero]))
  have hdiv : x =
      algebraMap (PrincipalSubring K) (PrincipalSubringFractionField K) B /
        algebraMap (PrincipalSubring K) (PrincipalSubringFractionField K)
          (C : PrincipalSubring K) :=
    eq_div_of_mul_eq hmapC hBC
  have hBne : B ≠ 0 := by
    intro hB
    exact hx0 (by rw [hdiv, hB, map_zero, zero_div])
  refine ⟨B, (C : PrincipalSubring K), hBne, hCne, ?_⟩
  have haeval : Polynomial.aeval
      (algebraMap (PrincipalSubring K) (PrincipalSubringFractionField K) B /
        algebraMap (PrincipalSubring K) (PrincipalSubringFractionField K)
          (C : PrincipalSubring K))
      (Q.map (algebraMap K (PrincipalSubring K))) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, ← hdiv]
    exact hQ
  have hsr := Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero hinj haeval C.2
  have hmapped : algebraMap (PrincipalSubring K) (PrincipalSubringFractionField K)
      (Polynomial.eval B ((Q.map (algebraMap K (PrincipalSubring K))).scaleRoots
        (C : PrincipalSubring K))) = 0 := by
    rw [← hsr, Polynomial.aeval_def, Polynomial.eval₂_at_apply]
  have heval : Polynomial.eval B ((Q.map (algebraMap K (PrincipalSubring K))).scaleRoots
      (C : PrincipalSubring K)) = 0 := hinj (by rw [hmapped, map_zero])
  rw [eval_scaleRoots_map] at heval
  rw [← heval]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-! ### The minimal-polynomial bound -/

/-- LM24, Lemma 6.3.3: a nonzero element of the fraction field of `P̂` that
is algebraic over the coefficient field has minimal polynomial of degree at most one. -/
theorem principalSubringFraction_minpoly_natDegree_le_one_of_ne_zero (x :
    PrincipalSubringFractionField K)
    (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    (minpoly K x).natDegree ≤ 1 := by
  classical
  have hint : IsIntegral K x := hx.isIntegral
  have hQmonic : (minpoly K x).Monic := minpoly.monic hint
  have hcd : (minpoly K x).coeff (minpoly K x).natDegree ≠ 0 := by
    rw [hQmonic.coeff_natDegree]
    exact one_ne_zero
  obtain ⟨B, C, hB, hC, hrel⟩ :=
    exists_relation_of_aeval_eq_zero (minpoly K x) (minpoly.aeval K x) hx0
  have hgr := leadingGrade_eq_of_relation hB hC (fun i ↦ (minpoly K x).coeff i) hcd hrel
  obtain ⟨m, hm, hBm⟩ := DirectSum.exists_grade_eq_leadingGrade (PrincipalComponent K) hB
  have hCm : DirectSum.leadingGrade (PrincipalComponent K) C = (m : WithBot NatOrdinal) := by
    rw [← hgr, hm]
  obtain ⟨b, hb, hbeq⟩ := exists_principalComponentMk m (B m)
  obtain ⟨c, hc, hceq⟩ := exists_principalComponentMk m (C m)
  have hlead := sum_leadingTerm_eq_zero (fun i ↦ (minpoly K x).coeff i) hm hCm hrel
  rw [← hbeq, ← hceq] at hlead
  have hlt := ordinalValue_relationSum_lt (fun i ↦ (minpoly K x).coeff i) b c hb hc hlead
  have hbdeg : ω^ m ≤ ordinalValue b := by
    by_contra hcon
    exact hBm (by rw [← hbeq, principalComponentMk_eq_zero_iff]; exact not_le.mp hcon)
  obtain ⟨z, hz⟩ :=
    exists_isRoot_of_ordinalValue_relationSum_lt (minpoly K x) hQmonic rfl b c hbdeg hlt
  obtain ⟨u, hu⟩ := Polynomial.dvd_iff_isRoot.mpr hz
  rcases (minpoly.irreducible hint).isUnit_or_isUnit hu with hunit | hunit
  · exact absurd hunit (Polynomial.not_isUnit_X_sub_C z)
  · have hune : u ≠ 0 := hunit.ne_zero
    rw [hu, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero z) hune,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hunit]

end

end Berarducci
