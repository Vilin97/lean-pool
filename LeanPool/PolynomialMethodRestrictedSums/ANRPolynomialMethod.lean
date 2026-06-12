/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Common
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Set

/-!
# The Alon-Nathanson-Ruzsa polynomial method

The core of the polynomial method for restricted sums in `ZMod p`: elimination
polynomials, the vanishing-coefficient lemma on product grids, and the main
theorem `ANR_polynomial_method` giving a non-vanishing-coefficient criterion
for lower-bounding restricted sumsets.
-/

open scoped Finset

variable {R : Type*} [CommRing R]
variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

open MvPolynomial

open Finsupp

/--
Lemma 2.2 : A multivariate polynomial that vanishes on a large product finset is the zero
polynomial
-/
lemma eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
      exact MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P S Hdeg Heval

/-- Definition of elimination polynomials g_i -/
noncomputable def eliminationPolynomials (A : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
  fun i => ∏ a ∈ A i, (MvPolynomial.X i - C a)

/-- The sum of variables polynomial -/
noncomputable def sumXPolynomial : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  ∑ i, MvPolynomial.X i

/-- The restricted sumset S from the ANR theorem -/
noncomputable def restrictedSumset (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p)) : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter (fun f => h.eval f ≠ 0)).image (fun f => ∑ i, f i)

/-- The polynomial Q = h * ∏_{e∈E} (∑X_i - e) -/
noncomputable def constructionPolynomial
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (E : Multiset (ZMod p)) :
    MvPolynomial (Fin (k + 1)) (ZMod p) :=
  h * (E.map (fun e => sumXPolynomial - C e)).prod

/-- The construction of E from S when |S| ≤ m -/
def extendToSize (S : Finset (ZMod p)) (m : ℕ) :
    Multiset (ZMod p) :=
  S.val + Multiset.replicate (m - S.card) (0 : ZMod p)

/-- Alternative name for clarity. Here use k explicitly -/
noncomputable def productPolynomial (k : ℕ) (E : Multiset (ZMod p)) :
    MvPolynomial (Fin (k + 1)) (ZMod p) :=
  (E.map (fun e => sumXPolynomial - C e)).prod

/-- Lemma 2.1.1 : Construction_polynomial vanishes on ∏ A_i -/
lemma constructionPolynomial_vanishes
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (E : Multiset (ZMod p))
    (hE_sub : (restrictedSumset h A).val ⊆ E) :
    ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) →
      eval x (h * (E.map (fun e => sumXPolynomial - C e)).prod) = 0 := by
  intro x hx
  rw [eval_mul]
  by_cases hh : eval x h = 0
  · simp [hh]
  · have h_sum_in_S : (∑ i, x i) ∈ restrictedSumset h A := by
      dsimp [restrictedSumset]
      simp_all only [Finset.mem_image, Finset.mem_filter, Fintype.mem_piFinset]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl}
        · simp_all only [implies_true, not_false_eq_true, and_self]
    have h_sum_in_E : (∑ i, x i) ∈ E := hE_sub h_sum_in_S
    have h_prod_zero : eval x ((E.map (fun e => sumXPolynomial - C e)).prod) = 0 := by
      have factor_zero : eval x (sumXPolynomial - C (∑ i, x i)) = 0 := by
        simp [sumXPolynomial]
      have mem : sumXPolynomial - C (∑ i, x i) ∈
          (show Multiset (MvPolynomial (Fin (k + 1)) (ZMod p)) from
            E.map (fun e => sumXPolynomial - C e)) :=
        Multiset.mem_map.mpr ⟨∑ i, x i, h_sum_in_E, rfl⟩
      -- Apply the lemma that states if a multiset contains a zero element, then its product is
      -- zero.
      have h_prod_zero : ∀ {m : Multiset (MvPolynomial (Fin (k + 1)) (ZMod p))},
          (∃ f ∈ m, MvPolynomial.eval x f = 0) → MvPolynomial.eval x (Multiset.prod m) = 0 := by
        -- If there exists an element in the multiset that evaluates to zero at x, then the product
        -- of the multiset also evaluates to zero at x.
        intros m hm
        obtain ⟨f, hf_mem, hf_zero⟩ := hm
        have h_prod_zero : MvPolynomial.eval x (Multiset.prod m) = MvPolynomial.eval x f *
            MvPolynomial.eval x (Multiset.prod (Multiset.erase m f)) := by
          simp only [← eval_mul, Multiset.prod_erase hf_mem]
        rw [h_prod_zero, hf_zero, MulZeroClass.zero_mul]
      exact h_prod_zero ⟨_, mem, factor_zero⟩
    simp [h_prod_zero]

/-- Lemma 2.1.2 : The product polynomial ∏_{e∈E} (∑X_i - C e) is always nonzero -/
lemma productPolynomial_ne_zero (k : ℕ) (E : Multiset (ZMod p)) :
    productPolynomial k E ≠ 0 := by
      by_contra h
      by_cases hE : E.card = 0 <;> simp_all? +decide [productPolynomial]
      obtain ⟨a, haE, ha⟩ := h
      replace ha := congr_arg (MvPolynomial.eval (fun i => if i = 0 then a + 1 else 0)) ha
      norm_num [sumXPolynomial] at ha

/-- Lemma 2.1.3.1 : About total degree of sumX -/
lemma totalDegree_sumX_sub_C_first {p k : ℕ} [Fact (Nat.Prime p)] (a : ZMod p) :
    (sumXPolynomial - C a : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = 1 := by
      refine le_antisymm ?_ ?_
      · refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        -- The total degree of a sum of polynomials is less than or equal to the maximum of the
        -- total degrees of the summands.
        have h_total_degree_sum : ∀ (s : Finset (Fin (k + 1))),
            (∑ i ∈ s, MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree ≤ 1 := by
          -- The total degree of a sum of polynomials is less than or equal to the maximum of their
          -- total degrees.
          have h_sum_deg : ∀ (s : Finset (Fin (k + 1))),
              (∑ i ∈ s,
                  MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree
                      ≤ Finset.sup s (fun i =>
                        (MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree) := by
            exact fun s => totalDegree_finsetSum s fun i => X i
          intro s
          simp_all only [totalDegree_X]
          exact le_trans (h_sum_deg s) (Finset.sup_le fun i hi => le_rfl)
        simp_all only [totalDegree_C, zero_le, sup_of_le_left, ge_iff_le]
        apply h_total_degree_sum
      · refine le_trans ?_ (Finset.le_sup <| show Finsupp.single 0 1 ∈ (∑ i : Fin (k + 1),
          MvPolynomial.X i - MvPolynomial.C a |> MvPolynomial.support) from ?_) <;> norm_num
        rw [MvPolynomial.coeff_sum];
        simp_all only [coeff_single_X, true_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        split at a_1
        next h => simpa using congr_arg (fun f => f 0) h.symm
        next h => simp_all only [sub_zero, one_ne_zero]

/-- Lemma 2.1.3.2 : Another version of the previous lemma -/
lemma totalDegree_sumX_sub_C_second (e : ZMod p) :
    totalDegree (∑ i : Fin (k + 1), X i - C e) = 1 := by
  have :
      (∑ i : Fin (k + 1), X i - C e) =
          (sumXPolynomial : MvPolynomial (Fin (k + 1)) (ZMod p)) - C e := by
    simp [sumXPolynomial]
  rw [this]
  exact totalDegree_sumX_sub_C_first e

/-- Lemma 2.1.3.3 : The total degree of the product polynomial ∏_{e∈E} (∑X_i - C e) is equal to |E|
(Induction steps from J.J. Zhang). -/
lemma totalDegree_prod_sumX_sub_C_eq_card (E : Multiset (ZMod p)) :
    ((Multiset.map (fun e ↦ ∑ i : Fin (k + 1), X i - C e) E).prod).totalDegree = E.card := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons x E ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rw [totalDegree_mul_of_isDomain]
    · have hdeg : ∀ e : ZMod p, (∑ i : Fin (k + 1), X i - C e).totalDegree = 1 :=
        fun e => totalDegree_sumX_sub_C_second e
      rw [ih, hdeg, add_comm]
    · simp only [ne_eq, sub_eq_zero]
      intro rid
      have := congr($(rid).coeff (fun₀ | 0 => 1))
      simp only [coeff_sum, coeff_single_X, true_and, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, coeff_C] at this
      rw [if_neg] at this
      · norm_num at this
      · rw [eq_comm, Finsupp.single_eq_zero]
        norm_num
    · intro rid
      rw [Multiset.prod_eq_zero_iff] at rid
      simp only [Multiset.mem_map] at rid
      obtain ⟨a, a_mem, rid⟩ := rid
      have := congr($(rid).coeff (fun₀ | 0 => 1))
      simp only [coeff_sub, coeff_sum, coeff_single_X, true_and, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, coeff_C, coeff_zero] at this
      rw [if_neg] at this
      · norm_num at this
      · rw [eq_comm, Finsupp.single_eq_zero]
        norm_num

/-- Lemma 2.1.4 : The total degree of the construction polynomial is equal to the sum of c_i -/
lemma constructionPolynomial_totalDegree
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (h_ne_zero : h ≠ 0)
    (c : Fin (k + 1) → ℕ)
    (m : ℕ)
    (E : Multiset (ZMod p))
    (hm : m + h.totalDegree = ∑ i, c i)
    (hE_card : E.card = m)
    (h_prod_ne_zero : productPolynomial k E ≠ 0) :
    (constructionPolynomial h E).totalDegree = ∑ i, c i := by
  have h_prod_deg :
      (show MvPolynomial (Fin (k + 1)) (ZMod p) from
        (E.map (fun e => sumXPolynomial - C e)).prod).totalDegree = m := by
    have key := totalDegree_prod_sumX_sub_C_eq_card (k := k) (p := p) E
    simp only [sumXPolynomial]
    rw [key, hE_card]
  -- (Removed previous in-line derivation to fix failing aesop tactics.)
  -- We instead delegate to `totalDegree_prod_sumX_sub_C_eq_card`.
  have h_h_deg : h.totalDegree = (∑ i, c i) - m := by
    exact Nat.eq_sub_of_add_eq' hm
  -- By definition of constructionPolynomial, we have constructionPolynomial h E = h *
  -- productPolynomial k E.
  have h_construction_eq : constructionPolynomial h E = h * productPolynomial k E := by
    exact rfl
  -- Apply the property that the total degree of a product of two polynomials is the sum of their
  -- total degrees.
  have h_total_deg : (h * productPolynomial k E).totalDegree = h.totalDegree +
      (productPolynomial k E).totalDegree := by
    exact totalDegree_mul_of_isDomain h_ne_zero h_prod_ne_zero
  subst h_prod_deg
  simp_all only [ne_eq]
  -- Apply the hypothesis `hm` directly to conclude the proof.
  convert hm using 1
  exact
    Nat.add_comm (∑ i, c i - (Multiset.map (fun e => sumXPolynomial - C e) E).prod.totalDegree)
      (productPolynomial k E).totalDegree

open MvPolynomial Finsupp
open scoped BigOperators

/--
Lemma 2.1.5 : The coefficient of a term of maximal degree in the product $\prod (S - e)$ is the
same as in $S^{|E|}$
-/
lemma coeff_prod_sumX_minus_C_eq_coeff_sumX_pow_of_degree_eq
    {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}
    (E : Multiset (ZMod p)) (x : (Fin (k + 1)) →₀ ℕ) (hx : ∑ i, x i = Multiset.card E) :
    MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k + 1),
        MvPolynomial.X i) - MvPolynomial.C e)).prod) =
    MvPolynomial.coeff x ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ Multiset.card E) := by
  revert x
  induction E using Multiset.induction with
  | empty => intro x _; simp
  | cons a E ih =>
  intro x hx
  rw [Multiset.card_cons, pow_succ', Multiset.map_cons, Multiset.prod_cons]
  simp only [sub_mul, MvPolynomial.coeff_mul, MvPolynomial.coeff_sub]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl]
  rintro ⟨fst, snd⟩ hx_mem
  simp only [Finset.mem_antidiagonal] at hx_mem
  -- replace `x` and `hx` by data on `fst + snd`
  subst hx_mem
  rw [Multiset.card_cons] at hx
  have hx_sum : ∑ x, (fst x + snd x) = E.card + 1 := by
    simpa [Finsupp.add_apply, Finset.sum_add_distrib] using hx
  by_cases h : 0 = fst
  · -- in the pos branch, coeff 0 (C a) = a
    subst h
    simp only [MvPolynomial.coeff_C, ↓reduceIte]
    -- carry hx in the simplified form (snd = E.card + 1) for the legacy bullet
    have hx_snd : ∑ x, snd x = E.card + 1 := by
      simpa [Finsupp.zero_apply, zero_add] using hx_sum
    clear hx_sum
    -- legacy bullet 1 body
    rw [MvPolynomial.coeff_sum]
    simp_all only [coeff_zero_X, Finset.sum_const_zero, zero_mul, zero_sub, neg_eq_zero,
        mul_eq_zero]
    refine Or.inr ?_
    rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_multiset_prod _) ?_
    refine lt_of_le_of_lt (Multiset.sum_le_card_nsmul _ ?_ ?_) ?_
    · exact 1
    · intro x a_1
      simp_all only [Multiset.map_map, Function.comp_apply, Multiset.mem_map]
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      norm_num [MvPolynomial.totalDegree]
      intro b hb; contrapose! hb; simp_all? +decide [MvPolynomial.coeff_sum, MvPolynomial.coeff_X']
      rw [Finset.card_eq_zero.mpr] <;> aesop
    · rw [Finset.sum_subset (Finset.subset_univ snd.support)] <;> aesop
  · -- the case fst ≠ 0: simplify the C-coeff to 0 and reduce to a disjunction
    rw [MvPolynomial.coeff_C, if_neg h, zero_mul, sub_zero]
    -- rewrite the goal as a disjunction expected by the legacy bullet 2
    suffices h_disj :
        coeff snd (Multiset.map (fun e => (∑ i, X i) - C e) E).prod =
          coeff snd ((∑ i, X i) ^ E.card) ∨
          coeff fst ((∑ i, X i) : MvPolynomial (Fin (k + 1)) (ZMod p)) = 0 by
      rcases h_disj with h_eq | h_zero
      · rw [h_eq]
      · rw [h_zero, zero_mul, zero_mul]
    -- continue with the legacy chain on the disjunction
    by_cases h_snd : ∑ i, snd i = E.card
    · exact Or.inl <| ih snd h_snd
    · right
      rw [MvPolynomial.coeff_sum, Finset.sum_eq_zero]
      intro x a_1
      simp_all only [Finset.mem_univ]
      -- Since $fst \neq Finsupp.single x 1$, the coefficient of $fst$ in $X x$ is zero.
      have h_coeff_zero : fst ≠ Finsupp.single x 1 := by
        intro H
        apply h_snd
        have h_eq : (∑ y, fst y) + (∑ y, snd y) = E.card + 1 := by
          rw [← Finset.sum_add_distrib]; exact hx_sum
        rw [H] at h_eq
        have h_one : ∑ y, (Finsupp.single x 1 : Fin (k + 1) →₀ ℕ) y = 1 := by
          simp [Finsupp.single_apply, Finset.mem_univ]
        omega
      rw [MvPolynomial.coeff_X']
      simp_all only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false]
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      subst a_1
      simp_all only [not_true_eq_false]

/--
Lemma 2.1.6 : The coefficient of a specific term in the construction polynomial is non-zero under
certain conditions
-/
lemma constructionPolynomial_coeff_target_generalized
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m * h) ≠ 0)
    (E : Multiset (ZMod p)) (hE_card : E.card = m)
    (coeff_prod_sumX_minus_C_target :
      coeff (Finsupp.equivFunOnFinite.symm c) ((E.map (fun e => (∑ i, X i) - C e)).prod) =
      coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m))
    (other_terms_vanish : ∀ (d : (Fin (k + 1)) →₀ ℕ), d ≠ 0 →
      coeff d h * coeff (Finsupp.equivFunOnFinite.symm c - d)
        ((E.map (fun e => (∑ i, X i) - C e)).prod) = 0)
    (h_constant_term_nonzero : coeff 0 h ≠ 0) :
    coeff (Finsupp.equivFunOnFinite.symm c) (constructionPolynomial h E) ≠ 0 := by
      -- By combining the results from `coeff_prod_sumX_minus_C_target` and `other_terms_vanish`, we
      -- can conclude that the coefficient of $c$ in the product is equal to the coefficient of $c$
      -- in $S^m$ times the constant term of $h$.
      have h_final :
          MvPolynomial.coeff
              ((Finsupp.equivFunOnFinite.symm : (Fin (k + 1) → ℕ) → Fin (k + 1) →₀ ℕ) c)
              (constructionPolynomial h E) =
            MvPolynomial.coeff
                ((Finsupp.equivFunOnFinite.symm : (Fin (k + 1) → ℕ) → Fin (k + 1) →₀ ℕ) c)
                (Multiset.prod
                    (Multiset.map (fun e => (∑ i, MvPolynomial.X i) - MvPolynomial.C e) E)) *
              MvPolynomial.coeff 0 h := by
        rw [constructionPolynomial, MvPolynomial.coeff_mul]
        rw [Finset.sum_eq_single (0, (Finsupp.equivFunOnFinite.symm c))]
        · -- the diagonal term
          change coeff 0 h *
              coeff (Finsupp.equivFunOnFinite.symm c)
                (Multiset.map (fun e => sumXPolynomial - C e) E).prod =
            coeff (Finsupp.equivFunOnFinite.symm c)
                (Multiset.map (fun e => (∑ i, X i) - C e) E).prod * coeff 0 h
          simp only [sumXPolynomial]
          rw [mul_comm]
        · -- the off-diagonal terms vanish
          rintro ⟨fst, snd⟩ hmem hne
          simp only [Finset.mem_antidiagonal] at hmem
          by_cases hfst : fst = 0
          · -- if fst = 0, then snd = equivFunOnFinite.symm c (from hmem), contradicting hne
            subst hfst
            exfalso; apply hne
            simp only [zero_add] at hmem
            rw [Prod.mk.injEq]; exact ⟨rfl, hmem⟩
          · -- if fst ≠ 0, use other_terms_vanish; need to rewrite snd as `(sym c) - fst`
            have h_snd_eq : snd = Finsupp.equivFunOnFinite.symm c - fst := by
              rw [← hmem, add_tsub_cancel_left]
            rw [h_snd_eq]
            exact other_terms_vanish fst hfst
        · -- the diagonal pair belongs to the antidiagonal
          intro h_not
          exfalso; apply h_not
          simp [Finset.mem_antidiagonal]
      contrapose! h_coeff
      simp_all +decide only [ne_eq, mul_eq_zero, mul_comm, zero_eq_mul, false_or]
      rw [MvPolynomial.coeff_mul]
      rw [Finset.sum_eq_single (0, (Finsupp.equivFunOnFinite.symm c))]
      · -- the diagonal term: coeff 0 h * coeff (sym c) ((∑ X)^m) = 0 via h_final
        change coeff 0 h *
            coeff (Finsupp.equivFunOnFinite.symm c)
              ((∑ i, X i : MvPolynomial (Fin (k + 1)) (ZMod p)) ^ m) = 0
        rw [h_final, mul_zero]
      · -- the off-diagonal terms vanish
        rintro ⟨fst, snd⟩ hmem hne
        simp only [Finset.mem_antidiagonal] at hmem
        by_cases h_fst : fst = 0
        · subst h_fst
          exfalso; apply hne
          simp only [zero_add] at hmem
          rw [Prod.mk.injEq]; exact ⟨rfl, hmem⟩
        · -- fst ≠ 0: use other_terms_vanish
          have h_snd_eq : snd = Finsupp.equivFunOnFinite.symm c - fst := by
            rw [← hmem, add_tsub_cancel_left]
          rcases other_terms_vanish fst h_fst with h_zero | h_prod_zero
          · rw [h_zero, zero_mul]
          · -- h_prod_zero : coeff (sym c - fst) (∏ (∑ X - C e)) = 0
            -- Branch on whether coeff fst h is zero
            by_cases h_coeff_fst : coeff fst h = 0
            · rw [h_coeff_fst, zero_mul]
            · -- coeff fst h ≠ 0, so fst ∈ h.support
              by_cases h_deg : ∑ i, snd i = E.card
              · -- snd has degree E.card; rewrite via the helper lemma
                have h_eq :
                    coeff snd ((∑ i, X i : MvPolynomial (Fin (k + 1)) (ZMod p)) ^ E.card) =
                    coeff snd (Multiset.map (fun e => (∑ i, X i) - C e) E).prod := by
                  rw [← coeff_prod_sumX_minus_C_eq_coeff_sumX_pow_of_degree_eq E snd h_deg]
                rw [← hE_card, h_eq, h_snd_eq, h_prod_zero, mul_zero]
              · -- snd has wrong degree; show coeff snd ((∑ X)^m) = 0
                have h_left : fst ∈ h.support :=
                  MvPolynomial.mem_support_iff.mpr h_coeff_fst
                have h_sum_eq : (∑ i, fst i) + (∑ i, snd i) = ∑ i, c i := by
                  have hh := congr_arg (fun x => ∑ i, x i) hmem
                  simp only [Finsupp.coe_add, Pi.add_apply, equivFunOnFinite_symm_apply_apply,
                    Finset.sum_add_distrib] at hh
                  exact hh
                have h_deg_le : ∑ i, fst i ≤ h.totalDegree := by
                  have h_le_sup :
                      (fst.sum fun _ e => e) ≤
                        h.support.sup (fun s => s.sum fun _ e => e) :=
                    Finset.le_sup (f := fun s => s.sum fun _ e => e) h_left
                  have h_eq_sum : (fst.sum fun _ e => e) = ∑ i, fst i := by
                    simp [Finsupp.sum_fintype]
                  rw [h_eq_sum] at h_le_sup
                  exact h_le_sup
                have h_total_pow :
                    ((∑ i, X i : MvPolynomial (Fin (k+1)) (ZMod p)) ^ E.card).totalDegree
                      ≤ E.card := by
                  induction E.card with
                  | zero => simp
                  | succ n ih =>
                    rw [pow_succ]
                    refine le_trans (MvPolynomial.totalDegree_mul _ _) (add_le_add ih ?_)
                    refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
                    refine Finset.sup_le ?_
                    intro i _
                    exact (MvPolynomial.totalDegree_X i).le
                have h_snd_zero : coeff snd ((∑ i, X i) ^ E.card :
                    MvPolynomial (Fin (k + 1)) (ZMod p)) = 0 := by
                  rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
                  refine lt_of_le_of_lt h_total_pow ?_
                  by_contra h_not_lt
                  rw [not_lt] at h_not_lt
                  -- h_not_lt : E.card ≤ ∑ i ∈ snd.support, snd i
                  -- But ∑ i ∈ snd.support, snd i = ∑ i, snd i
                  have h_supp : ∑ i ∈ snd.support, snd i = ∑ i, snd i := by
                    rw [Finset.sum_subset (Finset.subset_univ _)]
                    intro x _ hx
                    simpa [Finsupp.mem_support_iff] using hx
                  rw [h_supp] at h_not_lt
                  have h_snd_lt : ∑ i, snd i < E.card :=
                    lt_of_le_of_ne h_not_lt h_deg
                  have h_fst_gt : ∑ i, fst i > h.totalDegree := by
                    have hm' : E.card + h.totalDegree = ∑ i, c i := by
                      rw [hE_card]; exact hm
                    omega
                  exact absurd h_deg_le (not_le.mpr h_fst_gt)
                rw [← hE_card, h_snd_zero, mul_zero]
      · -- the diagonal pair belongs to the antidiagonal
        intro h_not
        exfalso; apply h_not
        simp [Finset.mem_antidiagonal]

noncomputable section AristotleLemmas

/-- Helper for `elimination_polynomial_properties`: degree of $g_i$ in $X_i$ equals $|A_i|$. -/
private lemma elimination_polynomial_degreeOf_eq
    (A : Fin (k + 1) → Finset (ZMod p)) (i : Fin (k + 1)) (_h_card : (A i).card > 0) :
    (eliminationPolynomials A i).degreeOf i = (A i).card := by
  unfold eliminationPolynomials
  rw [MvPolynomial.degreeOf_eq_sup]
  -- The leading coefficient of the product of linear factors is 1.
  have h_leading_coeff :
      (MvPolynomial.coeff (Finsupp.single i #(A i)) (∏ a ∈ A i,
          (MvPolynomial.X i - MvPolynomial.C a))) = 1 := by
    induction (A i) using Finset.induction with
    | empty =>
      simp_all only [gt_iff_lt, Finset.card_pos, Finset.card_empty, single_zero,
          Finset.prod_empty, coeff_zero_one]
    | @insert a s a_1 a_2 =>
    simp_all only [gt_iff_lt, Finset.card_pos, not_false_eq_true,
        Finset.card_insert_of_notMem, single_add, Finset.prod_insert]
    norm_num [sub_mul, MvPolynomial.coeff_mul]
    rw [Finset.sum_eq_single (Finsupp.single i 1, Finsupp.single i (Finset.card s))]
    · rw [Finset.sum_eq_single (0, Finsupp.single i (Finset.card s) + Finsupp.single i 1)]
      on_goal 2 =>
        rintro ⟨b1, b2⟩ hb hne
        simp only [Finset.mem_antidiagonal] at hb
        by_cases h_b1 : 0 = b1
        · subst h_b1
          exfalso; apply hne
          simp only [zero_add] at hb
          rw [Prod.mk.injEq]
          exact ⟨rfl, hb⟩
        · simp [if_neg h_b1]
      on_goal 2 =>
        intro h_notin
        exfalso; apply h_notin
        simp [Finset.mem_antidiagonal]
      simp only [MvPolynomial.coeff_X',
        a_2, mul_one, if_true, sub_eq_self, mul_eq_zero]
      refine Or.inr ?_
      erw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
      -- The total degree of the product of linear terms is the sum of the degrees of the
      -- individual terms.
      have h_total_degree :
          (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ s.card := by
        have h_total_degree : ∀ a ∈ s,
            (MvPolynomial.X i - MvPolynomial.C a).totalDegree ≤ 1 := by
          intro a ha; rw [MvPolynomial.totalDegree]
          simp_all only [Finset.sup_le_iff, MvPolynomial.mem_support_iff, coeff_sub, coeff_C,
              ne_eq]
          intro b a_4
          split at a_4
          next h =>
            subst h
            simp_all only [coeff_zero_X, zero_sub, neg_eq_zero, sum_zero_index, zero_le]
          next h =>
            simp_all only [sub_zero]
            rw [MvPolynomial.coeff_X'] at a_4
            simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]
            subst a_4
            simp_all only [sum_single_index, le_refl]
        have h_total_degree : ∀ {S : Finset (ZMod p)},
            (∀ a ∈ S, (MvPolynomial.X i - MvPolynomial.C a).totalDegree ≤ 1) →
                (∏ a ∈ S, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ S.card := by
          intros S hS; induction S using Finset.induction with
          | empty =>
            simp_all only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
                Finset.prod_empty, totalDegree_one, Finset.card_empty, Std.le_refl]
          | @insert a_3 s_1 a_4 a_5 =>
            simp_all only [Finset.mem_insert, or_true, implies_true, forall_const,
                forall_eq_or_imp, not_false_eq_true, Finset.prod_insert,
                Finset.card_insert_of_notMem]
            obtain ⟨left, right⟩ := hS
            exact le_trans (MvPolynomial.totalDegree_mul _ _) (by linarith)
        exact h_total_degree ‹_›
      refine lt_of_le_of_lt h_total_degree ?_
      rw [Finset.sum_eq_single i] <;> aesop
    · intro b a_3 a_4
      simp_all only [Finset.mem_antidiagonal, ne_eq, mul_eq_zero]
      obtain ⟨fst, snd⟩ := b
      simp_all only [Prod.mk.injEq, not_and]
      rw [MvPolynomial.coeff_X']
      simp_all only [ite_eq_right_iff, one_ne_zero, imp_false]
      contrapose! a_4
      simp_all only [ne_eq, true_and]
      obtain ⟨left, right⟩ := a_4
      subst left
      ext j; replace a_3 := congr_arg (fun f => f j) a_3
      simp_all only [Finsupp.coe_add, Pi.add_apply]
      rw [add_comm] at a_3
      simp_all only [Nat.add_right_cancel_iff]
    · simp +decide [add_comm]
  refine le_antisymm ?_ ?_
  · simp_all +decide only [Finset.sup_le_iff, MvPolynomial.mem_support_iff, ne_eq]
    intro b hb
    contrapose! hb
    rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
    refine lt_of_le_of_lt (b := ?_) ?_ ?_
    · exact (A i |> Finset.card)
    · induction (A i) using Finset.induction with
      | empty =>
        simp_all only [gt_iff_lt, Finset.card_pos, Finset.prod_empty, totalDegree_one,
            Finset.card_empty, Std.le_refl]
      | @insert a s a_1 a_2 =>
        simp_all only [gt_iff_lt, Finset.card_pos, not_false_eq_true, Finset.prod_insert,
            Finset.card_insert_of_notMem]
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        refine le_trans (add_le_add (MvPolynomial.totalDegree_sub _ _) a_2) ?_
        norm_num [add_comm, MvPolynomial.totalDegree_X]
    · exact lt_of_lt_of_le hb (Finset.single_le_sum (fun a _ => Nat.zero_le (b a)) (by
    simp_all only [Finsupp.mem_support_iff, ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [not_lt_zero]))
  · refine le_trans ?_ (Finset.le_sup <| show Finsupp.single i (# (A i)) ∈ _ from ?_)
      <;> aesop

/-- Helper for `elimination_polynomial_properties`: leading coefficient of $g_i$ equals 1. -/
private lemma elimination_polynomial_coeff_top_eq_one
    (A : Fin (k + 1) → Finset (ZMod p)) (i : Fin (k + 1)) (h_card : (A i).card > 0) :
    coeff (Finsupp.single i ((A i).card)) (eliminationPolynomials A i) = 1 := by
  have h_leading_coeff : ∀ (s : Finset (ZMod p)),
      (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).coeff (Finsupp.single i (s.card)) =
          1 := by
    intro s
    induction s using Finset.induction with
    | empty => simp +decide [MvPolynomial.coeff_one]
    | @insert a s ha ih =>
      simp_all? +decide [Finset.prod_insert ha, MvPolynomial.coeff_mul]
      -- The only non-zero term in the sum is when $x = (fun | i => 1)$ and $y = (fun | i =>
      -- #s)$.
      have h_nonzero_term : ∀ x y : (Fin (k + 1)) →₀ ℕ,
          x + y = (fun₀ | i => #s) +
              (fun₀ | i => 1) →
                  (MvPolynomial.coeff x (MvPolynomial.X i) - if 0 = x then a else 0) *
                  MvPolynomial.coeff y (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)) =
                      if x = (fun₀ | i => 1) ∧ y = (fun₀ | i => #s) then 1 else 0 := by
        intro x y hxy
        by_cases hx : x = (fun₀ | i => 1)
        · subst hx
          rw [eq_comm] at hxy
          simp only [MvPolynomial.coeff_X']
          by_cases h : (0 : Fin (k+1) →₀ ℕ) = fun₀ | i => 1
          · by_cases h_1 : y = fun₀ | i => #s
            · subst h_1
              simp only [if_pos h]
              simpa using congr_arg (fun f => f i) h.symm
            · simp only [if_pos h]
              simpa using congr_arg (fun f => f i) h.symm
          · by_cases h_1 : y = fun₀ | i => #s
            · subst h_1
              simp only [if_true, and_self, if_neg h, sub_zero, one_mul, ih]
            · simp only [if_true, if_neg h, sub_zero]
              rw [Finsupp.ext_iff] at hxy;
              simp_all only [Finsupp.coe_add, Pi.add_apply]
              contrapose! h_1; ext j; specialize hxy j; by_cases hj : j = i
              · subst hj
                simp_all only [ne_eq, single_eq_same]
                linarith
              · simp_all only [ne_eq, not_false_eq_true, single_eq_of_ne, add_zero, zero_add]
        · rw [MvPolynomial.coeff_X'];
          simp_all only [false_and, ↓reduceIte, mul_eq_zero]
          split
          next h =>
            subst h
            simp_all only [not_true_eq_false]
          next h =>
            simp_all only [zero_sub, neg_eq_zero, ite_eq_right_iff]
            contrapose! hx
            simp_all only [ne_eq]
            obtain ⟨left, right⟩ := hx
            obtain ⟨left, right_1⟩ := left
            subst left
            simp_all only [zero_add, single_eq_zero, one_ne_zero, not_false_eq_true]
            subst hxy
            -- The degree of the product of (X_i - C a) over s is #s, so any term with a
            -- higher degree than #s must have a coefficient of zero.
            have h_deg : (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ #s :=
                by
              have h_total_degree : ∀ (s : Finset (ZMod p)),
                  (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ s.card := by
                intro s; induction s using Finset.induction with
                | empty =>
                  simp_all only [Finset.prod_empty, totalDegree_one, Finset.card_empty,
                      Std.le_refl]
                | @insert a_1 s_1 a_2 a_3 =>
                  simp_all only [not_false_eq_true, Finset.prod_insert,
                      Finset.card_insert_of_notMem]
                  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
                  refine le_trans (add_le_add (MvPolynomial.totalDegree_sub _ _) a_3) ?_
                  norm_num [add_comm]
              exact h_total_degree s
            rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt] at right
            · simp_all only [not_true_eq_false]
            simp_all only [Finsupp.coe_add, Pi.add_apply]
            refine lt_of_le_of_lt h_deg ?_
            rw [Finset.sum_eq_single i] <;> aesop
      rw [Finset.sum_congr rfl fun x hx => h_nonzero_term _ _ <| by simpa using hx]
      simp_all only [Finset.sum_boole]
      rw [Finset.card_eq_one.mpr]
      · simp_all only [Nat.cast_one]
      use ((fun₀ | i => 1), (fun₀ | i => #s)); ext
      rename_i a_1
      simp_all only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton]
      obtain ⟨fst, snd⟩ := a_1
      simp_all only [Prod.mk.injEq, and_iff_right_iff_imp, and_imp]
      intro a_1 a_2
      subst a_1 a_2
      exact add_comm _ _
  exact h_leading_coeff _

/-- Helper for `elimination_polynomial_properties`: $g_i$ vanishes on inputs from $A_i$. -/
private lemma elimination_polynomial_eval_eq_zero
    (A : Fin (k + 1) → Finset (ZMod p)) (i : Fin (k + 1)) :
    ∀ x, x i ∈ A i → eval x (eliminationPolynomials A i) = 0 := by
  unfold eliminationPolynomials
  exact fun x hx =>
      by rw [MvPolynomial.eval_prod]; exact Finset.prod_eq_zero hx (by simp +decide)

/-- Helper for `elimination_polynomial_properties`: dropping the top monomial cuts degree. -/
private lemma elimination_polynomial_sub_top_totalDegree_lt
    (A : Fin (k + 1) → Finset (ZMod p)) (i : Fin (k + 1)) (h_card : (A i).card > 0) :
    (eliminationPolynomials A i - X i ^ (A i).card).totalDegree < (A i).card := by
  have h_deg : (eliminationPolynomials A i).degreeOf i = #(A i) :=
    elimination_polynomial_degreeOf_eq A i h_card
  have h_deg_mono :
      (eliminationPolynomials A i - (MvPolynomial.X i) ^ #(A i)).degreeOf i < #(A i) := by
    have h_deg_sub :
        (eliminationPolynomials A i).coeff (Finsupp.single i #(A i)) = 1 :=
      elimination_polynomial_coeff_top_eq_one A i h_card
    rw [MvPolynomial.degreeOf_eq_sup] at *;
    simp_all only [gt_iff_lt, Finset.card_pos, Nat.bot_eq_zero, Finset.sup_lt_iff,
      MvPolynomial.mem_support_iff, coeff_sub, ne_eq]
    intro b a
    by_cases hb : b i = #(A i)
    · simp_all? +decide [MvPolynomial.coeff_X_pow]
      by_cases h : (fun₀ | i => #(A i)) = b
      · simp_all only [if_true, sub_self, not_true_eq_false]
      · simp only [if_neg h, sub_zero] at a
        contrapose! h; ext j; by_cases hj : j = i
        · subst hj
          simp_all only [single_eq_same]
        simp_all only [ne_eq, not_false_eq_true, single_eq_of_ne]
        have h_deg_sub : ∀ m ∈ (eliminationPolynomials A i).support, m j = 0 := by
          unfold eliminationPolynomials
          intro m a_1
          simp_all only [MvPolynomial.mem_support_iff, ne_eq]
          rw [Finset.prod_congr rfl fun x hx => sub_eq_add_neg _ _] at a_1
          rw [Finset.prod_add] at a_1
          rw [MvPolynomial.coeff_sum] at a_1
          obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero a_1
          simp_all only [Finset.prod_const, Finset.mem_powerset, ne_eq]
          obtain ⟨left, right⟩ := hx
          rw [MvPolynomial.coeff_mul] at right
          obtain ⟨y, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero right
          simp_all only [Finset.mem_antidiagonal, ne_eq, mul_eq_zero, not_or]
          obtain ⟨fst, snd⟩ := y
          obtain ⟨left_1, right_1⟩ := hy
          obtain ⟨left_2, right_1⟩ := right_1
          subst left_1
          simp_all only [Finsupp.coe_add, Pi.add_apply, Nat.add_eq_zero_iff]
          apply And.intro
          · rw [MvPolynomial.coeff_X_pow] at left_2
            simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]
            subst left_2
            simp_all only [ne_eq, not_false_eq_true, single_eq_of_ne]
          · rw [Finset.prod_congr rfl fun _ _ => neg_eq_neg_one_mul _,
              Finset.prod_mul_distrib] at right_1
            simp_all only [Finset.prod_const]
            -- Since the product is over elements of A i \ x, and each element is a
            -- constant, the only way for the product to have a non-zero coefficient is if
            -- snd is the zero function. Otherwise, there would be a term in the product
            -- that's a constant, which can't contribute to the coefficient of snd unless
            -- snd is zero.
            have h_snd_zero : ∀ (c : ZMod p),
                MvPolynomial.coeff snd (MvPolynomial.C c) = if snd = 0 then c else 0 := by
              intro c; rw [MvPolynomial.coeff_C]
              split
              next h =>
                subst h
                simp_all only [add_zero, ↓reduceIte]
              next h =>
                simp_all only [right_eq_ite_iff]
                intro a_2
                subst a_2
                simp_all only [add_zero, not_true_eq_false]
            specialize h_snd_zero ((-1) ^ # (A i \ x) * ∏ x ∈ A i \ x, x); simp_all
        exact Eq.symm (h_deg_sub b
          (by simp_all only [MvPolynomial.mem_support_iff, ne_eq, not_false_eq_true]))
    · contrapose! a; simp_all? +decide [MvPolynomial.coeff_X_pow]
      rw [if_neg (by intro h; replace h := congr_arg (fun f => f i) h; aesop)]
      simp_all only [sub_zero]
      exact Classical.not_not.1 fun h => hb <|
          le_antisymm
            (h_deg ▸ Finset.le_sup (f := fun m => m i) (MvPolynomial.mem_support_iff.2 h)) a
  have h_total_deg : ∀ j ≠ i,
      (eliminationPolynomials A i - (MvPolynomial.X i) ^ #(A i)).degreeOf j ≤ 0 := by
    intros j hj_ne_i
    have h_deg_j : (eliminationPolynomials A i).degreeOf j = 0 := by
      unfold eliminationPolynomials
      induction (A i) using Finset.induction with
      | empty => simp [MvPolynomial.degreeOf]
      | @insert a s ha ih =>
        -- Since $j \neq i$, the degree of $X_i - C a$ in $j$ is zero.
        rw [Finset.prod_insert ha]
        have h_deg_j_zero :
            MvPolynomial.degreeOf j (MvPolynomial.X i - MvPolynomial.C a) = 0 := by
          refine Nat.eq_zero_of_le_zero (MvPolynomial.degreeOf_le_iff.mpr fun m hm => ?_)
          rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_X',
            MvPolynomial.coeff_C] at hm
          by_cases h1 : Finsupp.single i 1 = m
          · subst h1
            simp [Finsupp.single_eq_of_ne hj_ne_i]
          · by_cases h0 : m = 0
            · subst h0
              simp
            · simp [h1, Ne.symm h0] at hm
        exact le_antisymm
          (le_trans (MvPolynomial.degreeOf_mul_le _ _ _)
            (by simp_all only [add_zero, le_refl])) (Nat.zero_le _)
    refine MvPolynomial.degreeOf_le_iff.mpr fun m hm => ?_
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_X_pow] at hm
    by_cases h : Finsupp.single i #(A i) = m
    · subst h
      simp [Finsupp.single_eq_of_ne hj_ne_i]
    · have hmem : m ∈ (eliminationPolynomials A i).support := by
        rw [MvPolynomial.mem_support_iff]
        simpa [h] using hm
      have hle : m j ≤ (eliminationPolynomials A i).degreeOf j := by
        rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.le_sup (f := fun m => m j) hmem
      exact hle.trans (le_of_eq h_deg_j)
  rw [MvPolynomial.totalDegree]
  rw [Finset.sup_lt_iff (by simpa using h_card)]
  intro m hm
  have h_eq : (m.sum fun _ e => e) = m i := by
    rw [Finsupp.sum, Finset.sum_eq_single i]
    · intro b hbm hb
      have hle : m b ≤ (eliminationPolynomials A i - X i ^ #(A i)).degreeOf b := by
        rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.le_sup (f := fun m => m b) hm
      exact Nat.le_zero.mp (hle.trans (h_total_deg b hb))
    · exact fun h => Finsupp.notMem_support_iff.mp h
  have h_le : m i ≤ (eliminationPolynomials A i - X i ^ #(A i)).degreeOf i := by
    rw [MvPolynomial.degreeOf_eq_sup]
    exact Finset.le_sup (f := fun m => m i) hm
  rw [h_eq]
  exact lt_of_le_of_lt h_le h_deg_mono

/-- Lemma 2.1.7 : The elimination polynomial $g_i$ for a given index $i$ and set $A_i$ -/
lemma elimination_polynomial_properties (A : Fin (k + 1) → Finset (ZMod p)) (i : Fin (k + 1))
    (h_card : (A i).card > 0) :
    let g := eliminationPolynomials A i
    g.degreeOf i = (A i).card ∧
    coeff (Finsupp.single i ((A i).card)) g = 1 ∧
    (∀ x, x i ∈ A i → eval x g = 0) ∧
    (g - X i ^ (A i).card).totalDegree < (A i).card := by
  refine ⟨elimination_polynomial_degreeOf_eq A i h_card,
    elimination_polynomial_coeff_top_eq_one A i h_card,
    elimination_polynomial_eval_eq_zero A i,
    elimination_polynomial_sub_top_totalDegree_lt A i h_card⟩

/--
Lemma 2.1.8 : A single step in the monomial reduction process, reducing the degree in variable `i`
-/
lemma monomial_reduction_step (m : Fin (k + 1) →₀ ℕ) (i : Fin (k + 1))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ j, (A j).card = c j + 1)
    (hi : m i > c i) :
    ∃ Q : MvPolynomial (Fin (k + 1)) (ZMod p),
      Q.totalDegree < m.sum (fun _ n => n) ∧
      (∀ x, (∀ j, x j ∈ A j) → eval x Q = eval x (monomial m 1)) ∧
      (m.sum (fun _ n => n) ≤ ∑ j, c j →
        coeff (Finsupp.equivFunOnFinite.symm c) Q = coeff (Finsupp.equivFunOnFinite.symm c) (
            monomial m 1)) := by
          -- Define Q as X^{m'} * (X_i^{c_i+1} - g_i).
          set Q : MvPolynomial (Fin (k + 1)) (ZMod p) :=
              MvPolynomial.monomial (m - Finsupp.single i (c i + 1)) 1 *
              (MvPolynomial.X i ^ (c i + 1) - eliminationPolynomials A i)
          -- Show that the total degree of Q is less than the total degree of m.
          have hQ_totalDegree : Q.totalDegree < m.sum (fun _ n => n) := by
            have hQ_totalDegree :
                (MvPolynomial.X i ^ (c i + 1) - eliminationPolynomials A i).totalDegree < c i +
                1 := by
              have := elimination_polynomial_properties A i
              rw [← neg_sub, MvPolynomial.totalDegree_neg]
              simp_all
            have hQ_totalDegree :
                Q.totalDegree ≤ (m - Finsupp.single i (c i + 1)).sum (fun x n => n) +
                (MvPolynomial.X i ^ (c i + 1) - eliminationPolynomials A i).totalDegree := by
              convert MvPolynomial.totalDegree_mul _ _ using 1
              norm_num [MvPolynomial.totalDegree_monomial]
            have hQ_totalDegree : (m - Finsupp.single i (c i + 1)).sum (fun x n => n) +
                (MvPolynomial.X i ^ (c i + 1) - eliminationPolynomials A i).totalDegree
                  < m.sum (fun x n => n) := by
              have key : (m - Finsupp.single i (c i + 1)).sum (fun _ n => n) + (c i + 1)
                  ≤ m.sum (fun _ n => n) := by
                have h_le : Finsupp.single i (c i + 1) ≤ m := by
                  intro j
                  by_cases hji : j = i
                  · subst hji
                    simp only [single_add, Finsupp.coe_add, Pi.add_apply, single_eq_same,
                      Order.add_one_le_iff]
                    exact hi
                  · simp [Ne.symm hji]
                -- Rephrase both sums as sums over Finset.univ.
                rw [show (m - Finsupp.single i (c i + 1)).sum (fun _ n => n)
                      = ∑ j, (m - Finsupp.single i (c i + 1)) j from by
                    rw [Finsupp.sum_fintype]; intros; rfl]
                rw [show m.sum (fun _ n => n) = ∑ j, m j from by
                    rw [Finsupp.sum_fintype]; intros; rfl]
                -- Split each sum at index i.
                rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) i
                      (fun j => (m - Finsupp.single i (c i + 1)) j) (fun h => by simp at h),
                    Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) i
                      (fun j => m j) (fun h => by simp at h)]
                -- The sums over `Finset.univ \ {i}` agree.
                have h_outside :
                    ∀ j ∈ Finset.univ \ {i},
                      (m - Finsupp.single i (c i + 1)) j = m j := by
                  intro j hj
                  rcases Finset.mem_sdiff.mp hj with ⟨_, hji⟩
                  rw [Finset.mem_singleton] at hji
                  simp [Finsupp.single_apply, if_neg (Ne.symm hji)]
                rw [Finset.sum_congr rfl h_outside]
                have h_mi : c i + 1 ≤ m i := by
                  have := h_le i
                  simpa [Finsupp.single_apply] using this
                have happ : (m - Finsupp.single i (c i + 1)) i = m i - (c i + 1) := by
                  simp
                rw [happ]
                have h_sum_eq :
                    (Finset.univ \ {i}).sum (fun j => m j) = ∑ x ∈ Finset.univ \ {i}, m x := rfl
                rw [← h_sum_eq] at *
                omega
              linarith
            linarith
          refine ⟨Q, hQ_totalDegree, fun x a => ?_, fun a => ?_⟩
          on_goal 1 =>
            simp only [Q, MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
              MvPolynomial.eval_X]
          on_goal 2 =>
            simp only [Q]
            have hm_ne : m ≠ equivFunOnFinite.symm c := by
              intro hm_eq
              have := congr_arg (fun f : Fin (k+1) →₀ ℕ => f i) hm_eq
              simp [Finsupp.equivFunOnFinite_symm_apply_apply] at this
              omega
            rw [show coeff (equivFunOnFinite.symm c) ((monomial m) (1:ZMod p)) = 0 from by
              rw [MvPolynomial.coeff_monomial, if_neg hm_ne]]
          · -- By definition of $g_i$, we know that $g_i(x) = 0$ for all $x \in A_i$.
            have h_gi_zero : ∀ x : Fin (k + 1) → ZMod p,
                (∀ j, x j ∈ A j) → (MvPolynomial.eval x (eliminationPolynomials A i)) = 0 := by
              intro x hx; unfold eliminationPolynomials; simp +decide [Finset.prod_eq_zero_iff,
                  sub_eq_zero, hx]
            rw [h_gi_zero x a, sub_zero]; simp +decide [MvPolynomial.eval_monomial]; ring_nf
            simp? +decide [Finsupp.single_apply,
                Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ i), mul_assoc, ← pow_succ']
            rw [← pow_add, Nat.sub_add_cancel (by linarith)]
            exact congrArg₂ _ (Finset.prod_congr rfl fun j hj => by
            simp_all only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
            split
            next h =>
              subst h
              simp_all only [not_true_eq_false]
            next h => simp_all only [add_zero, tsub_zero]) rfl
          · rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
            simp_all only [equivFunOnFinite_symm_apply_support,
                equivFunOnFinite_symm_apply_apply]
            refine lt_of_lt_of_le hQ_totalDegree (le_trans a ?_)
            -- ∑ j ∈ univ, c j = ∑ x ∈ (support c).toFinset, c x (zero off support).
            apply le_of_eq
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro j _ hj
            by_contra hne
            apply hj
            simp [Function.mem_support, hne]

/--
Lemma 2.1.9 : Existence of a remainder polynomial R with bounded degrees matching Q on specified
points
-/
lemma exists_remainder (Q : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (hQ_deg : Q.totalDegree ≤ ∑ i, c i) :
    ∃ R : MvPolynomial (Fin (k + 1)) (ZMod p),
      (∀ i, R.degreeOf i ≤ c i) ∧
      (∀ x, (∀ i, x i ∈ A i) → eval x R = eval x Q) ∧
      (coeff (Finsupp.equivFunOnFinite.symm c) R = coeff (Finsupp.equivFunOnFinite.symm c) Q) := by
        by_contra h_contra
        -- Apply induction on the total degree of Q.
        induction hQ_deg : Q.totalDegree using Nat.strong_induction_on generalizing Q with
        | _ d ih =>
        -- Apply the induction hypothesis to each term in the sum.
        have h_induction : ∀ m ∈ Q.support,
            (∃ R : MvPolynomial (Fin (k + 1)) (ZMod p),
              (∀ i, R.degreeOf i ≤ c i) ∧
              (∀ x : Fin (k + 1) → ZMod p,
                  (∀ i, x i ∈ A i) → R.eval x = (MvPolynomial.monomial m 1).eval x) ∧
              R.coeff (Finsupp.equivFunOnFinite.symm c)
                = (MvPolynomial.monomial m 1).coeff (Finsupp.equivFunOnFinite.symm c)) := by
          intro m hm
          by_cases hm_deg : m.sum (fun _ n => n) ≤ ∑ i, c i
          · by_cases hm_deg : ∃ i, m i > c i
            · obtain ⟨i, hi⟩ : ∃ i, m i > c i := hm_deg
              obtain ⟨Q', hQ'_deg, hQ'_eval,
                  hQ'_coeff⟩ : ∃ Q' : MvPolynomial (Fin (k + 1)) (ZMod p),
                  Q'.totalDegree < m.sum (fun _ n => n) ∧
                      (∀ x : Fin (k + 1) → ZMod p, (∀ i,
                          x i ∈ A i) → Q'.eval x = (MvPolynomial.monomial m 1).eval x)
                              ∧ Q'.coeff (Finsupp.equivFunOnFinite.symm c)
                                  = (MvPolynomial.monomial m 1).coeff
                                      (Finsupp.equivFunOnFinite.symm c) := by
                -- Apply the monomial_reduction_step lemma to get Q'.
                obtain ⟨Q', hQ'_deg, hQ'_eval,
                    hQ'_coeff⟩ : ∃ Q' : MvPolynomial (Fin (k + 1)) (ZMod p),
                    Q'.totalDegree < m.sum (fun _ n => n) ∧
                        (∀ x : Fin (k + 1) → ZMod p, (∀ i,
                            x i ∈ A i) → Q'.eval x = (MvPolynomial.monomial m 1).eval x)
                                ∧ Q'.coeff (Finsupp.equivFunOnFinite.symm c)
                                    = (MvPolynomial.monomial m 1).coeff
                                      (Finsupp.equivFunOnFinite.symm c) := by
                  have := monomial_reduction_step m i A c hA hi
                  grind
                use Q'
              specialize ih (Q'.totalDegree) (by
                refine lt_of_lt_of_le hQ'_deg ?_
                exact hQ_deg ▸ Finset.le_sup (f := fun s => s.sum fun x n => n) hm) Q' (by
                linarith)
              subst hQ_deg
              simp_all
            · use MvPolynomial.monomial m 1
              simp_all (config := {decide := Bool.true}) only [degreeOf_eq_sup, Finset.sup_le_iff,
                MvPolynomial.mem_support_iff, ne_eq, not_exists, not_and, imp_false, gt_iff_lt,
                not_lt, coeff_monomial, ite_eq_right_iff, one_ne_zero, Decidable.not_not,
                forall_eq', implies_true, and_self]
          · refine False.elim (hm_deg <| le_trans ?_ ‹Q.totalDegree ≤ ∑ i, c i›)
            exact Finset.le_sup (f := fun m => m.sum fun _ n => n) hm
        choose! R hR₁ hR₂ hR₃ using h_induction
        refine h_contra ⟨∑ m ∈ Q.support, Q.coeff m • R m, ?_, ?_, ?_⟩
        · intro i
          refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
          simp +zetaDelta only [Finset.sup_le_iff, MvPolynomial.mem_support_iff, ne_eq] at *
          intro m hm; specialize hR₁ m hm i; rw [MvPolynomial.degreeOf_eq_sup] at *;
          simp_all only [Finset.sup_le_iff, MvPolynomial.mem_support_iff, ne_eq, not_false_eq_true,
            MvPolynomial.support_smul_eq, implies_true]
        · simp only [map_sum, smul_eval]
          intro x hx; rw [MvPolynomial.eval_eq']
          exact Finset.sum_congr rfl fun m hm => by rw [hR₂ m hm x hx]; simp only [eval_monomial,
            prod_pow, one_mul]
        · rw [MvPolynomial.coeff_sum]
          rw [Finset.sum_congr rfl fun m hm => by rw [MvPolynomial.coeff_smul, hR₃ m hm]]
          simp only [coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            MvPolynomial.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff]
          exact fun h => h.symm

/--
Lemma 2.1.10 : If a polynomial Q vanishes on a grid defined by sets A_i and has total degree at
most the sum of the sizes of these sets minus one, then the coefficient of the monomial defined by
these sizes is zero
-/
lemma coeff_target_eq_zero_of_vanishes_on_grid
    (Q : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (hQ_deg : Q.totalDegree ≤ ∑ i, c i)
    (hQ_vanishes : ∀ x, (∀ i, x i ∈ A i) → eval x Q = 0) :
    coeff (Finsupp.equivFunOnFinite.symm c) Q = 0 := by
      -- Apply `exists_remainder` to $Q$ to get $R$.
      obtain ⟨R, hR⟩ := exists_remainder Q A c hA hQ_deg
      -- By `eq_zero_of_eval_zero_at_prod_finset`, $R = 0$.
      have hR_zero : R = 0 := by
        -- Apply the fact that if a polynomial vanishes on a product of finite sets and its degree
        -- in each variable is less than the size of the corresponding set, then the polynomial must
        -- be zero.
        have hR_zero : ∀ (P : MvPolynomial (Fin (k + 1)) (ZMod p)),
            (∀ i, P.degreeOf i < #(A i)) →
                (∀ x : Fin (k + 1) → ZMod p, (∀ i, x i ∈ A i) → MvPolynomial.eval x P = 0) →
                P = 0 := by
          exact fun P a a_1 => _root_.eq_zero_of_eval_zero_at_prod_finset P A a a_1
        exact hR_zero R (fun i => by linarith [hR.1 i, hA i]) fun x hx =>
            by simp [hR.2.1 x hx, hQ_vanishes x hx]
      aesop

/--
Lemma 2.1.11 : If two polynomials P and Q are equal or their difference has a total degree less
than m, then the coefficients of the monomial defined by c in h * P and h * Q are equal, given that
h.totalDegree + m equals the sum of c_i
-/
lemma coeff_mul_eq_of_degree_bound
    (h P Q : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (m : ℕ)
    (h_deg : h.totalDegree + m = ∑ i, c i)
    (h_diff : P = Q ∨ (P - Q).totalDegree < m) :
    coeff (Finsupp.equivFunOnFinite.symm c) (h * P) =
    coeff (Finsupp.equivFunOnFinite.symm c) (h * Q) := by
      cases h_diff with
      | inl h_1 =>
        subst h_1
        simp_all only
      | inr h_2 => ?_
      -- Since $P - Q$ has a total degree less than $m$, $h * (P - Q)$ has a total degree less than
      -- $h.totalDegree + m$.
      have h_total_degree : (h * (P - Q)).totalDegree < h.totalDegree + m := by
        -- The total degree of a product of two polynomials is less than or equal to the sum of
        -- their total degrees.
        have h_total_degree_mul : (h * (P - Q)).totalDegree ≤ h.totalDegree +
            (P - Q).totalDegree := by
          exact totalDegree_mul h (P - Q)
        linarith
      -- Since the total degree of $h * (P - Q)$ is less than the sum of $c_i$, the coefficient of
      -- the monomial $c$ in $h * (P - Q)$ must be zero.
      have h_coeff_zero : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * (P - Q)) = 0 :=
          by
        rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
        simp only [Finsupp.equivFunOnFinite_symm_apply_apply,
          Finsupp.equivFunOnFinite_symm_apply_support]
        refine h_total_degree.trans_le ?_
        rw [h_deg]
        apply le_of_eq
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        by_contra hne
        apply hj
        simp [Function.mem_support, hne]
      simp_all? +decide [mul_sub]
      exact eq_of_sub_eq_zero h_coeff_zero

/--
Lemma 2.1.12 : The total degree of the difference between the product of linear terms and the
corresponding power of the sum polynomial is less than the size of the multiset
-/
lemma degree_product_minus_pow_lt {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}
    (E : Multiset (ZMod p)) (hE : E.card > 0) :
    ((E.map (fun e => (sumXPolynomial : MvPolynomial (Fin (k + 1)) (ZMod p)) - C e)).prod -
        (sumXPolynomial : MvPolynomial (Fin (k + 1)) (ZMod p)) ^ E.card).totalDegree
      < E.card := by
      -- Since every monomial of degree $|E|$ in $P$ has the same coefficient as in $Q$, the
      -- difference $P - Q$ has no terms of degree $|E|$.
      have h_coeff_eq : ∀ x : (Fin (k + 1)) →₀ ℕ, x.sum (fun _ n => n) = E.card →
          MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k + 1),
              MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                  MvPolynomial.X i) ^ E.card) = 0 := by
            -- Apply the lemma that states the coefficients of monomials of degree $|E|$ in $P$ and
            -- $Q$ are equal.
            intros x hx
            have h_coeff_eq :
                MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k + 1),
                    MvPolynomial.X i) - MvPolynomial.C e)).prod)
                        = MvPolynomial.coeff x ((∑ i : Fin (k + 1),
                            MvPolynomial.X i) ^ E.card) := by
              convert coeff_prod_sumX_minus_C_eq_coeff_sumX_pow_of_degree_eq E x _
              simpa [Finsupp.sum_fintype] using hx
            aesop
      -- Since there are no terms of degree $|E|$ in $P - Q$, the total degree of $P - Q$ must be
      -- strictly less than $|E|$.
      have h_total_degree_lt : ∀ x : (Fin (k + 1)) →₀ ℕ,
          x.sum (fun _ n => n) ≥ E.card →
              MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k + 1),
                  MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                      MvPolynomial.X i) ^ E.card) = 0 := by
        -- If x has degree greater than E.card, then since P and Q both have total degree E.card,
        -- their difference P - Q can't have any terms of degree higher than E.card. Therefore, the
        -- coefficient of x in P - Q must be zero because there are no such terms.
        intros x hx
        by_cases hx_eq : x.sum (fun _ n => n) = E.card
        · exact h_coeff_eq x hx_eq
        · -- Since $x$ has degree greater than $E.card$, it cannot be in the support of $P$ or $Q$,
          -- hence its coefficient in $P - Q$ is zero.
          have h_support : ∀ (P : MvPolynomial (Fin (k + 1)) (ZMod p)),
              P.totalDegree ≤ E.card → ∀ x : (Fin (k + 1)) →₀ ℕ,
              x.sum (fun _ n => n) > E.card → MvPolynomial.coeff x P = 0 := by
            intro P hP x hx
            rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
            exact lt_of_le_of_lt hP hx
          rw [MvPolynomial.coeff_sub, h_support _ _ _ (lt_of_le_of_ne hx (Ne.symm hx_eq)),
              h_support _ _ _ (lt_of_le_of_ne hx (Ne.symm hx_eq)), sub_self]
          · refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
            refine mul_le_of_le_one_right hE.le ?_
            refine le_trans (b := ?_) (Finset.sup_le ?_) ?_
            · exact 1
            · simp? +decide [MvPolynomial.coeff_sum, MvPolynomial.coeff_X']
              intro b hb; contrapose! hb; simp_all? +decide
              rw [Finset.card_eq_zero.mpr] <;> aesop
            · norm_num
          · convert totalDegree_prod_sumX_sub_C_eq_card E |> le_of_eq
      -- If the total degree were at least E.card, there would be a monomial in the support of P - Q
      -- with degree exactly E.card.
      by_contra h_contra
      obtain ⟨x, hx⟩ : ∃ x : (Fin (k + 1)) →₀ ℕ,
          x ∈ (MvPolynomial.support ((E.map (fun e => (∑ i : Fin (k + 1),
              MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                  MvPolynomial.X i) ^ E.card)) ∧ x.sum (fun _ n => n) = E.card := by
        have h_total_degree_lt :
            ∃ x ∈ MvPolynomial.support ((E.map (fun e => (∑ i : Fin (k + 1),
                MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                    MvPolynomial.X i) ^ E.card), x.sum (fun _ n => n) ≥ E.card := by
          contrapose! h_contra
          simp_all only [gt_iff_lt, ge_iff_le, Std.le_refl, implies_true, coeff_sub,
              MvPolynomial.mem_support_iff, ne_eq]
          rw [MvPolynomial.totalDegree]; aesop
        obtain ⟨x, hx₁, hx₂⟩ := h_total_degree_lt; use x; aesop
      exact absurd (h_coeff_eq x hx.2) (by aesop)

end AristotleLemmas

/-- Alon-Nathanson-Ruzsa Polynomial Method (Theorem 2.1)

Proof outline (by contradiction):
1. Assume the conclusion is false, so the restricted sumset S has at most m elements;
   extend S to a multiset E of Z_p with |E| = m (`extendToSize`).
2. Construct the polynomial Q(x_0,...,x_k) = h(x_0,...,x_k) * prod_{e in E} (x_0+...+x_k - e)
   (`constructionPolynomial`):
   - deg(Q) = deg(h) + m = sum c_i (`constructionPolynomial_totalDegree`)
   - Q vanishes on prod A_i, since each grid point sums to an element of E
     (`constructionPolynomial_vanishes`)
   - The coefficient of the monomial prod x_i^{c_i} in Q is nonzero, since it agrees with
     the corresponding coefficient of h * (x_0+...+x_k)^m
     (`constructionPolynomial_coeff_target_generalized`)
3. By Lemma 2.1.10 (`coeff_target_eq_zero_of_vanishes_on_grid`), a polynomial of total
   degree at most sum c_i that vanishes on prod A_i has zero coefficient at prod x_i^{c_i}:
   reducing Q modulo the elimination polynomials g_i = prod_{a in A_i} (x_i - a) leaves the
   target coefficient unchanged (`exists_remainder`), and the reduced polynomial vanishes
   identically by Lemma 2.2 (`eq_zero_of_eval_zero_at_prod_finset`).
4. Steps 2 and 3 contradict each other, so |S| >= m + 1; m < p follows since S is a subset
   of Z_p.
-/
theorem ANR_polynomial_method (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
    ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * h) ≠ 0) :
    let S : Finset (ZMod p) :=
      (Fintype.piFinset A).filter (fun f => h.eval f ≠ 0) |>.image (fun f => ∑ i, f i)
    S.card ≥ m + 1 ∧ m < p := by
  -- Define the restricted sumset S
  intro S
  have h_ne_zero : h ≠ 0 := by
    intro h_zero
    rw [h_zero, mul_zero, coeff_zero] at h_coeff
    exact h_coeff rfl
  -- Step 1: Prove |S| >= m + 1 by contradiction
  have hS_card : S.card ≥ m + 1 := by
    by_contra! H
    have hS_size : S.card ≤ m := by omega
    set E := extendToSize S m with hE_def
    have extendToSize_properties :
    S.val ⊆ extendToSize S m ∧ (extendToSize S m).card = m := by
      refine ⟨Multiset.subset_of_le (by simp [extendToSize]), ?_⟩
      dsimp [extendToSize]
      simp [hS_size]
    have hE_props : S.val ⊆ E ∧ E.card = m := by exact extendToSize_properties
    obtain ⟨hE_sub, hE_card⟩ := hE_props
    set Q := constructionPolynomial h E with hQ_def
    -- Q vanishes on prod A_i
    have hQ_zero : ∀ (x : Fin (k + 1) → ZMod p),
        (∀ i, x i ∈ A i) → eval x Q = 0 :=
            fun x a => constructionPolynomial_vanishes h A E hE_sub x a
    have h_prod_ne_zero : productPolynomial k E ≠ 0 := by exact productPolynomial_ne_zero k E
    have hQ_total_deg : Q.totalDegree = ∑ i, c i := by
      exact constructionPolynomial_totalDegree h h_ne_zero c m E hm hE_card h_prod_ne_zero
    have hQ_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q ≠ 0 := by
      rw [hQ_def]
      apply constructionPolynomial_coeff_target_generalized h c m hm h_coeff E hE_card
      · -- The product of (sumX - e) over E is equal to (sumX)^m plus a polynomial of degree less
        -- than m.
        have h_prod_eq :
            (E.map (fun e => (∑ i : Fin (k + 1), MvPolynomial.X i) - MvPolynomial.C e)).prod =
                (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m + (E.map (fun e => (∑ i : Fin (k + 1),
                    MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                        MvPolynomial.X i) ^ m := by
          ring
        -- The degree of the difference between the product and (sumX)^m is less than m.
        have h_diff_deg :
            (E.map (fun e => (∑ i : Fin (k + 1),
                MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                    MvPolynomial.X i) ^ m ≠ 0 →
          (E.map (fun e => (∑ i : Fin (k + 1),
              MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                  MvPolynomial.X i) ^ m ≠ 0 →
          ((E.map (fun e => (∑ i : Fin (k + 1),
              MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                  MvPolynomial.X i) ^ m).totalDegree < m := by
            intro h1 h2
            convert degree_product_minus_pow_lt E _
            · exact hE_card.symm
            · exact hE_card.symm
            · contrapose! h1; simp_all (config := { singlePass := Bool.true })
        by_cases h_diff_zero :
            (E.map (fun e => (∑ i : Fin (k + 1),
                MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                    MvPolynomial.X i) ^ m = 0
        · rw [sub_eq_zero.mp h_diff_zero]
        · -- Since the difference has a lower degree, the coefficient of the term with degree m in
          -- the product must be equal to the coefficient of the term with degree m in (sumX)^m.
          have h_coeff_eq : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (
              (E.map (fun e => (∑ i : Fin (k + 1),
                  MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1),
                      MvPolynomial.X i) ^ m) = 0 := by
            -- Since the total degree of the difference is less than m, any term with degree m must
            -- have a coefficient of zero.
            have h_coeff_zero : ∀ (P : MvPolynomial (Fin (k + 1)) (ZMod p)),
                P.totalDegree < m → MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) P = 0 := by
              intros P hP_deg
              have h_coeff_zero : ∀ (m : (Fin (k + 1)) →₀ ℕ),
                  m.sum (fun _ n => n) > P.totalDegree → MvPolynomial.coeff m P = 0 := by
                exact fun m a => coeff_eq_zero_of_totalDegree_lt a
              exact h_coeff_zero _ (by
                simpa [Finsupp.sum_fintype] using by
                  linarith [show h.totalDegree ≥ 0 from Nat.zero_le _])
            exact h_coeff_zero _ (h_diff_deg h_diff_zero h_diff_zero)
          simp? +zetaDelta at *
          exact eq_of_sub_eq_zero h_coeff_eq
      · intro d hd_ne_zero
        by_contra h_contra
        -- Apply the lemma `coeff_target_eq_zero_of_vanishes_on_grid` to $Q$.
        have h_coeff_zero : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q = 0 := by
          apply coeff_target_eq_zero_of_vanishes_on_grid
          any_goals tauto
          linarith
        -- Apply the lemma `coeff_mul_eq_of_degree_bound` with $h, P, P_{lead}, c, m$.
        have h_coeff_mul_eq : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (
            h *
            (E.map (fun e => ∑ i : Fin (k + 1),
                MvPolynomial.X i - MvPolynomial.C e)).prod)
                    = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * (∑ i : Fin (k + 1),
                        MvPolynomial.X i) ^ m) := by
          apply coeff_mul_eq_of_degree_bound
          any_goals exact m
          · linarith
          · norm_num +zetaDelta at *
            by_cases hm : m = 0
            · subst hm
              simp_all
            · -- Apply the lemma `degree_product_minus_pow_lt` with the hypothesis `hm` (which
              -- states that m is not zero).
              apply Or.inr; exact (by
              convert degree_product_minus_pow_lt _ _
              · exact hE_card.symm
              · exact hE_card.symm
              · exact hE_card.symm ▸ Nat.pos_of_ne_zero hm)
        exact h_coeff (by simpa only [mul_comm] using h_coeff_mul_eq.symm.trans h_coeff_zero)
      · -- By contradiction, assume the constant term of h is zero.
        by_contra h_const_zero
        -- If the constant term of h is zero, then the constant term of h * (∑ i, X i)^m is also
        -- zero.
        have h_const_zero_prod : MvPolynomial.coeff 0 (h * (∑ i, MvPolynomial.X i) ^ m) = 0 := by
          rw [MvPolynomial.coeff_mul, Finset.sum_eq_zero]; aesop
        -- By the properties of the product of polynomials, we can show that the coefficient of the
        -- target term in h * (∑ i, X i)^m is equal to the coefficient of the target term in h *
        -- P_{lead}.
        have h_coeff_eq : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (
            h *
            (∑ i,
                MvPolynomial.X i) ^ m)
                    = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
                        (h * (productPolynomial k E)) := by
          -- By the properties of polynomial multiplication, if the difference between two
          -- polynomials has a lower total degree, then their coefficients for the highest-degree
          -- term are equal.
          have h_diff_deg :
              (productPolynomial k E - (∑ i, MvPolynomial.X i) ^ m).totalDegree < m := by
            convert degree_product_minus_pow_lt E _
            · linarith
            · linarith
            · simp_all (config := { decide := Bool.true }) only [gt_iff_lt]
              contrapose! h_coeff
              have hm0 : m = 0 := Nat.le_zero.mp h_coeff
              subst hm0
              simp only [pow_zero, one_mul]
              have hS_empty : S = ∅ := by
                have hS_card : #S = 0 := by
                  have := H
                  omega
                exact Finset.card_eq_zero.mp hS_card
              have H_eval : ∀ ⦃x : Fin (k + 1) → ZMod p⦄,
                  (∀ a : Fin (k + 1), x a ∈ A a) → (MvPolynomial.eval x) h = 0 := by
                intro x hx
                by_contra heval
                have hx_mem : x ∈ Fintype.piFinset A := Fintype.mem_piFinset.mpr hx
                have hx_mem' : x ∈ ({f ∈ Fintype.piFinset A | (MvPolynomial.eval f) h ≠ 0}) :=
                  Finset.mem_filter.mpr ⟨hx_mem, heval⟩
                have : ∑ i, x i ∈ S := Finset.mem_image.mpr ⟨x, hx_mem', rfl⟩
                rw [hS_empty] at this
                exact Finset.notMem_empty _ this
              convert coeff_target_eq_zero_of_vanishes_on_grid h A c hA _ _
              · linarith
              · exact H_eval
          have h_coeff_eq : ∀ (P Q : MvPolynomial (Fin (k + 1)) (ZMod p)),
              (P - Q).totalDegree < m → MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (
                  h * P) = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * Q) := by
            intros P Q h_diff_deg
            apply coeff_mul_eq_of_degree_bound
            all_goals norm_cast
            · linarith
            · exact Or.inr h_diff_deg
          exact h_coeff_eq _ _ h_diff_deg |> Eq.symm
        apply h_coeff
        rw [mul_comm, h_coeff_eq]
        apply_rules [coeff_target_eq_zero_of_vanishes_on_grid]
        exact hQ_total_deg.le
    -- Since Q vanishes on the grid, the coefficient of the target monomial in Q is zero,
    -- contradicting hQ_coeff.
    have hQ_coeff_zero :
        MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q = 0 :=
      coeff_target_eq_zero_of_vanishes_on_grid Q A c hA hQ_total_deg.le hQ_zero
    contradiction
  -- Step 2: Prove m < p first (this is needed for the main argument)
  have hmp : m < p := by
    exact lt_of_lt_of_le (Nat.lt_of_succ_le hS_card) (
        le_trans (Finset.card_le_univ _) (by norm_num))
  exact ⟨hS_card, hmp⟩
