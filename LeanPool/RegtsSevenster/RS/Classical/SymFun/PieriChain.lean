/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SymFun.AlternantStrict
public import LeanPool.RegtsSevenster.RS.Common.RowLenChain

/-!
# Pieri chain: positivity of alternant coefficients along diagram chains

The staircase exponent vector `eVec`, and the positivity of the
coefficient of the target monomial in `p₁ʳ · a_{eVec λ}` when `μ`
extends `λ` by `r` cells.
-/

@[expose] public section

namespace RS

open Finset MvPolynomial Equiv

/-- The staircase exponent vector of a diagram in `k` variables. -/
noncomputable def eVec (nu : YoungDiagram) (k : ℕ) : Fin k → ℕ :=
  fun i => nu.rowLen i + ((k - 1) - (i : ℕ))

/-- The staircase exponent vector is strictly decreasing. -/
theorem eVec_strict (nu : YoungDiagram) (k : ℕ) :
    ∀ i j : Fin k, i < j → eVec nu k j < eVec nu k i := by
  intro i j hij
  unfold eVec
  have hi := i.isLt
  have hj := j.isLt
  have hrl : nu.rowLen ↑j ≤ nu.rowLen ↑i := nu.rowLen_anti ↑i ↑j (le_of_lt hij)
  omega

open scoped Classical in
/-- Coefficients of a power of the first power sum against an
alternant are natural numbers: no cancellation into negatives. -/
theorem coeff_pow_p1_altDet_natCast {k : ℕ} (r : ℕ) (w : Fin k → ℕ)
    (hw : ∀ i j : Fin k, i < j → w j < w i) :
    ∀ e : Fin k → ℕ, (∀ i j : Fin k, i < j → e j < e i) →
    ∃ N : ℕ, ((∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ r * altDet e).coeff
      (∑ i, Finsupp.single i (w i)) = N := by
  induction r with
  | zero =>
    intro e he
    rw [pow_zero, one_mul, alternant_coeff_strict e w he hw]
    split
    · exact ⟨1, Nat.cast_one.symm⟩
    · exact ⟨0, Nat.cast_zero.symm⟩
  | succ r ih =>
    intro e he
    rw [pow_succ, mul_assoc, p1_mul_altDet, Finset.mul_sum,
      MvPolynomial.coeff_sum]
    -- Each summand is a natural-number cast
    have hterm : ∀ i₀ : Fin k, ∃ N : ℕ,
        ((∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ r *
            altDet (Function.update e i₀ (e i₀ + 1))).coeff (∑ j, Finsupp.single j (w j)) = ↑N := by
      intro i₀
      by_cases hrep : ∃ a : Fin k, a ≠ i₀ ∧ e a = e i₀ + 1
      · -- Repeat: altDet vanishes
        obtain ⟨a, hai, hae⟩ := hrep
        have hzero : altDet (Function.update e i₀ (e i₀ + 1)) = 0 :=
          altDet_eq_zero_of_repeat _ hai (by
            rw [Function.update_of_ne hai _ _, Function.update_self]
            exact hae)
        rw [hzero, mul_zero, AddMonoidAlgebra.coeff_zero]
        exact ⟨0, Nat.cast_zero.symm⟩
      · -- No repeat: the bumped vector is still strictly decreasing
        push Not at hrep
        apply ih
        intro a b hab
        by_cases ha : a = i₀
        · subst ha
          rw [Function.update_self, Function.update_of_ne (ne_of_gt hab) _ _]
          exact Nat.lt_succ_of_lt (he _ b hab)
        · rw [Function.update_of_ne ha _ _]
          by_cases hb : b = i₀
          · subst hb
            rw [Function.update_self]
            have h1 := he a _ hab
            have h2 := hrep a ha
            omega
          · rw [Function.update_of_ne hb _ _]
            exact he a b hab
    choose Nf hNf using hterm
    exact ⟨Finset.univ.sum Nf, by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => hNf i⟩

open scoped Classical in
/-- **Positivity along a chain**: when one diagram extends another
by `r` cells, the target monomial's coefficient is a positive
natural number. -/
theorem coeff_chain_pos {k : ℕ} (lam mu : YoungDiagram)
    (hle : lam ≤ mu) (r : ℕ) (hcard : mu.card = lam.card + r)
    (hk : mu.colLen 0 ≤ k) :
    ∃ N : ℕ, 0 < N ∧
      ((∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ r *
          altDet (eVec lam k)).coeff (∑ i, Finsupp.single i (eVec mu k i)) = N := by
  induction r generalizing lam with
  | zero =>
    have heq : lam = mu := YoungDiagram.ext
      (Finset.eq_of_subset_of_card_le
        (YoungDiagram.cells_subset_iff.mpr hle)
        (show mu.card ≤ lam.card from by omega))
    subst heq
    rw [pow_zero, one_mul,
        alternant_coeff_strict _ _ (eVec_strict _ _) (eVec_strict _ _),
        ite_eq_left rfl]
    exact ⟨1, by omega, Nat.cast_one.symm⟩
  | succ r ih =>
    -- Intermediate diagram
    have hlt : lam.card < mu.card := by omega
    obtain ⟨nu, hle_nu, hnu_mu, hcard_nu⟩ :=
      exists_intermediate_diagram hle hlt
    -- Bump row
    obtain ⟨i₀, hrowLen⟩ := rowLen_of_card_succ hle_nu hcard_nu
    -- i₀ < k
    have hi₀_mem : (i₀, 0) ∈ nu := by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      have := hrowLen i₀; rw [ite_eq_left rfl] at this
      have := rowLen_mono hle_nu i₀; omega
    have hi₀k : i₀ < k := by
      have h1 : i₀ < nu.colLen 0 :=
        YoungDiagram.mem_iff_lt_colLen.mp hi₀_mem
      have h2 : nu.colLen 0 ≤ mu.colLen 0 := by
        by_contra h
        have : (mu.colLen 0, 0) ∈ nu :=
          YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        have := YoungDiagram.mem_iff_lt_colLen.mp (hnu_mu this)
        omega
      omega
    -- eVec nu k = update (eVec lam k) ⟨i₀, hi₀k⟩ ...
    have heVec : eVec nu k = Function.update (eVec lam k) ⟨i₀, hi₀k⟩
        (eVec lam k ⟨i₀, hi₀k⟩ + 1) := by
      funext ⟨i, hi⟩
      simp only [eVec, Function.update_apply, Fin.mk.injEq]
      have hbump := hrowLen i
      split_ifs at hbump ⊢ with heq
      · subst heq; omega
      · omega
    -- Expand via Pieri
    rw [pow_succ, mul_assoc, p1_mul_altDet, Finset.mul_sum,
        MvPolynomial.coeff_sum]
    -- Each summand is a ℕ-cast
    have hterm : ∀ i : Fin k, ∃ N : ℕ,
        ((∑ l : Fin k, (X l : MvPolynomial (Fin k) ℂ)) ^ r *
            altDet (Function.update (eVec lam k) i
              (eVec lam k i + 1))).coeff (∑ j, Finsupp.single j (eVec mu k j)) = ↑N := by
      intro i
      by_cases hrep : ∃ a : Fin k, a ≠ i ∧
          eVec lam k a = eVec lam k i + 1
      · obtain ⟨a, hai, hae⟩ := hrep
        rw [altDet_eq_zero_of_repeat _ hai (by
              rw [Function.update_of_ne hai _ _, Function.update_self]
              exact hae),
            mul_zero, AddMonoidAlgebra.coeff_zero]
        exact ⟨0, Nat.cast_zero.symm⟩
      · push Not at hrep
        exact coeff_pow_p1_altDet_natCast r (eVec mu k)
          (eVec_strict mu k) _ (by
          intro a b hab
          by_cases ha : a = i
          · subst ha
            rw [Function.update_self,
                Function.update_of_ne (ne_of_gt hab) _ _]
            exact Nat.lt_succ_of_lt (eVec_strict lam k _ _ hab)
          · rw [Function.update_of_ne ha _ _]
            by_cases hb : b = i
            · subst hb
              rw [Function.update_self]
              have h1 := eVec_strict lam k a _ hab
              have h2 := hrep a ha
              omega
            · rw [Function.update_of_ne hb _ _]
              exact eVec_strict lam k a b hab)
    choose Nf hNf using hterm
    -- The i₀-th term is positive via IH
    have hNf_pos : 0 < Nf ⟨i₀, hi₀k⟩ := by
      obtain ⟨N₀, hN₀_pos, hN₀_eq⟩ := ih nu hnu_mu (by omega)
      have h1 := hNf ⟨i₀, hi₀k⟩
      rw [← heVec] at h1
      rw [hN₀_eq] at h1
      rw [Nat.cast_inj] at h1
      omega
    -- Combine
    refine ⟨∑ i : Fin k, Nf i, ?_, ?_⟩
    · exact lt_of_lt_of_le hNf_pos
        (Finset.single_le_sum (fun i _ => Nat.zero_le (Nf i))
          (Finset.mem_univ (⟨i₀, hi₀k⟩ : Fin k)))
    · rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => hNf i

end RS
