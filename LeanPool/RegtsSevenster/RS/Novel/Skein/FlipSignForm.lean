/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.FlipSignProduct

/-!
# The closed form of the flip-sign product

Each label `a` with `n` instances in `flipLabels L` contributes
`(oddPartnerSign ℓ (f a))^n * (-1)^(n*(n-1)/2)` to the sign
product of the flip sequence, so a sequence in which every label
occurs evenly contributes exactly `(−1)^length`.  That is the sign
bookkeeping the paired step of Proposition 3 runs on.
-/

namespace RS

open scoped Classical

variable {α : Type} {ℓ : ℕ}

/-- The empty flip sequence contributes no sign. -/
theorem flipSignProd_nil (f : α → Fin (2 * ℓ)) :
    flipSignProd f ([] : List (α × α)) = 1 := rfl

/-- One more flip contributes its two port signs, at the colours
reached so far. -/
theorem flipSignProd_cons (f : α → Fin (2 * ℓ)) (p : α × α)
    (L : List (α × α)) :
    flipSignProd f (p :: L) =
      oddPartnerSign ℓ (f p.1) * oddPartnerSign ℓ (f p.2) *
        flipSignProd (flipColours f p) L := rfl

/-- The flipped colour of a participating label has the opposite
sign. -/
theorem oddPartnerSign_flipColours_of_mem (f : α → Fin (2 * ℓ))
    (p : α × α) {a : α} (ha : a = p.1 ∨ a = p.2) :
    oddPartnerSign ℓ (flipColours f p a) = -oddPartnerSign ℓ (f a) := by
  simp only [flipColours, if_pos ha]
  exact oddPartnerSign_oddPartner ℓ (f a)

/-- A non-participating label keeps its colour. -/
theorem flipColours_of_not_mem (f : α → Fin (2 * ℓ))
    (p : α × α) {a : α} (ha : ¬(a = p.1 ∨ a = p.2)) :
    flipColours f p a = f a := by
  simp only [flipColours, if_neg ha]

/-- The triangular-number increment `T (n+1) = T n + n`. -/
private theorem tri_succ (n : ℕ) :
    (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  rcases n with _ | m
  · rfl
  · obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
    have h1 : (m + 1 + 1) * (m + 1) = m * (m + 1) + 2 * (m + 1) := by
      ring
    have h2 : m + 1 - 1 = m := by omega
    rw [h2, h1, mul_comm (m + 1) m, hk]
    omega

/-- For even `n` the triangular number `n*(n-1)/2` has the parity
of `n/2`. -/
private theorem tri_mod_two {n : ℕ} (hn : n % 2 = 0) :
    n * (n - 1) / 2 % 2 = n / 2 % 2 := by
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  subst hk
  rcases k with _ | m
  · rfl
  · have h0 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have h1 : 2 * (m + 1) * (2 * (m + 1) - 1)
        = 2 * ((m + 1) * (2 * m + 1)) := by
      rw [h0]; ring
    rw [h1, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
    have h2 : 2 * (m + 1) / 2 = m + 1 := by omega
    rw [h2, Nat.mul_mod]
    have h3 : (2 * m + 1) % 2 = 1 := by omega
    rw [h3, mul_one]
    omega

/-- Each flip contributes two label instances. -/
theorem flipLabels_length (L : List (α × α)) :
    (flipLabels L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [flipLabels_cons, List.length_cons, List.length_cons, ih,
      List.length_cons]
    omega

/-- The per-label algebra of one flip step. -/
private theorem step_algebra (x : ℤ) (n : ℕ) :
    x ^ (n + 1) * (-1 : ℤ) ^ ((n + 1) * n / 2) =
      x * ((-x) ^ n * (-1) ^ (n * (n - 1) / 2)) := by
  rw [tri_succ, neg_pow, pow_add, pow_succ]
  ring

/-- **The closed form of the flip-sign product**: each label `a`
with `n` instances in `flipLabels L` contributes the initial sign
to the `n`-th power times the triangular-number sign. -/
theorem flipSignProd_formula (f : α → Fin (2 * ℓ))
    (L : List (α × α)) (hd : ∀ p ∈ L, p.1 ≠ p.2) :
    flipSignProd f L =
      ∏ a ∈ (flipLabels L).toFinset,
        (oddPartnerSign ℓ (f a)) ^ ((flipLabels L).count a) *
          (-1) ^ (((flipLabels L).count a) *
            ((flipLabels L).count a - 1) / 2) := by
  induction L generalizing f with
  | nil => simp [flipSignProd_nil, flipLabels_nil]
  | cons p L ih =>
    have hij : p.1 ≠ p.2 := hd p (by simp)
    have hd' : ∀ q ∈ L, q.1 ≠ q.2 := fun q hq => hd q (by simp [hq])
    rw [flipSignProd_cons, ih (flipColours f p) hd', flipLabels_cons,
      List.toFinset_cons, List.toFinset_cons]
    have hsub : (flipLabels L).toFinset ⊆
        insert p.1 (insert p.2 (flipLabels L).toFinset) := fun a ha =>
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)
    have hone : ∀ a ∈ insert p.1 (insert p.2 (flipLabels L).toFinset),
        a ∉ (flipLabels L).toFinset →
        oddPartnerSign ℓ (flipColours f p a) ^ ((flipLabels L).count a) *
          (-1 : ℤ) ^ ((flipLabels L).count a *
            ((flipLabels L).count a - 1) / 2) = 1 := by
      intro a _ ha
      have hz : (flipLabels L).count a = 0 :=
        List.count_eq_zero.mpr fun hmem => ha (List.mem_toFinset.mpr hmem)
      rw [hz]
      norm_num
    rw [Finset.prod_subset hsub hone]
    have hfac : ∀ a ∈ insert p.1 (insert p.2 (flipLabels L).toFinset),
        oddPartnerSign ℓ (f a) ^ ((p.1 :: p.2 :: flipLabels L).count a) *
          (-1 : ℤ) ^ ((p.1 :: p.2 :: flipLabels L).count a *
            ((p.1 :: p.2 :: flipLabels L).count a - 1) / 2) =
        (if a = p.1 then oddPartnerSign ℓ (f p.1) else 1) *
          ((if a = p.2 then oddPartnerSign ℓ (f p.2) else 1) *
            (oddPartnerSign ℓ (flipColours f p a) ^
                ((flipLabels L).count a) *
              (-1 : ℤ) ^ ((flipLabels L).count a *
                ((flipLabels L).count a - 1) / 2))) := by
      intro a _
      by_cases h1 : a = p.1
      · subst h1
        have hc : (p.1 :: p.2 :: flipLabels L).count p.1
            = (flipLabels L).count p.1 + 1 := by
          rw [List.count_cons_self, List.count_cons_of_ne (Ne.symm hij)]
        rw [hc, if_pos rfl, if_neg hij,
          oddPartnerSign_flipColours_of_mem f p (Or.inl rfl), one_mul,
          Nat.add_sub_cancel]
        exact step_algebra _ _
      · by_cases h2 : a = p.2
        · subst h2
          have hc : (p.1 :: p.2 :: flipLabels L).count p.2
              = (flipLabels L).count p.2 + 1 := by
            rw [List.count_cons_of_ne hij, List.count_cons_self]
          rw [hc, if_neg h1, if_pos rfl,
            oddPartnerSign_flipColours_of_mem f p (Or.inr rfl), one_mul,
            Nat.add_sub_cancel]
          exact step_algebra _ _
        · have hc : (p.1 :: p.2 :: flipLabels L).count a
              = (flipLabels L).count a := by
            rw [List.count_cons_of_ne (Ne.symm h1),
              List.count_cons_of_ne (Ne.symm h2)]
          rw [hc, if_neg h1, if_neg h2,
            flipColours_of_not_mem f p (not_or.mpr ⟨h1, h2⟩), one_mul,
            one_mul]
    refine Eq.trans ?_ (Finset.prod_congr rfl hfac).symm
    conv_rhs => rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_ite_eq', Finset.prod_ite_eq']
    rw [if_pos (Finset.mem_insert_self p.1 _),
      if_pos (Finset.mem_insert_of_mem (Finset.mem_insert_self p.2 _))]
    ring

/-- **The even corollary**: a flip sequence in which every label
occurs an even number of times has sign product `(−1)^length`. -/
theorem flipSignProd_of_even (f : α → Fin (2 * ℓ))
    (L : List (α × α)) (hd : ∀ p ∈ L, p.1 ≠ p.2)
    (heven : ∀ a, (flipLabels L).count a % 2 = 0) :
    flipSignProd f L = (-1) ^ L.length := by
  rw [flipSignProd_formula f L hd]
  have h1 : ∀ a ∈ (flipLabels L).toFinset,
      oddPartnerSign ℓ (f a) ^ ((flipLabels L).count a) *
        (-1 : ℤ) ^ ((flipLabels L).count a *
          ((flipLabels L).count a - 1) / 2)
      = (-1 : ℤ) ^ ((flipLabels L).count a *
          ((flipLabels L).count a - 1) / 2) := by
    intro a _
    have he := heven a
    obtain ⟨k, hk⟩ : ∃ k, (flipLabels L).count a = 2 * k :=
      ⟨(flipLabels L).count a / 2, by omega⟩
    rw [hk, pow_mul, pow_two, oddPartnerSign_mul_self, one_pow, one_mul,
      ← hk]
  rw [Finset.prod_congr rfl h1, Finset.prod_pow_eq_pow_sum]
  have hcard : ∑ a ∈ (flipLabels L).toFinset, (flipLabels L).count a
      = (flipLabels L).length := by
    simp
  have hsum2 : ∑ a ∈ (flipLabels L).toFinset,
      ((flipLabels L).count a / 2) = L.length := by
    have h2 : ∑ a ∈ (flipLabels L).toFinset, (flipLabels L).count a
        = 2 * ∑ a ∈ (flipLabels L).toFinset,
            ((flipLabels L).count a / 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have he := heven a
      omega
    have hlen := flipLabels_length L
    omega
  have hmod : (∑ a ∈ (flipLabels L).toFinset,
      ((flipLabels L).count a * ((flipLabels L).count a - 1) / 2)) % 2
      = L.length % 2 := by
    rw [Finset.sum_nat_mod]
    have h3 : ∀ a ∈ (flipLabels L).toFinset,
        ((flipLabels L).count a * ((flipLabels L).count a - 1) / 2) % 2
          = ((flipLabels L).count a / 2) % 2 :=
      fun a _ => tri_mod_two (heven a)
    rw [Finset.sum_congr rfl h3, ← Finset.sum_nat_mod, hsum2]
  rw [neg_one_pow_eq_pow_mod_two, hmod, ← neg_one_pow_eq_pow_mod_two]

end RS
