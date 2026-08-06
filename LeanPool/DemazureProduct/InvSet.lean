/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import LeanPool.DemazureProduct.AspPerm
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.Interval.Set.Infinite

/-!
# Inversion sets

This file gives a characterization of the inversion set of ASP permutations.
It corresponds to Theorem 2.13 of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).
-/

namespace LeanPool.DemazureProduct


/-- The axioms characterizing inversion sets of ASP permutations: directedness,
closure, coclosure, and finite in/out degree. *Definition 2.12 (`defn:aspSet`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
structure AspSet_prop (I : Set (ℤ × ℤ)) where
  directed :
    (∀ u v : ℤ, ⟨u, v⟩ ∈ I → u < v)
  closed:
    (∀ u v w : ℤ, (u, v) ∈ I → (v, w) ∈ I → ⟨u, w⟩ ∈ I)
  coclosed:
    (∀ u v w : ℤ, (u < v) → (v < w) → (u, v) ∉ I → (v, w) ∉ I → ⟨u, w⟩ ∉ I)
  finiteOutdegree:
    (∀ u : ℤ, { v : ℤ | ⟨u, v⟩ ∈ I }.Finite)
  finiteIndegree:
    (∀ v : ℤ, { u : ℤ | ⟨u, v⟩ ∈ I }.Finite)

/-- An abstract ASP inversion set: a set of boxes equipped with the axioms of
`AspSet_prop`. -/
structure AspSet where
  /-- The underlying set of inversion boxes. -/
  I : Set (ℤ × ℤ)
  /-- The axioms satisfied by the underlying inversion-box set. -/
  prop : AspSet_prop I

instance : SetLike AspSet (ℤ × ℤ) where
  coe := AspSet.I
  coe_injective := by
    intro a b h
    cases a; simp_all

@[simp] lemma mem_AspSet (asps : AspSet) (u v : ℤ) :
    ⟨u, v⟩ ∈ asps ↔ ⟨u, v⟩ ∈ asps.I := Iff.rfl

namespace AspSet

/-- Two `AspSet`s are equal if their underlying sets of boxes are equal. -/
theorem ext {A B : AspSet} (hI : A.I = B.I) : A = B := by
  cases A
  simp_all

/-- Every inversion box of an abstract ASP set is directed upward. -/
theorem directed (asps : AspSet) : ∀ u v : ℤ, ⟨u, v⟩ ∈ asps → u < v :=
  asps.prop.directed

/-- Abstract ASP inversion sets are transitively closed. -/
theorem closed (asps : AspSet) :
    ∀ u v w : ℤ, (u, v) ∈ asps → (v, w) ∈ asps → ⟨u, w⟩ ∈ asps :=
  asps.prop.closed

/-- Abstract ASP inversion sets are transitively coclosed. -/
theorem coclosed (asps : AspSet) :
    ∀ u v w : ℤ, u < v → v < w → (u, v) ∉ asps → (v, w) ∉ asps → ⟨u, w⟩ ∉ asps :=
  asps.prop.coclosed

/-- Each row of an abstract ASP inversion set is finite. -/
theorem finiteOutdegree (asps : AspSet) :
    ∀ u : ℤ, { v : ℤ | ⟨u, v⟩ ∈ asps }.Finite :=
  asps.prop.finiteOutdegree

/-- Each column of an abstract ASP inversion set is finite. -/
theorem finiteIndegree (asps : AspSet) :
    ∀ v : ℤ, { u : ℤ | ⟨u, v⟩ ∈ asps }.Finite :=
  asps.prop.finiteIndegree

private lemma not_mem_of_ge (asps : AspSet) {m n : ℤ} (n_le_m : n ≤ m) : ⟨m, n⟩ ∉ asps := by
  intro h
  exact (not_lt_of_ge n_le_m) (asps.directed m n h)

@[simp] private lemma not_mem_self (asps : AspSet) (n : ℤ) : ⟨n, n⟩ ∉ asps.I :=
  asps.not_mem_of_ge (le_refl n)

/-- The order on indices after the inversions in `asps` are applied. -/
private def post_lt (asps : AspSet) (m n : ℤ) : Prop :=
  (m < n ∧ ⟨m, n⟩ ∉ asps) ∨ (n < m ∧ ⟨n, m⟩ ∈ asps)

@[simp] private lemma not_post_lt_self (asps : AspSet) (n : ℤ) : ¬ asps.post_lt n n := by
  simp only [post_lt, lt_self_iff_false, mem_AspSet, false_and, or_self, not_false_eq_true]

private lemma post_lt_iff_not_mem (asps : AspSet) {m n : ℤ} (m_lt_n : m < n) :
    asps.post_lt m n ↔ ⟨m, n⟩ ∉ asps := by
  simp only [post_lt, m_lt_n, mem_AspSet, true_and, not_lt_of_gt m_lt_n, false_and, or_false]

private lemma post_lt_swap_iff_mem (asps : AspSet) {m n : ℤ} (m_le_n : m ≤ n) :
    asps.post_lt n m ↔ ⟨m, n⟩ ∈ asps := by
  rcases lt_or_eq_of_le m_le_n with m_lt_n | rfl
  · simp only [post_lt, not_lt_of_gt m_lt_n, mem_AspSet, false_and, m_lt_n, true_and, false_or]
  · exact iff_of_false (not_post_lt_self asps m) (not_mem_self asps m)

private lemma post_lt_trans (asps : AspSet) {l m n : ℤ}
  (hlm : asps.post_lt l m) (hmn : asps.post_lt m n) :
  asps.post_lt l n := by
  rcases hlm with (⟨l_lt_m, lm_nI⟩ | ⟨m_lt_l, ml_I⟩)
  · rcases hmn with (⟨m_lt_n, mn_nI⟩ | ⟨n_lt_m, nm_I⟩)
    · left
      refine ⟨lt_trans l_lt_m m_lt_n, ?_⟩
      apply asps.coclosed l m n <;> assumption
    · by_cases hl : l < n
      · left
        refine ⟨hl, ?_⟩
        contrapose! lm_nI with hln
        apply asps.closed l n m <;> assumption
      · right
        have n_lt_l : n < l := lt_of_le_of_ne (le_of_not_gt hl) fun h => lm_nI (h ▸ nm_I)
        refine ⟨n_lt_l, ?_⟩
        contrapose! nm_I with nl_nI
        apply asps.coclosed n l m <;> assumption
  · rcases hmn with (⟨m_lt_n, mn_nI⟩ | ⟨n_lt_m, nm_I⟩)
    · by_cases hl : l < n
      · left
        refine ⟨hl, ?_⟩
        contrapose! mn_nI with ln_I
        apply asps.closed m l n <;> assumption
      · right
        have n_lt_l : n < l := lt_of_le_of_ne (le_of_not_gt hl) fun h => mn_nI (h ▸ ml_I)
        refine ⟨n_lt_l, ?_⟩
        contrapose! ml_I with nl_nI
        apply asps.coclosed m n l <;> assumption
    · right
      refine ⟨lt_trans n_lt_m m_lt_l, ?_⟩
      apply asps.closed n m l <;> assumption

private theorem post_lt_trichotomous (asps : AspSet) : Std.Trichotomous asps.post_lt := by
  -- Proof written by Codex.
  exact Std.trichotomous_of_rel_or_eq_or_rel_swap fun {m n} => by
    rcases lt_trichotomy m n with m_lt_n | rfl | n_lt_m
    · by_cases mn_I : ⟨m, n⟩ ∈ asps
      · exact Or.inr <| Or.inr <| (post_lt_swap_iff_mem asps (le_of_lt m_lt_n)).mpr mn_I
      · exact Or.inl <| (post_lt_iff_not_mem asps m_lt_n).mpr mn_I
    · exact Or.inr <| Or.inl rfl
    · by_cases nm_I : ⟨n, m⟩ ∈ asps
      · exact Or.inl <| (post_lt_swap_iff_mem asps (le_of_lt n_lt_m)).mpr nm_I
      · exact Or.inr <| Or.inr <| (post_lt_iff_not_mem asps n_lt_m).mpr nm_I

instance (asps : AspSet) : IsStrictTotalOrder ℤ asps.post_lt where
  toTrichotomous := post_lt_trichotomous asps
  irrefl := not_post_lt_self asps
  trans _ _ _ := post_lt_trans asps

/-- The inversion set of an ASP permutation forms an ASP set. -/
lemma AspSet_InvSet_of_AspPerm (τ : AspPerm) : AspSet_prop (invSet τ) := by
  constructor
  · intro u v uv_inv
    exact uv_inv.1
  · intro u v w uv_inv vw_inv
    have h1 := lt_trans uv_inv.1 vw_inv.1
    have h2 := lt_trans vw_inv.2 uv_inv.2
    exact ⟨h1, h2⟩
  · intro u v w u_lt_v v_lt_w uv_inv vw_inv
    have h1 : u < w := lt_trans u_lt_v v_lt_w
    have h2 : τ u ≤ τ v := by
      contrapose! uv_inv
      exact ⟨u_lt_v, uv_inv⟩
    have h3 : τ v ≤ τ w := by
      contrapose! vw_inv
      exact ⟨v_lt_w, vw_inv⟩
    have h4 := le_trans h2 h3
    contrapose! h4
    exact h4.2
  · exact τ.outset_finite
  · exact τ.inset_finite

/-- The abstract inversion set associated to an ASP permutation. -/
def ofAspPerm (τ : AspPerm) : AspSet :=
  ⟨invSet τ, AspSet_InvSet_of_AspPerm τ⟩

/-- The finite set of inversion sources ending at `n`. -/
noncomputable abbrev inset (asps : AspSet) (n : ℤ) : Finset ℤ :=
  (asps.finiteIndegree n).toFinset

/-- The finite set of inversion targets starting at `n`. -/
noncomputable abbrev outset (asps : AspSet) (n : ℤ) : Finset ℤ :=
  (asps.finiteOutdegree n).toFinset

lemma mem_inset (asps : AspSet) (n x : ℤ) :
    x ∈ asps.inset n ↔ ⟨x, n⟩ ∈ asps := by
  simp only [inset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, mem_AspSet]

lemma mem_outset (asps : AspSet) (n x : ℤ) :
    x ∈ asps.outset n ↔ ⟨n, x⟩ ∈ asps := by
  simp only [outset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, mem_AspSet]

/-- The half-open interval for the order `post_lt`. These are the elements
`l` with `m ≤ l < n` in the post-inversion order. -/
private lemma post_Ico_set_finite (asps : AspSet) (m n : ℤ) :
    ({l : ℤ | asps.post_lt l n ∧ ¬ asps.post_lt l m} : Set ℤ).Finite := by
  -- Proof written by GPT 5.5.
  refine (Finset.finite_toSet (Finset.Ico m n ∪ (asps.inset m ∪ asps.outset n))).subset ?_
  intro l hl
  simp only [Set.mem_ofPred_eq] at hl
  simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_Ico, mem_inset, mem_outset]
  rcases hl.1 with ⟨l_lt_n, ln_nI⟩ | ⟨n_lt_l, nl_I⟩
  · by_cases m_le_l : m ≤ l
    · exact Or.inl ⟨m_le_l, l_lt_n⟩
    · right
      left
      have l_lt_m : l < m := lt_of_not_ge m_le_l
      by_contra lm_nI
      exact hl.2 (Or.inl ⟨l_lt_m, lm_nI⟩)
  · exact Or.inr (Or.inr nl_I)

private noncomputable def post_Ico (asps : AspSet) (m n : ℤ) : Finset ℤ :=
  (asps.post_Ico_set_finite m n).toFinset

@[simp] private lemma mem_post_Ico (asps : AspSet) (m n l : ℤ) :
    l ∈ asps.post_Ico m n ↔ asps.post_lt l n ∧ ¬ asps.post_lt l m := by
  simp only [post_Ico, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

private lemma post_Ico_swap_eq_empty_of_post_lt (asps : AspSet) {m n : ℤ} (hmn : asps.post_lt m n) :
    asps.post_Ico n m = ∅ := by
  -- Proof written by GPT 5.5.
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := (mem_post_Ico asps n m x).mp hx
  exact hx'.2 (post_lt_trans asps hx'.1 hmn)

/-- Reconstruct a function `ℤ → ℤ` from an abstract ASP inversion set and a
shift parameter `χ`. -/
noncomputable def recon (asps : AspSet) (χ : ℤ) : ℤ → ℤ :=
  fun n => n + (asps.outset n).card - (asps.inset n).card - χ

section σ_diff
variable (asps : AspSet) (m n χ : ℤ)
/-- The reconstructed function with the fixed shift `χ`. -/
noncomputable abbrev σ := asps.recon χ

open Utils

private lemma endpointIndicator_eq_post_lt (a k : ℤ) :
    oneIf (k < a) - oneIf (k ∈ asps.inset a) + oneIf (k ∈ asps.outset a) =
      oneIf (asps.post_lt k a) := by
  classical
  rcases lt_trichotomy k a with k_lt_a | rfl | a_lt_k
  · have not_out : k ∉ asps.outset a := fun hk =>
      absurd (asps.directed a k ((mem_outset asps a k).mp hk)) (not_lt_of_ge k_lt_a.le)
    rw [post_lt_iff_not_mem asps k_lt_a]; simp only [← mem_inset]
    by_cases hin : k ∈ asps.inset a <;> simp [oneIf, k_lt_a, not_out, hin]
  · simp_all
  · have not_k_lt_a : ¬ k < a := not_lt_of_ge a_lt_k.le
    have not_in : k ∉ asps.inset a := fun hk =>
      absurd (asps.directed k a ((mem_inset asps a k).mp hk)) (not_lt_of_ge a_lt_k.le)
    rw [post_lt_swap_iff_mem asps a_lt_k.le]; simp_all

private noncomputable def sigmaIndicator (asps : AspSet) (m n k : ℤ) : ℤ :=
  oneIf (k ∈ Finset.Ico m n)
    + oneIf (k ∈ asps.inset m)
    - oneIf (k ∈ asps.outset m)
    - oneIf (k ∈ asps.inset n)
    + oneIf (k ∈ asps.outset n)

private noncomputable def postIndicator (asps : AspSet) (m n k : ℤ) : ℤ :=
  oneIf (k ∈ asps.post_Ico m n) - oneIf (k ∈ asps.post_Ico n m)

private lemma sigmaIndicator_support_subset :
    Function.support (sigmaIndicator asps m n) ⊆
      (Finset.Ico m n ∪
        (asps.inset m ∪ (asps.outset m ∪ (asps.inset n ∪ asps.outset n)))) := by
  -- Proof written by GPT 5.5.
  intro k hk
  by_contra hkU
  simp only [Set.mem_union, not_or] at hkU
  have hIco : k ∉ Finset.Ico m n := hkU.1
  have hin_m : k ∉ asps.inset m := hkU.2.1
  have hout_m : k ∉ asps.outset m := hkU.2.2.1
  have hin_n : k ∉ asps.inset n := hkU.2.2.2.1
  have hout_n : k ∉ asps.outset n := hkU.2.2.2.2
  have hk_zero : sigmaIndicator asps m n k = 0 := by
    simp only [sigmaIndicator, oneIf, hIco, ↓reduceIte, hin_m, add_zero,
      hout_m, sub_self, hin_n, hout_n]
  exact hk hk_zero

private lemma postIndicator_support_subset :
    Function.support (postIndicator asps m n) ⊆
      (asps.post_Ico m n ∪ asps.post_Ico n m) := by
  -- Proof written by GPT 5.5.
  intro k hk
  by_contra hkU
  simp only [Set.mem_union, not_or] at hkU
  have hmn : k ∉ asps.post_Ico m n := hkU.1
  have hnm : k ∉ asps.post_Ico n m := hkU.2
  have hk_zero : postIndicator asps m n k = 0 := by
    simp only [postIndicator, oneIf, hmn, ↓reduceIte, hnm, sub_self]
  exact hk hk_zero

private lemma finsum_sigmaIndicator (m_le_n : m ≤ n) :
    (∑ᶠ k : ℤ, sigmaIndicator asps m n k) = asps.σ χ n - asps.σ χ m := by
  -- Proof written by GPT 5.5.
  let U := Finset.Ico m n ∪
    (asps.inset m ∪ (asps.outset m ∪ (asps.inset n ∪ asps.outset n)))
  have hIco : Finset.Ico m n ⊆ U := by
    intro k hk
    simp only [Finset.mem_union, hk, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, true_or, U]
  have hin_m : asps.inset m ⊆ U := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_Ico, hk, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, true_or, or_true, U]
  have hout_m : asps.outset m ⊆ U := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_Ico, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, hk, true_or, or_true, U]
  have hin_n : asps.inset n ⊆ U := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_Ico, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, hk, true_or, or_true, U]
  have hout_n : asps.outset n ⊆ U := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_Ico, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, hk, or_true, U]
  rw [finsum_eq_sum_of_support_subset
    (f := fun k : ℤ => sigmaIndicator asps m n k) (s := U)]
  · calc
      (∑ k ∈ U, sigmaIndicator asps m n k)
          = (∑ k ∈ U, oneIf (k ∈ Finset.Ico m n))
            + (∑ k ∈ U, oneIf (k ∈ asps.inset m))
            - (∑ k ∈ U, oneIf (k ∈ asps.outset m))
            - (∑ k ∈ U, oneIf (k ∈ asps.inset n))
            + (∑ k ∈ U, oneIf (k ∈ asps.outset n)) := by
              simp only [sigmaIndicator, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = asps.σ χ n - asps.σ χ m := by
        rw [sum_oneIf_mem_of_subset hIco, sum_oneIf_mem_of_subset hin_m,
          sum_oneIf_mem_of_subset hout_m, sum_oneIf_mem_of_subset hin_n,
          sum_oneIf_mem_of_subset hout_n]
        unfold σ recon
        have hIco_card : ((Finset.Ico m n).card : ℤ) = n - m := by
          simp only [Int.card_Ico, Int.ofNat_toNat, Int.sub_nonneg, m_le_n, sup_of_le_left]
        linarith
  · simpa [U] using sigmaIndicator_support_subset asps m n

private lemma finsum_postIndicator :
    (∑ᶠ k : ℤ, postIndicator asps m n k) =
      ((asps.post_Ico m n).card : ℤ) - (asps.post_Ico n m).card := by
  -- Proof written by GPT 5.5.
  let U := asps.post_Ico m n ∪ asps.post_Ico n m
  have hmn : asps.post_Ico m n ⊆ U := by
    intro k hk
    simp only [U, Finset.mem_union, hk, true_or]
  have hnm : asps.post_Ico n m ⊆ U := by
    intro k hk
    simp only [U, Finset.mem_union, hk, or_true]
  rw [finsum_eq_sum_of_support_subset
    (f := fun k : ℤ => postIndicator asps m n k) (s := U)]
  · calc
      (∑ k ∈ U, postIndicator asps m n k)
          = (∑ k ∈ U, oneIf (k ∈ asps.post_Ico m n))
            - (∑ k ∈ U, oneIf (k ∈ asps.post_Ico n m)) := by
              simp only [postIndicator, Finset.sum_sub_distrib]
      _ = ((asps.post_Ico m n).card : ℤ) - (asps.post_Ico n m).card := by
        rw [sum_oneIf_mem_of_subset hmn, sum_oneIf_mem_of_subset hnm]
  · simpa [U] using postIndicator_support_subset asps m n

private lemma sigmaIndicator_eq_post_lt_sub (m_le_n : m ≤ n) (k : ℤ) :
    sigmaIndicator asps m n k = oneIf (asps.post_lt k n) - oneIf (asps.post_lt k m) := by
  -- Proof written by GPT 5.5.
  classical
  calc
    sigmaIndicator asps m n k
        = (oneIf (k < n) - oneIf (k < m))
          + oneIf (k ∈ asps.inset m)
          - oneIf (k ∈ asps.outset m)
          - oneIf (k ∈ asps.inset n)
          + oneIf (k ∈ asps.outset n) := by
            rw [sigmaIndicator, oneIf_Ico_eq_sub m n m_le_n k]
    _ = (oneIf (k < n) - oneIf (k ∈ asps.inset n) + oneIf (k ∈ asps.outset n))
          - (oneIf (k < m) - oneIf (k ∈ asps.inset m) + oneIf (k ∈ asps.outset m)) := by
            ring
    _ = oneIf (asps.post_lt k n) - oneIf (asps.post_lt k m) := by
      rw [endpointIndicator_eq_post_lt asps n k, endpointIndicator_eq_post_lt asps m k]

private lemma postIndicator_eq_post_lt_sub (k : ℤ) :
    postIndicator asps m n k = oneIf (asps.post_lt k n) - oneIf (asps.post_lt k m) := by
  -- Proof written by GPT 5.5.
  classical
  by_cases hn : asps.post_lt k n <;> by_cases hm : asps.post_lt k m <;>
    simp only [postIndicator, mem_post_Ico, oneIf, hn, hm, if_true, if_false,
      true_and, false_and, not_true_eq_false, not_false_eq_true, sub_self,
      sub_zero, zero_sub]

private lemma sigmaIndicator_eq_postIndicator (m_le_n : m ≤ n) (k : ℤ) :
    sigmaIndicator asps m n k = postIndicator asps m n k := by
  -- Proof written by GPT 5.5.
  rw [sigmaIndicator_eq_post_lt_sub asps m n m_le_n k, postIndicator_eq_post_lt_sub asps m n k]

private lemma σ_diff_post (m_le_n : m ≤ n) : asps.σ χ n - asps.σ χ m =
    ((asps.post_Ico m n).card : ℤ) - (asps.post_Ico n m).card := by
  -- Proof written by GPT 5.5.
  calc
    asps.σ χ n - asps.σ χ m
        = ∑ᶠ k : ℤ, sigmaIndicator asps m n k :=
          (finsum_sigmaIndicator asps m n χ m_le_n).symm
    _ = ∑ᶠ k : ℤ, postIndicator asps m n k := by
      apply finsum_congr
      exact sigmaIndicator_eq_postIndicator asps m n m_le_n
    _ = ((asps.post_Ico m n).card : ℤ) - (asps.post_Ico n m).card :=
      finsum_postIndicator asps m n

private lemma σ_diff_of_post_lt (hmn : asps.post_lt m n) :
    asps.σ χ n - asps.σ χ m = (asps.post_Ico m n).card := by
  rcases hmn with ⟨m_lt_n, mn_nI⟩ | ⟨n_lt_m, nm_I⟩
  · simpa [post_Ico_swap_eq_empty_of_post_lt asps ((post_lt_iff_not_mem asps m_lt_n).mpr mn_nI)]
      using σ_diff_post asps m n χ m_lt_n.le
  · have key := σ_diff_post asps n m χ n_lt_m.le
    have h_swap := post_Ico_swap_eq_empty_of_post_lt asps
      ((post_lt_swap_iff_mem asps n_lt_m.le).mpr nm_I)
    simp only [h_swap, Finset.card_empty, Nat.cast_zero, zero_sub] at key
    omega

private lemma σ_lt_of_post_lt (hmn : asps.post_lt m n) : asps.σ χ m < asps.σ χ n := by
  -- Proof written by GPT 5.5.
  have diff := σ_diff_of_post_lt asps m n χ hmn
  suffices (asps.post_Ico m n).card > 0 by linarith
  apply Finset.card_pos.mpr
  use m
  simpa

private lemma σ_inc (m_lt_n : m < n) (mn_nI : ⟨m, n⟩ ∉ asps) : asps.σ χ m < asps.σ χ n := by
  -- Proof written by GPT 5.5.
  exact σ_lt_of_post_lt asps m n χ ((post_lt_iff_not_mem asps m_lt_n).mpr mn_nI)

private lemma σ_dec (m_lt_n : m < n) (mn_I : ⟨m, n⟩ ∈ asps) : asps.σ χ m > asps.σ χ n := by
  -- Proof written by GPT 5.5.
  exact σ_lt_of_post_lt asps n m χ ((post_lt_swap_iff_mem asps (le_of_lt m_lt_n)).mpr mn_I)

private lemma post_lt_iff_σ_lt : asps.post_lt m n ↔ asps.σ χ m < asps.σ χ n := by
  -- Proof written by GPT 5.5.
  constructor
  · exact σ_lt_of_post_lt asps m n χ
  · intro hσ
    rcases trichotomous_of asps.post_lt m n with hmn | rfl | hnm
    · exact hmn
    · exact (lt_irrefl _ hσ).elim
    · exact ((not_lt_of_gt (σ_lt_of_post_lt asps n m χ hnm)) hσ).elim

private lemma not_post_lt_iff_σ_le :
    ¬ asps.post_lt m n ↔ asps.σ χ n ≤ asps.σ χ m := by
  rw [post_lt_iff_σ_lt]
  exact not_lt

private lemma mem_iff_lt (m_le_n : m ≤ n) : ⟨m, n⟩ ∈ asps ↔ asps.σ χ n < asps.σ χ m := by
  rw [← post_lt_iff_σ_lt asps n m χ]
  exact (post_lt_swap_iff_mem asps m_le_n).symm

private theorem func_injective (asps : AspSet) : Function.Injective (asps.recon χ) := by
  -- Proof written by GPT 5.5.
  intro m n hσ
  rcases trichotomous_of asps.post_lt m n with hmn | rfl | hnm
  · have hlt := σ_lt_of_post_lt asps m n χ hmn
    exact ((ne_of_lt hlt) hσ).elim
  · rfl
  · have hlt := σ_lt_of_post_lt asps n m χ hnm
    exact ((ne_of_gt hlt) hσ).elim

private lemma contiguity_helper :
  (asps.σ χ) ⁻¹' (Set.Ico (asps.σ χ m) (asps.σ χ n))
  = ↑(asps.post_Ico m n) := by
  -- Proof written by GPT 5.5.
  ext k
  simp only [Set.mem_preimage, Set.mem_Ico, Finset.mem_coe, mem_post_Ico]
  rw [← not_post_lt_iff_σ_le asps k m χ,
    ← post_lt_iff_σ_lt asps k n χ]
  exact and_comm

private lemma func_contiguous (σ_m_lt_n : asps.σ χ m < asps.σ χ n) :
  ∀ k : ℤ, asps.recon χ m ≤ k → k < asps.recon χ n
  → ∃ l : ℤ, k = asps.recon χ l := by
  let σ := asps.recon χ
  let I := Finset.Ico (σ m) (σ n)
  let J := asps.post_Ico m n
  let K := Finset.image σ J
  have inv_image : σ ⁻¹' I = ↑J:= by
    simpa [I, J, σ] using contiguity_helper asps m n χ
  have card_J : (J.card : ℤ) = (σ n - σ m) := by
    have hmn := (post_lt_iff_σ_lt asps m n χ).mpr σ_m_lt_n
    simpa [J] using (σ_diff_of_post_lt asps m n χ hmn).symm
  have card_K : (K.card : ℤ) = (σ n - σ m) := by
    rw [← card_J, Finset.card_image_of_injective J (func_injective χ asps)]
  have K_eq_I : K = I := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      rcases Finset.mem_image.mp hk with ⟨j, j_in_J, rfl⟩
      have : j ∈ (J : Set ℤ) := Finset.mem_coe.mpr j_in_J
      rw [← inv_image] at this; exact this
    · have hIcard : (I.card : ℤ) = σ n - σ m := by unfold I; simp; omega
      exact_mod_cast (hIcard.trans card_K.symm).le
  intro k σm_le_k k_lt_σn
  have hk : k ∈ I := Finset.mem_Ico.mpr ⟨σm_le_k, k_lt_σn⟩
  rw [← K_eq_I] at hk
  rcases Finset.mem_image.mp hk with ⟨l, _, hl⟩
  exact ⟨l, hl.symm⟩

end σ_diff

/-! ### Reconstructing ASP permutations from ASP sets

Starting from an abstract ASP set `asps` and a shift `χ`, this section proves
that the reconstructed function is bijective, ASP, and has the expected
inversion data, yielding an `AspPerm`. -/

section OfAspSet
variable (asps : AspSet) (χ : ℤ)

/-- The reconstructed function from an inversion set has that inversion set. -/
theorem invSet_func : invSet (asps.recon χ) = asps := by
  ext ⟨u, v⟩
  wlog u_lt_v : u < v
  · exact iff_of_false (fun h => u_lt_v h.1) (fun h => u_lt_v (asps.directed u v h))
  constructor
  · intro h
    exact (mem_iff_lt asps u v χ (le_of_lt u_lt_v)).mpr h.2
  · intro h
    exact ⟨u_lt_v, (mem_iff_lt asps u v χ (le_of_lt u_lt_v)).mp h⟩

private lemma inset_eq_nw (n : ℤ) : ↑(asps.inset n)
   = northwestSet (asps.σ χ) ((asps.σ χ n) + 1) n := by
  ext x
  unfold northwestSet
  have hmem : ⟨x, n⟩ ∈ asps ↔ ⟨x, n⟩ ∈ invSet (asps.σ χ) :=
    (Set.ext_iff.mp (invSet_func asps χ) ⟨x, n⟩).symm
  simp only [Finset.mem_coe, mem_inset, Set.mem_ofPred_eq]
  constructor
  · intro hx
    rcases hmem.mp hx with ⟨hxn, hσ⟩
    exact ⟨hxn, by omega⟩
  · rintro ⟨hxn, hσ⟩
    exact hmem.mpr ⟨hxn, by omega⟩

private lemma outset_eq_se (n : ℤ) : ↑(asps.outset n)
   = southeastSet (asps.σ χ) (asps.σ χ n) (n+1) := by
  ext x
  unfold southeastSet
  have hmem : ⟨n, x⟩ ∈ asps ↔ ⟨n, x⟩ ∈ invSet (asps.σ χ) :=
    (Set.ext_iff.mp (invSet_func asps χ) ⟨n, x⟩).symm
  simp only [Finset.mem_coe, mem_outset, Set.mem_ofPred_eq]
  constructor
  · intro hx
    rcases hmem.mp hx with ⟨hnx, hσ⟩
    exact ⟨by omega, hσ⟩
  · rintro ⟨hnx, hσ⟩
    exact hmem.mpr ⟨by omega, hσ⟩

/-- This lemma is equivalent to the reconstructed function being unbounded above
on every tail, but is stated in a form convenient for the proof of
surjectivity. -/
private lemma surj_helper_up (m : ℤ) (n : ℕ) :
  ∃ x : ℤ, x ≥ m ∧ asps.recon χ x ≥ asps.recon χ m + n := by
  induction n with
  | zero =>
    use m
    simp
  | succ n ih =>
  rcases ih with ⟨x, x_ge_m, fx_ge⟩
  obtain ⟨y, y_gt_x, y_not_outset_x⟩ : ∃ y : ℤ, y > x ∧ y ∉ asps.outset x := by
    by_contra! hall
    have heq : {y : ℤ | y > x} = ↑(asps.outset x) := by
      ext y; simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_outset]
      exact ⟨fun hy => (mem_outset asps x y).mp (hall y hy),
             fun hy => by linarith [asps.directed x y hy]⟩
    have hfin : ({y : ℤ | y > x}).Finite := heq ▸ Finset.finite_toSet _
    exact Set.Ioi_infinite x hfin
  use y
  constructor
  · omega
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at y_not_outset_x
    have hlt := σ_inc asps x y χ y_gt_x y_not_outset_x
    simp only [Nat.cast_add, Nat.cast_one]; linarith [lt_of_le_of_lt fx_ge hlt]

private lemma surj_helper_down (m : ℤ) (n : ℕ) :
  ∃ x : ℤ, x ≤ m ∧ asps.recon χ x ≤ asps.recon χ m - n := by
  induction n with
  | zero =>
    use m
    simp
  | succ n ih =>
  rcases ih with ⟨x, x_le_m, fx_le⟩
  obtain ⟨y, y_lt_x, y_not_inset_x⟩ : ∃ y : ℤ, y < x ∧ y ∉ asps.inset x := by
    by_contra! hall
    have heq : {y : ℤ | y < x} = ↑(asps.inset x) := by
      ext y; simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_inset]
      exact ⟨fun hy => (mem_inset asps x y).mp (hall y hy),
             fun hy => by linarith [asps.directed y x hy]⟩
    have hfin : ({y : ℤ | y < x}).Finite := heq ▸ Finset.finite_toSet _
    exact Set.Iio_infinite x hfin
  use y
  constructor
  · omega
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at y_not_inset_x
    have hlt := σ_inc asps y x χ y_lt_x y_not_inset_x
    simp only [Nat.cast_add, Nat.cast_one, ge_iff_le]; linarith [lt_of_lt_of_le hlt fx_le]


/-- The function reconstructed from an ASP set and a shift is surjective. -/
private theorem func_surjective : Function.Surjective (asps.recon χ) := by
  intro y
  have : ∃ m : ℤ, m ≤ 0 ∧ asps.recon χ m ≤ y := by
    by_cases h0 : asps.recon χ 0 ≤ y
    · use 0
    rcases surj_helper_down asps χ 0 (asps.recon χ 0 - y).toNat with ⟨m, m_le_0, fm_le⟩
    exact ⟨m, m_le_0, by omega⟩
  rcases this with ⟨m, _, fm_le_y⟩
  have : ∃ n : ℤ, n ≥ 1 ∧ asps.recon χ n ≥ y + 1 := by
    by_cases h1 : asps.recon χ 1 ≥ y + 1
    · use 1
    rcases surj_helper_up asps χ 1 (y + 1 - asps.recon χ 1).toNat with ⟨n, n_ge_1, fn_ge⟩
    exact ⟨n, n_ge_1, by omega⟩
  rcases this with ⟨n, _, fn_ge_y1⟩
  rcases func_contiguous asps m n χ (lt_of_le_of_lt fm_le_y fn_ge_y1) y fm_le_y fn_ge_y1
    with ⟨l, hl⟩
  exact ⟨l, hl.symm⟩

private theorem func_bijective : Function.Bijective (asps.recon χ) :=
  ⟨func_injective χ asps, func_surjective asps χ⟩

/-- The function reconstructed from an ASP set is an ASP permutation. -/
theorem func_asp : isAsp (asps.recon χ) := by
  let τ := asps.recon χ
  let se := southeastSet τ (τ 0) 1
  have se_fin : se.Finite := by
    suffices se = outset asps 0 by
      rw [this]
      simp only [Set.Finite.coe_toFinset, asps.finiteOutdegree 0]
    rw [outset_eq_se asps χ 0]
    congr
  let nw := northwestSet τ ((τ 0) + 1) 0
  have nw_fin : nw.Finite := by
    suffices nw = inset asps 0 by
      rw [this]
      simp only [Set.Finite.coe_toFinset, asps.finiteIndegree 0]
    rw [inset_eq_nw asps χ 0]
  apply asp_of_finite_quadrants (func_injective χ asps) se_fin nw_fin

/-- Package the function reconstructed from an ASP set and a shift as an
`AspPerm`. -/
noncomputable def toAspPerm : AspPerm :=
  ⟨asps.recon χ, func_bijective asps χ, func_asp asps χ⟩

lemma invSet_of_toAspPerm : invSet (toAspPerm asps χ)= asps := invSet_func asps χ

lemma inset_of_toAspPerm (n : ℤ) : (toAspPerm asps χ).inset n = asps.inset n := by
  ext x
  have h1 : x ∈ (toAspPerm asps χ).inset n ↔ ⟨x, n⟩ ∈ invSet (toAspPerm asps χ) := by
    apply AspPerm.invset_iff_inset
  have h2 : x ∈ ↑(asps.inset n) ↔ ⟨x, n⟩ ∈ invSet (toAspPerm asps χ) := by
    have := asps.inset_eq_nw χ n
    rw [invSet_of_toAspPerm asps χ]
    simp
  simp_all

lemma outset_of_toAspPerm (n : ℤ) : (toAspPerm asps χ).outset n = asps.outset n := by
  ext x
  have h1 : x ∈ (toAspPerm asps χ).outset n ↔ ⟨n, x⟩ ∈ invSet (toAspPerm asps χ) := by
    apply AspPerm.invset_iff_outset
  have h2 : x ∈ ↑(asps.outset n) ↔ ⟨n, x⟩ ∈ invSet (toAspPerm asps χ) := by
    have := asps.outset_eq_se χ n
    rw [invSet_of_toAspPerm asps χ]
    simp
  simp_all

lemma chi_of_toAspPerm : (toAspPerm asps χ).χ = χ := by
  let σ := toAspPerm asps χ
  have h1 : σ 0 = (asps.outset 0).card - (asps.inset 0).card - χ := by
    unfold σ toAspPerm recon
    simp
  have h2 : σ 0 = (σ.outset 0).ncard - (σ.inset 0).ncard - σ.χ := by
    rw [σ.reconstruction 0]
    omega
  have hout : σ.outset 0 = asps.outset 0 := outset_of_toAspPerm asps χ 0
  have hin : σ.inset 0 = asps.inset 0 := inset_of_toAspPerm asps χ 0
  rw [hout, hin] at h2
  repeat rw [Set.ncard_coe_finset] at h2
  rw [h1] at h2
  linarith [h2]

end OfAspSet

/-- ASP permutations are equivalent to abstract ASP inversion sets together
with a shift parameter. *Theorem 2.13 (`thm:aspSetReconstruction`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
noncomputable def aspPermEquivAspSet :
  AspPerm ≃ AspSet × ℤ where
  toFun τ := (⟨invSet τ, AspSet_InvSet_of_AspPerm τ⟩, τ.χ)
  invFun := fun ⟨asps, χ⟩ => asps.toAspPerm χ
  left_inv := by
    intro τ
    refine AspPerm.eq_of_inv_set_eq_of_chi_eq _ _ ?_ ?_
    · have h_inv := invSet_of_toAspPerm ⟨invSet τ, AspSet_InvSet_of_AspPerm τ⟩ τ.χ
      change invSet (toAspPerm ⟨invSet τ, AspSet_InvSet_of_AspPerm τ⟩ τ.χ) = invSet τ
      exact h_inv
    · have h_chi := chi_of_toAspPerm ⟨invSet τ, AspSet_InvSet_of_AspPerm τ⟩ τ.χ
      simpa using h_chi
  right_inv := by
    intro ⟨asps, χ⟩
    apply Prod.ext
    · apply SetLike.coe_injective
      change invSet (asps.toAspPerm χ) = asps
      exact invSet_of_toAspPerm asps χ
    · simpa using chi_of_toAspPerm asps χ

@[simp] lemma AspPerm_equiv_AspSet_toFun_fst (τ : AspPerm) :
    ((aspPermEquivAspSet τ).1 : Set (ℤ × ℤ)) = invSet τ := rfl

@[simp] lemma AspPerm_equiv_AspSet_toFun_snd (τ : AspPerm) :
    (aspPermEquivAspSet τ).2 = τ.χ := rfl

@[simp] lemma inv_set_AspPerm_equiv_AspSet_invFun (asps : AspSet) (χ : ℤ) :
    invSet (aspPermEquivAspSet.symm (asps, χ)) = asps :=
  invSet_of_toAspPerm asps χ

@[simp] lemma chi_AspPerm_equiv_AspSet_invFun (asps : AspSet) (χ : ℤ) :
    (aspPermEquivAspSet.symm (asps, χ)).χ = χ :=
  chi_of_toAspPerm asps χ

/-!
A set $I \subseteq \mathbb{Z} \times \mathbb{Z}$ is the inversion set of an ASP permutation
with shift parameter $\chi$ if and only if it satisfies the ASP set properties.
*Theorem 2.13* (`thm:aspSetReconstruction`) from [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
theorem invSets_of_AspPerms (I : Set (ℤ × ℤ)) (χ : ℤ) :
  (∃ τ : AspPerm, invSet τ = I ∧ τ.χ = χ) ↔  (AspSet_prop I) := by
  constructor
  · intro h
    rcases h with ⟨τ, τ_inv_eq, τ_chi_eq⟩
    rw [← τ_inv_eq]
    exact AspSet_InvSet_of_AspPerm τ
  · intro asp
    let asps : AspSet := ⟨I, asp⟩
    use asps.toAspPerm χ
    exact ⟨invSet_of_toAspPerm asps χ, chi_of_toAspPerm asps χ⟩

end AspSet

end LeanPool.DemazureProduct
