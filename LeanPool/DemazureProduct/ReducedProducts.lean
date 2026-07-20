/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import LeanPool.DemazureProduct.Submodular

/-!
# Reduced products

This file compares the Demazure operations with ordinary multiplication on ASP
permutations. It corresponds roughly to Section 5 of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).
-/

namespace LeanPool.DemazureProduct


/-! ### Reduced products and ordinary products

This file formalizes Section 5 of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), comparing the
Demazure operations `⋆`, `◃`, and `▹` with ordinary multiplication on `AspPerm`. -/

namespace ReducedProducts

/-- The part of $s_\alpha(a,\ell)$ coming from indices above $\ell$ whose
preimages under $\beta$ lie below $b$. -/
private noncomputable def star_hi_error (α β : AspPerm) (a b l : ℤ) : Finset ℤ :=
  (α.seFinset a l).filter (fun n => β⁻¹ n < b)

/-- The part of $s_\beta(\ell,b)$ coming from indices below $\ell$ whose
images under $\alpha$ lie above $a$. -/
private noncomputable def star_lo_error (α β : AspPerm) (a b l : ℤ) : Finset ℤ :=
  ((β⁻¹).nwFinset b l).filter (fun n => a ≤ α n)

@[simp] private lemma mem_star_hi_error (α β : AspPerm) (a b l n : ℤ) :
    n ∈ star_hi_error α β a b l ↔ l ≤ n ∧ α n < a ∧ β⁻¹ n < b := by
  simp only [star_hi_error, Finset.mem_filter, AspPerm.mem_se, ge_iff_le, and_assoc]

@[simp] private lemma mem_star_lo_error (α β : AspPerm) (a b l n : ℤ) :
    n ∈ star_lo_error α β a b l ↔ n < l ∧ b ≤ β⁻¹ n ∧ a ≤ α n := by
  simp only [star_lo_error, Finset.mem_filter, AspPerm.mem_nw, ge_iff_le, and_assoc]

/-- The two nonnegative error terms in the product-counting formula for
Lemma 5.1. This is the partition from
[An extended Demazure product](https://arxiv.org/abs/2206.14227) of
$s_\alpha(a,\ell) + s_\beta(\ell,b)$ into the ordinary-product count
$s_{\alpha\beta}(a,b)$ and the two remaining quadrants.

*Proof component for Lemma 5.1 (`lem:reducedStar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
private lemma star_sum_eq_mul_add_errors (α β : AspPerm) (a b l : ℤ) :
    α.s a l + β.s l b =
      (α * β).s a b
        + (star_hi_error α β a b l).card
        + (star_lo_error α β a b l).card := by
  -- Proof written by Codex.
  let A := α.seFinset a l
  let B := (β⁻¹).nwFinset b l
  let P := Finset.image β ((α * β).seFinset a b)
  let P_hi := A.filter (fun n => b ≤ β⁻¹ n)
  let P_lo := B.filter (fun n => α n < a)
  have hβ_image : Finset.image β (β.seFinset l b) = B := by
    ext n
    simp only [Finset.mem_image, AspPerm.mem_se, AspPerm.mem_nw, ge_iff_le, B]
    constructor
    · rintro ⟨k, ⟨hbk, hβk⟩, rfl⟩
      simpa only [AspPerm.inv_mul_cancel_eval] using ⟨hβk, hbk⟩
    · intro hn
      refine ⟨β⁻¹ n, ?_, by simp only [AspPerm.mul_inv_cancel_eval]⟩
      simpa only [AspPerm.mul_inv_cancel_eval] using ⟨hn.2, hn.1⟩
  have hβ_card : β.s l b = B.card := by
    rw [β.s_eq_se_card]
    have hcard :
        (β.seFinset l b).card = B.card := calc
      (β.seFinset l b).card = (Finset.image β (β.seFinset l b)).card := by
        exact (Finset.card_image_of_injective _ β.injective).symm
      _ = B.card := by rw [hβ_image]
    exact_mod_cast hcard
  have hmul_card : (α * β).s a b = P.card := by
    rw [(α * β).s_eq_se_card]
    exact_mod_cast (Finset.card_image_of_injective _ β.injective).symm
  have hA_error : A.card = P_hi.card + (star_hi_error α β a b l).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := A) (p := fun n => b ≤ β⁻¹ n)
    have herr :
        A.filter (fun n => ¬ b ≤ β⁻¹ n) = star_hi_error α β a b l := by
      ext n
      simp only [not_le, Finset.mem_filter, AspPerm.mem_se, ge_iff_le, star_hi_error, A]
    simpa only [P_hi, herr] using hsplit.symm
  have hB_error : B.card = P_lo.card + (star_lo_error α β a b l).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := B) (p := fun n => α n < a)
    have herr :
        B.filter (fun n => ¬ α n < a) = star_lo_error α β a b l := by
      ext n
      simp only [not_lt, Finset.mem_filter, AspPerm.mem_nw, ge_iff_le, star_lo_error, B]
    simpa only [P_lo, herr] using hsplit.symm
  have hP_hi : P.filter (fun n => l ≤ n) = P_hi := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, AspPerm.mem_se, ge_iff_le,
      AspPerm.mul_apply, P, P_hi, A]
    constructor
    · rintro ⟨⟨k, ⟨hbk, hαβk⟩, rfl⟩, hlβk⟩
      simp_all
    · rintro ⟨⟨hln, hαn⟩, hbn⟩
      refine ⟨⟨β⁻¹ n, ?_, by simp only [AspPerm.mul_inv_cancel_eval]⟩, hln⟩
      simpa only [AspPerm.mul_apply, AspPerm.mul_inv_cancel_eval] using ⟨hbn, hαn⟩
  have hP_lo : P.filter (fun n => ¬ l ≤ n) = P_lo := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, AspPerm.mem_se, ge_iff_le,
      AspPerm.mem_nw, AspPerm.mul_apply, P, P_lo, B]
    constructor
    · rintro ⟨⟨k, ⟨hbk, hαβk⟩, rfl⟩, hlβk⟩
      simp_all
    · rintro ⟨⟨hnl, hbn⟩, hαn⟩
      refine ⟨⟨β⁻¹ n, ?_, by simp only [AspPerm.mul_inv_cancel_eval]⟩, by omega⟩
      simpa only [AspPerm.mul_apply, AspPerm.mul_inv_cancel_eval] using ⟨hbn, hαn⟩
  have hP_split : P.card = P_hi.card + P_lo.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := P) (p := fun n => l ≤ n)
    simpa only [hP_hi, hP_lo] using hsplit.symm
  have hcards :
      A.card + B.card =
        P.card
          + (star_hi_error α β a b l).card
          + (star_lo_error α β a b l).card := by
    omega
  rw [α.s_eq_se_card, hβ_card, hmul_card]
  exact_mod_cast hcards

/-- An ordinary product lies below the corresponding Demazure product in
Bruhat order. *Lemma 5.1 (`lem:reducedStar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
theorem mul_le_star (α β : AspPerm) : α * β ≤ α ⋆ β := by
  rw [AspPerm.le_star_iff]
  intro a b l
  have hcount := star_sum_eq_mul_add_errors α β a b l
  omega

/-- If the Demazure product lies below the ordinary product, then the ordinary
product is reduced. *Proof component for Lemma 5.1 (`lem:reducedStar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
private lemma reducedProduct_of_star_le_mul (α β : AspPerm) (hupper : α ⋆ β ≤ α * β) :
    AspPerm.ReducedProduct α β := by
  -- Proof written by Codex.
  apply Set.disjoint_left.mpr
  rintro ⟨m, n⟩ hα hβ
  obtain ⟨l, hl⟩ :=
    (AspPerm.ge_star_iff (α * β) α β).mp hupper (α m) (β⁻¹ m)
  have hcount := star_sum_eq_mul_add_errors α β (α m) (β⁻¹ m) l
  by_cases hln : l ≤ n
  · have hn : n ∈ star_hi_error α β (α m) (β⁻¹ m) l :=
      (mem_star_hi_error α β (α m) (β⁻¹ m) l n).mpr ⟨hln, hα.2, hβ.2⟩
    have hncard : 0 < (star_hi_error α β (α m) (β⁻¹ m) l).card :=
      Finset.card_pos.mpr ⟨n, hn⟩
    omega
  · have hm : m ∈ star_lo_error α β (α m) (β⁻¹ m) l := by
      apply (mem_star_lo_error α β (α m) (β⁻¹ m) l m).mpr
      exact ⟨lt_of_lt_of_le hα.1 (le_of_lt (lt_of_not_ge hln)), le_refl _, le_refl _⟩
    have hmcard : 0 < (star_lo_error α β (α m) (β⁻¹ m) l).card :=
      Finset.card_pos.mpr ⟨m, hm⟩
    omega

/-- A reduced ordinary product is an upper bound for the Demazure product.
*Proof component for Lemma 5.1 (`lem:reducedStar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
private lemma star_le_mul_of_reducedProduct (α β : AspPerm)
    (h_reduced : AspPerm.ReducedProduct α β) : α ⋆ β ≤ α * β := by
  -- Proof written by Codex.
  apply (AspPerm.s_le_iff (α ⋆ β) (α * β)).mp
  rw [AspPerm.star_spec]
  intro a b
  -- Contrapose and use the witnessing value of l to construct a common inversion.
  by_contra hnot
  have hstrict : (α * β).s a b < (α.s ⋆ β.s) a b := by
    omega
  obtain ⟨l₀, hl₀⟩ := β.tend_zero_a b
  have hse₀ : β.seFinset l₀ b = ∅ := by
    apply Finset.card_eq_zero.mp
    have hcard : ((β.seFinset l₀ b).card : ℤ) = 0 := by
      rwa [← β.s_eq_se_card]
    exact_mod_cast hcard
  have hlo₀ : star_lo_error α β a b l₀ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    have hm' := (mem_star_lo_error α β a b l₀ m).mp hm
    have hβm : β⁻¹ m ∈ β.seFinset l₀ b := by
      simpa only [AspPerm.mem_se, ge_iff_le, AspPerm.mul_inv_cancel_eval] using
        ⟨hm'.2.1, hm'.1⟩
    simp_all
  have hval₀ : (α.s ⋆ β.s) a b ≤ α.s a l₀ + β.s l₀ b := by
    simpa using
      SlipFace.star_val_le α.s β.s a b l₀
  have hcount₀ := star_sum_eq_mul_add_errors α β a b l₀
  simp only [hl₀, add_zero, hlo₀, Finset.card_empty, Nat.cast_zero] at hcount₀
  have hhi₀ : 0 < (star_hi_error α β a b l₀).card := by
    omega
  let H := star_hi_error α β a b l₀
  let n := H.max' (Finset.card_pos.mp hhi₀)
  have hnH : n ∈ H := Finset.max'_mem H (Finset.card_pos.mp hhi₀)
  have hn_data : l₀ ≤ n ∧ α n < a ∧ β⁻¹ n < b :=
    (mem_star_hi_error α β a b l₀ n).mp hnH
  have hhi_succ : star_hi_error α β a b (n + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n' hn'
    have hn'_hi := (mem_star_hi_error α β a b (n + 1) n').mp hn'
    have hn'H : n' ∈ H := by
      apply (mem_star_hi_error α β a b l₀ n').mpr
      have hnn' : n ≤ n' := le_trans (le_of_lt (lt_add_one n)) hn'_hi.1
      exact ⟨le_trans hn_data.1 hnn', hn'_hi.2⟩
    have hn'_le : n' ≤ n := Finset.le_max' H n' hn'H
    omega
  have hval_succ : (α.s ⋆ β.s) a b ≤ α.s a (n + 1) + β.s (n + 1) b := by
    simpa using
      SlipFace.star_val_le α.s β.s a b (n + 1)
  have hcount_succ := star_sum_eq_mul_add_errors α β a b (n + 1)
  simp only [hhi_succ, Finset.card_empty, Nat.cast_zero] at hcount_succ
  have hlo_succ : 0 < (star_lo_error α β a b (n + 1)).card := by
    omega
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hlo_succ
  have hm' : m < n + 1 ∧ b ≤ β⁻¹ m ∧ a ≤ α m :=
    (mem_star_lo_error α β a b (n + 1) m).mp hm
  have hmn : m < n := by
    have hmn_le : m ≤ n := Int.le_of_lt_add_one hm'.1
    apply lt_of_le_of_ne hmn_le
    intro hmn_eq
    subst m
    omega
  have hαmn : ⟨m, n⟩ ∈ invSet α :=
    ⟨hmn, lt_of_lt_of_le hn_data.2.1 hm'.2.2⟩
  have hβmn : ⟨m, n⟩ ∈ invSet (β⁻¹).func :=
    ⟨hmn, lt_of_lt_of_le hn_data.2.2 hm'.2.1⟩
  exact Set.disjoint_left.mp h_reduced hαmn hβmn

/-- The Demazure product agrees with ordinary multiplication exactly for a
reduced product. *Lemma 5.1 (`lem:reducedStar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
theorem star_eq_mul_iff_reducedProduct (α β : AspPerm) :
    α ⋆ β = α * β ↔ AspPerm.ReducedProduct α β := by
  -- Proof written by Codex.
  constructor
  · intro h_eq
    apply reducedProduct_of_star_le_mul α β
    rw [h_eq]
  · intro h_reduced
    exact le_antisymm
      (star_le_mul_of_reducedProduct α β h_reduced)
      (mul_le_star α β)

/-- The left-residual error below the cutoff $\ell$: indices counted by
$s_{\alpha\beta}(a,b)$ but omitted from the candidate
$s_\alpha(a,\ell)-s_{\beta^{-1}}(b,\ell)$. -/
private noncomputable def lres_lo_error (α β : AspPerm) (a b l : ℤ) : Finset ℤ :=
  ((β⁻¹).nwFinset b l).filter (fun n => α n < a)

/-- The left-residual error above the cutoff $\ell$: indices subtracted by
$s_{\beta^{-1}}(b,\ell)$ but not counted by $s_\alpha(a,\ell)$. -/
private noncomputable def lres_hi_error (α β : AspPerm) (a b l : ℤ) : Finset ℤ :=
  ((β⁻¹).seFinset b l).filter (fun n => a ≤ α n)

@[simp] private lemma mem_lres_lo_error (α β : AspPerm) (a b l n : ℤ) :
    n ∈ lres_lo_error α β a b l ↔ n < l ∧ b ≤ β⁻¹ n ∧ α n < a := by
  simp only [lres_lo_error, Finset.mem_filter, AspPerm.mem_nw, ge_iff_le, and_assoc]

@[simp] private lemma mem_lres_hi_error (α β : AspPerm) (a b l n : ℤ) :
    n ∈ lres_hi_error α β a b l ↔ l ≤ n ∧ β⁻¹ n < b ∧ a ≤ α n := by
  simp only [lres_hi_error, Finset.mem_filter, AspPerm.mem_se, ge_iff_le, and_assoc]

/-- The two nonnegative error terms in the left-residual counting formula
for Lemma 5.2. The candidate in
[An extended Demazure product](https://arxiv.org/abs/2206.14227),
$s_\alpha(a,\ell)-s_{\beta^{-1}}(b,\ell)$ is the ordinary-product count
$s_{\alpha\beta}(a,b)$ minus these two errors.

*Proof component for Lemma 5.2 (`lem:reducedRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
private lemma lres_diff_eq_mul_sub_errors (α β : AspPerm) (a b l : ℤ) :
    α.s a l - (β⁻¹).s b l =
      (α * β).s a b
        - (lres_lo_error α β a b l).card
        - (lres_hi_error α β a b l).card := by
  -- Proof written by Codex.
  let A := α.seFinset a l
  let B := (β⁻¹).seFinset b l
  let P := Finset.image β ((α * β).seFinset a b)
  let P_hi := A.filter (fun n => b ≤ β⁻¹ n)
  let C := B.filter (fun n => α n < a)
  have hmul_card : (α * β).s a b = P.card := by
    rw [(α * β).s_eq_se_card]
    exact_mod_cast (Finset.card_image_of_injective _ β.injective).symm
  have hA_split : A.card = P_hi.card + C.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := A) (p := fun n => b ≤ β⁻¹ n)
    have hC :
        A.filter (fun n => ¬ b ≤ β⁻¹ n) = C := by
      ext n
      simp only [A, B, C, Finset.mem_filter, AspPerm.mem_se, ge_iff_le, not_le]
      omega
    simpa only [P_hi, hC] using hsplit.symm
  have hB_split :
      B.card = C.card + (lres_hi_error α β a b l).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := B) (p := fun n => α n < a)
    have hhi :
        B.filter (fun n => ¬ α n < a) = lres_hi_error α β a b l := by
      ext n
      simp only [B, lres_hi_error, Finset.mem_filter, AspPerm.mem_se, ge_iff_le, not_lt]
    simpa only [C, hhi] using hsplit.symm
  have hP_hi : P.filter (fun n => l ≤ n) = P_hi := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, AspPerm.mem_se, ge_iff_le,
      AspPerm.mul_apply, P, P_hi, A]
    constructor
    · rintro ⟨⟨k, ⟨hbk, hαβk⟩, rfl⟩, hlβk⟩
      simp_all
    · rintro ⟨⟨hln, hαn⟩, hbn⟩
      refine ⟨⟨β⁻¹ n, ?_, by simp only [AspPerm.mul_inv_cancel_eval]⟩, hln⟩
      simpa only [AspPerm.mul_apply, AspPerm.mul_inv_cancel_eval] using ⟨hbn, hαn⟩
  have hP_lo :
      P.filter (fun n => ¬ l ≤ n) = lres_lo_error α β a b l := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, AspPerm.mem_se, ge_iff_le,
      AspPerm.mem_nw, AspPerm.mul_apply, P, lres_lo_error]
    constructor
    · rintro ⟨⟨k, ⟨hbk, hαβk⟩, rfl⟩, hlβk⟩
      simp_all
    · rintro ⟨⟨hnl, hbn⟩, hαn⟩
      refine ⟨⟨β⁻¹ n, ?_, by simp only [AspPerm.mul_inv_cancel_eval]⟩, by omega⟩
      simpa only [AspPerm.mul_apply, AspPerm.mul_inv_cancel_eval] using ⟨hbn, hαn⟩
  have hP_split :
      P.card = P_hi.card + (lres_lo_error α β a b l).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := P) (p := fun n => l ≤ n)
    simpa only [hP_hi, hP_lo] using hsplit.symm
  have hcards :
      (A.card : ℤ) - B.card =
        (P.card : ℤ)
          - (lres_lo_error α β a b l).card
          - (lres_hi_error α β a b l).card := by
    omega
  rw [α.s_eq_se_card, (β⁻¹).s_eq_se_card, hmul_card]
  exact hcards

/-- Left residual lies below ordinary multiplication in Bruhat order.
*Lemma 5.2 (`lem:reducedRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/4.* -/
theorem lres_le_mul (α β : AspPerm) : α ◃ β ≤ α * β := by
  -- Proof written by Codex.
  apply (AspPerm.s_le_iff (α ◃ β) (α * β)).mp
  rw [AspPerm.lres_spec]
  intro a b
  let l := SlipFace.lresWit α.s β.s a b
  have hcount := lres_diff_eq_mul_sub_errors α β a b l
  dsimp only [l] at hcount
  rw [SlipFace.lres_wit_spec, AspPerm.s_dual]
  omega

/-- If ordinary multiplication lies below left residual, then the inverse
of the right factor lies below the left factor in left weak order.
*Proof component for Lemma 5.2 (`lem:reducedRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
private lemma le_weak_L_of_mul_le_lres (α β : AspPerm)
    (hle : α * β ≤ α ◃ β) : β⁻¹ ≤L α := by
  -- Proof written by Codex.
  rintro ⟨m, n⟩ hβ
  refine ⟨hβ.1, ?_⟩
  by_contra hnot
  have hα_le : α m ≤ α n := le_of_not_gt hnot
  have hα_ne : α m ≠ α n := by
    intro hα_eq
    exact (ne_of_lt hβ.1) (α.injective hα_eq)
  have hα_lt : α m < α n := lt_of_le_of_ne hα_le hα_ne
  let a := α n
  let b := β⁻¹ m
  let l := SlipFace.lresWit α.s β.s a b
  have hcount := lres_diff_eq_mul_sub_errors α β a b l
  have hlc :
      (α ◃ β).s a b = α.s a l - (β⁻¹).s b l := by
    dsimp only [l]
    rw [AspPerm.lres_spec, SlipFace.lres_wit_spec, AspPerm.s_dual]
  have hcomp := hle a b
  rw [hlc] at hcomp
  by_cases hln : l ≤ n
  · have hn : n ∈ lres_hi_error α β a b l :=
      (mem_lres_hi_error α β a b l n).mpr ⟨hln, hβ.2, le_refl _⟩
    have hncard : 0 < (lres_hi_error α β a b l).card :=
      Finset.card_pos.mpr ⟨n, hn⟩
    omega
  · have hm : m ∈ lres_lo_error α β a b l := by
      apply (mem_lres_lo_error α β a b l m).mpr
      exact
        ⟨lt_of_lt_of_le hβ.1 (le_of_lt (lt_of_not_ge hln)),
          le_refl _, hα_lt⟩
    have hmcard : 0 < (lres_lo_error α β a b l).card :=
      Finset.card_pos.mpr ⟨m, hm⟩
    omega

/-- If the inverse of the right factor lies below the left factor in left weak
order, then ordinary multiplication lies below left residual.
Proof component of *Lemma 5.2* (`lem:reducedRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
private lemma mul_le_lres_of_le_weak_L (α β : AspPerm)
    (hweak : β⁻¹ ≤L α) : α * β ≤ α ◃ β := by
  -- Proof written by Codex.
  intro a b
  have hle_of_errors_empty (l : ℤ)
      (hlo : lres_lo_error α β a b l = ∅)
      (hhi : lres_hi_error α β a b l = ∅) :
      (α * β).s a b ≤ (α ◃ β).s a b := by
    have hcount := lres_diff_eq_mul_sub_errors α β a b l
    simp only [hlo, hhi, Finset.card_empty, Nat.cast_zero, sub_zero] at hcount
    have hcand := Submodular.lres_candidate_le α β a b l
    simp_all
  obtain ⟨l₀, hl₀⟩ := β.tend_zero_a b
  have hse₀ : β.seFinset l₀ b = ∅ := by
    apply Finset.card_eq_zero.mp
    have hcard : ((β.seFinset l₀ b).card : ℤ) = 0 := by
      rwa [← β.s_eq_se_card]
    exact_mod_cast hcard
  have hlo₀ : lres_lo_error α β a b l₀ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    have hm' := (mem_lres_lo_error α β a b l₀ m).mp hm
    have hβm : β⁻¹ m ∈ β.seFinset l₀ b := by
      simpa only [AspPerm.mem_se, ge_iff_le, AspPerm.mul_inv_cancel_eval] using
        ⟨hm'.2.1, hm'.1⟩
    simp_all
  by_cases hhi₀_empty : lres_hi_error α β a b l₀ = ∅
  · exact hle_of_errors_empty l₀ hlo₀ hhi₀_empty
  · have hhi₀ : 0 < (lres_hi_error α β a b l₀).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hhi₀_empty)
    let H := lres_hi_error α β a b l₀
    let n := H.max' (Finset.card_pos.mp hhi₀)
    have hnH : n ∈ H := Finset.max'_mem H (Finset.card_pos.mp hhi₀)
    have hn_data : l₀ ≤ n ∧ β⁻¹ n < b ∧ a ≤ α n :=
      (mem_lres_hi_error α β a b l₀ n).mp hnH
    have hhi_succ : lres_hi_error α β a b (n + 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n' hn'
      have hn'_hi := (mem_lres_hi_error α β a b (n + 1) n').mp hn'
      have hn'H : n' ∈ H := by
        apply (mem_lres_hi_error α β a b l₀ n').mpr
        have hnn' : n ≤ n' := le_trans (le_of_lt (lt_add_one n)) hn'_hi.1
        exact ⟨le_trans hn_data.1 hnn', hn'_hi.2⟩
      have hn'_le : n' ≤ n := Finset.le_max' H n' hn'H
      omega
    have hlo_succ : lres_lo_error α β a b (n + 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      have hm' := (mem_lres_lo_error α β a b (n + 1) m).mp hm
      have hmn : m < n := by
        have hmn_le : m ≤ n := Int.le_of_lt_add_one hm'.1
        apply lt_of_le_of_ne hmn_le
        intro hmn_eq
        subst m
        omega
      have hβmn : ⟨m, n⟩ ∈ invSet (β⁻¹).func :=
        ⟨hmn, lt_of_lt_of_le hn_data.2.1 hm'.2.1⟩
      have hαmn := hweak hβmn
      have hα_bad : α n < α m := hαmn.2
      omega
    exact hle_of_errors_empty (n + 1) hlo_succ hhi_succ

/-- Left residual agrees with ordinary multiplication exactly when the
inverse of the right factor is below the left factor in left weak order.
*Lemma 5.2 (`lem:reducedRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/4.* -/
theorem lres_eq_mul_iff (α β : AspPerm) :
    α ◃ β = α * β ↔ β⁻¹ ≤L α := by
  -- Proof written by Codex.
  constructor
  · intro h_eq
    apply le_weak_L_of_mul_le_lres α β
    rw [h_eq]
  · intro hweak
    exact le_antisymm
      (lres_le_mul α β)
      (mul_le_lres_of_le_weak_L α β hweak)

/-- Right residual lies below ordinary multiplication in Bruhat order.
*Lemma 5.2 (`lem:reducedRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/4.* -/
theorem rres_le_mul (α β : AspPerm) : α ▹ β ≤ α * β := by
  -- Proof written by Codex.
  have hχ : (β⁻¹ ◃ α⁻¹).χ = (β⁻¹ * α⁻¹).χ := by
    simp only [AspPerm.chi_lres, AspPerm.chi_mul]
  have hleχ : β⁻¹ ◃ α⁻¹ ≤χ β⁻¹ * α⁻¹ :=
    ⟨lres_le_mul β⁻¹ α⁻¹, hχ⟩
  have hinv :=
    (AspPerm.le_chi_inv_iff (β⁻¹ ◃ α⁻¹) (β⁻¹ * α⁻¹)).mp hleχ
  simpa only [AspPerm.inverse_lres, inv_inv, mul_inv_rev] using hinv.1

/-- Right residual agrees with ordinary multiplication exactly when the
inverse of the left factor is below the right factor in right weak order.
*Lemma 5.2 (`lem:reducedRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/4.* -/
theorem rres_eq_mul_iff (α β : AspPerm) :
    α ▹ β = α * β ↔ α⁻¹ ≤R β := by
  -- Proof written by Codex.
  have h_eq :
      α ▹ β = α * β ↔ β⁻¹ ◃ α⁻¹ = β⁻¹ * α⁻¹ := by
    constructor
    · intro h
      calc
        β⁻¹ ◃ α⁻¹ = (α ▹ β)⁻¹ := by
          have hdual := congrArg (fun τ : AspPerm => τ⁻¹)
            (AspPerm.inverse_lres β⁻¹ α⁻¹)
          simpa only [inv_inv] using hdual
        _ = (α * β)⁻¹ := by rw [h]
        _ = β⁻¹ * α⁻¹ := by rw [mul_inv_rev]
    · intro h
      calc
        α ▹ β = (β⁻¹ ◃ α⁻¹)⁻¹ := by
          simpa only [inv_inv] using (AspPerm.inverse_lres β⁻¹ α⁻¹).symm
        _ = (β⁻¹ * α⁻¹)⁻¹ := by rw [h]
        _ = α * β := by simp only [mul_inv_rev, inv_inv]
  rw [h_eq, lres_eq_mul_iff]
  constructor
  · intro hweak
    simpa only [inv_inv] using AspPerm.le_weak_R_of_L hweak
  · intro hweak
    exact AspPerm.le_weak_L_of_R hweak


/-! ### Weak order implies strong order -/

/-- Left weak order implies Bruhat order when the shifts are weakly ordered.
*Corollary 5.3 (`cor:weakStrong`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
theorem le_of_le_weak_L_of_chi_le {α β : AspPerm}
    (hweak : α ≤L β) (hχ : α.χ ≤ β.χ) : α ≤ β := by
  -- Proof written by Codex.
  let γ := β ◃ α⁻¹
  have hγ_eq : γ = β * α⁻¹ := by
    apply (lres_eq_mul_iff β α⁻¹).mpr
    simpa only [inv_inv] using hweak
  have hγ_red : AspPerm.ReducedProduct γ α := by
    simpa only [γ, inv_inv] using Submodular.reducedProduct_of_lres β α⁻¹
  have hγ_nonneg : 0 ≤ γ.χ := by
    simp only [γ, AspPerm.chi_lres, AspPerm.chi_dual]
    omega
  calc
    α = AspPerm.id ⋆ α := (AspPerm.id_star α).symm
    _ ≤ γ ⋆ α := AspPerm.star_mono
      (AspPerm.id_le_of_chi_nonneg hγ_nonneg) (le_refl α)
    _ = γ * α := (star_eq_mul_iff_reducedProduct γ α).mpr hγ_red
    _ = β := by
      rw [hγ_eq, mul_assoc, inv_mul_cancel, mul_one]

/-- Right weak order implies Bruhat order when the shifts are weakly ordered.
*Corollary 5.3 (`cor:weakStrong`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
theorem le_of_le_weak_R_of_chi_le {α β : AspPerm}
    (hweak : α ≤R β) (hχ : α.χ ≤ β.χ) : α ≤ β := by
  -- Proof written by Codex.
  let γ := α⁻¹ ▹ β
  have hγ_eq : γ = α⁻¹ * β := by
    apply (rres_eq_mul_iff α⁻¹ β).mpr
    simpa only [inv_inv] using hweak
  have hγ_red : AspPerm.ReducedProduct α γ := by
    simpa only [γ, inv_inv] using Submodular.reducedProduct_of_rres α⁻¹ β
  have hγ_nonneg : 0 ≤ γ.χ := by
    simp only [γ, AspPerm.chi_rres, AspPerm.chi_dual]
    omega
  calc
    α = α ⋆ AspPerm.id := (AspPerm.star_id α).symm
    _ ≤ α ⋆ γ := AspPerm.star_mono
      (le_refl α) (AspPerm.id_le_of_chi_nonneg hγ_nonneg)
    _ = α * γ := (star_eq_mul_iff_reducedProduct α γ).mpr hγ_red
    _ = β := by
      rw [hγ_eq, ← mul_assoc, mul_inv_cancel, one_mul]

end ReducedProducts

/-! ### Reduced factorizations -/

/-- A reduced factorization of `γ` into the ordinary product of `α` and `β`.

This bundles the ordinary-product equality with reducedness so that the other
equivalent descriptions from Section 5 can be recovered from one object. -/
structure ReducedFact (α β γ : AspPerm) where
  reduced : AspPerm.ReducedProduct α β
  mul_eq : α * β = γ

namespace ReducedFact

/-- Construct a reduced fact from its defining two properties. -/
theorem of_mul_reduced {α β γ : AspPerm} (h_mul : α * β = γ)
    (h_reduced : AspPerm.ReducedProduct α β) : ReducedFact α β γ :=
  ReducedFact.mk h_reduced h_mul

/-- Construct a reduced fact when ordinary and Demazure multiplication have
the same value. -/
private theorem of_mul_star {α β γ : AspPerm} (h_mul : α * β = γ)
    (h_star : α ⋆ β = γ) : ReducedFact α β γ := by
  apply of_mul_reduced h_mul
  rw [← ReducedProducts.star_eq_mul_iff_reducedProduct α β, h_star, h_mul]

/-- Construct a reduced fact from an ordinary product and the right weak-order
inequality for its left factor. -/
private theorem of_mul_ler {α β γ : AspPerm} (h_mul : α * β = γ)
    (h_weak : α ≤R γ) : ReducedFact α β γ := by
  apply of_mul_reduced h_mul
  rwa [AspPerm.reduced_iff_leR, h_mul]

/-- Construct a reduced fact from an ordinary product and the left weak-order
inequality for its right factor. -/
theorem of_mul_lel {α β γ : AspPerm} (h_mul : α * β = γ)
    (h_weak : β ≤L γ) : ReducedFact α β γ := by
  apply of_mul_reduced h_mul
  rwa [AspPerm.reduced_iff_leL, h_mul]

/-- Construct a reduced fact when the right residual by the inverse left
factor collapses to ordinary multiplication. -/
private theorem of_mul_rres {α β γ : AspPerm} (h_mul : α * β = γ)
    (h_residual : α⁻¹ ▹ γ = α⁻¹ * γ) : ReducedFact α β γ := by
  apply of_mul_reduced h_mul
  rw [ReducedProducts.rres_eq_mul_iff α⁻¹ γ, inv_inv, ← h_mul] at h_residual
  rwa [AspPerm.reduced_iff_leR]

/-- Construct a reduced fact when the left residual by the inverse right
factor collapses to ordinary multiplication. -/
private theorem of_mul_lres {α β γ : AspPerm} (h_mul : α * β = γ)
    (h_residual : γ ◃ β⁻¹ = γ * β⁻¹) : ReducedFact α β γ := by
  apply of_mul_reduced h_mul
  rw [ReducedProducts.lres_eq_mul_iff γ β⁻¹, inv_inv, ← h_mul] at h_residual
  rwa [AspPerm.reduced_iff_leL]

private theorem of_reduced_star {α β γ : AspPerm}
  (h_red : α.ReducedProduct β) (h_star : α ⋆ β = γ) : ReducedFact α β γ := by
  apply of_mul_reduced _ h_red
  rwa [← (ReducedProducts.star_eq_mul_iff_reducedProduct α β).mpr h_red]

private theorem of_lel_lres {α β γ : AspPerm}
    (h_lel : β ≤L γ) (h_lres : γ ◃ β⁻¹ = α) : ReducedFact α β γ
  := by
  have eq_α : γ * β⁻¹ = α := by
    have := ReducedProducts.lres_eq_mul_iff γ β⁻¹
    simp_all
  have h_mul : α * β = γ := by
    rw [← eq_α, mul_assoc, inv_mul_cancel, mul_one]
  rw [← h_mul] at h_lel
  exact ReducedFact.mk ((AspPerm.reduced_iff_leL α β).mpr h_lel) h_mul

theorem of_ler_rres {α β γ : AspPerm}
    (h_ler : α ≤R γ) (h_rres : α⁻¹ ▹ γ = β) : ReducedFact α β γ := by
  have eq_β : α⁻¹ * γ = β := by
    have := ReducedProducts.rres_eq_mul_iff α⁻¹ γ
    simp_all
  have h_mul : α * β = γ := by
    rw [← eq_β, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← h_mul] at h_ler
  exact ReducedFact.mk ((AspPerm.reduced_iff_leR α β).mpr h_ler) h_mul

/-- The Demazure product in a reduced factorization has the same value as its ordinary
product. -/
lemma star_eq {α β γ : AspPerm} (h : ReducedFact α β γ) : α ⋆ β = γ := by
  rw [(ReducedProducts.star_eq_mul_iff_reducedProduct α β).mpr h.reduced, h.mul_eq]

/-- The left factor of a reduced factorization is below the product in right weak
order. -/
private lemma ler {α β γ : AspPerm} (h : ReducedFact α β γ) : α ≤R γ := by
  convert (AspPerm.reduced_iff_leR α β).mp h.reduced
  rw [h.mul_eq]

/-- The right factor of a reduced factorization is below the product in left weak
order. -/
private lemma lel {α β γ : AspPerm} (h : ReducedFact α β γ) : β ≤L γ := by
  convert (AspPerm.reduced_iff_leL α β).mp h.reduced
  rw [h.mul_eq]

/-- Right residual by the inverse left factor collapses to ordinary
multiplication in a reduced factorization. -/
private lemma rres_eq {α β γ : AspPerm} (h : ReducedFact α β γ) : α⁻¹ ▹ γ = α⁻¹ * γ := by
  apply (ReducedProducts.rres_eq_mul_iff α⁻¹ γ).mpr
  rw [inv_inv]
  exact h.ler

/-- Left residual by the inverse right factor collapses to ordinary
multiplication in a reduced factorization. -/
lemma lres_eq {α β γ : AspPerm} (h : ReducedFact α β γ) : γ ◃ β⁻¹ = γ * β⁻¹ := by
  apply (ReducedProducts.lres_eq_mul_iff γ β⁻¹).mpr
  rw [inv_inv]
  exact h.lel

end ReducedFact

end LeanPool.DemazureProduct
