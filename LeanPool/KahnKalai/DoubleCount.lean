/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Clemens Posch
-/
import LeanPool.KahnKalai.Cost
import LeanPool.KahnKalai.Numeric

/-!
Tran–Vu Lemma 2.4 (double counting of large minimals `G_W`).
-/

open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section

/-- `w = ⌊0.1 L p N⌋`. -/
noncomputable def coveringWidth (p : ℝ) (N : ℕ) : ℕ :=
  ⌊((1 : ℝ) / 10) * coveringConstant * p * N⌋₊

lemma coveringWidth_eq (p : ℝ) (N : ℕ) :
    coveringWidth p N = ⌊(100 : ℝ) * p * N⌋₊ := by
  unfold coveringWidth coveringConstant
  ring_nf

lemma choose_add_le (N w k : ℕ) :
    (N.choose (w + k) : ℝ) ≤ N.choose w * ((N : ℝ) / (w + 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc]
    by_cases h0 : N.choose (w + k + 1) = 0
    · rw [h0, Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) _)
    · have hratio :
          (N.choose (w + k + 1) : ℝ)
            = N.choose (w + k) * ((N - (w + k) : ℕ) / (w + k + 1) : ℝ) := by
        have hmul := Nat.choose_succ_right_eq N (w + k)
        have hk : (w + k + 1 : ℝ) ≠ 0 := by positivity
        rw [← mul_div_assoc, eq_div_iff hk]
        exact_mod_cast hmul
      have hfrac : ((N - (w + k) : ℕ) : ℝ) / (w + k + 1) ≤ (N : ℝ) / (w + 1) := by
        have hnum : ((N - (w + k) : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr (Nat.sub_le _ _)
        have hden : (w + 1 : ℝ) ≤ w + k + 1 := by
          exact_mod_cast (by omega : w + 1 ≤ w + k + 1)
        exact div_le_div₀ (Nat.cast_nonneg _) hnum (by positivity) hden
      have hstep : (N.choose (w + k + 1) : ℝ)
          ≤ N.choose (w + k) * ((N : ℝ) / (w + 1)) := by
        rw [hratio]
        exact mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
      have hpow : ((N : ℝ) / (w + 1)) ^ (k + 1)
          = ((N : ℝ) / (w + 1)) ^ k * ((N : ℝ) / (w + 1)) := pow_succ _ _
      calc
        (N.choose (w + k + 1) : ℝ)
            ≤ N.choose (w + k) * ((N : ℝ) / (w + 1)) := hstep
        _ ≤ (N.choose w * ((N : ℝ) / (w + 1)) ^ k) * ((N : ℝ) / (w + 1)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ = N.choose w * ((N : ℝ) / (w + 1)) ^ (k + 1) := by rw [hpow]; ring

lemma np_div_width_succ_le (p : ℝ) (N : ℕ) :
    (N : ℝ) * p / (coveringWidth p N + 1) ≤ 1 / 100 := by
  set w := coveringWidth p N
  have hx : (100 : ℝ) * p * N < (w + 1 : ℝ) := by
    have := Nat.lt_floor_add_one ((100 : ℝ) * p * N)
    simpa [coveringWidth_eq, w, add_comm] using this
  have hden : (0 : ℝ) < (w + 1 : ℝ) := by positivity
  refine (div_le_iff₀ hden).mpr ?_
  nlinarith

lemma largeMinimals_disjoint {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (h : T ∈ largeMinimals H W ℓ) : Disjoint T W :=
  restrictFamily_disjoint (minimals_subset _ (largeMinimals_mem_minimals h))

omit [Fintype α] in
lemma exists_mem_subset_union {H : Finset (Finset α)} {W' S₀ : Finset α}
    (h : S₀ ∈ restrictFamily H (W' \ S₀)) (hsub : S₀ ⊆ W') :
    ∃ S ∈ H, S ⊆ W' ∧ S₀ ⊆ S := by
  obtain ⟨S, hS, hSeq⟩ := mem_restrictFamily.mp h
  have hS0S : S₀ ⊆ S := by
    rw [← hSeq]
    exact sdiff_subset
  have hSW' : S ⊆ W' := by
    intro x hxS
    by_contra hxW'
    have hx_not : x ∉ W' \ S₀ := by
      simp [mem_sdiff, hxW']
    have hxS0 : x ∈ S₀ := by
      have : x ∈ S \ (W' \ S₀) := mem_sdiff.mpr ⟨hxS, hx_not⟩
      rwa [hSeq] at this
    exact hxW' (hsub hxS0)
  exact ⟨S, hS, hSW', hS0S⟩

lemma subset_of_minimal_fiber {H : Finset (Finset α)} {W' S S' : Finset α}
    (hS' : S' ∈ minimals (restrictFamily H (W' \ S')))
    (hS : S ∈ H) (hSW' : S ⊆ W') :
    S' ⊆ S := by
  set W := W' \ S'
  have hres : S \ W ∈ restrictFamily H W := mem_restrictFamily.mpr ⟨S, hS, rfl⟩
  have hsub : S \ W ⊆ S' := by
    intro x hx
    have hxS : x ∈ S := (mem_sdiff.mp hx).1
    have hxW : x ∉ W := (mem_sdiff.mp hx).2
    have hxW' : x ∈ W' := hSW' hxS
    by_contra hxS'
    exact hxW (mem_sdiff.mpr ⟨hxW', hxS'⟩)
  have hmin := (mem_minimals.mp hS').2 (S \ W) hres hsub
  exact hmin ▸ sdiff_subset

lemma card_fiber_le {H : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded H ℓ)
    (W' : Finset α) (k : ℕ) :
    #{S' : Finset α | S'.card = k ∧ S' ⊆ W' ∧ S' ∈ largeMinimals H (W' \ S') ℓ}
      ≤ ℓ.choose k := by
  classical
  set Fiber := univ.filter
    (fun S' : Finset α => S'.card = k ∧ S' ⊆ W' ∧ S' ∈ largeMinimals H (W' \ S') ℓ)
  by_cases hF : Fiber.Nonempty
  · obtain ⟨S₀, hS₀mem⟩ := hF
    have hS₀ : S₀.card = k ∧ S₀ ⊆ W' ∧ S₀ ∈ largeMinimals H (W' \ S₀) ℓ :=
      (mem_filter.mp hS₀mem).2
    have hres : S₀ ∈ restrictFamily H (W' \ S₀) :=
      minimals_subset _ (largeMinimals_mem_minimals hS₀.2.2)
    obtain ⟨S, hSH, hSW', _hS₀S⟩ := exists_mem_subset_union hres hS₀.2.1
    have hcardS : S.card ≤ ℓ := hb S hSH
    have hinj : Fiber ⊆ S.powersetCard k := by
      intro S' hS'
      have h' : S'.card = k ∧ S' ⊆ W' ∧ S' ∈ largeMinimals H (W' \ S') ℓ :=
        (mem_filter.mp hS').2
      have hsub : S' ⊆ S :=
        subset_of_minimal_fiber (largeMinimals_mem_minimals h'.2.2) hSH hSW'
      exact mem_powersetCard.mpr ⟨hsub, h'.1⟩
    have : #Fiber ≤ #(S.powersetCard k) := card_le_card hinj
    have hch : #(S.powersetCard k) = S.card.choose k := card_powersetCard _ _
    have hch' : S.card.choose k ≤ ℓ.choose k := Nat.choose_le_choose k hcardS
    exact this.trans (hch.trans_le hch')
  · have : Fiber = ∅ := not_nonempty_iff_eq_empty.mp hF
    simp [this]

/-- Pairs of a width-`w` set and a size-`k` large minimal restricted member. -/
def largePairs (H : Finset (Finset α)) (ℓ w k : ℕ) : Finset (Finset α × Finset α) :=
  (univ.filter (fun W : Finset α => W.card = w)).biUnion fun W =>
    ((largeMinimals H W ℓ).filter (fun S' => S'.card = k)).image fun S' => (W, S')

lemma mem_largePairs {H : Finset (Finset α)} {ℓ w k : ℕ} {p : Finset α × Finset α} :
    p ∈ largePairs H ℓ w k ↔
      p.1.card = w ∧ p.2.card = k ∧ p.2 ∈ largeMinimals H p.1 ℓ := by
  simp only [largePairs, mem_biUnion, mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨W, hw, S', ⟨hL, hk⟩, rfl⟩
    exact ⟨hw, hk, hL⟩
  · rintro ⟨hw, hk, hL⟩
    exact ⟨p.1, hw, p.2, ⟨hL, hk⟩, rfl⟩

lemma card_pairs_le {H : Finset (Finset α)} {ℓ w k : ℕ} (hb : IsBounded H ℓ) :
    #(largePairs H ℓ w k) ≤ (Fintype.card α).choose (w + k) * ℓ.choose k := by
  classical
  let L := univ.filter (fun W' : Finset α => W'.card = w + k)
  have htoL : ∀ p ∈ largePairs H ℓ w k, p.1 ∪ p.2 ∈ L := by
    intro p hp
    obtain ⟨hw, hk, hL⟩ := mem_largePairs.mp hp
    have hdis := (largeMinimals_disjoint hL).symm
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [card_union_of_disjoint hdis, hw, hk]
  have hP := card_eq_sum_card_fiberwise (s := largePairs H ℓ w k) (t := L)
    (f := fun p => p.1 ∪ p.2) (fun p hp => htoL p hp)
  have hfib : ∀ W' ∈ L, #{p ∈ largePairs H ℓ w k | p.1 ∪ p.2 = W'} ≤ ℓ.choose k := by
    intro W' _
    let i : Finset α → Finset α × Finset α := fun S' => (W' \ S', S')
    let Fiber := univ.filter fun S' : Finset α =>
      S'.card = k ∧ S' ⊆ W' ∧ S' ∈ largeMinimals H (W' \ S') ℓ
    have himage : {p ∈ largePairs H ℓ w k | p.1 ∪ p.2 = W'} ⊆ Fiber.image i := by
      intro p hp
      obtain ⟨hpP, hU⟩ := mem_filter.mp hp
      obtain ⟨_hw, hk, hL⟩ := mem_largePairs.mp hpP
      have hdis := (largeMinimals_disjoint hL).symm
      have hW : p.1 = W' \ p.2 := by
        rw [← hU, union_sdiff_cancel_right hdis]
      refine mem_image.mpr ⟨p.2, mem_filter.mpr ⟨mem_univ _, hk, ?_, ?_⟩, ?_⟩
      · intro x hx
        rw [← hU]
        exact mem_union.mpr (Or.inr hx)
      · simpa [hW] using hL
      · simp [i, Prod.ext_iff, hW]
    exact ((card_le_card himage).trans card_image_le).trans (card_fiber_le hb W' k)
  have hsum : #(largePairs H ℓ w k) ≤ ∑ _W' ∈ L, ℓ.choose k := by
    rw [hP]
    exact sum_le_sum hfib
  have : #(largePairs H ℓ w k) ≤ #L * ℓ.choose k := by
    simpa [sum_const, nsmul_eq_mul, mul_comm] using hsum
  simpa [L, card_level] using this

lemma card_pairs_fst {H : Finset (Finset α)} {ℓ w k : ℕ} {W : Finset α}
    (hW : W.card = w) :
    #{p ∈ largePairs H ℓ w k | p.1 = W} =
      #{S' ∈ largeMinimals H W ℓ | S'.card = k} := by
  classical
  let f : Finset α → Finset α × Finset α := fun S' => (W, S')
  have himg :
      ((largeMinimals H W ℓ).filter (fun S' => S'.card = k)).image f =
        (largePairs H ℓ w k).filter (fun p => p.1 = W) := by
    ext p
    simp only [mem_image, mem_filter, f]
    constructor
    · rintro ⟨S', ⟨hL, hk⟩, rfl⟩
      exact ⟨mem_largePairs.mpr ⟨hW, hk, hL⟩, rfl⟩
    · rintro ⟨hp, hfst⟩
      obtain ⟨_hw, hk, hL⟩ := mem_largePairs.mp hp
      subst hfst
      exact ⟨p.2, ⟨hL, hk⟩, rfl⟩
  have hinj : Set.InjOn f ((largeMinimals H W ℓ).filter (fun S' => S'.card = k)) := by
    intro S₁ _ S₂ _ h
    exact (Prod.ext_iff.mp h).2
  rw [← himg, card_image_of_injOn hinj]

lemma sum_card_large_eq_pairs (H : Finset (Finset α)) (ℓ w k : ℕ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
        #{S' ∈ largeMinimals H W ℓ | S'.card = k}
      = #(largePairs H ℓ w k) := by
  classical
  set Lw := univ.filter (fun W : Finset α => W.card = w)
  have hto : ∀ p ∈ largePairs H ℓ w k, p.1 ∈ Lw := by
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _, (mem_largePairs.mp hp).1⟩
  have hsum := card_eq_sum_card_fiberwise (s := largePairs H ℓ w k) (t := Lw)
    (f := fun p => p.1) (fun p hp => hto p hp)
  calc
    ∑ W ∈ Lw, #{S' ∈ largeMinimals H W ℓ | S'.card = k}
        = ∑ W ∈ Lw, #{p ∈ largePairs H ℓ w k | p.1 = W} := by
          refine sum_congr rfl ?_
          intro W hW
          exact (card_pairs_fst (mem_filter.mp hW).2).symm
    _ = #(largePairs H ℓ w k) := hsum.symm

omit [DecidableEq α] [Fintype α] in
lemma expectation_eq_sum_level {p : ℝ} (G : Finset (Finset α)) (ℓ : ℕ)
    (hb : IsBounded G ℓ) :
    expectation p G = ∑ k ∈ Icc 0 ℓ, p ^ k * (#{S ∈ G | S.card = k} : ℝ) := by
  classical
  have hmap : ∀ S ∈ G, S.card ∈ Icc 0 ℓ := fun S hS =>
    mem_Icc.mpr ⟨Nat.zero_le _, hb S hS⟩
  simp only [expectation]
  rw [← sum_fiberwise_of_maps_to' hmap (fun k => p ^ k)]
  refine sum_congr rfl ?_
  intro k _hk
  rw [sum_const, nsmul_eq_mul, mul_comm]

lemma sum_expectation_large {p : ℝ} (H : Finset (Finset α)) (ℓ : ℕ)
    (hb : IsBounded H ℓ) (w : ℕ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
        expectation p (largeMinimals H W ℓ)
      = ∑ k ∈ Icc 0 ℓ, p ^ k * (#(largePairs H ℓ w k) : ℝ) := by
  have hbW : ∀ W, IsBounded (largeMinimals H W ℓ) ℓ := fun W => hb.largeMinimals W
  have h1 :
      ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
          expectation p (largeMinimals H W ℓ)
        = ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
            ∑ k ∈ Icc 0 ℓ, p ^ k * (#{S ∈ largeMinimals H W ℓ | S.card = k} : ℝ) :=
    sum_congr rfl fun W _ => expectation_eq_sum_level _ ℓ (hbW W)
  rw [h1, sum_comm]
  refine sum_congr rfl ?_
  intro k hk
  rw [← mul_sum, ← Nat.cast_sum, sum_card_large_eq_pairs]

lemma largePairs_eq_empty_of_lt_kmin {H : Finset (Finset α)} {ℓ w k : ℕ}
    (hk : k < kmin ℓ) : largePairs H ℓ w k = ∅ := by
  ext p
  constructor
  · intro hp
    obtain ⟨_hw, hkcard, hL⟩ := mem_largePairs.mp hp
    have : kmin ℓ ≤ p.2.card := by
      simpa [kmin] using largeMinimals_card_gt hL
    omega
  · intro h
    cases h

lemma sum_expectation_large_tail {p : ℝ} (H : Finset (Finset α)) (ℓ : ℕ)
    (hb : IsBounded H ℓ) (w : ℕ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
        expectation p (largeMinimals H W ℓ)
      = ∑ k ∈ Icc (kmin ℓ) ℓ, p ^ k * (#(largePairs H ℓ w k) : ℝ) := by
  rw [sum_expectation_large H ℓ hb w]
  have hsub : Icc (kmin ℓ) ℓ ⊆ Icc 0 ℓ := by
    intro k hk
    have hk' := mem_Icc.mp hk
    exact mem_Icc.mpr ⟨Nat.zero_le _, hk'.2⟩
  have hzero : ∀ k ∈ Icc 0 ℓ, k ∉ Icc (kmin ℓ) ℓ →
      p ^ k * (#(largePairs H ℓ w k) : ℝ) = 0 := by
    intro k hk hkmin
    have hkI := mem_Icc.mp hk
    have : k < kmin ℓ := lt_of_not_ge fun hle =>
      hkmin (mem_Icc.mpr ⟨hle, hkI.2⟩)
    simp [largePairs_eq_empty_of_lt_kmin this]
  exact (sum_subset hsub hzero).symm

lemma double_counting_tail {p : ℝ} (hp0 : 0 ≤ p) (H : Finset (Finset α))
    (ℓ : ℕ) (hb : IsBounded H ℓ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = coveringWidth p (Fintype.card α)),
        coverCost p (largeMinimals H W ℓ)
      ≤ ((Fintype.card α).choose (coveringWidth p (Fintype.card α)) : ℝ) *
          ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := by
  set N := Fintype.card α
  set w := coveringWidth p N
  have hE :
      ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
          expectation p (largeMinimals H W ℓ)
        ≤ (N.choose w : ℝ) *
            ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := by
    rw [sum_expectation_large_tail H ℓ hb w]
    have hterm : ∀ k ∈ Icc (kmin ℓ) ℓ,
        p ^ k * (#(largePairs H ℓ w k) : ℝ)
          ≤ (N.choose w : ℝ) * ((1 : ℝ) / 100) ^ k * ℓ.choose k := by
      intro k _hk
      have hcard : (#(largePairs H ℓ w k) : ℝ) ≤ N.choose (w + k) * ℓ.choose k := by
        exact_mod_cast (card_pairs_le hb)
      have hch := choose_add_le N w k
      have hpW := np_div_width_succ_le p N
      have hr : (N : ℝ) / (w + 1) * p ≤ 1 / 100 := by
        have : (N : ℝ) / (w + 1) * p = N * p / (w + 1) := by ring
        simpa [this, w] using hpW
      have hnonneg : (0 : ℝ) ≤ N / (w + 1) * p :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) hp0
      have hpow : ((N : ℝ) / (w + 1) * p) ^ k ≤ ((1 : ℝ) / 100) ^ k :=
        pow_le_pow_left₀ hnonneg hr k
      have hpkn : 0 ≤ p ^ k := pow_nonneg hp0 _
      have hchN : 0 ≤ (ℓ.choose k : ℝ) := Nat.cast_nonneg _
      calc
        p ^ k * (#(largePairs H ℓ w k) : ℝ)
            ≤ p ^ k * (N.choose (w + k) * ℓ.choose k) :=
          mul_le_mul_of_nonneg_left hcard hpkn
        _ = N.choose (w + k) * p ^ k * ℓ.choose k := by ring
        _ ≤ N.choose w * ((N : ℝ) / (w + 1)) ^ k * p ^ k * ℓ.choose k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hch hpkn) hchN
        _ = N.choose w * ((N : ℝ) / (w + 1) * p) ^ k * ℓ.choose k := by
          rw [mul_pow]; ring
        _ ≤ N.choose w * ((1 : ℝ) / 100) ^ k * ℓ.choose k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) hchN
    have hsum := sum_le_sum hterm
    have hfactor :
        ∑ k ∈ Icc (kmin ℓ) ℓ, (N.choose w : ℝ) * ((1 : ℝ) / 100) ^ k * ℓ.choose k
          = (N.choose w : ℝ) * ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := by
      simp [mul_sum, mul_left_comm, mul_comm]
    calc
      ∑ k ∈ Icc (kmin ℓ) ℓ, p ^ k * (#(largePairs H ℓ w k) : ℝ)
          ≤ ∑ k ∈ Icc (kmin ℓ) ℓ,
              (N.choose w : ℝ) * ((1 : ℝ) / 100) ^ k * ℓ.choose k := hsum
      _ = (N.choose w : ℝ) *
            ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := hfactor
  have hcost :
      ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
          coverCost p (largeMinimals H W ℓ)
        ≤ ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
            expectation p (largeMinimals H W ℓ) :=
    sum_le_sum fun W _ => coverCost_le_expectation hp0 (covers_self _)
  calc
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
          coverCost p (largeMinimals H W ℓ)
        ≤ ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
            expectation p (largeMinimals H W ℓ) := hcost
    _ ≤ (N.choose w : ℝ) *
          ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := hE

lemma double_counting {p : ℝ} (hp0 : 0 ≤ p) (H : Finset (Finset α))
    (ℓ : ℕ) (hb : IsBounded H ℓ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = coveringWidth p (Fintype.card α)),
        coverCost p (largeMinimals H W ℓ)
      ≤ ((Fintype.card α).choose (coveringWidth p (Fintype.card α)) : ℝ) *
          ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ := by
  have htail := double_counting_tail hp0 H ℓ hb
  have hgeom := choose_geom_tail_le ℓ
  have hmul :=
    mul_le_mul_of_nonneg_left hgeom
      (Nat.cast_nonneg ((Fintype.card α).choose (coveringWidth p (Fintype.card α))))
  calc
    _ ≤ _ := htail
    _ ≤ ((Fintype.card α).choose (coveringWidth p (Fintype.card α)) : ℝ) *
          (((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ) := hmul
    _ = _ := by ring

end

end KahnKalai
