/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Clemens Posch
-/
import LeanPool.KahnKalai.DoubleCount

/-!
Tran–Vu Theorem 2.3: the covering theorem.
-/

open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section

lemma frac_le_one (ℓ : ℕ) :
    (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2) ≤ 1 := by
  have : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 2) ≤ 1 / 4 := by
    have : (2 : ℝ) ^ (2 : ℕ) ≤ 2 ^ (ℓ + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
    simpa [h4] using one_div_le_one_div_of_le (by positivity) this
  linarith

lemma covering_of_empty_mem {H : Finset (Finset α)} {ℓ : ℕ} {p : ℝ}
    (h : ∅ ∈ H) :
    ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) *
        ((Fintype.card α).choose (coveringLevel p (Fintype.card α) ℓ) : ℝ) ≤
      (((generate H).filter
          (fun S => S.card = coveringLevel p (Fintype.card α) ℓ)).card : ℝ) := by
  set N := Fintype.card α
  set m := coveringLevel p N ℓ
  have hgen : generate H = univ := generate_eq_univ_of_empty_mem h
  have hfilter : (generate H).filter (fun S => S.card = m) =
      univ.filter (fun S => S.card = m) := by rw [hgen]
  have hcard : (((generate H).filter (fun S => S.card = m)).card : ℝ) = N.choose m := by
    rw [hfilter, card_level]
  rw [hcard]
  have hfrac := frac_le_one ℓ
  by_cases hm : m ≤ N
  · have hpos : (0 : ℝ) ≤ N.choose m := Nat.cast_nonneg _
    exact mul_le_of_le_one_left hpos hfrac
  · have : N.choose m = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hm)
    simp [this]

lemma covering_of_level_ge_card {H : Finset (Finset α)} {ℓ : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hf : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) ≤ coverCost p H)
    (hm : Fintype.card α ≤ coveringLevel p (Fintype.card α) ℓ) :
    ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) *
        ((Fintype.card α).choose (coveringLevel p (Fintype.card α) ℓ) : ℝ) ≤
      (((generate H).filter
          (fun S => S.card = coveringLevel p (Fintype.card α) ℓ)).card : ℝ) := by
  set N := Fintype.card α
  set m := coveringLevel p N ℓ
  have hpos : (0 : ℝ) < (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) := by
    have : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 2) ≤ 1 / 4 := by
      have : (2 : ℝ) ^ (2 : ℕ) ≤ 2 ^ (ℓ + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
      simpa [h4] using one_div_le_one_div_of_le (by positivity) this
    linarith
  have hH : H.Nonempty := coverCost_pos_imp_nonempty hp0 (lt_of_lt_of_le hpos hf)
  rcases lt_or_eq_of_le hm with hlt | heq
  · have : N.choose m = 0 := Nat.choose_eq_zero_of_lt hlt
    simp [this]
  · -- m = N: the unique N-set is `univ`, which is in `generate H`.
    have hch : N.choose m = 1 := by
      rw [heq, Nat.choose_self]
    have huniv : univ ∈ generate H := by
      obtain ⟨S, hS⟩ := hH
      exact mem_generate.mpr ⟨S, hS, subset_univ _⟩
    have hmem : univ ∈ (generate H).filter (fun S => S.card = m) := by
      refine mem_filter.mpr ⟨huniv, ?_⟩
      rw [card_univ]
      exact heq
    have hone : (1 : ℝ) ≤ (((generate H).filter (fun S => S.card = m)).card : ℝ) := by
      have : 0 < ((generate H).filter (fun S => S.card = m)).card :=
        card_pos.mpr ⟨univ, hmem⟩
      exact_mod_cast this
    have hfrac := frac_le_one ℓ
    have : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose m : ℝ)
        ≤ (((generate H).filter (fun S => S.card = m)).card : ℝ) := by
      rw [hch]
      simpa using (hfrac.trans hone)
    simpa [m] using this

lemma ell1_lt {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : ⌊((9 : ℝ) / 10) * ℓ⌋₊ < ℓ := by
  have hk : kmin ℓ ≤ ℓ := kmin_le ℓ hℓ
  have : ⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1 ≤ ℓ := by simpa [kmin] using hk
  omega

lemma coveringLevel_nonneg (p : ℝ) (N ℓ : ℕ) (hp0 : 0 ≤ p) :
    0 ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
  have hL : 0 ≤ coveringConstant := by simp [coveringConstant]
  have hlog : 0 ≤ Real.logb 2 (ℓ + 1 : ℝ) :=
    Real.logb_nonneg (by norm_num) (by
      have : (1 : ℝ) ≤ ℓ + 1 := by exact_mod_cast (Nat.le_add_left 1 ℓ)
      exact this)
  positivity

lemma floor_add_floor_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ⌊a⌋₊ + ⌊b⌋₊ ≤ ⌊a + b⌋₊ := by
  have h : (⌊a⌋₊ : ℝ) + ⌊b⌋₊ ≤ a + b :=
    add_le_add (Nat.floor_le ha) (Nat.floor_le hb)
  have : ((⌊a⌋₊ + ⌊b⌋₊ : ℕ) : ℝ) ≤ a + b := by
    push_cast
    exact h
  exact (Nat.le_floor_iff (add_nonneg ha hb)).mpr this

lemma log_ell1_add_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Real.logb 2 (⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1 : ℝ) + (1 : ℝ) / 10
      ≤ Real.logb 2 (ℓ + 1 : ℝ) := by
  set ℓ₁ := ⌊((9 : ℝ) / 10) * ℓ⌋₊
  have hℓ₁ : ℓ₁ + 1 = kmin ℓ := by simp [ℓ₁, kmin]
  have h2 := two_rpow_one_div_ten_le
  have hk := eleven_mul_kmin_le ℓ hℓ
  have hmul : (ℓ₁ + 1 : ℝ) * ((11 : ℝ) / 10) ≤ ℓ + 1 := by
    have : (11 : ℝ) * (ℓ₁ + 1) ≤ 10 * (ℓ + 1) := by
      have hcast : (ℓ₁ + 1 : ℝ) = kmin ℓ := by exact_mod_cast hℓ₁
      rw [hcast]
      exact_mod_cast hk
    calc
      (ℓ₁ + 1 : ℝ) * (11 / 10) = 11 * (ℓ₁ + 1) / 10 := by ring
      _ ≤ 10 * (ℓ + 1) / 10 :=
        div_le_div_of_nonneg_right this (by positivity)
      _ = ℓ + 1 := by ring
  have hmul' : (ℓ₁ + 1 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ ℓ + 1 :=
    le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) hmul
  have hx : 0 < (ℓ₁ + 1 : ℝ) := by exact_mod_cast Nat.succ_pos ℓ₁
  have hprod : 0 < (ℓ₁ + 1 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 10) := by positivity
  have hlogprod :
      Real.logb 2 ((ℓ₁ + 1 : ℝ) * 2 ^ ((1 : ℝ) / 10))
        = Real.logb 2 (ℓ₁ + 1 : ℝ) + (1 : ℝ) / 10 := by
    have := Real.logb_mul (b := 2) (hx.ne') (by positivity : (2 : ℝ) ^ ((1 : ℝ) / 10) ≠ 0)
    have hpow : Real.logb 2 ((2 : ℝ) ^ ((1 : ℝ) / 10)) = (1 : ℝ) / 10 :=
      Real.logb_rpow (by norm_num) (by norm_num)
    simpa [hpow] using this
  have hle : Real.logb 2 ((ℓ₁ + 1 : ℝ) * 2 ^ ((1 : ℝ) / 10))
      ≤ Real.logb 2 (ℓ + 1 : ℝ) :=
    (Real.logb_le_logb (by norm_num) hprod (by positivity)).2 hmul'
  linarith [hlogprod, hle]

lemma coveringLevel_lift {p : ℝ} {N w ℓ : ℕ} (hp0 : 0 ≤ p) (hℓ : 1 ≤ ℓ)
    (hw : w = coveringWidth p N) :
    coveringLevel p (N - w) ⌊((9 : ℝ) / 10) * ℓ⌋₊ + w ≤
      coveringLevel p N ℓ := by
  set ℓ₁ := ⌊((9 : ℝ) / 10) * ℓ⌋₊
  have ha := coveringLevel_nonneg p (N - w) ℓ₁ hp0
  have hb : 0 ≤ ((1 : ℝ) / 10) * coveringConstant * p * N := by
    have : 0 ≤ coveringConstant := by simp [coveringConstant]
    positivity
  have hw' : w = ⌊((1 : ℝ) / 10) * coveringConstant * p * N⌋₊ := by
    simpa [coveringWidth] using hw
  have hfl := floor_add_floor_le ha hb
  have hsum : coveringLevel p (N - w) ℓ₁ + w
      ≤ ⌊coveringConstant * p * ((N - w : ℕ) : ℝ) * Real.logb 2 (ℓ₁ + 1 : ℝ)
          + ((1 : ℝ) / 10) * coveringConstant * p * N⌋₊ := by
    simpa [coveringLevel, hw'] using hfl
  have hre :
      coveringConstant * p * ((N - w : ℕ) : ℝ) * Real.logb 2 (ℓ₁ + 1 : ℝ)
        + ((1 : ℝ) / 10) * coveringConstant * p * N
        ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
    have hlog := log_ell1_add_le ℓ hℓ
    have hNw : ((N - w : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr (Nat.sub_le _ _)
    have hL : 0 ≤ coveringConstant * p := by
      have : 0 ≤ coveringConstant := by simp [coveringConstant]
      positivity
    have hlog0 : 0 ≤ Real.logb 2 (ℓ₁ + 1 : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (Nat.le_add_left 1 ℓ₁))
    have h1 : coveringConstant * p * ((N - w : ℕ) : ℝ) * Real.logb 2 (ℓ₁ + 1 : ℝ)
        ≤ coveringConstant * p * N * Real.logb 2 (ℓ₁ + 1 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNw hL) hlog0
    have h2 : coveringConstant * p * N * Real.logb 2 (ℓ₁ + 1 : ℝ)
        + ((1 : ℝ) / 10) * coveringConstant * p * N
        = coveringConstant * p * N * (Real.logb 2 (ℓ₁ + 1 : ℝ) + 1 / 10) := by
      ring
    have h3 : coveringConstant * p * N * (Real.logb 2 (ℓ₁ + 1 : ℝ) + 1 / 10)
        ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hL (Nat.cast_nonneg _))
    linarith [h1, h2, h3]
  exact hsum.trans (Nat.floor_le_floor hre)

lemma card_subtype_not_mem (W : Finset α) :
    Fintype.card {x : α // x ∉ W} = Fintype.card α - W.card := by
  classical
  rw [Fintype.card_subtype]
  have : univ.filter (fun x : α => x ∉ W) = univ \ W := by
    ext x
    simp [mem_sdiff]
  rw [this, card_sdiff_of_subset (subset_univ _), card_univ]

/-- Regard the part of `S` outside `W` as a finset in the complementary subtype. -/
def toSub (W : Finset α) (S : Finset α) : Finset {x : α // x ∉ W} :=
  S.subtype fun x => x ∉ W

/-- Map a finset in the complement of `W` back to the ambient type. -/
def ofSub (W : Finset α) (T : Finset {x : α // x ∉ W}) : Finset α :=
  T.map ⟨Subtype.val, Subtype.val_injective⟩

omit [DecidableEq α] [Fintype α] in
lemma ofSub_card (W : Finset α) (T : Finset {x : α // x ∉ W}) :
    (ofSub W T).card = T.card :=
  card_map _

omit [Fintype α] in
lemma ofSub_toSub {W S : Finset α} (h : Disjoint S W) :
    ofSub W (toSub W S) = S :=
  subtype_map_of_mem fun _ hx => disjoint_left.mp h hx

omit [Fintype α] in
lemma toSub_subset {W S T : Finset α} (h : S ⊆ T) :
    toSub W S ⊆ toSub W T :=
  subtype_mono h

omit [DecidableEq α] [Fintype α] in
lemma ofSub_subset {W : Finset α} {T₁ T₂ : Finset {x : α // x ∉ W}} (h : T₁ ⊆ T₂) :
    ofSub W T₁ ⊆ ofSub W T₂ :=
  map_subset_map.mpr h

lemma smallMinimals_disjoint {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (h : T ∈ smallMinimals H W ℓ) : Disjoint T W :=
  restrictFamily_disjoint (minimals_subset _ (filter_subset _ _ h))

omit [Fintype α] in
lemma toSub_card {W S : Finset α} (h : Disjoint S W) :
    (toSub W S).card = S.card := by
  rw [toSub, card_subtype, filter_eq_self.2 fun x hx => disjoint_left.mp h hx]

lemma coverCost_toSub {p : ℝ} (hp0 : 0 ≤ p)
    (F : Finset (Finset α)) (W : Finset α)
    (hF : ∀ S ∈ F, Disjoint S W) :
    coverCost p (F.image (toSub W)) = coverCost p F := by
  apply le_antisymm
  · obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p F
    let G₀ := G.filter fun T => Disjoint T W
    have hG₀ : Covers G₀ F := by
      intro S hS
      obtain ⟨T, hT, hTS⟩ := mem_generate.mp (hG hS)
      have hdis : Disjoint T W := Disjoint.mono_left hTS (hF S hS)
      exact mem_generate.mpr ⟨T, mem_filter.mpr ⟨hT, hdis⟩, hTS⟩
    have hcov : Covers (G₀.image (toSub W)) (F.image (toSub W)) := by
      intro S' hS'
      obtain ⟨S, hS, rfl⟩ := mem_image.mp hS'
      obtain ⟨T, hT, hTS⟩ := mem_generate.mp (hG₀ hS)
      exact mem_generate.mpr ⟨toSub W T, mem_image.mpr ⟨T, hT, rfl⟩, toSub_subset hTS⟩
    have hinj : Set.InjOn (toSub W) (G₀ : Set (Finset α)) := by
      intro T₁ hT₁ T₂ hT₂ h
      have d1 := (mem_filter.mp (by exact hT₁)).2
      have d2 := (mem_filter.mp (by exact hT₂)).2
      simpa [ofSub_toSub d1, ofSub_toSub d2] using congrArg (ofSub W) h
    have hE : expectation p (G₀.image (toSub W)) = expectation p G₀ := by
      simp only [expectation]
      rw [sum_image hinj]
      refine sum_congr rfl ?_
      intro T hT
      rw [toSub_card (mem_filter.mp hT).2]
    have : coverCost p (F.image (toSub W)) ≤ expectation p G :=
      (coverCost_le_expectation hp0 hcov).trans <|
        (le_of_eq hE).trans (expectation_mono hp0 (filter_subset _ _))
    exact this.trans_eq hGe
  · obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p (F.image (toSub W))
    have hcov : Covers (G.image (ofSub W)) F := by
      intro S hS
      have hS' : toSub W S ∈ F.image (toSub W) := mem_image.mpr ⟨S, hS, rfl⟩
      obtain ⟨T, hT, hTS⟩ := mem_generate.mp (hG hS')
      have hsub : ofSub W T ⊆ S := by
        have h1 : ofSub W T ⊆ ofSub W (toSub W S) := ofSub_subset hTS
        simpa [ofSub_toSub (hF S hS)] using h1
      exact mem_generate.mpr ⟨ofSub W T, mem_image.mpr ⟨T, hT, rfl⟩, hsub⟩
    have hinj : Function.Injective (ofSub W) :=
      map_injective ⟨Subtype.val, Subtype.val_injective⟩
    have hE : expectation p (G.image (ofSub W)) = expectation p G := by
      simp only [expectation]
      rw [sum_image (Set.injOn_of_injective hinj)]
      simp [ofSub_card]
    exact (coverCost_le_expectation hp0 hcov).trans_eq (hE.trans hGe)

lemma generate_union_mem {H : Finset (Finset α)} {W : Finset α} {ℓ : ℕ}
    {T : Finset {x : α // x ∉ W}}
    (hT : T ∈ generate ((smallMinimals H W ℓ).image (toSub W))) :
    ofSub W T ∪ W ∈ generate H := by
  obtain ⟨U, hU, hUT⟩ := mem_generate.mp hT
  obtain ⟨S', hS', rfl⟩ := mem_image.mp hU
  have hdis := smallMinimals_disjoint hS'
  have hS'sub : S' ⊆ ofSub W T := by
    have : ofSub W (toSub W S') ⊆ ofSub W T := ofSub_subset hUT
    rwa [ofSub_toSub hdis] at this
  have hres : S' ∈ restrictFamily H W :=
    minimals_subset _ (filter_subset _ _ hS')
  obtain ⟨S, hSH, hSeq⟩ := mem_restrictFamily.mp hres
  have hSsub : S ⊆ ofSub W T ∪ W := by
    intro x hxS
    by_cases hxW : x ∈ W
    · exact mem_union.mpr (Or.inr hxW)
    · have : x ∈ S' := by
        have : x ∈ S \ W := mem_sdiff.mpr ⟨hxS, hxW⟩
        rwa [hSeq] at this
      exact mem_union.mpr (Or.inl (hS'sub this))
  exact mem_generate.mpr ⟨S, hSH, hSsub⟩

omit [Fintype α] in
lemma ofSub_union_card {W : Finset α} (T : Finset {x : α // x ∉ W}) :
    (ofSub W T ∪ W).card = T.card + W.card := by
  have hdis : Disjoint (ofSub W T) W := by
    refine disjoint_left.mpr ?_
    intro x hxT hxW
    rcases mem_map.mp hxT with ⟨⟨_, hx⟩, _, rfl⟩
    exact hx hxW
  rw [card_union_of_disjoint hdis, ofSub_card, Nat.add_comm]

lemma coveringWidth_le_card {p : ℝ} {N ℓ : ℕ} (hp0 : 0 ≤ p) (hℓ : 1 ≤ ℓ)
    (hlev : ¬N ≤ coveringLevel p N ℓ) : coveringWidth p N ≤ N := by
  set w := coveringWidth p N
  by_contra hgt
  have hw' : N + 1 ≤ w := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hgt)
  have h100 : (N : ℝ) + 1 ≤ 100 * p * N := by
    have hwle : (w : ℝ) ≤ 100 * p * N := by
      have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 100 * p * N)
      simpa [w, coveringWidth_eq] using this
    have : (N : ℝ) + 1 ≤ w := by exact_mod_cast hw'
    exact this.trans hwle
  have hlog : (1 : ℝ) ≤ Real.logb 2 (ℓ + 1 : ℝ) := by
    have h2 : (2 : ℝ) ≤ ℓ + 1 := by exact_mod_cast Nat.succ_le_succ hℓ
    have hself : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    have hle : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (ℓ + 1 : ℝ) :=
      (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) (by norm_num)
        (by positivity)).mpr h2
    simpa [hself] using hle
  have harg : (N : ℝ) < coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
    have hge : 10 * (100 * p * N) ≤
        coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
      rw [show coveringConstant = (1000 : ℝ) by rfl]
      have : (1000 : ℝ) * p * N * 1 ≤ 1000 * p * N * Real.logb 2 (ℓ + 1 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      convert this using 1
      ring
    have hlt : (N : ℝ) < 10 * (100 * p * N) := by
      have : (N : ℝ) < 10 * (N + 1) := by linarith
      have : 10 * ((N : ℝ) + 1) ≤ 10 * (100 * p * N) :=
        mul_le_mul_of_nonneg_left h100 (by positivity)
      linarith
    exact hlt.trans_le hge
  have : N ≤ coveringLevel p N ℓ :=
    (Nat.le_floor_iff (coveringLevel_nonneg p N ℓ hp0)).mpr (le_of_lt (by
      simpa [coveringLevel] using harg))
  exact hlev this

lemma floor_nine_tenths_le_card_sub_width {p : ℝ} {N ℓ : ℕ}
    (hp0 : 0 ≤ p) (hℓ : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (hN : 1 ≤ N)
    (hlev : ¬N ≤ coveringLevel p N ℓ) :
    ⌊((9 : ℝ) / 10) * ℓ⌋₊ ≤ N - coveringWidth p N := by
  set w := coveringWidth p N
  set ℓ₁ := ⌊((9 : ℝ) / 10) * ℓ⌋₊
  by_contra h
  have hlt : N - w < ℓ₁ := Nat.lt_of_not_ge h
  have hwN := coveringWidth_le_card hp0 hℓ hlev
  have hcast : ((N - w : ℕ) : ℝ) = (N : ℝ) - w := Nat.cast_sub hwN
  have hfl : (ℓ₁ : ℝ) ≤ ((9 : ℝ) / 10) * ℓ := Nat.floor_le (by positivity)
  have : (N : ℝ) - w < ((9 : ℝ) / 10) * N := by
    have : ((N - w : ℕ) : ℝ) < ℓ₁ := by exact_mod_cast hlt
    have hℓN' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓN
    nlinarith [hcast, hfl, hℓN']
  have hltw : (1 : ℝ) / 10 * N < w := by linarith
  have hwle : (w : ℝ) ≤ 100 * p * N := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 100 * p * N)
    simpa [w, coveringWidth_eq] using this
  have hp : (1 : ℝ) / 1000 < p := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.succ_le_iff.mp hN)
    have : (1 : ℝ) / 10 * N < 100 * p * N := hltw.trans_le hwle
    have : (1 : ℝ) / 10 < 100 * p := by
      have := (mul_lt_mul_iff_left₀ hNpos).mp this
      simpa [mul_comm] using this
    linarith
  have hlog : (1 : ℝ) ≤ Real.logb 2 (ℓ + 1 : ℝ) := by
    have h2 : (2 : ℝ) ≤ ℓ + 1 := by exact_mod_cast Nat.succ_le_succ hℓ
    have hself : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    have hle : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (ℓ + 1 : ℝ) :=
      (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) (by norm_num)
        (by positivity)).mpr h2
    simpa [hself] using hle
  have harg : (N : ℝ) < coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.succ_le_iff.mp hN)
    have h1 : (1 : ℝ) < 1000 * p := by linarith
    have h1' : (1 : ℝ) < 1000 * p * Real.logb 2 (ℓ + 1 : ℝ) :=
      one_lt_mul_of_lt_of_le h1 hlog
    have : N * 1 < N * (1000 * p * Real.logb 2 (ℓ + 1 : ℝ)) :=
      mul_lt_mul_of_pos_left h1' hNpos
    rw [show coveringConstant = (1000 : ℝ) by rfl]
    convert this using 1 <;> ring
  have : N ≤ coveringLevel p N ℓ :=
    (Nat.le_floor_iff (coveringLevel_nonneg p N ℓ hp0)).mpr (le_of_lt (by
      simpa [coveringLevel] using harg))
  exact hlev this

lemma geometric_tail_bound (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
        (2 : ℝ) ^ (ℓ + 2) ≤ (12 / 11) * (1 / (2 : ℝ) ^ (ℓ + 2)) := by
  have hgeom := choose_geom_tail_le ℓ
  by_cases h1 : ℓ = 1
  · subst h1
    have hk : kmin 1 = 1 := by unfold kmin; norm_num
    have : ∑ k ∈ Icc (kmin 1) 1, ((1 : ℝ) / 100) ^ k * (1 : ℕ).choose k
        = (1 : ℝ) / 100 := by
      simp [hk, Nat.choose_self]
    rw [this]
    norm_num
  · have h2 : 2 ≤ ℓ := Nat.succ_le_iff.mpr (lt_of_le_of_ne hℓ (Ne.symm h1))
    have hbf := bad_frac_le_of_two ℓ h2
    have : (∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
        (2 : ℝ) ^ (ℓ + 2) ≤
        ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ * 2 ^ (ℓ + 2) :=
      mul_le_mul_of_nonneg_right hgeom (by positivity)
    exact this.trans hbf

lemma restricted_level_card_le {H : Finset (Finset α)} {W : Finset α} {ℓ k w : ℕ}
    (hWcard : W.card = w) :
    (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
        (fun T => T.card = k)).card : ℝ) ≤
      (((generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)).card : ℝ) := by
  let src := (generate ((smallMinimals H W ℓ).image (toSub W))).filter
    (fun T => T.card = k)
  let tgt := (generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)
  let f := fun T : Finset {x : α // x ∉ W} => ofSub W T ∪ W
  have himg : src.image f ⊆ tgt := by
    intro U hU
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hU
    have ⟨hgen, hkT⟩ := mem_filter.mp hT
    refine mem_filter.mpr ⟨generate_union_mem hgen, ?_⟩
    exact ⟨by rw [ofSub_union_card, hkT, hWcard], subset_union_right⟩
  have hinj : Set.InjOn f src := by
    intro T₁ _ T₂ _ heq
    have d1 : Disjoint (ofSub W T₁) W := by
      refine disjoint_left.mpr fun x hxT hxW => ?_
      rcases mem_map.mp hxT with ⟨⟨_, hx⟩, _, rfl⟩
      exact hx hxW
    have d2 : Disjoint (ofSub W T₂) W := by
      refine disjoint_left.mpr fun x hxT hxW => ?_
      rcases mem_map.mp hxT with ⟨⟨_, hx⟩, _, rfl⟩
      exact hx hxW
    have : ofSub W T₁ = ofSub W T₂ := by
      rw [(union_sdiff_cancel_right d1).symm, (union_sdiff_cancel_right d2).symm]
      exact congrArg (fun s : Finset α => s \ W) heq
    exact map_injective ⟨Subtype.val, Subtype.val_injective⟩ this
  have : #src ≤ #tgt := (card_image_of_injOn hinj).symm.trans_le (card_le_card himg)
  exact Nat.cast_le.mpr this

lemma good_width_card_lower_bound {H : Finset (Finset α)} {p : ℝ} {N w ℓ : ℕ}
    (hp0 : 0 ≤ p) (hb : IsBounded H ℓ) (hNcard : Fintype.card α = N)
    (hw : w = coveringWidth p N) :
    let Good := (univ.filter (fun W : Finset α => W.card = w)).filter fun W =>
      coverCost p (largeMinimals H W ℓ) ≤ 1 / (2 : ℝ) ^ (ℓ + 2)
    (N.choose w : ℝ) *
        (1 - (∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
          (2 : ℝ) ^ (ℓ + 2)) ≤ (#Good : ℝ) := by
  let Lw := univ.filter (fun W : Finset α => W.card = w)
  let Good := Lw.filter fun W =>
    coverCost p (largeMinimals H W ℓ) ≤ 1 / (2 : ℝ) ^ (ℓ + 2)
  let Bad := Lw.filter fun W =>
    1 / (2 : ℝ) ^ (ℓ + 2) < coverCost p (largeMinimals H W ℓ)
  set β : ℝ :=
    (∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
      (2 : ℝ) ^ (ℓ + 2)
  have hpart : Good ∪ Bad = Lw := by
    ext W
    simp only [Good, Bad, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hle : coverCost p (largeMinimals H W ℓ) ≤ 1 / (2 : ℝ) ^ (ℓ + 2)
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, lt_of_not_ge hle⟩
  have hdisGB : Disjoint Good Bad := by
    refine disjoint_left.mpr ?_
    intro W hG hB
    exact (not_le_of_gt (mem_filter.mp hB).2) (mem_filter.mp hG).2
  have htail := double_counting_tail hp0 H ℓ hb
  have hBad : (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) ≤
      ∑ W ∈ Lw, coverCost p (largeMinimals H W ℓ) := by
    have h1 : ∑ W ∈ Bad, (1 / (2 : ℝ) ^ (ℓ + 2)) ≤
        ∑ W ∈ Bad, coverCost p (largeMinimals H W ℓ) :=
      sum_le_sum fun W hW => le_of_lt (mem_filter.mp hW).2
    have h2 : ∑ W ∈ Bad, (1 / (2 : ℝ) ^ (ℓ + 2)) =
        (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) := by
      simp [sum_const, nsmul_eq_mul]
    have h3 : ∑ W ∈ Bad, coverCost p (largeMinimals H W ℓ) ≤
        ∑ W ∈ Lw, coverCost p (largeMinimals H W ℓ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        fun _ _ _ => coverCost_nonneg hp0 _
    linarith
  have hadd : #Good + #Bad = #Lw := by
    rw [← card_union_of_disjoint hdisGB, hpart]
  have hsub : (#Good : ℝ) = (#Lw : ℝ) - (#Bad : ℝ) := by
    have : (#Good : ℝ) + (#Bad : ℝ) = (#Lw : ℝ) := by exact_mod_cast hadd
    linarith
  have hLw : (#Lw : ℝ) = (N.choose w : ℝ) := by
    simp [Lw, hNcard]
  have hBd : (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) ≤
      (N.choose w : ℝ) *
        ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k :=
    hBad.trans (by simpa [Lw, hNcard, hw] using htail)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (ℓ + 2) := by positivity
  have hBadle : (#Bad : ℝ) ≤ (N.choose w : ℝ) * β := by
    have hmul : (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) * (2 : ℝ) ^ (ℓ + 2)
        ≤ ((N.choose w : ℝ) *
            ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
          (2 : ℝ) ^ (ℓ + 2) :=
      mul_le_mul_of_nonneg_right hBd (le_of_lt hpow)
    have hL : (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) * (2 : ℝ) ^ (ℓ + 2)
        = (#Bad : ℝ) := by
      rw [mul_assoc, one_div_mul_cancel (ne_of_gt hpow), mul_one]
    have hR : ((N.choose w : ℝ) *
          ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
        (2 : ℝ) ^ (ℓ + 2) = (N.choose w : ℝ) * β := by
      simp only [β]
      ring
    rwa [hL, hR] at hmul
  have hdiff : (N.choose w : ℝ) - (#Bad : ℝ) ≥
      (N.choose w : ℝ) * (1 - β) := by
    have : (N.choose w : ℝ) - (#Bad : ℝ) ≥
        (N.choose w : ℝ) - (N.choose w : ℝ) * β :=
      sub_le_sub_left hBadle _
    have hre : (N.choose w : ℝ) - (N.choose w : ℝ) * β =
        (N.choose w : ℝ) * (1 - β) := by ring
    rwa [hre] at this
  change (N.choose w : ℝ) * (1 - β) ≤ (#Good : ℝ)
  rw [hsub, hLw]
  exact hdiff

lemma good_level_of_induction {H : Finset (Finset α)} {W : Finset α}
    {p : ℝ} {N w ℓ ℓ₁ : ℕ}
    (hind : ∀ (H' : Finset (Finset {x : α // x ∉ W})) (p' : ℝ),
      ℓ₁ ≤ Fintype.card {x : α // x ∉ W} → 0 ≤ p' → p' ≤ 1 → IsBounded H' ℓ₁ →
      (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ₁ + 2) ≤ coverCost p' H' →
      ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
          ((Fintype.card {x : α // x ∉ W}).choose
            (coveringLevel p' (Fintype.card {x : α // x ∉ W}) ℓ₁) : ℝ) ≤
        (((generate H').filter (fun S => S.card =
          coveringLevel p' (Fintype.card {x : α // x ∉ W}) ℓ₁)).card : ℝ))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hℓ₁N : ℓ₁ ≤ N - w)
    (hℓ₁lt : ℓ₁ < ℓ) (hℓ₁ : ℓ₁ = ⌊((9 : ℝ) / 10) * ℓ⌋₊)
    (hf : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) ≤ coverCost p H)
    (hNcard : Fintype.card α = N)
    (hWcard : W.card = w)
    (hgood : coverCost p (largeMinimals H W ℓ) ≤ 1 / (2 : ℝ) ^ (ℓ + 2)) :
    ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
        ((N - w).choose (coveringLevel p (N - w) ℓ₁) : ℝ) ≤
      (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
          (fun T => T.card = coveringLevel p (N - w) ℓ₁)).card : ℝ) := by
  have hcard : Fintype.card {x : α // x ∉ W} = N - w := by
    rw [card_subtype_not_mem, hNcard, hWcard]
  have hb' : IsBounded ((smallMinimals H W ℓ).image (toSub W)) ℓ₁ := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hT
    have hs := IsBounded.smallMinimals (H := H) (W := W) hℓ₁ S hS
    rwa [toSub_card (smallMinimals_disjoint hS)]
  have hf' : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ₁ + 2) ≤
      coverCost p ((smallMinimals H W ℓ).image (toSub W)) := by
    rw [coverCost_toSub hp0 _ _ fun S hS => smallMinimals_disjoint hS]
    have hsm := coverCost_small_ge hp0 H W ℓ
    have hHle := coverCost_le_minimals_restrict hp0 H W
    have h1 : coverCost p (smallMinimals H W ℓ) ≥
        coverCost p H - 1 / (2 : ℝ) ^ (ℓ + 2) := by linarith
    have h2 : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 1) ≤
        coverCost p H - 1 / (2 : ℝ) ^ (ℓ + 2) := by
      have hexp : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 1) = 2 / (2 : ℝ) ^ (ℓ + 2) := by
        have hpow : (2 : ℝ) ^ (ℓ + 2) = 2 ^ (ℓ + 1) * 2 := pow_succ _ _
        field_simp [hpow]
        ring
      calc
        (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 1)
            = 1 / 2 - 2 / (2 : ℝ) ^ (ℓ + 2) := by rw [hexp]
        _ = (1 / 2 - 1 / (2 : ℝ) ^ (ℓ + 2)) - 1 / (2 : ℝ) ^ (ℓ + 2) := by ring
        _ ≤ coverCost p H - 1 / (2 : ℝ) ^ (ℓ + 2) := sub_le_sub_right hf _
    have h3 : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 1) ≤ 1 / (2 : ℝ) ^ (ℓ₁ + 2) :=
      one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))
    linarith
  have := hind ((smallMinimals H W ℓ).image (toSub W)) p
    (by rw [hcard]; exact hℓ₁N) hp0 hp1 hb' hf'
  simpa [hcard] using this

/-- Strong inductive form of Tran–Vu Theorem 2.3. -/
lemma covering_aux (ℓ : ℕ) :
    ∀ {α : Type*} [DecidableEq α] [Fintype α]
      (H : Finset (Finset α)) (p : ℝ),
      ℓ ≤ Fintype.card α → 0 ≤ p → p ≤ 1 → IsBounded H ℓ →
      (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) ≤ coverCost p H →
      ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) *
          ((Fintype.card α).choose (coveringLevel p (Fintype.card α) ℓ) : ℝ) ≤
        (((generate H).filter
            (fun S => S.card = coveringLevel p (Fintype.card α) ℓ)).card : ℝ) := by
  induction ℓ using Nat.strong_induction_on with
  | h ℓ ih =>
    intro α _ _ H p hℓN hp0 hp1 hb hf
    by_cases hempty : ∅ ∈ H
    · exact covering_of_empty_mem hempty
    by_cases hlev : Fintype.card α ≤ coveringLevel p (Fintype.card α) ℓ
    · exact covering_of_level_ge_card hp0 hf hlev
    have hℓ : 1 ≤ ℓ := by
      by_contra h0
      have : ℓ = 0 := Nat.le_zero.mp (Nat.le_of_not_gt h0)
      subst this
      have : ∀ S ∈ H, S.card = 0 := fun S hS => Nat.le_zero.mp (hb S hS)
      have hH : H.Nonempty := by
        have hpos : (0 : ℝ) < (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (0 + 2) := by norm_num
        exact coverCost_pos_imp_nonempty hp0 (lt_of_lt_of_le hpos hf)
      obtain ⟨S, hS⟩ := hH
      have : S = ∅ := card_eq_zero.mp (this S hS)
      exact hempty (this ▸ hS)
    set N := Fintype.card α
    set w := coveringWidth p N
    set ℓ₁ := ⌊((9 : ℝ) / 10) * ℓ⌋₊
    set m := coveringLevel p N ℓ
    have hN : 1 ≤ N := le_trans hℓ hℓN
    have hwN : w ≤ N := by
      simpa [w, N] using coveringWidth_le_card hp0 hℓ (by simpa [N] using hlev)
    have hℓ₁lt : ℓ₁ < ℓ := ell1_lt hℓ
    have hlift := coveringLevel_lift (p := p) (N := N) (w := w) (ℓ := ℓ) hp0 hℓ rfl
    have hℓ₁le : ℓ₁ ≤ N - w := by
      simpa [ℓ₁, w, N] using floor_nine_tenths_le_card_sub_width hp0 hℓ hℓN hN
        (by simpa [N] using hlev)
    let Lw := univ.filter (fun W : Finset α => W.card = w)
    let Good := Lw.filter fun W =>
      coverCost p (largeMinimals H W ℓ) ≤ 1 / (2 : ℝ) ^ (ℓ + 2)
    have hβ :
        (∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
          (2 : ℝ) ^ (ℓ + 2)
        ≤ (12 / 11) * (1 / (2 : ℝ) ^ (ℓ + 2)) := geometric_tail_bound ℓ hℓ
    set k := coveringLevel p (N - w) ℓ₁
    have hkN : k + w ≤ N :=
      (hlift.trans (Nat.le_of_lt (lt_of_not_ge hlev)))
    have hocc := occupation_mul_le ℓ hℓ hβ
    -- For each good W, apply IH to the restricted family on X \ W.
    have hgood : ∀ W ∈ Good,
        ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
            ((N - w).choose k : ℝ) ≤
          (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
              (fun T => T.card = k)).card : ℝ) := by
      intro W hW
      have hWcard : W.card = w := (mem_filter.mp (mem_filter.mp hW).1).2
      simpa [k] using good_level_of_induction (ih ℓ₁ hℓ₁lt) hp0 hp1 hℓ₁le
        hℓ₁lt rfl hf rfl hWcard (mem_filter.mp hW).2
    -- Map each good fibre into level `k+w` of `⟨H⟩` and average.
    have hmap : ∀ W ∈ Good,
        (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
            (fun T => T.card = k)).card : ℝ) ≤
          (((generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)).card : ℝ) := by
      intro W hW
      exact restricted_level_card_le (mem_filter.mp (mem_filter.mp hW).1).2
    let Flev := (generate H).filter (fun S => S.card = k + w)
    have hGood : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
          ((N - w).choose k : ℝ) * (#Good : ℝ) ≤
        ∑ W ∈ Good,
          (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
              (fun T => T.card = k)).card : ℝ) := by
      have h := sum_le_sum hgood
      have hconst :
          ∑ W ∈ Good, ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * ((N - w).choose k : ℝ) =
            ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * ((N - w).choose k : ℝ) * (#Good : ℝ) := by
        simp [sum_const, nsmul_eq_mul, mul_comm, mul_assoc]
      rwa [hconst] at h
    have hsum_le : ∑ W ∈ Good,
          (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
              (fun T => T.card = k)).card : ℝ) ≤
        ∑ W ∈ Good, (((generate H).filter
            (fun S => S.card = k + w ∧ W ⊆ S)).card : ℝ) :=
      sum_le_sum hmap
    have hswap : ∑ W ∈ Good,
          #((generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)) =
        ∑ S ∈ Flev, #(Good.filter (fun W => W ⊆ S)) := by
      have hF : ∀ W, (generate H).filter (fun S => S.card = k + w ∧ W ⊆ S) =
          Flev.filter (fun S => W ⊆ S) := by
        intro W
        ext S
        simp [Flev, mem_filter, and_comm, and_left_comm]
      simp_rw [hF]
      simp only [card_eq_sum_ones, sum_filter]
      rw [sum_comm]
    have hchW : ∀ S ∈ Flev, #(Good.filter (fun W => W ⊆ S)) ≤ (k + w).choose w := by
      intro S hS
      have hSc : S.card = k + w := (mem_filter.mp hS).2
      have : Good.filter (fun W => W ⊆ S) ⊆ S.powersetCard w := by
        intro W hW
        have hG := (mem_filter.mp hW).1
        have hsub := (mem_filter.mp hW).2
        have hw : W.card = w := (mem_filter.mp (filter_subset _ _ hG)).2
        exact mem_powersetCard.mpr ⟨hsub, hw⟩
      simpa [card_powersetCard, hSc] using card_le_card this
    have hchoose :
        (N.choose w : ℝ) * ((N - w).choose k : ℝ) =
          (N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ) := by
      have h := Nat.choose_mul (n := N) (k := w + k) (s := w) (Nat.le_add_right w k)
      have hk : k + w = w + k := Nat.add_comm _ _
      have hkw : (w + k - w : ℕ) = k := Nat.add_sub_cancel_left w k
      rw [hk]
      simpa [hkw] using (congrArg (fun n : ℕ => (n : ℝ)) h.symm)
    have hFlev : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose (k + w) : ℝ) ≤
        (#Flev : ℝ) := by
      set β : ℝ :=
        (∑ i ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ i * ℓ.choose i) * (2 : ℝ) ^ (ℓ + 2)
      have hG : (#Good : ℝ) ≥ (N.choose w : ℝ) * (1 - β) := by
        simpa [Good, Lw, β] using
          good_width_card_lower_bound hp0 hb (by rfl) (by rfl)
      have havg : (#Flev : ℝ) * ((k + w).choose w : ℝ) ≥
          ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * ((N - w).choose k : ℝ) *
            (#Good : ℝ) := by
        have h1 := hGood.trans hsum_le
        have hsw : ∑ W ∈ Good,
              (((generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)).card : ℝ) =
            ∑ S ∈ Flev, ((Good.filter (fun W => W ⊆ S)).card : ℝ) := by
          exact_mod_cast hswap
        have h2 : ∑ S ∈ Flev, ((Good.filter (fun W => W ⊆ S)).card : ℝ) ≤
            ∑ S ∈ Flev, ((k + w).choose w : ℝ) :=
          sum_le_sum fun S hS => Nat.cast_le.mpr (hchW S hS)
        have h3 : ∑ S ∈ Flev, ((k + w).choose w : ℝ) =
            (#Flev : ℝ) * ((k + w).choose w : ℝ) := by
          simp [sum_const, nsmul_eq_mul]
        linarith
      have ha : (0 : ℝ) ≤ (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2) := by positivity
      have hCnk : (0 : ℝ) ≤ ((N - w).choose k : ℝ) := Nat.cast_nonneg _
      have hCkw : (0 : ℝ) ≤ ((k + w).choose w : ℝ) := Nat.cast_nonneg _
      have hCnkw : (0 : ℝ) ≤ (N.choose (k + w) : ℝ) := Nat.cast_nonneg _
      have hocc' :
          (2 / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) ≤
            ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) := by
        simpa [β, kmin, ℓ₁] using hocc
      have hstep : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
            ((N - w).choose k : ℝ) * (#Good : ℝ)
          ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * ((N - w).choose k : ℝ) *
              ((N.choose w : ℝ) * (1 - β)) :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg ha hCnk)
      have hcomb : (#Flev : ℝ) * ((k + w).choose w : ℝ) ≥
          ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose (k + w) : ℝ) *
            ((k + w).choose w : ℝ) := by
        have hL : (#Flev : ℝ) * ((k + w).choose w : ℝ)
            ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
              (N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ) := by
          calc
            (#Flev : ℝ) * ((k + w).choose w : ℝ)
                ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
                    ((N - w).choose k : ℝ) * (#Good : ℝ) := havg
            _ ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
                    ((N - w).choose k : ℝ) * ((N.choose w : ℝ) * (1 - β)) := hstep
            _ = ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
                    ((N.choose w : ℝ) * ((N - w).choose k : ℝ)) := by ring
            _ = ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
                    ((N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ)) := by
              rw [hchoose]
            _ = ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
                    (N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ) := by ring
        have hR :
            ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
                (N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ)
              ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose (k + w) : ℝ) *
                ((k + w).choose w : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hocc' hCnkw) hCkw
        exact (ge_iff_le.mp hR).trans (ge_iff_le.mp hL)
      have hpos' : (0 : ℝ) < ((k + w).choose w : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_left w k))
      exact (mul_le_mul_iff_of_pos_right hpos').mp (ge_iff_le.mp hcomb)
    have hmfrac : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose m : ℝ) ≤
        (((generate H).filter (fun S => S.card = m)).card : ℝ) := by
      have hle : k + w ≤ m := hlift
      have hkw : k + w ≤ N := hkN
      have hch0 : 0 < (N.choose (k + w) : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos hkw)
      have hch1 : 0 < (N.choose m : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos (le_of_lt (lt_of_not_ge hlev)))
      have hfrac := generate_level_frac_le (α := α) H hle (le_of_lt (lt_of_not_ge hlev))
      have hfrac' : (#Flev : ℝ) / (N.choose (k + w) : ℝ) ≤
          (((generate H).filter (fun S => S.card = m)).card : ℝ) / (N.choose m : ℝ) := by
        simpa [Flev, N] using hfrac
      have hα : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) ≤
          (#Flev : ℝ) / (N.choose (k + w) : ℝ) :=
        (le_div_iff₀ hch0).mpr hFlev
      exact (le_div_iff₀ hch1).mp (hα.trans hfrac')
    simpa [m, N] using hmfrac

end

end KahnKalai
