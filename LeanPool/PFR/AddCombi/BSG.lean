/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/

module
public import LeanPool.PFR.AddCombi.Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Data.Real.Basic

public import LeanPool.PFR.AddCombi.Convolution.Finite.Order
public import LeanPool.PFR.AddCombi.Mathlib.Algebra.Star.Pi
public import LeanPool.PFR.AddCombi.Mathlib.Algebra.Order.GroupWithZero.Indicator
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Group.Pointwise.Finset.Density
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Finset.CastCard
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Tactic.Positivity

/-!
# The Balog-Szemerédi-Gowers theorem

A straightforward calculation shows that sets of small doubling have large additive energy.
The converse is *almost* true, in the sense that a set of large additive energy contains a large set
of small doubling. This is the content of the Balog-Szemerédi-Gowers theorem, which this file
proves.
-/

open Finset hiding card
open Fintype
open scoped BigOperators Pointwise Combinatorics.Additive' Indicator

section
variable {α : Type*} [Fintype α] [DecidableEq α] {H : Finset (α × α)} {A B X : Finset α} {a b x : α}
  {K : ℝ}

omit [Fintype α] in
public
lemma oneOfPair_aux (hH : H ⊆ X ×ˢ X) : #{yz ∈ H | yz.1 = x} = #{c ∈ X | (x, c) ∈ H} := by
  refine card_nbij' Prod.snd (fun c ↦ (x, c)) ?_ (by simp [Set.MapsTo])
    (by grind [Set.LeftInvOn]) (by simp [Set.LeftInvOn])
  simpa +contextual [Set.MapsTo, eq_comm] using fun a b hab _ ↦ (mem_product.1 (hH hab)).2

/-- Elements of `X` with at least the threshold density of partners in `H`. -/
@[expose]
public
noncomputable def oneOfPair (H : Finset (α × α)) (X : Finset α) : Finset α :=
  {x ∈ X | (3 / 4 : ℝ) * X.dens ≤ {c ∈ X | (x, c) ∈ H}.dens}

public
lemma oneOfPair_subset : oneOfPair H X ⊆ X := filter_subset ..

public
lemma mem_oneOfPair :
    x ∈ oneOfPair H X ↔ x ∈ X ∧ (3 / 4 : ℝ) * X.dens ≤ {c ∈ X | (x, c) ∈ H}.dens := mem_filter

public
lemma oneOfPair_bound_one :
    (∑ x ∈ X \ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α ≤ (3 / 4) * X.dens ^ 2 := calc
  _ ≤ (∑ _x ∈ X \ oneOfPair H X, 3 / 4 * X.dens : ℝ) / card α := by
    gcongr
    grind [oneOfPair]
  _ = (X \ oneOfPair H X).dens * (3 / 4 * X.dens) := by simp [dens]; ring
  _ ≤ X.dens * (3 / 4 * X.dens) := by grw [sdiff_subset]
  _ = _ := by ring

public
lemma oneOfPair_bound_two (hH : H ⊆ X ×ˢ X) (Hcard : (7 / 8 : ℝ) * X.dens ^ 2 ≤ H.dens) :
    (1 / 8 : ℝ) * X.dens ^ 2 ≤ X.dens * (oneOfPair H X).dens := calc
  _ ≤ H.dens - (3 / 4 : ℝ) * X.dens ^ 2 := by linarith
  _ ≤ H.dens - (∑ x ∈ X \ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    gcongr; exact oneOfPair_bound_one
  _ = H.dens - (∑ x ∈ X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α
    + (∑ x ∈ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    rw [sum_sdiff_eq_sub oneOfPair_subset, sub_add, sub_div]
  _ = (∑ x ∈ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    simp only [dens, Fintype.card_prod, Nat.cast_mul, NNRat.cast_div, NNRat.cast_natCast,
      NNRat.cast_mul, ← sum_div, div_div, add_eq_right, sub_eq_zero, ← oneOfPair_aux hH]
    norm_cast
    rw [← card_eq_sum_card_fiberwise fun x hx ↦ (mem_product.1 (hH hx)).1]
  _ ≤ (∑ _x ∈ oneOfPair H X, (X.dens : ℝ)) / card α := by gcongr with i; exact filter_subset ..
  _ = X.dens * (oneOfPair H X).dens := by simp [dens]; ring

private lemma oneOfPair_bound (hH : H ⊆ X ×ˢ X) (hX : X.Nonempty)
    (Hcard : (7 / 8 : ℝ) * X.dens ^ 2 ≤ H.dens) (h : A.dens / (2 * K) ≤ X.dens) :
    A.dens / (2 ^ 4 * K : ℝ) ≤ (oneOfPair H X).dens := calc
    _ = (A.dens / (2 * K) : ℝ) / 8 := by ring
    _ ≤ (X.dens / 8 : ℝ) := by gcongr
    _ ≤ (oneOfPair H X).dens :=
      le_of_mul_le_mul_left ((oneOfPair_bound_two hH Hcard).trans_eq' (by ring)) <| by positivity

public
lemma quadruple_bound_c {a b : α} (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X) :
    (X.dens : ℝ) / 2 ≤ {c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.dens := by
  rw [mem_oneOfPair] at ha hb
  rw [filter_and, cast_dens_inter, ← filter_or]
  have : ({c ∈ X | (a, c) ∈ H ∨ (b, c) ∈ H}.dens : ℝ) ≤ X.dens := by grw [filter_subset]
  linarith [ha.2, hb.2, this]

end

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset G} {x : G}

omit [Fintype G] in
public
lemma quadruple_bound_right {a b : G} (H : Finset (G × G)) (X : Finset G) (h : x = a - b) :
    (#({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦ ((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) : ℝ)
      ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = a - b) := by
  rw [← h, Nat.cast_le]
  refine card_le_card_of_injOn Sigma.snd (by simp +contextual [Set.MapsTo, *]) ?_
  simp +contextual [Set.InjOn]
  aesop

variable {K : Type*} [Semifield K] [CharZero K] [StarRing K]

section lemma1

public
lemma claim_one : 𝔼 x : G, (𝟭_[A, K] ○ 𝟭_[B]) x * (A ∩ (x +ᵥ B)).dens = E[A, B] := by
  simp only [← expect_indicator_one_dconv_indicator_sq, ← indicator_one_dconv_indicator_one_eq_dens,
    sq]

public
lemma claim_two :
    (E[A, B]) ^ 2 / (A.dens * B.dens) ≤
      𝔼 x, (𝟭_[(A : Set G), ℝ] ○ 𝟭_[B]) x * (A ∩ (x +ᵥ B)).dens ^ 2 := by
  let f := fun x ↦ ((𝟭_[(A : Set G), ℝ] ○ 𝟭_[B]) x).sqrt
  have hf : ∀ x, f x ^ 2 = (𝟭_[A, ℝ] ○ 𝟭_[B]) x := by
    intro x
    rw [Real.sq_sqrt]
    exact dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have := expect_mul_sq_le_sq_mul_sq univ f (fun x ↦ f x * (A ∩ (x +ᵥ B)).dens)
  refine div_le_of_le_mul₀ (by positivity) ?_ ?_
  · refine expect_nonneg fun i _ ↦ ?_
    -- FIXME: `Set.indicator_one_nonneg` should be a positivity lemma.
    exact mul_nonneg (dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg _)
      (by positivity)
  simp only [← sq, ← mul_assoc, hf, expect_indicator_one_dconv_indicator_one, mul_pow, claim_one]
    at this
  grind

public
lemma claim_three {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H).dens =
      (∑ ab ∈ H, 𝔼 x, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] (ab.1 - x) * 𝟭_[B] (ab.2 - x)))
        / card G ^ 2 := by
  simp only [dens, Fintype.card_prod, Nat.cast_mul, NNRat.cast_div, NNRat.cast_natCast,
    NNRat.cast_mul, mul_div, Fintype.expect_eq_sum_div_card, ← sum_div]
  field_simp
  simp only [sum_comm (s := H), mul_sum, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  congr! 1 with x
  rw [inter_comm, ← filter_mem_eq_inter, sum_filter]
  congr! 1 with ⟨a, b⟩ hab
  have : a ∈ A ∧ b ∈ A := by simpa using hH hab
  simp [this, Set.indicator_apply, ← neg_vadd_mem_iff, neg_add_eq_sub]
  grind

public
lemma claim_four (ab : G × G) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] (ab.1 - x) * 𝟭_[B] (ab.2 - x)) ≤
      B.dens * (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) := by
  obtain ⟨a, b⟩ := ab
  have (x : G) : (𝟭_[A, ℝ] ○ 𝟭_[B]) x ≤ B.dens := by
    simp only [dconv_eq_expect_add, Set.conj_indicator_one_apply, dens,
      Fintype.expect_eq_sum_div_card, NNRat.cast_div, NNRat.cast_natCast]
    gcongr
    simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    simp only [Set.indicator_apply, mul_boole, SetLike.mem_coe,
      ← sum_filter (· ∈ B), filter_mem_eq_inter, univ_inter]
    gcongr with i
    grind
  have : 𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] ((a, b).1 - x) * 𝟭_[B] ((a, b).2 - x)) ≤
    B.dens * 𝔼 x : G, (𝟭_[B] ((a, b).1 - x) * 𝟭_[B] ((a, b).2 - x)) := by
    rw [mul_expect]
    gcongr with s hs
    · exact mul_nonneg Set.indicator_one_apply_nonneg Set.indicator_one_apply_nonneg
    · exact this _
  refine this.trans_eq ?_
  congr 1
  simp only [dconv_eq_expect_add]
  exact Fintype.expect_equiv (Equiv.subLeft b) _ _ <| by simp

public
lemma claim_five {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H).dens ≤
      B.dens * (∑ ab ∈ H, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2)) / card G ^ 2 := by
  rw [claim_three hH, mul_sum]; gcongr; exact claim_four _

/-- Pairs in `A × A` whose difference has bounded convolution weight in `B`. -/
@[expose]
public
noncomputable def choiceH (A B : Finset G) (c : ℝ) : Finset (G × G) :=
  {ab ∈ A ×ˢ A |
    (𝟭_[B, ℝ] ○ 𝟭_[B]) (ab.1 - ab.2) ≤ c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))}

public
lemma choiceH_subset {c : ℝ} : choiceH A B c ⊆ A ×ˢ A := filter_subset ..

public
lemma claim_six (c : ℝ) (hc : 0 ≤ c) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens ≤
      c / 2 * (E[A, B] ^ 2 / (A.dens * B.dens)) := by
  have : ∑ ab ∈ choiceH A B c, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) ≤
      #(choiceH A B c) * (c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2
  replace : (∑ ab ∈ choiceH A B c, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2)) / card G ^ 2 ≤
      (choiceH A B c).dens * (c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))) := by
    grw [this, mul_div_right_comm]; simp [dens, sq]
  have hH : ((choiceH A B c).dens : ℝ) ≤ A.dens ^ 2 := by grw [choiceH_subset]; simp [sq]
  grw [claim_five choiceH_subset, ← mul_div, this, hH]
  field_simp
  rfl

public
lemma claim_seven {c : ℝ} (hc : 0 ≤ c) :
    𝔼 x : G,
      (𝟭_[A, ℝ] ○ 𝟭_[B]) x *
          ((c / 2) * (E[A, B] ^ 2 / (A.dens ^ 2 * B.dens ^ 2)) +
            ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens) ≤
      𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (c * (A ∩ (x +ᵥ B)).dens ^ 2) :=
  calc
    _ = (c / 2 * (E[A, B] ^ 2 / (A.dens * B.dens))) + 𝔼 x : G,
          (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens := by
        simp only [mul_add, expect_add_distrib, expect_indicator_one_dconv_indicator_one,
          ← expect_mul, ← mul_pow]
        field_simp
    _ ≤ _ := by
      grw [claim_six c hc, ← add_mul, add_halves]
      simp only [mul_left_comm _ c, ← mul_expect]
      gcongr
      exact claim_two

public
lemma claim_eight {c : ℝ} (hc : 0 ≤ c) (A B : Finset G) :
    ∃ x : G, ((c / 2) * (E[A, B] ^ 2 / (A.dens ^ 2 * B.dens ^ 2)) +
          ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens) ≤
      c * (A ∩ (x +ᵥ B)).dens ^ 2 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  by_contra!
  refine (claim_seven hc (A := A) (B := B)).not_gt <| expect_lt_expect (fun x _ ↦ ?_) ?_
  · grw [this x]
    exact dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have : 0 < 𝟭_[(A : Set G), ℝ] ○ 𝟭_[B] := by apply dconv_pos <;> simpa
  rw [Pi.lt_def] at this
  obtain ⟨-, i, hi : 0 < _⟩ := this
  exact ⟨i, by simp, mul_lt_mul_of_pos_left (this i) hi⟩

public
lemma lemma_one {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B])
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x : G, ∃ X ⊆ A ∩ (x +ᵥ B), A.dens / (Real.sqrt 2 * K) ≤ X.dens ∧
      (1 - c) * X.dens ^ 2 ≤
      ((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.dens ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)).dens := by
  obtain ⟨x, hx⟩ := claim_eight hc.le A B
  set X := A ∩ (x +ᵥ B)
  refine ⟨x, X, subset_rfl, ?_, ?_⟩
  · have : (2 : ℝ)⁻¹ * (E[A, B] / (A.dens * B.dens)) ^ 2 ≤ X.dens ^ 2 := by
      refine le_of_mul_le_mul_left (hx.trans' ?_) hc
      exact (le_add_of_nonneg_right <| NNRat.cast_nonneg _).trans_eq' (by ring)
    grw [← sq_le_sq₀ (by positivity) (by positivity), ← this, ← hE]
    -- TODO: `field_simp` doesn't know how to handle `Real.sqrt`.
    field_simp
    norm_num
  rw [one_sub_mul, sub_le_comm]
  refine ((le_add_of_nonneg_left (by positivity)).trans hx).trans' ?_
  rw [sq, ← NNRat.cast_mul, ← dens_product, ← cast_dens_sdiff (filter_subset _ _), ← filter_not,
    ← filter_mem_eq_inter]
  gcongr ↑(dens ?_)
  rintro ⟨a, b⟩
  simp +contextual only [not_le, mem_product, mem_inter, and_imp, mem_filter, choiceH, and_self,
    true_and, X]
  rintro _ _ _ _ h
  grw [h, ← hE]
  apply le_of_eq
  field_simp [hA, hB, hK, le_div_iff₀, div_le_iff₀] at hE ⊢

public
lemma lemma_one' {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B])
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x : G, ∃ X ⊆ A ∩ (x +ᵥ B), A.dens / (2 * K) ≤ X.dens ∧
      (1 - c) * X.dens ^ 2 ≤
      ((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.dens ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)).dens := by
  obtain ⟨x, X, hX₁, hX₂, hX₃⟩ := lemma_one hc hK hE hA hB
  refine ⟨x, X, hX₁, hX₂.trans' ?_, hX₃⟩
  gcongr _ / (?_ * _)
  rw [Real.sqrt_le_iff]
  norm_num

end lemma1

section lemma2
variable {H : Finset (G × G)} {X : Finset G}

public
lemma quadruple_bound_other {a b c : G} {K : ℝ} {H : Finset (G × G)}
    (hac : (a, c) ∈ H) (hbc : (b, c) ∈ H)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (A.dens / (2 ^ 4 * K ^ 2)) ^ 2 ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 2 := by
  rw [filter_product (s := B ×ˢ B) (t := B ×ˢ B) (fun z ↦ z.1 - z.2 = a - c)
    (fun z ↦ z.1 - z.2 = b - c), card_product, sq, sq (card G : ℝ), Nat.cast_mul,
      mul_div_mul_comm]
  gcongr ?_ * ?_
  · grw [card_sub_eq, hH _ hac, indicator_one_dconv_indicator_one_eq_addConvolution_div]
  · grw [card_sub_eq, hH _ hbc, indicator_one_dconv_indicator_one_eq_addConvolution_div]

public
lemma quadruple_bound_left {a b : G} {K : ℝ} {H : Finset (G × G)}
    (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    X.dens / 2 * (A.dens / (2 ^ 4 * K ^ 2)) ^ 2 ≤
      #({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 3  :=
  calc
    _ ≤ (∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, ((A.dens / (2 ^ 4 * K ^ 2)) ^ 2 : ℝ))
      / card G := by
      grw [sum_const, quadruple_bound_c ha hb]
      apply le_of_eq
      simp [dens]
      ring
    _ ≤ (∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, #(((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ((a₁, a₂), a₃, a₄) ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 2 : ℝ)
          / card G := by
      gcongr with i hi
      simp only [mem_filter] at hi
      convert quadruple_bound_other hi.2.1 hi.2.2 hH
    _ = _ := by rw [card_sigma, Nat.cast_sum, ← sum_div]; ring

public
lemma quadruple_bound {K : ℝ} {x : G} (hx : x ∈ oneOfPair H X - oneOfPair H X)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4) ≤
      #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
      card G ^ 3 := by
  rw [mem_sub] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  grw [← quadruple_bound_right H X rfl, ← quadruple_bound_left ha hb hH]
  apply le_of_eq
  ring

public
lemma big_quadruple_bound {K : ℝ}
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2))
    (hX : A.dens / (2 * K) ≤ X.dens) :
    (oneOfPair H X - oneOfPair H X).dens * (A.dens ^ 3 / (2 ^ 10 * K ^ 5)) ≤ B.dens ^ 4 :=
  calc
    _ = (oneOfPair H X - oneOfPair H X).dens * ((A.dens ^ 2 * (A.dens / (2 * K)))
      / (2 ^ 9 * K ^ 4)) := by ring
    _ ≤ (oneOfPair H X - oneOfPair H X).dens * ((A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4)) := by
      gcongr
    _ = (∑ _x ∈ oneOfPair H X - oneOfPair H X, (A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4) : ℝ)
      / card G := by simp [dens]; ring
    _ ≤ (∑ x ∈ oneOfPair H X - oneOfPair H X,
          #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
            card G ^ 3 : ℝ)
      / card G := by gcongr (∑ _ ∈ _, ?_) / _ with x hx; exact quadruple_bound hx hH
    _ ≤ 𝔼 x, (#(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
          card G ^ 3 : ℝ) := by grw [Fintype.expect_eq_sum_div_card, ← subset_univ]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, ← sum_div]
      norm_cast
      rw [← card_eq_sum_card_fiberwise (by simp [Set.mapsTo_univ])]
      simp [dens]
      field_simp

public
lemma BSG_aux {K : ℝ} (hK : 0 < K) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ x : G, ∃ A' ⊆ A ∩ (x +ᵥ B), (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain ⟨x, X, hX₁, hX₂, hX₃⟩ := lemma_one' (c := 1 / 8) (by norm_num) hK hAB hA hB
  set H : Finset (G × G) := (X ×ˢ X).filter
    fun ⟨a, b⟩ ↦ A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)
  have : (0 : ℝ) < X.dens := hX₂.trans_lt' (by positivity)
  refine ⟨x, oneOfPair H X, (filter_subset _ _).trans hX₁, ?_, ?_⟩
  · rw [← mul_inv, inv_mul_eq_div]
    refine oneOfPair_bound (filter_subset _ _) (by simpa using this) ?_ hX₂
    convert hX₃ using 2
    · norm_num
    · unfold H
      ring_nf
  have := big_quadruple_bound (H := H) (fun x hx ↦ (mem_filter.1 hx).2) hX₂
  rw [le_div_iff₀ (by positivity)]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
  grind

end lemma2

/-- The **Balog-Szemerédi-Gowers theorem** for two sets.

If two sets `A` and `B` have large energy, then there exists a large subset `A'` of `A` of small
difference. -/
public
theorem BSG {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hK := eq_or_lt_of_le hK
  · simp
  · grind [BSG_aux]



/-- The **Balog-Szemerédi-Gowers theorem** for two sets.

If a set `A` has large energy, then there exists a large subset `A'` of `A` of small difference. -/
public
theorem BSG_self {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.dens ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧ (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * A.dens := by
  convert BSG hK hA ?_ using 5 <;> grind

/-- The **Balog-Szemerédi-Gowers theorem** for two sets.

If a set `A` has large energy, then there exists a large subset `A'` of `A` of small difference. -/
public
theorem BSG_self' {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.dens ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧ (A' - A').dens ≤ 2 ^ 14 * K ^ 6 * A'.dens := by
  obtain ⟨A', hA', hAA', hAK'⟩ := BSG_self hK hA hAK
  refine ⟨A', hA', hAA', hAK'.trans ?_⟩
  calc
    _ = 2 ^ 14 * K ^ 6 * ((2 ^ 4)⁻¹ * K⁻¹ * A.dens) := ?_
    _ ≤ _ := by gcongr
  grind
