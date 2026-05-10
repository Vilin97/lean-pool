/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import LeanPool.DeadEnds.CountingBlocks

/-!
Finite-prime counting bounds and comparison with the Euler product density.
-/

namespace LeanPool.DeadEnds

lemma count_upper_bound (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    count ≤ (X / M + 1) * A.card := by
  intro M A count
  show count ≤ (X / M + 1) * A.card
  have hdecomp := count_eq_sum_blocks b T S X
  simp only at hdecomp
  have hcount_eq : count = ∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card +
      ((partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card := hdecomp
  rw [hcount_eq]
  have hblock : ∀ k, ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = A.card :=
    fun k => completeBlock_valid_count b T S k
  have hsum : ∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = (X / M) * A.card :=
          by
    simp only [hblock]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hsum]
  have hpartial : ((partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card ≤ A.card :=
    partialBlock_valid_count_le b T S X
  calc X / M * A.card + ((partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
      ≤ X / M * A.card + A.card := Nat.add_le_add_left hpartial _
    _ = (X / M + 1) * A.card := by ring

lemma count_bounds (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (X / M) * A.card ≤ count ∧ count ≤ (X / M + 1) * A.card := by
  constructor
  · exact count_lower_bound b T S X
  · exact count_upper_bound b T S X

/-- Helper: localDensityProduct is non-negative (product of non-negative factors). -/
lemma localDensityProduct_nonneg (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    0 ≤ localDensityProduct b T S := by
  rw [localDensityProduct]
  exact Finset.prod_nonneg fun p _ => localDensityFactor_nonneg _ b T

lemma interval_bound {a b lo hi d : ℝ}
    (ha_lo : lo ≤ a) (ha_hi : a ≤ hi) (hb_lo : lo ≤ b) (hb_hi : b ≤ hi)
    (hd : hi - lo ≤ d) : |a - b| ≤ d := by
  have h₃ : |a - b| ≤ hi - lo := by
    rw [abs_le]
    constructor <;> linarith
  linarith

lemma floor_div_bounds (X M : ℕ) (hM : 0 < M) :
    (X / M) * M ≤ X ∧ X < (X / M + 1) * M := by
  have h_div_add_mod : X = M * (X / M) + (X % M) := (Nat.div_add_mod X M).symm
  have h_mod_lt : X % M < M := Nat.mod_lt X hM
  have h₁ : (X / M) * M ≤ X := Nat.div_mul_le_self X M
  have h₂ : X < (X / M + 1) * M := by nlinarith [h_div_add_mod, h_mod_lt]
  exact ⟨h₁, h₂⟩

/-- Helper: From count_bounds + validResidues_card_eq_mul, get the real-valued bounds. -/
lemma count_real_bounds (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let q := X / M
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (q : ℝ) * M * L ≤ count ∧ (count : ℝ) ≤ (q + 1) * M * L := by
  intro M L q count
  have hbounds := count_bounds b T S X
  simp only at hbounds
  have hA := validResidues_card_eq_mul b hb T hT S
  constructor
  · calc (q : ℝ) * M * L = q * (M * L) := by ring
      _ = q * (validResiduesMod b T S).card := by rw [← hA]
      _ = (q * (validResiduesMod b T S).card : ℕ) := by simp
      _ ≤ count := by exact Nat.cast_le.mpr hbounds.1
  · calc (count : ℝ) ≤ ((q + 1) * (validResiduesMod b T S).card : ℕ) := by
           exact Nat.cast_le.mpr hbounds.2
      _ = (q + 1) * (validResiduesMod b T S).card := by simp
      _ = (q + 1) * (M * L) := by rw [← hA]
      _ = (q + 1) * M * L := by ring

lemma xL_real_bounds (X M : ℕ) (L : ℝ) (hL : 0 ≤ L) (hM : 0 < M) :
    let q := X / M
    (q : ℝ) * M * L ≤ (X : ℝ) * L ∧ (X : ℝ) * L ≤ (q + 1) * M * L := by
  intro q
  have hfloor := floor_div_bounds X M hM
  constructor
  · have hqM : q * M ≤ X := by
      simpa [q] using hfloor.1
    have hqM_real : (q : ℝ) * M ≤ (X : ℝ) := by
      exact_mod_cast hqM
    nlinarith
  · have hXle : X ≤ (q + 1) * M := by
      simpa [q] using Nat.le_of_lt hfloor.2
    have hXle_real : (X : ℝ) ≤ (q + 1 : ℝ) * M := by
      exact_mod_cast hXle
    nlinarith

lemma final_error_bound {count X M : ℕ} {L : ℝ} {q : ℕ}
    (hcount_lo : (q : ℝ) * M * L ≤ count)
    (hcount_hi : (count : ℝ) ≤ (q + 1) * M * L)
    (hxL_lo : (q : ℝ) * M * L ≤ (X : ℝ) * L)
    (hxL_hi : (X : ℝ) * L ≤ (q + 1) * M * L)
    (_hL_nonneg : 0 ≤ L)
    (hL_le_one : L ≤ 1) :
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := by
  have h_upper : (count : ℝ) - (X : ℝ) * L ≤ (M : ℝ) := by nlinarith
  have h_lower : (-(M : ℝ)) ≤ (count : ℝ) - (X : ℝ) * L := by nlinarith
  have h_main : |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := abs_le.mpr ⟨h_lower, h_upper⟩
  exact h_main

lemma error_bound_empty_case (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) (hM : primeSquareProduct S = 0) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := by
  exact (Nat.ne_of_gt (primeSquareProduct_pos S) hM).elim

/-- Finite-prime counts differ from the expected local-density main term by at most the modulus. -/
lemma error_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := by
  intro M L count
  have hcount := count_real_bounds b hb T hT S X
  have hL_nonneg := localDensityProduct_nonneg b T S
  have hL_le_one := localDensityProduct_le_one b T S
  by_cases hM : M = 0
  · exact error_bound_empty_case b hb T hT S X hM
  · have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have hxL := xL_real_bounds X M L hL_nonneg hM_pos
    exact final_error_bound hcount.1 hcount.2 hxL.1 hxL.2 hL_nonneg hL_le_one

lemma count_finite_prime_approx (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    |(((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card : ℝ) -
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T| ≤
      (∏ p ∈ S, (p : ℕ) ^ 2 : ℝ) := by
  have h := error_bound b hb T hT S X
  simp only [primeSquareProduct, localDensityProduct] at h
  convert h using 2
  simp only [Nat.cast_prod, Nat.cast_pow]

lemma hasProd_implies_finite_approx (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Finset Nat.Primes, ∀ S : Finset Nat.Primes, A ⊆ S →
      |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε := by
  have h_multi := jointSquarefreeDensity_multipliable b hb T hT
  have h_hasProd := Multipliable.hasProd h_multi
  rw [HasProd.eq_1] at h_hasProd
  simp only [SummationFilter.unconditional_filter] at h_hasProd
  rw [Metric.tendsto_nhds] at h_hasProd
  specialize h_hasProd ε hε
  rw [Filter.eventually_atTop] at h_hasProd
  obtain ⟨A, hA⟩ := h_hasProd
  use A
  intro S hAS
  specialize hA S hAS
  rwa [Real.dist_eq] at hA

/-- For any ε > 0, the tail contribution from primes p > y to the joint density
    (measuring how much the finite product differs from the infinite product)
    can be made arbitrarily small by choosing y large enough.
    Uses jointSquarefreeDensity_multipliable to ensure convergence. -/
lemma finite_product_converges_to_density (b : ℕ) (hb : 2 ≤ b)
    (T : Finset ℕ) (hT : T ⊆ Finset.range b) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, ∀ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) →
      |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε := by
  obtain ⟨A, hA⟩ := hasProd_implies_finite_approx b hb T hT ε hε
  use A.image (fun p : Nat.Primes => (p : ℕ)) |>.sup id
  intro S hS
  apply hA S
  intro p hp
  apply hS p
  calc (p : ℕ) = id (p : ℕ) := rfl
    _ ≤ (A.image (fun q : Nat.Primes => (q : ℕ))).sup id :=
        Finset.le_sup (Finset.mem_image_of_mem _ hp)

/-- Upper bound: For any S, C(X) ≤ #{N ≤ X : N satisfies S-conditions} since C(X)
    imposes more constraints. Combined with count_finite_prime_approx, this gives
    limsup C(X)/X ≤ D(b,T). -/
lemma count_upper_bound_via_finite (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (countJointSquarefree b T X : ℝ) ≤
      ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card := by
  rw [Nat.cast_le]
  apply Finset.card_le_card
  intro N hN
  simp only [Finset.mem_filter] at hN ⊢
  refine ⟨hN.1, ?_⟩
  intro p _
  obtain ⟨hSqN, hSqAll⟩ := hN.2
  constructor
  · rw [Nat.squarefree_iff_prime_squarefree] at hSqN
    rw [sq]
    exact hSqN p p.prop
  · intro d hd
    have hSqd := hSqAll d hd
    rw [Nat.squarefree_iff_prime_squarefree] at hSqd
    rw [sq]
    exact hSqd p p.prop

/-- The number of `N ∈ [1, X]` such that for every `p ∈ S` we have `p² ∤ N` and `p² ∤ b * N + d`
for all `d ∈ T` (i.e. the square-free conditions checked only at the primes in `S`). -/
noncomputable def countFinitePrime (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun N =>
    ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card

/-- The primes `p ≤ n`, packaged as a `Finset Nat.Primes`. -/
def primesUpTo (n : ℕ) : Finset Nat.Primes :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).subtype Nat.Prime |>.image (fun ⟨p, hp⟩ => ⟨p,
      hp⟩)

lemma mem_primesUpTo (n : ℕ) (p : Nat.Primes) :
    (p : ℕ) ≤ n → p ∈ primesUpTo n := by
  intro hpn
  have h1 : (p : ℕ) ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) := by
    have h₁ : (p : ℕ) < n + 1 := by omega
    have h₂ : (p : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr h₁
    have h₃ : Nat.Prime (p : ℕ) := p.prop
    exact Finset.mem_filter.mpr ⟨h₂, h₃⟩
  have h2 : (⟨(p : ℕ), p.prop⟩ : { q : ℕ // Nat.Prime q }) ∈ (Finset.filter Nat.Prime (
      Finset.range (n + 1))).subtype Nat.Prime := by
    simp only [Finset.mem_subtype] at h1 ⊢
    exact h1
  have h5 : p ∈ ((Finset.filter Nat.Prime (Finset.range (n + 1))).subtype Nat.Prime).image (fun ⟨q,
      hq⟩ => ⟨q, hq⟩) := by
    apply Finset.mem_image.mpr
    refine ⟨⟨(p : ℕ), p.prop⟩, h2, ?_⟩
    simp
  simpa [primesUpTo] using h5

lemma crt_error_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    |(countFinitePrime b T S X : ℝ) - (X : ℝ) * localDensityProduct b T S| ≤
      (primeSquareProduct S : ℝ) := by
  let M := primeSquareProduct S
  let L := localDensityProduct b T S
  let q := X / M
  let count := countFinitePrime b T S X
  have hM_pos : 0 < M := primeSquareProduct_pos S
  have hL_nonneg : 0 ≤ L := localDensityProduct_nonneg b T S
  have hL_le_one : L ≤ 1 := localDensityProduct_le_one b T S
  have h_count_bounds := count_real_bounds b hb T hT S X
  have h_xL_bounds := xL_real_bounds X M L hL_nonneg hM_pos
  exact final_error_bound h_count_bounds.1 h_count_bounds.2 h_xL_bounds.1 h_xL_bounds.2
    hL_nonneg hL_le_one

lemma count_finite_lower (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (countFinitePrime b T S X : ℝ) ≥ (X : ℝ) * localDensityProduct b T S -
      (primeSquareProduct S : ℝ) := by
  have h := crt_error_bound b hb T hT S X
  have h' := neg_abs_le ((countFinitePrime b T S X : ℝ) - (X : ℝ) * localDensityProduct b T S)
  linarith

lemma finite_product_ge_density (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) :
    localDensityProduct b T S ≥ jointSquarefreeDensity b T := by
  let f := fun p : Nat.Primes => localDensityFactor (p : ℕ) b T
  have hmult := jointSquarefreeDensity_multipliable b hb T hT
  have hmult_S : Multipliable (f ∘ Subtype.val (p := (· ∈ S))) := Finset.multipliable S f
  have hmult_compl : Multipliable (f ∘ Subtype.val (p := (· ∉ S))) :=
    multipliable_compl_of_multipliable b hb T hT S
  have hfactor : (∏' (x : {p : Nat.Primes // p ∈ S}), f x) *
                 (∏' (x : {p : Nat.Primes // p ∉ S}), f x) =
                 (∏' (p : Nat.Primes), f p) :=
    Multipliable.tprod_mul_tprod_compl hmult_S hmult_compl
  have hcompl_le : (∏' (x : {p : Nat.Primes // p ∉ S}), f x) ≤ 1 :=
    tprod_compl_le_one b hb T hT S
  have hS_eq : (∏' (x : {p : Nat.Primes // p ∈ S}), f x) = ∏ p ∈ S, f p :=
    Finset.tprod_subtype S f
  have hS_nonneg : 0 ≤ (∏' (x : {p : Nat.Primes // p ∈ S}), f x) := by
    rw [hS_eq]
    apply Finset.prod_nonneg
    intro p _
    exact localDensityFactor_nonneg p b T
  unfold localDensityProduct jointSquarefreeDensity
  rw [ge_iff_le, ← hfactor, ← hS_eq]
  have h1 : (∏' (x : {p // p ∈ S}), f ↑x) * (∏' (x : {p // p ∉ S}), f ↑x)
          ≤ (∏' (x : {p // p ∈ S}), f ↑x) * 1 := by
    apply mul_le_mul_of_nonneg_left hcompl_le hS_nonneg
  simp only [mul_one] at h1
  exact h1

lemma jointSquarefree_subset_finitePrime (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) ⊆
    (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N +
        d)) := by
  intro N hN
  simp only [Finset.mem_filter] at hN ⊢
  refine ⟨hN.1, ?_⟩
  intro p _
  obtain ⟨hSqN, hSqAll⟩ := hN.2
  constructor
  · rw [Nat.squarefree_iff_prime_squarefree] at hSqN
    rw [sq]
    exact hSqN p p.prop
  · intro d hd
    have hSqd := hSqAll d hd
    rw [Nat.squarefree_iff_prime_squarefree] at hSqd
    rw [sq]
    exact hSqd p p.prop

lemma not_squarefree_has_prime_sq_divisor (n : ℕ) (h : ¬Squarefree n) :
    ∃ p : Nat.Primes, (p : ℕ) ^ 2 ∣ n := by
  have h₁ : ¬ (∀ (x : ℕ), Nat.Prime x → ¬x * x ∣ n) := by
    intro h₂
    have h₃ : Squarefree n := by
      rw [Nat.squarefree_iff_prime_squarefree]
      exact h₂
    contradiction
  have h₂ : ∃ (x : ℕ), Nat.Prime x ∧ x * x ∣ n := by
    by_contra! h₃
    have h₄ : ∀ (x : ℕ), Nat.Prime x → ¬x * x ∣ n := fun x hx => h₃ x hx
    exact h₁ h₄
  obtain ⟨p, hp, hp'⟩ := h₂
  refine ⟨⟨p, hp⟩, ?_⟩
  simpa [pow_two] using hp'

lemma sdiff_subset_violations (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N +
        d)) \
    (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) ⊆
    (Finset.Icc 1 X).filter (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (
        q : ℕ) ^ 2 ∣ b * N + d)) := by
  intro N hN
  rw [Finset.mem_sdiff] at hN
  rw [Finset.mem_filter] at hN ⊢
  obtain ⟨⟨hNIcc, hNS⟩, hNotG⟩ := hN
  refine ⟨hNIcc, ?_⟩
  simp only [Finset.mem_filter, not_and] at hNotG
  specialize hNotG hNIcc
  by_cases hSqN : Squarefree N
  · have hNotAll := hNotG hSqN
    push Not at hNotAll
    obtain ⟨d, hd_mem, hd_not_sq⟩ := hNotAll
    obtain ⟨q, hq_dvd⟩ := not_squarefree_has_prime_sq_divisor (b * N + d) hd_not_sq
    refine ⟨q, ?_, Or.inr ⟨d, hd_mem, hq_dvd⟩⟩
    intro hqS
    have := (hNS q hqS).2 d hd_mem
    exact this hq_dvd
  · obtain ⟨q, hq_dvd⟩ := not_squarefree_has_prime_sq_divisor N hSqN
    refine ⟨q, ?_, Or.inl hq_dvd⟩
    intro hqS
    have := (hNS q hqS).1
    exact this hq_dvd

lemma count_ge_finite_minus_violations (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ)
    (_hT : T ⊆ Finset.range b) (S : Finset Nat.Primes) (X : ℕ) :
    (countJointSquarefree b T X : ℝ) ≥ (countFinitePrime b T S X : ℝ) -
      ((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card := by
  let A := (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d))
  let B := (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣
      b * N + d))
  let V := (Finset.Icc 1 X).filter (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (
      q : ℕ) ^ 2 ∣ b * N + d))
  change (A.card : ℝ) ≥ (B.card : ℝ) - (V.card : ℝ)
  have hAB : A ⊆ B := jointSquarefree_subset_finitePrime b T S X
  have hDiff : B \ A ⊆ V := sdiff_subset_violations b T S X
  have hCard : (B \ A).card + A.card = B.card := Finset.card_sdiff_add_card_eq_card hAB
  have hDiffCard : (B \ A).card ≤ V.card := Finset.card_le_card hDiff
  have h2 : (A.card : ℤ) ≥ B.card - V.card := by omega
  have h3 : (A.card : ℝ) ≥ (B.card : ℤ) - (V.card : ℤ) := by exact_mod_cast h2
  simp only [Int.cast_natCast] at h3
  exact h3

lemma combine_bounds_lower (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) (hX : 0 < X)
    (δ₁ δ₂ : ℝ)
    (hδ₁ : (((Finset.Icc 1 X).filter fun N =>
          ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
              d)).card : ℝ) / X < δ₁)
    (hδ₂ : (primeSquareProduct S : ℝ) / X < δ₂) :
    (countJointSquarefree b T X : ℝ) / X ≥ jointSquarefreeDensity b T - δ₁ - δ₂ := by
  have h1 := count_ge_finite_minus_violations b hb T hT S X
  have h2 := count_finite_lower b hb T hT S X
  have h3 := finite_product_ge_density b hb T hT S
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  set V := ((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card with hV
  set M := primeSquareProduct S with hM
  set L := localDensityProduct b T S with hL
  set D := jointSquarefreeDensity b T with hD
  set C := countJointSquarefree b T X with hC
  set Cs := countFinitePrime b T S X with hCs
  have hCbound : (C : ℝ) ≥ (X : ℝ) * L - (M : ℝ) - (V : ℝ) := by linarith
  have hCdiv : (C : ℝ) / (X : ℝ) ≥ L - (M : ℝ) / (X : ℝ) - (V : ℝ) / (X : ℝ) := by
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    rw [ge_iff_le, sub_sub, ← add_div, le_div_iff₀ hXpos]
    have heq : (L - ((M : ℝ) + (V : ℝ)) / (X : ℝ)) * (X : ℝ) = L * (X : ℝ) - (M : ℝ) - (V : ℝ) := by
      field_simp
      ring
    rw [heq]
    linarith
  have hCdiv' : (C : ℝ) / (X : ℝ) ≥ D - (M : ℝ) / (X : ℝ) - (V : ℝ) / (X : ℝ) := by linarith
  linarith

end LeanPool.DeadEnds
