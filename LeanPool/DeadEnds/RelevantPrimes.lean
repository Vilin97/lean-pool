/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import LeanPool.DeadEnds.PrimeTail

/-!
Bounding the finite set of primes relevant to square-divisibility violations.
-/

namespace LeanPool.DeadEnds

/-- Convert `Nat.primesBelow` to a finset of bundled primes. -/
noncomputable def primesBelow' (n : ℕ) : Finset Nat.Primes :=
  (n.primesBelow).subtype Nat.Prime

/-- The set of primes q with q ≤ √(bX+b) that are not in S.
    Any violation by q ∉ S must have q² ≤ bX+b, so q ≤ √(bX+b) < √(bX+b)+1.
    Either q² | N (so q² ≤ X ≤ bX+b) or q² | bN+d with d < b (so q² ≤ bX + b - 1 < bX+b). -/
noncomputable def relevantNotInS (b X : ℕ) (S : Finset Nat.Primes) : Finset Nat.Primes :=
  (primesBelow' (Nat.sqrt (b * X + b) + 1)).filter (· ∉ S)

lemma primesBelow_succ_card_le (k : ℕ) : (k + 1).primesBelow.card ≤ k := by
  have h₁ : (k + 1).primesBelow.card ≤ k := by
    have h₂ : (k + 1).primesBelow ⊆ Finset.Icc 2 k := by
      intro p hp
      simp only [Finset.mem_Icc,
        Finset.mem_Icc] at hp ⊢
      have h₃ : p < k + 1 := by
        simp_all [Nat.primesBelow]
      have h₄ : Nat.Prime p := by
        simp_all [Nat.primesBelow]
      have h₅ : p ≥ 2 := Nat.Prime.two_le h₄
      have h₆ : p ≤ k := by
        omega
      exact ⟨h₅, h₆⟩
    have h₃ : (k + 1).primesBelow.card ≤ (Finset.Icc 2 k).card := Finset.card_le_card h₂
    have h₄ : (Finset.Icc 2 k).card ≤ k := by
      have h₅ : (Finset.Icc 2 k).card = k + 1 - 2 := by
        simp
      have h₆ : k + 1 - 2 ≤ k := by
        cases k with
        | zero => simp_all
        | succ k' =>
          simp_all [Nat.add_assoc]
      omega
    omega
  exact h₁

lemma primesBelow'_card (n : ℕ) : (primesBelow' n).card = n.primesBelow.card := by
  have h1 : (primesBelow' n).card = ((n.primesBelow).subtype Nat.Prime).card := by rfl
  have h2 : ((n.primesBelow).subtype Nat.Prime).card = (n.primesBelow.filter Nat.Prime).card := by
    rw [Finset.card_subtype]
  have h3 : n.primesBelow.filter Nat.Prime = n.primesBelow := by
    apply Finset.filter_true_of_mem
    intro p hp
    have h₄ : p.Prime := by
      have h₅ : p ∈ n.primesBelow := hp
      have h₆ : p.Prime := by
        have h₇ : p.Prime := by
          simp only [Nat.mem_primesBelow] at h₅
          exact h₅.2
        exact h₇
      exact h₆
    exact h₄
  have h4 : (n.primesBelow.filter Nat.Prime).card = n.primesBelow.card := by
    rw [h3]
  have h5 : (primesBelow' n).card = n.primesBelow.card := by
    calc
      (primesBelow' n).card = ((n.primesBelow).subtype Nat.Prime).card := by rw [h1]
      _ = (n.primesBelow.filter Nat.Prime).card := by rw [h2]
      _ = n.primesBelow.card := by rw [h4]
  apply h5

lemma relevantNotInS_card_le (b X : ℕ) (S : Finset Nat.Primes) :
    (relevantNotInS b X S).card ≤ Nat.sqrt (b * X + b) := by
  calc (relevantNotInS b X S).card
      ≤ (primesBelow' (Nat.sqrt (b * X + b) + 1)).card :=
          Finset.card_filter_le _ _
    _ = (Nat.sqrt (b * X + b) + 1).primesBelow.card := primesBelow'_card _
    _ ≤ Nat.sqrt (b * X + b) := primesBelow_succ_card_le _

lemma not_in_S_implies_gt_y (S : Finset Nat.Primes) (y : ℕ)
    (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (q : Nat.Primes) (hq : q ∉ S) :
    (q : ℕ) > y := by
  have h_main : (q : ℕ) > y := not_le.mp (fun h => hq (hy q h))
  aesop

lemma relevantNotInS_gt_y (b X : ℕ) (S : Finset Nat.Primes) (y : ℕ)
    (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (q : Nat.Primes)
    (hq : q ∈ relevantNotInS b X S) :
    (q : ℕ) > y := by
  have h_main : (q : ℕ) > y := by
    by_contra h
    have h₁ : (q : ℕ) ≤ y := by linarith
    have h₂ : q ∈ S := hy q h₁
    have h₃ : q ∉ S := by
      simp only [relevantNotInS, primesBelow', Finset.mem_filter] at hq
      simp_all
    exact h₃ h₂
  exact h_main

lemma relevantNotInS_gt_b (b X : ℕ) (S : Finset Nat.Primes) (y : ℕ)
    (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b) (q : Nat.Primes)
    (hq : q ∈ relevantNotInS b X S) :
    (q : ℕ) > b := by
  have hq_not_in_S : q ∉ S := by
    simp only [relevantNotInS, Finset.mem_filter] at hq
    have h₁ : q ∉ S := by aesop
    exact h₁
  have h_main : (q : ℕ) > b := by
    by_cases hqy : (q : ℕ) ≤ y
    · have hq_in_S : q ∈ S := hy q hqy
      exact absurd hq_in_S hq_not_in_S
    · have h₂ : (q : ℕ) > b := by omega
      exact h₂
  exact h_main

lemma prime_sq_bound_from_N_dvd (b X N : ℕ) (hb : 2 ≤ b) (q : Nat.Primes)
    (hN : N ∈ Finset.Icc 1 X) (hdvd : (q : ℕ) ^ 2 ∣ N) : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
  have hN' : N ≤ X := (Finset.mem_Icc.mp hN).2
  have hN'' : 1 ≤ N := (Finset.mem_Icc.mp hN).1
  have hq : (q : ℕ) ^ 2 ≤ N := Nat.le_of_dvd (by positivity) hdvd
  have hq'' : (q : ℕ) ^ 2 ≤ b * X + b := by
    have h₂ : X ≤ b * X := by
      nlinarith
    nlinarith
  have hq''' : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
    have h₁ : (q : ℕ) ^ 2 ≤ b * X + b := hq''
    have h₂ : Nat.sqrt (b * X + b) ≥ q := by
      apply Nat.le_sqrt.mpr;
      (try norm_cast at h₁ ⊢);
      nlinarith [Nat.Prime.two_le q.prop]
    have h₃ : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
      omega
    exact h₃
  exact hq'''

theorem prime_sq_bound_from_shifted_dvd (b X N d : ℕ) (hb : 2 ≤ b) (q : Nat.Primes)
    (hN : N ∈ Finset.Icc 1 X) (hd : d ∈ Finset.range b) (hdvd : (q : ℕ) ^ 2 ∣ b * N + d) :
    (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
  have h₁ : (q : ℕ) ^ 2 ∣ b * N + d := hdvd
  have h₂ : 1 ≤ N := by
    simp [Finset.mem_Icc] at hN
    linarith
  have h₃ : N ≤ X := by
    simp [Finset.mem_Icc] at hN
    linarith
  have h₄ : d < b := by
    simp [Finset.mem_range] at hd
    linarith
  have h₅ : b * N + d < b * X + b := by
    have h₅₁ : b * N ≤ b * X := by
      nlinarith
    nlinarith
  have h₆ : (q : ℕ) ^ 2 ≤ b * N + d := Nat.le_of_dvd (by
    have h₆₁ : 0 < b * N + d := by
      nlinarith
    linarith) h₁
  have h₉ : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
    have h₉₂ : (q : ℕ) ≤ Nat.sqrt (b * X + b) := by
      apply Nat.le_sqrt.mpr; nlinarith
    have h₉₃ : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
      omega
    exact h₉₃
  exact h₉

lemma violation_subset_biUnion (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (Finset.Icc 1 X).filter (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (
        q : ℕ) ^ 2 ∣ b * N + d))
    ⊆ (relevantNotInS b X S).biUnion
        (fun q => (Finset.Icc 1 X).filter (fun N => (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
            d)) := by
  intro N hN
  simp only [Finset.mem_filter, Finset.mem_biUnion] at hN ⊢
  obtain ⟨hN_Icc, q₀, hq₀_not_S, hq₀_dvd⟩ := hN
  refine ⟨q₀, ?_, hN_Icc, hq₀_dvd⟩
  simp only [relevantNotInS, Finset.mem_filter]
  refine ⟨?_, hq₀_not_S⟩
  have hq₀_bound : (q₀ : ℕ) < Nat.sqrt (b * X + b) + 1 :=
    hq₀_dvd.elim
      (fun h => prime_sq_bound_from_N_dvd b X N hb q₀ hN_Icc h)
      (fun ⟨d, hd, hdvd⟩ => prime_sq_bound_from_shifted_dvd b X N d hb q₀ hN_Icc (hT hd) hdvd)
  exact Finset.mem_subtype.mpr (Nat.mem_primesBelow.mpr ⟨hq₀_bound, q₀.prop⟩)

/-- Union bound: card(V) ≤ ∑_{q ∈ relevantNotInS} card(V_q).
    Combines violation_subset_biUnion with Finset.card_le_card and Finset.card_biUnion_le.
    Uses `Finset.card_biUnion_le : (s.biUnion t).card ≤ ∑ a ∈ s, (t a).card`. -/
lemma union_card_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (y : ℕ) (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b) (
        X : ℕ) :
    ((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card
    ≤ ∑ q ∈ relevantNotInS b X S, (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) := by
  calc ((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card
      ≤ ((relevantNotInS b X S).biUnion
          (fun q => (Finset.Icc 1 X).filter (fun N => (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b *
              N + d))).card := by
        apply Finset.card_le_card
        exact violation_subset_biUnion b hb T hT S X
    _ ≤ ∑ q ∈ relevantNotInS b X S,
        ((Finset.Icc 1 X).filter (fun N => (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
            d)).card := by
        apply Finset.card_biUnion_le
    _ ≤ ∑ q ∈ relevantNotInS b X S, (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        apply single_prime_violation_bound b hb T hT q
        exact relevantNotInS_gt_b b X S y hy hyb q hq

/-- The finite sum ∑_{q∈Q} 1/q² over primes in Q is ≤ the tsum ∑'_{p>y} 1/p²
    where all primes q in Q satisfy q > y.
    This uses that Q (as a subset of {primes p > y}) contributes to the infinite sum.
    Since 1/q² ≥ 0 for all primes q, and the sum over primes converges,
    the finite partial sum is bounded by the full tail sum.
    Uses `Summable.sum_le_tsum : ∀ {ι : Type*} {f : ι → ℝ} (s : Finset ι),
      (∀ i ∉ s, 0 ≤ f i) → Summable f → ∑ i ∈ s, f i ≤ ∑' i, f i`. -/
lemma finsum_le_tsum_tail (y : ℕ) (Q : Finset Nat.Primes) (hQ : ∀ q ∈ Q, (q : ℕ) > y) :
    (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2))
    ≤ (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2) := by
  let S := {q : Nat.Primes // (q : ℕ) > y}
  let f : S → ℝ := fun p => 1 / ((((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
  have hf_summable : Summable f := primes_summable_one_div_sq.subtype _
  have hf_nonneg : ∀ p : S, 0 ≤ f p := fun p => by positivity
  let e : Q → S := fun ⟨q, hq⟩ => ⟨q, hQ q hq⟩
  have he_inj : Function.Injective e := fun ⟨q1, hq1⟩ ⟨q2, hq2⟩ h => by
    simp only [e] at h
    exact Subtype.ext (Subtype.mk.injEq _ _ _ _ ▸ h)
  let Q_S : Finset S := Q.attach.map ⟨e, he_inj⟩
  have h_sum_eq : ∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2) = ∑ s ∈ Q_S, f s := by
    rw [Finset.sum_map]
    conv_lhs => rw [← Finset.sum_attach]
    rfl
  rw [h_sum_eq]
  exact hf_summable.sum_le_tsum Q_S (fun _ _ => hf_nonneg _)

lemma sum_expand (c : ℝ) (X : ℕ) (Q : Finset Nat.Primes) :
    (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1)))
    = c * X * (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2)) + c * Q.card := by
  have h₁ : (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1))) = (∑ q ∈ Q, (c * ((X : ℝ) / (
      (q : ℕ) : ℝ) ^ 2)) + ∑ _ ∈ Q, c) := by
    calc
      (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1))) = (∑ q ∈ Q, (c * ((X : ℝ) / (
          (q : ℕ) : ℝ) ^ 2) + c)) := by
        apply Finset.sum_congr rfl
        intro q _
        ring_nf
      _ = (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2)) + ∑ _ ∈ Q, c) := by
        rw [Finset.sum_add_distrib]
  have h₂ : (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2))) = c * X * (∑ q ∈ Q, 1 / (
      ((q : ℕ) : ℝ) ^ 2)) := by
    calc
      (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2))) = c * (∑ q ∈ Q, ((X : ℝ) / (
          (q : ℕ) : ℝ) ^ 2)) := by
        rw [Finset.mul_sum]
      _ = c * (X * ∑ q ∈ Q, (1 / ((q : ℕ) : ℝ) ^ 2)) := by
        have h₃ : (∑ q ∈ Q, ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2)) = X * ∑ q ∈ Q, (1 / ((q : ℕ) : ℝ) ^ 2) :=
            by
          calc
            (∑ q ∈ Q, ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2)) = ∑ q ∈ Q, ((X : ℝ) * (1 / (
                (q : ℕ) : ℝ) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro q _
              field_simp [Nat.cast_ne_zero]
            _ = (X : ℝ) * ∑ q ∈ Q, (1 / ((q : ℕ) : ℝ) ^ 2) := by
              rw [Finset.mul_sum]
        rw [h₃]
      _ = c * X * (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2)) := by
        ring_nf
  have h₃ : (∑ _ ∈ Q, c : ℝ) = c * Q.card := by
    calc
      (∑ _ ∈ Q, c : ℝ) = (Q.card : ℝ) * c := by
        simp [Finset.sum_const]
      _ = c * Q.card := by ring
  have h₄ : (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1))) = c * X * (∑ q ∈ Q, 1 / (
      ((q : ℕ) : ℝ) ^ 2)) + c * Q.card := by
    calc
      (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1))) = (∑ q ∈ Q, (c * ((X : ℝ) / (
          (q : ℕ) : ℝ) ^ 2)) + ∑ _ ∈ Q, c) := by rw [h₁]
      _ = (c * X * (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2)) + ∑ _ ∈ Q, c) := by
        rw [h₂]
      _ = (c * X * (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2)) + c * Q.card) := by
        rw [h₃]
  rw [h₄]

lemma sum_bound_real (T : Finset ℕ) (y : ℕ) (X : ℕ)
    (Q : Finset Nat.Primes) (hQ : ∀ q ∈ Q, (q : ℕ) > y) :
    (∑ q ∈ Q, ((T.card + 1 : ℝ) * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1)))
    ≤ (T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
      + (T.card + 1 : ℝ) * Q.card := by
  rw [sum_expand]
  have h := finsum_le_tsum_tail y Q hQ
  have hc : (0 : ℝ) ≤ (T.card + 1 : ℝ) * X := by positivity
  gcongr

lemma nat_div_floor_le_real_div (X : ℕ) (q : Nat.Primes) :
    ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((q : ℕ) ^ 2 : ℝ) := by
  have h₁ : ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) * ((q : ℕ) ^ 2 : ℝ) ≤ (X : ℝ) := by
    have h₂ : (X / (q : ℕ) ^ 2 : ℕ) * (q : ℕ) ^ 2 ≤ X := by
      have h₃ : (X / (q : ℕ) ^ 2 : ℕ) * (q : ℕ) ^ 2 ≤ X := Nat.div_mul_le_self X ((q : ℕ) ^ 2)
      exact h₃
    norm_cast at h₂ ⊢
  have h₂ : 0 < ((q : ℕ) : ℝ) := by
    norm_cast
    exact Nat.Prime.pos q.property
  have h₄ : ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((q : ℕ) ^ 2 : ℝ) := by
    have h₆ : 0 < ((q : ℕ) ^ 2 : ℝ) := by positivity
    calc
      ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) = (((X / (q : ℕ) ^ 2 : ℕ) : ℝ) * ((q : ℕ) ^ 2 : ℝ)) / (
          (q : ℕ) ^ 2 : ℝ) := by
        field_simp [h₆.ne']
      _ ≤ (X : ℝ) / ((q : ℕ) ^ 2 : ℝ) := by
        gcongr
  exact h₄

lemma nat_sum_le_real_sum (T : Finset ℕ) (X : ℕ) (Q : Finset Nat.Primes) :
    ((∑ q ∈ Q, (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) : ℕ) : ℝ)
    ≤ ∑ q ∈ Q, ((T.card + 1 : ℝ) * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1)) := by
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro q _
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  apply mul_le_mul_of_nonneg_left
  · have h := nat_div_floor_le_real_div X q
    linarith
  · linarith [T.card.cast_nonneg (α := ℝ)]

/-- Violation count is bounded by the prime-square tail term plus a square-root count term. -/
lemma violation_count_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (y : ℕ) (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b) (
        X : ℕ) :
    (((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card : ℝ)
    ≤ (T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
      + (T.card + 1 : ℝ) * Nat.sqrt (b * X + b) := by
  have hU := union_card_bound b hb T hT S y hy hyb X
  have hNR := nat_sum_le_real_sum T X (relevantNotInS b X S)
  have hS := sum_bound_real T y X (relevantNotInS b X S)
              (fun q hq => relevantNotInS_gt_y b X S y hy q hq)
  have hC := relevantNotInS_card_le b X S
  calc (((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card : ℝ)
      ≤ (∑ q ∈ relevantNotInS b X S, (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) : ℕ) := Nat.cast_le.mpr hU
    _ ≤ ∑ q ∈ relevantNotInS b X S, ((T.card + 1 : ℝ) * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1)) := hNR
    _ ≤ (T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
        + (T.card + 1 : ℝ) * (relevantNotInS b X S).card := hS
    _ ≤ (T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
        + (T.card + 1 : ℝ) * Nat.sqrt (b * X + b) := by
        have hpos : (0 : ℝ) ≤ (T.card : ℝ) + 1 := by positivity
        have hle : ((relevantNotInS b X S).card : ℝ) ≤ (Nat.sqrt (b * X + b) : ℝ) :=
            Nat.cast_le.mpr hC
        linarith [mul_le_mul_of_nonneg_left hle hpos]

end LeanPool.DeadEnds
