/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Weighted finite collections and certificate mass decomposition

This file defines the weighted collection framework and the positive/negative
mass decomposition of a dual certificate, as needed
for the low-frequency construction (Lemma 2.3) and the intersection/
recombination pipeline (Sections 3–5).

**Reference**: Lemma 2.3 and Section 5 of the companion paper.
-/
import LeanPool.KaltonRoberts.Defs

/-!
# Weighted finite collections and certificate mass decomposition

Weighted collections and the positive/negative mass decomposition of a dual
certificate for the low-frequency construction and recombination pipeline.
-/

namespace KaltonRoberts

open Finset BigOperators

universe v

variable {U : Type*} [DecidableEq U] [Fintype U]

/-! ## Weighted finite collections -/

/-- A weighted finite collection of subsets of `U`.
The weights are nonneg reals with positive total weight, so the collection
represents a (possibly unnormalized) distribution over finsets.

This avoids the need for literal multisets (which would require rational
certificates and denominator clearing). -/
structure WeightedCollection (U : Type v) [DecidableEq U] where
  /-- Finite index type. -/
  J : Type v
  /-- Fintype instance for J. -/
  [finJ : Fintype J]
  /-- DecidableEq instance for J. -/
  [decJ : DecidableEq J]
  /-- The indexed family of sets. -/
  sets : J → Finset U
  /-- Weight of each index. -/
  weight : J → ℝ
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ j, 0 ≤ weight j
  /-- Weights sum to a positive value (total mass). -/
  total_pos : 0 < ∑ j : J, weight j

attribute [instance] WeightedCollection.finJ WeightedCollection.decJ

/-- Total weight of a weighted collection. -/
noncomputable def WeightedCollection.totalWeight (C : WeightedCollection U) : ℝ :=
  ∑ j : C.J, C.weight j

omit [Fintype U] in
lemma WeightedCollection.totalWeight_pos (C : WeightedCollection U) :
    0 < C.totalWeight := C.total_pos

/-- Item frequency: the weighted fraction of sets containing item `i`. -/
noncomputable def WeightedCollection.itemFreq (C : WeightedCollection U) (i : U) : ℝ :=
  (∑ j : C.J, C.weight j * if i ∈ C.sets j then 1 else 0) / C.totalWeight

/-- Weighted average deficit. -/
noncomputable def WeightedCollection.avgDeficit
    (C : WeightedCollection U) (f : Finset U → ℝ) (M : ℝ) : ℝ :=
  (∑ j : C.J, C.weight j * deficit f M (C.sets j)) / C.totalWeight

/-- Weighted average surplus. -/
noncomputable def WeightedCollection.avgSurplus
    (C : WeightedCollection U) (f : Finset U → ℝ) (M : ℝ) : ℝ :=
  (∑ j : C.J, C.weight j * surplus f M (C.sets j)) / C.totalWeight

omit [Fintype U] in
/-- Item frequency is nonneg. -/
lemma WeightedCollection.itemFreq_nonneg (C : WeightedCollection U) (i : U) :
    0 ≤ C.itemFreq i := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (C.weight_nonneg j) (by split_ifs <;> norm_num)
  · exact le_of_lt C.total_pos

omit [Fintype U] in
/-- Item frequency is at most 1. -/
lemma WeightedCollection.itemFreq_le_one (C : WeightedCollection U) (i : U) :
    C.itemFreq i ≤ 1 := by
  unfold itemFreq totalWeight
  rw [div_le_one C.total_pos]
  apply Finset.sum_le_sum; intro j _
  by_cases h : i ∈ C.sets j <;> simp [h, C.weight_nonneg j]

/-! ## Certificate mass decomposition -/

/-- Positive mass of a dual certificate: `p = ∑_S max(λ(S), 0)`. -/
noncomputable def DualCertificate.posMass
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) : ℝ :=
  ∑ S : Finset U, max (cert.lam S) 0

/-- Negative mass of a dual certificate: `q = ∑_S max(−λ(S), 0)`. -/
noncomputable def DualCertificate.negMass
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) : ℝ :=
  ∑ S : Finset U, max (-cert.lam S) 0

/-- Positive mass is nonneg. -/
lemma DualCertificate.posMass_nonneg
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    0 ≤ cert.posMass :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- Negative mass is nonneg. -/
lemma DualCertificate.negMass_nonneg
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    0 ≤ cert.negMass :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- `|x| = max(x, 0) + max(-x, 0)` -/
private lemma abs_eq_max_add (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
  rcases le_or_gt x 0 with h | h
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [abs_of_pos h, max_eq_left h.le, max_eq_right (by linarith)]; ring

/-
Positive mass plus negative mass equals 1.
-/
lemma DualCertificate.posMass_add_negMass
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    cert.posMass + cert.negMass = 1 := by
  have h_sum : ∑ S : Finset U, |cert.lam S| = 1 := by
    exact cert.norm_one;
  rw [ ← h_sum, DualCertificate.posMass, DualCertificate.negMass, ← Finset.sum_add_distrib ];
  exact Finset.sum_congr rfl fun _ _ => by rw [ max_def, max_def ]; split_ifs <;> cases abs_cases (
    cert.lam _ ) <;> linarith;

/-- p ≤ 1 -/
lemma DualCertificate.posMass_le_one
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    cert.posMass ≤ 1 := by
  linarith [cert.posMass_add_negMass, cert.negMass_nonneg]

/-- q ≤ 1 -/
lemma DualCertificate.negMass_le_one
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    cert.negMass ≤ 1 := by
  linarith [cert.posMass_add_negMass, cert.posMass_nonneg]

/-- Positive mass is positive when there is a positively-weighted set. -/
lemma DualCertificate.posMass_pos
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (h : ∃ S : Finset U, 0 < cert.lam S) :
    0 < cert.posMass := by
  obtain ⟨S, hS⟩ := h
  exact lt_of_lt_of_le hS (le_trans (le_max_left _ _)
    (Finset.single_le_sum (fun T _ => le_max_right _ _) (Finset.mem_univ S)))

/-- Negative mass is positive when there is a negatively-weighted set. -/
lemma DualCertificate.negMass_pos
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (h : ∃ S : Finset U, cert.lam S < 0) :
    0 < cert.negMass := by
  obtain ⟨S, hS⟩ := h
  have h1 : 0 < -cert.lam S := by linarith
  have h2 : -cert.lam S ≤ max (-cert.lam S) 0 := le_max_left _ _
  have h3 : max (-cert.lam S) 0 ≤ cert.negMass :=
    Finset.single_le_sum (f := fun T => max (-cert.lam T) 0)
      (fun T _ => le_max_right _ _) (Finset.mem_univ S)
  linarith

/-! ## Zero-marginal frequency identity -/

/-
The zero-marginal property implies that for each item `i`,
the positive and negative contributions from sets containing `i` are equal.
-/
lemma DualCertificate.marginal_pos_eq_neg
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (i : U) :
    (Finset.univ.filter (fun S => i ∈ S)).sum (fun S => max (cert.lam S) 0) =
    (Finset.univ.filter (fun S => i ∈ S)).sum (fun S => max (-cert.lam S) 0) := by
  have h1 : ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), (cert.lam S) = 0 := by
    convert cert.zero_marginals i using 1;
  have h2 : ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), max (cert.lam S) 0 - ∑ S ∈ Finset.univ.filter
    (fun S => i ∈ S), max (-cert.lam S) 0 = ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), cert.lam S :=
      by
    simpa only [← Finset.sum_sub_distrib] using
      Finset.sum_congr rfl fun x hx => by
        cases max_cases (cert.lam x) 0 <;>
          cases max_cases (-cert.lam x) 0 <;>
          linarith
  linarith

/-- Item frequency bound: for each item `i`, the sum of positive weights
over sets containing `i` is at most the negative mass `q`. -/
lemma DualCertificate.pos_item_sum_le_negMass
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (i : U) :
    (Finset.univ.filter (fun S => i ∈ S)).sum (fun S => max (cert.lam S) 0)
      ≤ cert.negMass := by
  rw [cert.marginal_pos_eq_neg i]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun S _ _ => le_max_right _ _)

/-- Symmetric bound: for each item `i`, the sum of negative weights
over sets containing `i` is at most the positive mass `p`. -/
lemma DualCertificate.neg_item_sum_le_posMass
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (i : U) :
    (Finset.univ.filter (fun S => i ∈ S)).sum (fun S => max (-cert.lam S) 0)
      ≤ cert.posMass := by
  rw [← cert.marginal_pos_eq_neg i]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun S _ _ => le_max_right _ _)

/-! ## Positive and negative weighted collections from a certificate -/

/-- The positive weighted collection from a dual certificate. -/
noncomputable def DualCertificate.posCollection
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hp : 0 < cert.posMass) :
    WeightedCollection U where
  J := Finset U
  sets := id
  weight := fun S => max (cert.lam S) 0
  weight_nonneg := fun _ => le_max_right _ _
  total_pos := hp

/-- The negative weighted collection from a dual certificate. -/
noncomputable def DualCertificate.negCollection
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hq : 0 < cert.negMass) :
    WeightedCollection U where
  J := Finset U
  sets := id
  weight := fun S => max (-cert.lam S) 0
  weight_nonneg := fun _ => le_max_right _ _
  total_pos := hq

/-- The total weight of the positive collection is `p`. -/
lemma DualCertificate.posCollection_totalWeight
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hp : 0 < cert.posMass) :
    (cert.posCollection hp).totalWeight = cert.posMass := rfl

/-- The total weight of the negative collection is `q`. -/
lemma DualCertificate.negCollection_totalWeight
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hq : 0 < cert.negMass) :
    (cert.negCollection hq).totalWeight = cert.negMass := rfl

/-! ## Frequency and deficit bounds for certificate collections -/

/-
Item frequency in the positive collection is at most `q / p`.
-/
lemma DualCertificate.posCollection_itemFreq_le
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hp : 0 < cert.posMass) (i : U) :
    (cert.posCollection hp).itemFreq i ≤ cert.negMass / cert.posMass := by
  rw [WeightedCollection.itemFreq, DualCertificate.posCollection_totalWeight]
  exact div_le_div_of_nonneg_right (by
    rw [show (∑ j, (cert.posCollection hp).weight j *
            if i ∈ (cert.posCollection hp).sets j then 1 else 0) =
          (∑ S : Finset U, if i ∈ S then max (cert.lam S) 0 else 0) by
        simp [DualCertificate.posCollection, mul_ite]
        rfl]
    simpa [Finset.sum_filter] using cert.pos_item_sum_le_negMass i) hp.le

/-
Average deficit of the positive collection is 0.
-/
lemma DualCertificate.posCollection_avgDeficit_eq_zero
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hp : 0 < cert.posMass) :
    (cert.posCollection hp).avgDeficit f M = 0 := by
  -- For each set S, if cert.lam S is positive, then f S = M by cert.pos_support. Therefore, M - f S
  -- = 0.
  have h_deficit_zero : ∀ S : Finset U, max (cert.lam S) 0 * (M - f S) = 0 := by
    intro S
    by_cases h : 0 < cert.lam S
    · simp_all +decide only [mul_eq_zero, sup_eq_right, sub_eq_zero]
      exact Or.inr (Eq.symm (cert.pos_support S h))
    · simp_all +decide only [not_lt, sup_of_le_right, zero_mul]
  exact div_eq_zero_iff.mpr ( Or.inl <| Finset.sum_eq_zero fun S _ => h_deficit_zero S )

/-
Average surplus of the negative collection is 0.
-/
lemma DualCertificate.negCollection_avgSurplus_eq_zero
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hq : 0 < cert.negMass) :
    (cert.negCollection hq).avgSurplus f M = 0 := by
  -- By definition of `negCollection`, we know that its weights are non-negative and sum to
  -- `cert.negMass`.
  have h_negCollection_weights : ∀ S : Finset U, (cert.negCollection hq).weight S * (M + f S) = 0 :=
    by
    intro S
    by_cases hS : cert.lam S < 0;
    · have := cert.neg_support S hS; aesop;
    · simp only [DualCertificate.negCollection]
      rw [max_eq_right]
      · ring
      · linarith [le_of_not_gt hS]
  exact div_eq_zero_iff.mpr ( Or.inl <| Finset.sum_eq_zero fun S _ => h_negCollection_weights S )

/-
Item frequency in the negative collection is at most `p / q`.
-/
lemma DualCertificate.negCollection_itemFreq_le
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hq : 0 < cert.negMass) (i : U) :
    (cert.negCollection hq).itemFreq i ≤ cert.posMass / cert.negMass := by
  rw [WeightedCollection.itemFreq, DualCertificate.negCollection_totalWeight]
  exact div_le_div_of_nonneg_right (by
    rw [show (∑ j, (cert.negCollection hq).weight j *
            if i ∈ (cert.negCollection hq).sets j then 1 else 0) =
          (∑ S : Finset U, if i ∈ S then max (-cert.lam S) 0 else 0) by
        simp [DualCertificate.negCollection, mul_ite]
        rfl]
    simpa [Finset.sum_filter] using cert.neg_item_sum_le_posMass i) hq.le

/-! ## Swapping lemma: ensure q ≤ 1/2 -/

/-- By possibly replacing `f` by `−f`, we may arrange `q ≤ 1/2 ≤ p`. -/
lemma DualCertificate.can_swap_to_small_q
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    cert.negMass ≤ 1 / 2 ∨ cert.posMass ≤ 1 / 2 := by
  by_contra h
  push Not at h
  linarith [cert.posMass_add_negMass]

/-! ## Augmented collections (Lemma 2.3 of the paper)

The *augmented positive collection* A consists of:
- Positive active sets P (with weight λ⁺(P))
- Complements Nᶜ of negative active sets N (with weight λ⁻(N))

Total weight = p + q = 1. Every item has frequency exactly q
(by the zero-marginal property). Average deficit ≤ q(1 − u).

Symmetrically for the augmented negative collection B.
-/

private noncomputable def augPosWeight
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    Finset U ⊕ Finset U → ℝ
  | Sum.inl S => max (cert.lam S) 0
  | Sum.inr S => max (-cert.lam S) 0

private def augPosSets : Finset U ⊕ Finset U → Finset U
  | Sum.inl S => S
  | Sum.inr S => Sᶜ

private noncomputable def augNegWeight
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    Finset U ⊕ Finset U → ℝ
  | Sum.inl S => max (-cert.lam S) 0
  | Sum.inr S => max (cert.lam S) 0

private def augNegSets : Finset U ⊕ Finset U → Finset U
  | Sum.inl S => S
  | Sum.inr S => Sᶜ

/-- The augmented positive collection from a dual certificate (Lemma 2.3).
Includes positive active sets and complements of negative active sets. -/
noncomputable def DualCertificate.augPosCollection
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    WeightedCollection U where
  J := Finset U ⊕ Finset U
  sets := augPosSets
  weight := augPosWeight cert
  weight_nonneg j := by cases j <;> simp [augPosWeight]
  total_pos := by
    simp only [Fintype.sum_sum_type, augPosWeight]
    rw [show
      (∑ x : Finset U, max (cert.lam x) 0) +
          ∑ x : Finset U, max (-cert.lam x) 0 =
        cert.posMass + cert.negMass from rfl]
    rw [cert.posMass_add_negMass]; exact one_pos

/-- The augmented negative collection from a dual certificate (Lemma 2.3).
Includes negative active sets and complements of positive active sets. -/
noncomputable def DualCertificate.augNegCollection
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    WeightedCollection U where
  J := Finset U ⊕ Finset U
  sets := augNegSets
  weight := augNegWeight cert
  weight_nonneg j := by cases j <;> simp [augNegWeight]
  total_pos := by
    simp only [Fintype.sum_sum_type, augNegWeight]
    rw [show
      (∑ x : Finset U, max (-cert.lam x) 0) +
          ∑ x : Finset U, max (cert.lam x) 0 =
        cert.negMass + cert.posMass from rfl]
    rw [add_comm, cert.posMass_add_negMass]; exact one_pos

/-- Total weight of the augmented positive collection is 1. -/
lemma DualCertificate.augPosCollection_totalWeight
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    cert.augPosCollection.totalWeight = 1 := by
  unfold WeightedCollection.totalWeight augPosCollection
  simp only [Fintype.sum_sum_type]
  exact cert.posMass_add_negMass

/-- Total weight of the augmented negative collection is 1. -/
lemma DualCertificate.augNegCollection_totalWeight
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    cert.augNegCollection.totalWeight = 1 := by
  unfold WeightedCollection.totalWeight augNegCollection
  simp only [Fintype.sum_sum_type]
  rw [add_comm]
  exact cert.posMass_add_negMass

/-
Item frequency in the augmented positive collection equals q (= negMass)
for every item. This follows from the zero-marginal property.
-/
lemma DualCertificate.augPosCollection_itemFreq
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) (i : U) :
    cert.augPosCollection.itemFreq i = cert.negMass := by
  rw [WeightedCollection.itemFreq, DualCertificate.augPosCollection_totalWeight, div_one]
  change
    (∑ j : Finset U ⊕ Finset U,
        augPosWeight cert j * if i ∈ augPosSets j then 1 else 0) = cert.negMass
  rw [Fintype.sum_sum_type]
  simp only [augPosSets, augPosWeight, Finset.mem_compl, mul_ite, mul_one, mul_zero]
  have h_marg :
      (∑ S : Finset U, if i ∈ S then max (cert.lam S) 0 else 0) =
        ∑ S : Finset U, if i ∈ S then max (-cert.lam S) 0 else 0 := by
    simpa [Finset.sum_filter] using cert.marginal_pos_eq_neg i
  calc
    (∑ S : Finset U, if i ∈ S then max (cert.lam S) 0 else 0) +
        (∑ S : Finset U, if i ∉ S then max (-cert.lam S) 0 else 0)
        = (∑ S : Finset U, if i ∈ S then max (-cert.lam S) 0 else 0) +
          (∑ S : Finset U, if i ∉ S then max (-cert.lam S) 0 else 0) := by rw [h_marg]
    _ = ∑ S : Finset U, max (-cert.lam S) 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      by_cases h : i ∈ S <;> simp [h]
    _ = cert.negMass := rfl

/-
Item frequency in the augmented negative collection equals p (= posMass)
for every item.
-/
lemma DualCertificate.augNegCollection_itemFreq
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) (i : U) :
    cert.augNegCollection.itemFreq i = cert.posMass := by
  -- By definition of `augNegCollection`, we can split the sum into two parts: one over the negative
  -- sets and one over the complements of the positive sets.
  have h_split : ∑ j : Finset U ⊕ Finset U, (if i ∈ (augNegSets j) then augNegWeight cert j else 0)
    = ∑ S : Finset U, (if i ∈ S then max (-cert.lam S) 0 else 0) + ∑ S : Finset U, (if i ∉ S then
      max (cert.lam S) 0 else 0) := by
    simp [augNegSets, augNegWeight]
  unfold WeightedCollection.itemFreq DualCertificate.posMass
  simp_all +decide only [mul_ite, mul_one, mul_zero]
  convert congr_arg ( fun x : ℝ => x / 1 ) h_split using 1;
  · congr! 1;
    convert DualCertificate.augNegCollection_totalWeight cert;
  · have := cert.marginal_pos_eq_neg i
    simp_all +decide only [ite_not, div_one]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S => i ∈ S) (fun S => max (cert.lam S) 0), this]
    simp +decide only [Finset.sum_ite, Finset.sum_const_zero, add_zero, zero_add]

/-
Average deficit of the augmented positive collection is at most q(1 − u)
where u = f(U). Uses 1-additivity of f.
-/
lemma DualCertificate.augPosCollection_avgDeficit_le
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hf : IsApproxAdditive f 1)
    (_hM : ∀ S : Finset U, |f S| ≤ M) :
    cert.augPosCollection.avgDeficit f M ≤ cert.negMass * (1 - f Finset.univ) := by
  rw [WeightedCollection.avgDeficit, DualCertificate.augPosCollection_totalWeight, div_one]
  rw [show cert.negMass = ∑ S : Finset U, max (-cert.lam S) 0 from rfl]
  -- By definition of $f$, we know that for any $S$, $|f S + f (Finset.univ \ S) - f Finset.univ| ≤
  -- 1$.
  have h_additivity : ∀ S : Finset U, |f S + f (Finset.univ \ S) - f Finset.univ| ≤ 1 := by
    intro S;
    convert hf.2 S ( Finset.univ \ S ) _ using 1;
    · rw [ Finset.union_sdiff_of_subset ( Finset.subset_univ S ) ];
    · exact Finset.disjoint_sdiff;
  -- By definition of $f$, we know that for any $S$, if $cert.lam S > 0`, then `f S = M`, and if
  -- `cert.lam S < 0`, then `f S = -M`.
  have h_cases : ∀ S : Finset U, (0 < cert.lam S → f S = M) ∧ (cert.lam S < 0 → f S = -M) := by
    exact fun S => ⟨ fun h => cert.pos_support S h, fun h => cert.neg_support S h ⟩;
  -- Split the augmented sum into positive active sets and complements of negative active sets.
  have h_split : ∀ S : Finset U, max (cert.lam S) 0 * (M - f S) + max (-cert.lam S) 0 * (M - f
    (Finset.univ \ S)) ≤ max (-cert.lam S) 0 * (1 - f Finset.univ) := by
    intro S
    rcases max_cases (cert.lam S) 0 with hpos | hnonpos
    · rcases max_cases (-cert.lam S) 0 with hneg | hnonneg
      · have hlam : cert.lam S = 0 := by linarith [hpos.2, hneg.2]
        simp only [hpos.1, hneg.1]
        norm_num [hlam]
      · simp only [hpos.1, hnonneg.1, zero_mul, add_zero]
        rw [h_cases S |>.1 (by linarith)]
        nlinarith
    · rcases max_cases (-cert.lam S) 0 with hneg | hnonneg
      · simp only [hnonpos.1, hneg.1, zero_mul, zero_add]
        have hadd := abs_le.mp (h_additivity S)
        rw [h_cases S |>.2 hnonpos.2] at hadd
        nlinarith [hneg.2, hadd.1]
      · linarith [hnonpos.2, hnonneg.2]
  calc
    ∑ j, cert.augPosCollection.weight j * deficit f M (cert.augPosCollection.sets j)
        ≤ ∑ S : Finset U, max (-cert.lam S) 0 * (1 - f Finset.univ) := by
      change
        (∑ j : Finset U ⊕ Finset U, augPosWeight cert j * deficit f M (augPosSets j)) ≤
          ∑ S : Finset U, max (-cert.lam S) 0 * (1 - f Finset.univ)
      rw [Fintype.sum_sum_type]
      simpa [augPosSets, augPosWeight, deficit, Finset.sum_add_distrib,
          Finset.compl_eq_univ_sdiff] using
        Finset.sum_le_sum fun S (_ : S ∈ Finset.univ) => h_split S
    _ = (∑ S : Finset U, max (-cert.lam S) 0) * (1 - f Finset.univ) := by
      rw [Finset.sum_mul]

/-
Average surplus of the augmented negative collection is at most p(1 + u)
where u = f(U). Uses 1-additivity of f.
-/
lemma DualCertificate.augNegCollection_avgSurplus_le
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M)
    (hf : IsApproxAdditive f 1)
    (_hM : ∀ S : Finset U, |f S| ≤ M) :
    cert.augNegCollection.avgSurplus f M ≤ cert.posMass * (1 + f Finset.univ) := by
  have h_sum : (∑ j, cert.augNegCollection.weight j * (M + f (cert.augNegCollection.sets j))) ≤
    cert.posMass * (1 + f Finset.univ) := by
    have h_sum : (∑ S ∈ Finset.univ, max (-cert.lam S) 0 * (M + f S)) + (∑ S ∈ Finset.univ, max
      (cert.lam S) 0 * (M + f Sᶜ)) ≤ cert.posMass * (1 + f Finset.univ) := by
      have h_sum : ∀ S : Finset U, max (cert.lam S) 0 * (M + f Sᶜ) ≤ max (cert.lam S) 0 * (1 + f
        Finset.univ) := by
        intro S
        by_cases hS : cert.lam S > 0;
        · have := hf.2 S Sᶜ; simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
          linarith [ abs_le.mp this, cert.pos_support S hS ];
        · simp +decide [ max_eq_right ( le_of_not_gt hS ) ];
      refine le_trans ( add_le_add ( Finset.sum_nonpos fun S _ => ?_ ) ( Finset.sum_le_sum fun S _
        => h_sum S ) ) ?_
      · by_cases h : cert.lam S < 0 <;> simp_all +decide [ abs_le ];
        have := cert.neg_support S h; aesop;
      · simp +decide [ ← Finset.sum_mul _ _ _, DualCertificate.posMass ];
    convert h_sum using 1;
    unfold DualCertificate.augNegCollection; simp +decide;
    rfl;
  rw [WeightedCollection.avgSurplus, DualCertificate.augNegCollection_totalWeight, div_one]
  exact h_sum

/-! ## Uniform weighted collection from a finite family -/

section UniformOfFamily

universe u
variable {U' : Type u} [DecidableEq U'] [Fintype U']

/-- Build a `WeightedCollection` with uniform weight 1 from a finite family
of subsets indexed by a type `J` with positive cardinality. -/
noncomputable def WeightedCollection.uniformOfFamily
    {J : Type u} [Fintype J] [DecidableEq J]
    (sets : J → Finset U')
    (hJ : 0 < Fintype.card J) : WeightedCollection U' where
  J := J
  sets := sets
  weight := fun _ => 1
  weight_nonneg := fun _ => zero_le_one
  total_pos := by
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_pos]
    exact hJ

omit [Fintype U'] in
/-- Total weight of a uniform collection equals the cardinality. -/
lemma WeightedCollection.uniformOfFamily_totalWeight
    {J : Type u} [Fintype J] [DecidableEq J]
    (sets : J → Finset U') (hJ : 0 < Fintype.card J) :
    (uniformOfFamily sets hJ).totalWeight = Fintype.card J := by
  simp [totalWeight, uniformOfFamily]
  rfl

omit [Fintype U'] in
/-- Item frequency in a uniform collection equals
`card {j | i ∈ sets j} / card J`. -/
lemma WeightedCollection.uniformOfFamily_itemFreq
    {J : Type u} [Fintype J] [DecidableEq J]
    (sets : J → Finset U') (hJ : 0 < Fintype.card J) (i : U') :
    (uniformOfFamily sets hJ).itemFreq i =
      (Finset.univ.filter (fun j => i ∈ sets j)).card / (Fintype.card J : ℝ) := by
  simp [itemFreq, uniformOfFamily, totalWeight]
  rfl

omit [Fintype U'] in
/-- Average deficit of a uniform collection equals
`(∑ j, deficit f M (sets j)) / card J`. -/
lemma WeightedCollection.uniformOfFamily_avgDeficit
    {J : Type u} [Fintype J] [DecidableEq J]
    (sets : J → Finset U') (hJ : 0 < Fintype.card J)
    (f : Finset U' → ℝ) (M : ℝ) :
    (uniformOfFamily sets hJ).avgDeficit f M =
      (∑ j : J, deficit f M (sets j)) / (Fintype.card J : ℝ) := by
  simp [avgDeficit, uniformOfFamily, totalWeight]
  rfl

omit [Fintype U'] in
/-- Average surplus of a uniform collection equals
`(∑ j, surplus f M (sets j)) / card J`. -/
lemma WeightedCollection.uniformOfFamily_avgSurplus
    {J : Type u} [Fintype J] [DecidableEq J]
    (sets : J → Finset U') (hJ : 0 < Fintype.card J)
    (f : Finset U' → ℝ) (M : ℝ) :
    (uniformOfFamily sets hJ).avgSurplus f M =
      (∑ j : J, surplus f M (sets j)) / (Fintype.card J : ℝ) := by
  simp [avgSurplus, uniformOfFamily, totalWeight]
  rfl

end UniformOfFamily

end KaltonRoberts
