/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/

import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-!
# Binary Matrix VC Dimension and Sauer-Shelah

Pure combinatorics: VC dimension on binary matrices, bridged to Mathlib's
`Finset.Shatters` infrastructure. No learning theory types.
-/

open Finset

universe u

/-- An `m x n` binary matrix, represented as `Fin m -> Fin n -> Bool`. -/
abbrev BinaryMatrix (m n : ℕ) := Fin m → Fin n → Bool

namespace BinaryMatrix

/-- A binary matrix `M` shatters a column set `S` if for every subset `t ⊆ S`,
    there is a row `i` whose `true` columns within `S` are exactly `t`. -/
def shatters {m n : ℕ} (M : BinaryMatrix m n) (S : Finset (Fin n)) : Prop :=
  ∀ t ⊆ S, ∃ i : Fin m, ∀ j ∈ S, (M i j = true) ↔ (j ∈ t)

/-- Transpose of a binary matrix. -/
def transpose {m n : ℕ} (M : BinaryMatrix m n) : BinaryMatrix n m :=
  fun j i => M i j

/-- Convert a binary matrix to a Finset family: each row becomes the set of
    columns where that row is `true`. -/
def toFinsetFamily {m n : ℕ} (M : BinaryMatrix m n) :
    Finset (Finset (Fin n)) :=
  Finset.univ.image (fun i : Fin m => Finset.univ.filter (fun j => M i j = true))

/-- The VC dimension of a binary matrix, defined via the Mathlib Finset family. -/
noncomputable def vcDim {m n : ℕ} (M : BinaryMatrix m n) : ℕ :=
  M.toFinsetFamily.vcDim

/-- Our `shatters` coincides with Mathlib's `Finset.Shatters` on the associated family. -/
theorem shatters_iff {m n : ℕ} (M : BinaryMatrix m n) (S : Finset (Fin n)) :
    M.shatters S ↔ M.toFinsetFamily.Shatters S := by
  constructor
  · -- Forward: our definition → Mathlib's
    intro hM t ht
    obtain ⟨i, hi⟩ := hM t ht
    refine ⟨Finset.univ.filter (fun j => M i j = true), ?_, ?_⟩
    · simp only [toFinsetFamily, mem_image, mem_univ, true_and]
      exact ⟨i, rfl⟩
    · ext j
      simp only [mem_inter, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hj, hMij⟩
        exact (hi j hj).mp hMij
      · intro hjt
        have hjS := ht hjt
        exact ⟨hjS, (hi j hjS).mpr hjt⟩
  · -- Backward: Mathlib's → our definition
    intro hS t ht
    obtain ⟨u, hu, hut⟩ := hS ht
    simp only [toFinsetFamily, mem_image, mem_univ, true_and] at hu
    obtain ⟨i, rfl⟩ := hu
    refine ⟨i, fun j hj => ?_⟩
    constructor
    · intro hMij
      have : j ∈ S ∩ Finset.univ.filter (fun j => M i j = true) := by
        simp only [mem_inter, mem_filter, mem_univ, true_and]; exact ⟨hj, hMij⟩
      rwa [hut] at this
    · intro hjt
      have : j ∈ S ∩ Finset.univ.filter (fun j => M i j = true) := by rw [hut]; exact hjt
      simp only [mem_inter, mem_filter, mem_univ, true_and] at this
      exact this.2

/-- Two `Bool`-valued functions on `Fin n` that agree on which indices are `true`
    (as witnessed by equal `univ.filter`) are equal. -/
theorem bool_fun_eq_of_filter_eq {n : ℕ} (f g : Fin n → Bool)
    (h : Finset.univ.filter (fun j => f j = true) =
         Finset.univ.filter (fun j => g j = true)) :
    f = g := by
  funext j
  by_cases hf : f j = true <;> by_cases hg : g j = true
  · rw [hf, hg]
  · exfalso
    have : j ∈ Finset.univ.filter (fun j => f j = true) := by simp [hf]
    rw [h] at this; simp [hg] at this
  · exfalso
    have : j ∈ Finset.univ.filter (fun j => g j = true) := by simp [hg]
    rw [← h] at this; simp [hf] at this
  · simp only [Bool.not_eq_true] at hf hg
    rw [hf, hg]

/-- **Sauer-Shelah lemma for binary matrices**: the number of distinct rows in the
    Finset family is bounded by the sum of binomial coefficients up to the VC dimension. -/
theorem card_toFinsetFamily_le {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (hd : M.toFinsetFamily.vcDim ≤ d) :
    M.toFinsetFamily.card ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
  calc M.toFinsetFamily.card
      _ ≤ M.toFinsetFamily.shatterer.card := card_le_card_shatterer _
      _ ≤ ∑ k ∈ Iic M.toFinsetFamily.vcDim, (Fintype.card (Fin n)).choose k :=
          card_shatterer_le_sum_vcDim
      _ = ∑ k ∈ Iic M.toFinsetFamily.vcDim, n.choose k := by
          simp [Fintype.card_fin]
      _ ≤ ∑ k ∈ Iic d, n.choose k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Iic_subset_Iic.mpr hd)
            (fun _ _ _ => Nat.zero_le _)

/-!
## Assouad's Dual VC Bound for Matrices

If `M` has VC dimension ≤ `d`, then `M.transpose` has VC dimension ≤ `2^(d+1) - 1`.

The proof uses the bitstring coding argument: index `2^(d+1)` shattered rows by
`Fin (d+1) → Bool`, extract `d+1` columns via coordinate projections, and show
these columns are shattered by `M`.
-/

/-- Auxiliary: if `M.transpose` shatters `S ⊆ Fin m` with `|S| ≥ 2^(d+1)`,
    then `M` shatters some set of `d+1` columns. -/
theorem transpose_shatters_imp_shatters {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (S : Finset (Fin m)) (hS : M.transpose.shatters S)
    (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset (Fin n), T.card = d + 1 ∧ M.shatters T := by
  -- Embed (Fin (d+1) → Bool) into S
  let eS := S.equivFin
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp)
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin S.card := Fin.castLEEmb hcard
  let eFinS : Fin S.card ≃ ↥S := eS.symm
  let embed : (Fin (d + 1) → Bool) → ↥S := eFinS ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab
    simp only [embed, Function.comp] at hab
    exact eFun.injective (eFin.injective (eFinS.injective hab))
  -- For each coordinate k, define the "k-th half" subset T_k ⊆ S
  -- T_k = {embed(b) | b(k) = true} viewed as a subset of S
  let T_k (k : Fin (d + 1)) : Finset (Fin m) :=
    S.filter (fun i => ∃ b : Fin (d + 1) → Bool, (embed b).val = i ∧ b k = true)
  have hT_k_sub : ∀ k, T_k k ⊆ S := fun k => Finset.filter_subset _ _
  -- M^T shattering gives columns c_k witnessing T_k
  have hcols : ∀ k : Fin (d + 1), ∃ c : Fin n, ∀ i ∈ S,
      (M i c = true ↔ i ∈ T_k k) := by
    intro k
    obtain ⟨c, hc⟩ := hS (T_k k) (hT_k_sub k)
    exact ⟨c, fun i hi => by simpa only [transpose] using hc i hi⟩
  choose c hc using hcols
  -- The key property: M (embed b) (c k) = b k
  have hM_embed : ∀ (b : Fin (d + 1) → Bool) (k : Fin (d + 1)),
      M (embed b).val (c k) = b k := by
    intro b k
    have hemb_mem : (embed b).val ∈ S := (embed b).property
    by_cases hbk : b k = true
    · -- b k = true, so embed b ∈ T_k k
      have hmem : (embed b).val ∈ T_k k := by
        simp only [T_k, Finset.mem_filter]
        exact ⟨hemb_mem, ⟨b, rfl, hbk⟩⟩
      rw [(hc k _ hemb_mem).mpr hmem, hbk]
    · -- b k = false, so embed b ∉ T_k k
      simp only [Bool.not_eq_true] at hbk
      have hmem : (embed b).val ∉ T_k k := by
        simp only [T_k, Finset.mem_filter, not_and]
        intro _
        rintro ⟨b', hb'eq, hb'k⟩
        have : embed b' = embed b := by
          exact Subtype.val_injective (by rw [hb'eq])
        have := hembed_inj this
        rw [this] at hb'k
        rw [hbk] at hb'k
        exact Bool.noConfusion hb'k
      rw [Bool.eq_false_iff.mpr (mt (hc k _ hemb_mem).mp hmem), hbk]
  -- Build T = {c 0, c 1, ..., c d}
  let T : Finset (Fin n) := Finset.univ.image c
  -- The c_k are distinct
  have hc_inj : Function.Injective c := by
    intro j k hjk
    by_contra hjk_ne
    -- Choose b with b j = true, b k = false
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    have h1 : M (embed b0).val (c j) = true := by
      rw [hM_embed b0 j]; simp [b0]
    have h2 : M (embed b0).val (c k) = false := by
      rw [hM_embed b0 k]; simp only [b0]
      cases hkj : (k == j)
      · rfl
      · exact absurd (beq_iff_eq.mp hkj).symm hjk_ne
    rw [hjk] at h1
    exact Bool.noConfusion (h1 ▸ h2)
  have hT_card : T.card = d + 1 := by
    simp only [T, card_image_of_injective _ hc_inj, card_univ, Fintype.card_fin]
  -- M shatters T
  have hT_shatters : M.shatters T := by
    intro t ht
    -- t ⊆ T. Define g : Fin (d+1) → Bool by g(k) = (c k ∈ t)
    let g : Fin (d + 1) → Bool := fun k => decide (c k ∈ t)
    -- The row embed(g) witnesses t
    refine ⟨(embed g).val, fun j hj => ?_⟩
    -- j ∈ T means j = c k for some k
    simp only [T] at hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, _, rfl⟩ := hj
    rw [hM_embed g k]
    simp only [g, decide_eq_true_eq]
  exact ⟨T, hT_card, hT_shatters⟩

/-- **Assouad's dual VC bound (matrix form)**: if `M` has VC dimension ≤ `d`,
    then `M.transpose` has VC dimension ≤ `2^(d+1) - 1`.

    This is the fundamental bridge between primal and dual shattering.
    Proved via the bitstring coding argument (Assouad 1983). -/
theorem assouad_transpose_vcDim {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (hd : M.vcDim ≤ d) :
    M.transpose.vcDim ≤ 2 ^ (d + 1) - 1 := by
  -- By contradiction: if M^T.vcDim ≥ 2^(d+1), extract a large shattered set
  by_contra hlt
  push Not at hlt
  have hge : 2 ^ (d + 1) ≤ M.transpose.vcDim := by omega
  -- vcDim = shatterer.sup card. Extract a shattered set of size ≥ 2^(d+1).
  -- Use Finset.le_sup_iff with ⊥ < 2^(d+1) (since 2^(d+1) > 0)
  have hpos : (⊥ : ℕ) < 2 ^ (d + 1) := Nat.two_pow_pos (d + 1)
  -- Extract shattered set from vcDim bound using le_sup_iff
  obtain ⟨S, hS_mem, hS_card⟩ := (Finset.le_sup_iff hpos).mp hge
  -- S ∈ shatterer means M^T.toFinsetFamily.Shatters S
  rw [Finset.mem_shatterer] at hS_mem
  -- Convert to our shatters definition
  have hS_shat : M.transpose.shatters S := (shatters_iff M.transpose S).mpr hS_mem
  -- Apply the coding lemma
  obtain ⟨T, hT_card, hT_shat⟩ := transpose_shatters_imp_shatters M S hS_shat hS_card
  -- Convert M.shatters T to M.toFinsetFamily.Shatters T, then get vcDim ≥ d+1
  have hT_mathlib : M.toFinsetFamily.Shatters T := (shatters_iff M T).mp hT_shat
  have hvc_ge : d + 1 ≤ M.vcDim := by
    calc d + 1 = T.card := hT_card.symm
    _ ≤ M.vcDim := hT_mathlib.card_le_vcDim
  omega

end BinaryMatrix
