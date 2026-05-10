/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.Sensitivity.Defs
import LeanPool.Sensitivity.Multilinear
import LeanPool.Sensitivity.Subcube
import LeanPool.Sensitivity.Parity
import LeanPool.Sensitivity.HuangBridge

/-!
# The Sensitivity Theorem

This file proves the main quantitative form of the sensitivity conjecture:
for every Boolean function `f` of multilinear degree `d ≥ 1`, the sensitivity
of `f` is bounded below by `√d`. The proof combines the parity imbalance
lemma with the Huang hypercube lemma imported from `Mathlib`'s
`Archive.Sensitivity`.

## Proof outline

1. Find a `d`-dimensional subcube on which the restriction of `f` has full
   degree `d`.
2. Reindex this subcube to `Fin (m+1) → Bool` and obtain a parity-sign
   imbalance: a class of more than `2^m` vertices with the same parity sign.
3. Apply the Huang hypercube lemma to extract a vertex with at least
   `√(m+1)` same-class neighbours.
4. Each such neighbour is a bit-flip image `flipBit q i` along a distinct
   coordinate `i`, and at each such `i` the function `f` is sensitive.
5. Lift this lower bound on the local sensitivity of the restriction back to
   `f` itself.
-/

namespace LeanPoolSensitivity

/-- **Sensitivity Theorem** (Huang 2019). For any Boolean function `f` of
multilinear degree `d ≥ 1`, the sensitivity `s(f)` satisfies
`√d ≤ s(f)`. -/
theorem sensitivity_ge_sqrt_degree {n : ℕ} (f : BoolFun n) (hd : 1 ≤ f.degree) :
    Real.sqrt (f.degree : ℝ) ≤ (f.sensitivity : ℝ) := by
  obtain ⟨S, hcard, _, hmoeb⟩ := f.exists_fullDegree_restriction (by omega)
  set f' := f.restrictTo S (fun _ => false) with f'_def
  obtain ⟨m, hm⟩ : ∃ m, f.degree = m + 1 := ⟨f.degree - 1, by omega⟩
  have hcard' : Fintype.card S = Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_coe, Fintype.card_fin]; omega
  let e : S ≃ Fin (m + 1) := Fintype.equivOfCardEq hcard'
  let toN : Fin (m + 1) → Fin n := fun i => (e.symm i).val
  let g : BoolFun (m + 1) := fun y =>
    f (fun j => if hj : j ∈ S then y (e ⟨j, hj⟩) else false)
  have toN_inj : Function.Injective toN :=
    fun i j h => e.symm.injective (Subtype.ext h)
  have hg_moeb : g.moebius Finset.univ ≠ 0 := by
    suffices h : g.moebius Finset.univ = f'.moebius S by rwa [h]
    have toN_e : ∀ (j : Fin n) (hj : j ∈ S), toN (e ⟨j, hj⟩) = j :=
      fun j hj => show (e.symm (e ⟨j, hj⟩)).val = j by simp
    unfold BoolFun.moebius
    apply Finset.sum_nbij (fun U => U.map ⟨toN, toN_inj⟩)
    · intro U _; rw [Finset.mem_powerset]; intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj; exact (e.symm i).property
    · exact fun _ _ _ _ h => Finset.map_injective ⟨toN, toN_inj⟩ h
    · intro T hT
      simp only [Finset.mem_coe, Finset.mem_powerset] at hT
      rw [Set.mem_image]
      refine ⟨T.preimage toN (toN_inj.injOn.mono (Set.subset_univ _)),
              Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.subset_univ _)),
              Finset.ext fun j => ?_⟩
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨i, hi, hij⟩ => hij ▸ hi,
             fun hj => ⟨e ⟨j, hT hj⟩,
               show toN (e ⟨j, hT hj⟩) ∈ T by rw [toN_e]; exact hj,
               toN_e j (hT hj)⟩⟩
    · intro U _
      congr 1
      · congr 1
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_map]; omega
      · congr 1
        change f (fun j => if hj : j ∈ S then indicator U (e ⟨j, hj⟩) else false) =
               f (embed S (fun _ => false) (indicator (U.map ⟨toN, toN_inj⟩)))
        congr 1; funext j; simp only [embed]
        by_cases hj : j ∈ S
        · simp only [hj, dite_true, ite_true, indicator,
                    Finset.mem_map, Function.Embedding.coeFn_mk]
          have hiff : (e ⟨j, hj⟩ ∈ U) ↔ (∃ a ∈ U, toN a = j) :=
            ⟨fun h => ⟨e ⟨j, hj⟩, h, toN_e j hj⟩,
             fun ⟨i, hi, hij⟩ => by
               rwa [show i = e ⟨j, hj⟩ from by
                 rw [← Equiv.apply_symm_apply e i]; congr 1
                 exact Subtype.ext hij] at hi⟩
          simp only [hiff]
        · simp only [hj, dite_false, ite_false]
  obtain ⟨c, _, hH⟩ := fullDegree_imbalance g (Nat.succ_pos m) hg_moeb
  set H := Finset.univ.filter (fun x : Fin (m + 1) → Bool => g.paritySigned x = c)
  rw [show m + 1 - 1 = m from by omega] at hH
  obtain ⟨q, hqH, hq_bound⟩ := huang_finset H (by omega)
  have hq_par : g.paritySigned q = c := (Finset.mem_filter.mp hqH).2
  rw [show (f.degree : ℝ) = ↑m + 1 from by exact_mod_cast hm]
  apply le_trans hq_bound
  push_cast [Nat.cast_le]
  let embedQ : Fin n → Bool := fun j => if hj : j ∈ S then q (e ⟨j, hj⟩) else false
  have toN_e : ∀ (j : Fin n) (hj : j ∈ S), toN (e ⟨j, hj⟩) = j :=
    fun j hj => show (e.symm (e ⟨j, hj⟩)).val = j by simp
  have e_toN : ∀ (i : Fin (m + 1)), e ⟨toN i, (e.symm i).property⟩ = i :=
    fun i => show e (e.symm i) = i by simp
  have toN_mem : ∀ (i : Fin (m + 1)), toN i ∈ S := fun i => (e.symm i).property
  have g_flip_eq : ∀ i, g (flipBit q i) = f (flipBit embedQ (toN i)) := by
    intro i; change f _ = f _; congr 1; funext j
    by_cases hj : j ∈ S
    · simp only [hj, dite_true]
      by_cases hji : j = toN i
      · subst hji
        rw [show (e ⟨toN i, hj⟩ : Fin (m + 1)) = i from e_toN i,
            flipBit_apply_same, flipBit_apply_same]
        have : embedQ (toN i) = q i := by
          change (if h : toN i ∈ S then q (e ⟨toN i, h⟩) else false) = q i
          rw [dif_pos (toN_mem i)]
          congr 1; exact e_toN i
        rw [this]
      · have : e ⟨j, hj⟩ ≠ i := fun h => hji (by rw [← toN_e j hj, h])
        rw [flipBit_apply_ne _ _ this, flipBit_apply_ne _ _ hji]
        change q (e ⟨j, hj⟩) = (if h : j ∈ S then q (e ⟨j, h⟩) else false)
        rw [dif_pos hj]
    · simp only [hj, dite_false]
      have : j ≠ toN i := fun h => hj (h ▸ toN_mem i)
      rw [flipBit_apply_ne _ _ this]
      change false = embedQ j
      change false = (if h : j ∈ S then q (e ⟨j, h⟩) else false)
      rw [dif_neg hj]
  have g_to_f : ∀ i, g.sensitiveAt q i → f.sensitiveAt embedQ (toN i) := by
    intro i hi; unfold BoolFun.sensitiveAt at hi ⊢; rwa [← g_flip_eq]
  calc (H.filter (fun p => ∃ i, p = flipBit q i)).card
      ≤ g.localSensitivity q := by
        unfold BoolFun.localSensitivity
        have key : H.filter (fun p => ∃ i, p = flipBit q i) ⊆
            (Finset.univ.filter (fun i => g.sensitiveAt q i)).image (flipBit q) := by
          intro p hp
          simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hp ⊢
          obtain ⟨hp_par, i, rfl⟩ := hp
          exact ⟨i, g.sensitiveAt_of_paritySigned_eq q i (hp_par.trans hq_par.symm), rfl⟩
        exact le_trans (Finset.card_le_card key) Finset.card_image_le
    _ ≤ f.localSensitivity embedQ := by
        unfold BoolFun.localSensitivity
        apply Finset.card_le_card_of_injOn toN
          (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            g_to_f i (Finset.mem_filter.mp hi).2⟩)
          (fun _ _ _ _ h => toN_inj h)
    _ ≤ f.sensitivity := f.localSensitivity_le_sensitivity embedQ

end LeanPoolSensitivity
