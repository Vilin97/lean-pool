/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.Selection
import LeanPool.RearrangementNumber.NonMRR.FiniteVectors
import Mathlib.Data.Finset.Sort

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NonMRR

/-- A finite injective sequence can be ordered by a permutation of its labels. -/
theorem exists_strictMono_perm {L : ℕ} (f : Fin L → ℕ) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin L), StrictMono (f ∘ σ) := by
  classical
  let s : Finset ℕ := univ.image f
  have hc : s.card = L := by simp [s, card_image_of_injective _ hf]
  let e : Fin L ≃ s := Equiv.ofBijective
    (fun i => ⟨f i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => hf (congrArg Subtype.val h), by
      intro x
      obtain ⟨i, _hi, hix⟩ := mem_image.mp x.property
      exact ⟨i, Subtype.ext hix⟩⟩
  let o : Fin L ≃o s := s.orderIsoOfFin hc
  let σ : Equiv.Perm (Fin L) := o.toEquiv.trans e.symm
  refine ⟨σ, ?_⟩
  have heq (i : Fin L) : f (σ i) = (o i).val :=
    congrArg Subtype.val (e.apply_symm_apply (o i))
  intro i k hik
  simpa only [Function.comp_apply, heq] using o.strictMono hik

/-- A cut through an increasing finite sequence is an initial segment of its labels. -/
theorem strictMono_cut {L : ℕ} (f : Fin L → ℕ) (hf : StrictMono f) (j : ℕ) :
    ∃ r ≤ L, ∀ i : Fin L, f i < j ↔ i.val < r := by
  classical
  let s : Finset (Fin L) := univ.filter fun i => j ≤ f i
  by_cases hs : s.Nonempty
  · let i₀ : Fin L := s.min' hs
    have hi₀ : j ≤ f i₀ := (mem_filter.mp (min'_mem s hs)).2
    refine ⟨i₀.val, i₀.is_lt.le, ?_⟩
    intro i
    constructor
    · intro hi
      have hil : i < i₀ := by
        by_contra h
        have := hf.monotone (le_of_not_gt h)
        omega
      exact hil
    · intro hi
      by_contra h
      have his : i ∈ s := mem_filter.mpr ⟨mem_univ _, le_of_not_gt h⟩
      have := min'_le s i his
      change i₀ ≤ i at this
      exact (not_le_of_gt hi) this
  · refine ⟨L, le_rfl, ?_⟩
    intro i
    have hi : f i < j := by
      by_contra h
      exact hs ⟨i, mem_filter.mpr ⟨mem_univ _, le_of_not_gt h⟩⟩
    exact iff_of_true hi i.is_lt

/-- Put a finite vector on an arbitrary injectively labelled subset of the naturals. -/
def embedVector {L : ℕ} (e : Fin L ↪ ℕ) (v : Fin L → ℝ) (i : ℕ) : ℝ :=
  ∑ k, if e k = i then v k else 0

theorem rearrangedPartialSum_embedVector {L : ℕ} (e : Fin L ↪ ℕ)
    (v : Fin L → ℝ) (π : Equiv.Perm ℕ) (j : ℕ) :
    rearrangedPartialSum (embedVector e v) π j =
      ∑ k ∈ univ.filter (fun k : Fin L => π.symm (e k) < j), v k := by
  classical
  unfold rearrangedPartialSum embedVector
  rw [sum_comm, sum_filter]
  apply sum_congr rfl
  intro k _hk
  have heq (i : ℕ) : e k = π i ↔ π.symm (e k) = i := by
    constructor
    · intro h
      rw [h, π.symm_apply_apply]
    · intro h
      rw [← h, π.apply_symm_apply]
  simp_rw [heq]
  simp

/-- A permutation visits a finite support in one fixed finite ordering. Each global
partial sum is a prefix of that ordering, with the same cut for every vector. -/
theorem exists_perm_embedVector_prefix {L : ℕ} (e : Fin L ↪ ℕ)
    (π : Equiv.Perm ℕ) :
    ∃ σ : Equiv.Perm (Fin L), ∀ j : ℕ, ∃ r ≤ L, ∀ v : Fin L → ℝ,
      rearrangedPartialSum (embedVector e v) π j = vectorPrefix (v ∘ σ) r := by
  classical
  obtain ⟨σ, hσ⟩ := exists_strictMono_perm (π.symm ∘ e) (π.symm.injective.comp e.injective)
  refine ⟨σ, ?_⟩
  intro j
  obtain ⟨r, hr, hcut⟩ := strictMono_cut ((π.symm ∘ e) ∘ σ) hσ j
  refine ⟨r, hr, ?_⟩
  intro v
  rw [rearrangedPartialSum_embedVector, vectorPrefix, sum_filter, sum_filter]
  have h := Equiv.sum_comp σ (fun k : Fin L => if π.symm (e k) < j then v k else 0)
  rw [← h]
  apply sum_congr rfl
  intro k _hk
  simp only [Function.comp_apply] at hcut ⊢
  simp only [hcut k]

@[simp] theorem embedVector_apply {L : ℕ} (e : Fin L ↪ ℕ)
    (v : Fin L → ℝ) (k : Fin L) : embedVector e v (e k) = v k := by
  classical
  simp [embedVector, e.injective.eq_iff]

theorem embedVector_eq_zero {L : ℕ} (e : Fin L ↪ ℕ)
    (v : Fin L → ℝ) (i : ℕ) (hi : i ∉ univ.image e) : embedVector e v i = 0 := by
  classical
  apply sum_eq_zero
  intro k _hk
  have hki : e k ≠ i := fun h => hi (mem_image.mpr ⟨k, mem_univ _, h⟩)
  simp [hki]

theorem sum_embedVector {L : ℕ} (e : Fin L ↪ ℕ) (v : Fin L → ℝ) :
    ∑ i ∈ univ.image e, embedVector e v i = ∑ k, v k := by
  classical
  rw [sum_image (fun _ _ _ _ h => e.injective h)]
  simp

theorem sum_norm_embedVector {L : ℕ} (e : Fin L ↪ ℕ) (v : Fin L → ℝ) :
    ∑ i ∈ univ.image e, ‖embedVector e v i‖ = ∑ k, ‖v k‖ := by
  classical
  rw [sum_image (fun _ _ _ _ h => e.injective h)]
  simp

theorem sum_norm_embedVector_eq_one {L : ℕ} (hL : 0 < L)
    (e : Fin L ↪ ℕ) (v : Fin L → ℝ) (habs : ∀ k, |v k| = 1 / (L : ℝ)) :
    ∑ i ∈ univ.image e, ‖embedVector e v i‖ = 1 := by
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  rw [sum_norm_embedVector]
  simp [Real.norm_eq_abs, habs, hLne]

/-- The finite counting bound is unchanged when the coordinates are put on any
finite subset of the naturals and visited by an arbitrary infinite permutation. -/
theorem card_bad_embedVector_le {m L q : ℕ} (e : Fin L ↪ ℕ)
    (v : Fin m → Fin L → ℝ)
    (hbad : ∀ σ : Equiv.Perm (Fin L),
      (univ.filter fun k : Fin m =>
        ∃ r ≤ L, 1 / (q : ℝ) < |vectorPrefix (v k ∘ σ) r|).card ≤ 4 * q ^ 4)
    (π : Equiv.Perm ℕ) :
    (univ.filter fun k : Fin m =>
      ∃ j, 1 / (q : ℝ) < ‖rearrangedPartialSum (embedVector e (v k)) π j‖).card
        ≤ 4 * q ^ 4 := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_embedVector_prefix e π
  apply le_trans (card_le_card ?_) (hbad σ)
  intro k hk
  obtain ⟨j, hj⟩ := (mem_filter.mp hk).2
  obtain ⟨r, hr, hprefix⟩ := hσ j
  apply mem_filter.mpr
  refine ⟨mem_univ _, r, hr, ?_⟩
  simpa only [hprefix (v k), Real.norm_eq_abs] using hj

/-- The union of the exceptional values in the natural and permuted orders
has cardinality at most `8*q^4`. -/
theorem card_bad_embedVector_two_orders_le {m L q : ℕ} (e : Fin L ↪ ℕ)
    (v : Fin m → Fin L → ℝ)
    (hbad : ∀ σ : Equiv.Perm (Fin L),
      (univ.filter fun k : Fin m =>
        ∃ r ≤ L, 1 / (q : ℝ) < |vectorPrefix (v k ∘ σ) r|).card ≤ 4 * q ^ 4)
    (π : Equiv.Perm ℕ) :
    (univ.filter fun k : Fin m =>
      (∃ j, 1 / (q : ℝ) < ‖rearrangedPartialSum (embedVector e (v k)) (Equiv.refl ℕ) j‖) ∨
      (∃ j, 1 / (q : ℝ) < ‖rearrangedPartialSum (embedVector e (v k)) π j‖)).card
        ≤ 8 * q ^ 4 := by
  classical
  rw [filter_or]
  have h₁ := card_bad_embedVector_le e v hbad (Equiv.refl ℕ)
  have h₂ := card_bad_embedVector_le e v hbad π
  exact (card_union_le _ _).trans (by omega)

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
