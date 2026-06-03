/-
Copyright (c) 2026 Command Master. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Command Master
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.SetLike.Fintype
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import LeanPool.LeanBourgain.Geometry.Lines

/-!
# Projective transformations sending a line to the line at infinity

For two distinct affine points `p` and `q`, there is a linear automorphism of the
projective space `α × α × α` sending the line through `p` and `q` to the line at
infinity (`projectiveTransform`). This is the key change of coordinates used to
reduce incidence estimates for general lines to the grid case.
-/

namespace LeanPool.LeanBourgain

open Finset Module

variable {α : Type*} [Field α]

/-- A linear automorphism of `α × α × α` sending the line through two distinct
points `p` and `q` to the line at infinity. -/
noncomputable def projectiveTransform (p q : α × α) (h : p ≠ q) :
    (α × α × α) ≃ₗ[α] (α × α × α) := by
  let l := Submodule.pair p q
  let inf := Submodule.infinity α
  have b₁ := Submodule.pairBasis p q h
  have b₂ := Submodule.infinityBasis α
  have f : l ≃ₗ[α] inf := b₁.repr.trans b₂.repr.symm
  let l' := Classical.choose (Submodule.exists_isCompl l)
  have l'p : IsCompl l l' := Classical.choose_spec _
  let inf' := Classical.choose (Submodule.exists_isCompl inf)
  have inf'p : IsCompl inf inf' := Classical.choose_spec _
  have f' : l' ≃ₗ[α] inf' := by
    apply LinearEquiv.ofFinrankEq
    apply add_left_cancel (a := 2)
    conv =>
      congr
      · lhs
        tactic =>
          change 2 = Module.finrank α l
          rw [finrank_eq_nat_card_basis b₁]
          simp
      · lhs
        tactic =>
          change 2 = Module.finrank α inf
          rw [finrank_eq_nat_card_basis b₂]
          simp
    rw [Submodule.finrank_add_eq_of_isCompl l'p, Submodule.finrank_add_eq_of_isCompl inf'p]
  have f'₁ := Submodule.prodEquivOfIsCompl l l' l'p
  have f'₂ := Submodule.prodEquivOfIsCompl inf inf' inf'p
  exact f'₁.symm ≪≫ₗ (LinearEquiv.prodCongr f f') ≪≫ₗ f'₂

lemma project_p (p q : α × α) (h : p ≠ q) :
    (projectiveTransform p q h) ⟨p.1, p.2, 1⟩ = ⟨1, 0, 0⟩ := by
  let p' : Submodule.pair p q := ⟨⟨p.1, p.2, 1⟩, mem_span1 p q⟩
  simp only [projectiveTransform, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]
  rw [(Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero ..).mpr (mem_span1 p q)]
  have : (⟨p.1, p.2, 1⟩ : (α × α × α)) = ↑p' := by simp [p']
  rw [this, Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp only [map_zero, Prod.mk_zero_zero]
  rw [show (p' : Submodule.pair p q) = ⟨⟨p.1, p.2, 1⟩, mem_span1 p q⟩ from rfl,
    repr_pair_basis_first]
  simp [infinity_first]

lemma project_q (p q : α × α) (h : p ≠ q) :
    (projectiveTransform p q h) ⟨q.1, q.2, 1⟩ = ⟨0, 1, 0⟩ := by
  let q' : Submodule.pair p q := ⟨(q.1, q.2, 1), mem_span2 p q⟩
  simp only [projectiveTransform, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]
  rw [(Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero ..).mpr (mem_span2 p q)]
  have : (⟨q.1, q.2, 1⟩ : (α × α × α)) = ↑q' := by simp [q']
  rw [this, Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp only [map_zero]
  rw [show (q' : Submodule.pair p q) = ⟨⟨q.1, q.2, 1⟩, mem_span2 p q⟩ from rfl,
    repr_pair_basis_second]
  simp [infinity_second]

lemma of_line (p q : α × α) (h : p ≠ q) (x : α × α × α)
    (h₂ : x ∈ (Submodule.pair p q : Set _)) :
    (projectiveTransform p q h) x ∈ (Submodule.infinity α : Set _) := by
  rw [infinity_mem]
  rw [SetLike.mem_coe, Submodule.pair, Submodule.mem_span_pair] at h₂
  have ⟨a, b, h₂⟩ := h₂
  rw [← h₂]
  simp only [map_add, map_smul]
  rw [project_p, project_q]
  simp

lemma of_infinity (p q : α × α) (h : p ≠ q) (x : α × α × α)
    (h₂ : x ∈ (Submodule.infinity α : Set _)) :
    (projectiveTransform p q h).symm x ∈ (Submodule.pair p q : Set _) := by
  rw [infinity_mem] at h₂
  rw [SetLike.mem_coe, Submodule.pair, Submodule.mem_span_pair]
  exists x.1, x.2.1
  rw [LinearEquiv.eq_symm_apply]
  simp only [map_add, map_smul]
  rw [project_p, project_q]
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨?_, ?_, ?_⟩ <;> simp [h₂]

lemma non_erasing (p q x : α × α) (h : p ≠ q) (h₂ : ¬x ∈ Line.of p q h) :
    ((projectiveTransform p q h) ⟨x.1, x.2, 1⟩).2.2 ≠ 0 := by
  intro nh
  rw [← infinity_mem] at nh
  suffices x ∈ Line.of p q h by contradiction
  have := of_infinity p q h _ nh
  rw [LinearEquiv.symm_apply_apply] at this
  exact this

end LeanPool.LeanBourgain
