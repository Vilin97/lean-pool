/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Complexity.VCDimension
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.CompleteLattice.Basic

/-!
# Dual VC Dimension (Assouad's Lemma)

The dual concept class and the bound `VCDim*(C) ≤ 2^(d+1) - 1`
where `d = VCDim(C)`. This is Assouad's (1983) coding lemma.

The **dual class** of a concept class `C ⊆ (X → Bool)` is the concept class
on the domain `↥C` where each point `x : X` induces a concept `c ↦ c x`.

## Main results

* `DualClass`  -  the dual concept class
* `dual_shatters_imp_original_shatters`  -  coding lemma: if the dual shatters
  `2^(d+1)` concepts, then the original class shatters `d+1` points
* `dual_vcdim_le_pow`  -  Assouad's bound: `VCDim*(C) ≤ 2^(VCDim(C)+1) - 1`
-/

open Finset

universe u

/-- The dual concept class: for each point `x : X`, the evaluation map
    `c ↦ c x` is a concept on the domain `↥C`. The dual class collects
    all such evaluation concepts. -/
def DualClass (X : Type u) (C : ConceptClass X Bool) : ConceptClass (↥C) Bool :=
  { f | ∃ x : X, ∀ c : ↥C, f c = c.val x }

namespace DualVC

variable {X : Type u} {C : ConceptClass X Bool}

/-- A dual concept is determined by a point: the evaluation-at-x function. -/
def evalConcept (x : X) : ↥C → Bool := fun c => c.val x

/-- Membership lemma for Assouad's dual VC construction: the evaluation function
`fun c => c x` belongs to the dual class `C^T` of `C`. Used in the bitstring coding
step of the dual bound `vcDim(C^T) ≤ 2^(vcDim(C) + 1) - 1`, the standard inequality
that lets compression arguments switch between primal and dual without losing
dimension control. -/
theorem evalConcept_mem_dualClass (x : X) : evalConcept x ∈ DualClass X C :=
  ⟨x, fun _ => rfl⟩

/-- Core coding lemma (Assouad 1983): if the dual class shatters a set `S`
    of concepts with `|S| ≥ 2^(d+1)`, then the original class shatters
    some set of `d+1` points.

    Proof: index `2^(d+1)` concepts by bitstrings `b : Fin (d+1) → Bool`.
    For each coordinate `j`, dual shattering provides a point `x_j` that
    "reads off" the `j`-th bit. Then `{x_0, ..., x_d}` is shattered by `C`. -/
theorem dual_shatters_imp_original_shatters {d : ℕ}
    (S : Finset ↥C) (hS : Shatters ↥C (DualClass X C) S)
    (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset X, T.card = d + 1 ∧ Shatters X C T := by
  classical
  -- Embed the `2^(d+1)` bitstrings into `↥S` as a subset of the shattered concepts.
  let eS := S.equivFin
  have h2le : 2 ^ (d + 1) ≤ S.card := hcard
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_bool, Fintype.card_fin])
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin S.card := Fin.castLEEmb h2le
  let eFinS : Fin S.card ≃ ↥S := eS.symm
  let embed : (Fin (d + 1) → Bool) → ↥S := eFinS ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab
    simp only [embed, Function.comp] at hab
    exact eFun.injective (eFin.injective (eFinS.injective hab))
  -- For coordinate `j`, label each embedded concept by its `j`-th bit (and `false` elsewhere).
  let label (j : Fin (d + 1)) : ↥S → Bool := fun s =>
    if h : ∃ b, embed b = s then (h.choose) j else false
  -- Dual shattering of each labeling yields a point `x j` reading off the `j`-th bit.
  have hpoints : ∀ j : Fin (d + 1), ∃ x : X, ∀ s : ↥S,
      (s : ↥C).val x = label j s := by
    intro j
    obtain ⟨f, ⟨x, hx⟩, hf_eq⟩ := hS (label j)
    exact ⟨x, fun s => by rw [← hx s, ← hf_eq s]⟩
  choose x hx using hpoints
  let T : Finset X := Finset.univ.image x
  -- The `x j` are distinct: a bitstring singleton at `j` separates coordinates `j ≠ k`.
  have hx_inj : Function.Injective x := by
    intro j k hjk
    by_contra hjk_ne
    have hlabel_eq : ∀ s : ↥S, label j s = label k s := by
      intro s
      have hj := hx j s
      have hk := hx k s
      rw [hjk] at hj
      rwa [hj] at hk
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    have hlabel_j_b0 : label j (embed b0) = true := by
      simp only [label]
      rw [dif_pos ⟨b0, rfl⟩, hembed_inj (⟨b0, rfl⟩ : ∃ b, embed b = embed b0).choose_spec]
      simp [b0]
    have hlabel_k_b0 : label k (embed b0) = false := by
      simp only [label]
      rw [dif_pos ⟨b0, rfl⟩, hembed_inj (⟨b0, rfl⟩ : ∃ b, embed b = embed b0).choose_spec]
      simp only [b0]
      cases hkj : (k == j)
      · rfl
      · exact absurd (beq_iff_eq.mp hkj).symm hjk_ne
    have := hlabel_eq (embed b0)
    rw [hlabel_j_b0, hlabel_k_b0] at this
    exact Bool.noConfusion this
  have hT_card : T.card = d + 1 := by
    simp only [T, card_image_of_injective _ hx_inj, card_univ, Fintype.card_fin]
  -- `C` shatters `T`: realise labeling `f` by the concept `embed g`, where `g j = f (x j)`.
  have hT_shatters : Shatters X C T := by
    intro f
    have hx_mem : ∀ j : Fin (d + 1), x j ∈ T := by
      intro j; simp only [T]; exact mem_image_of_mem _ (mem_univ _)
    let g : Fin (d + 1) → Bool := fun j => f ⟨x j, hx_mem j⟩
    let cg : ↥C := (embed g).val
    refine ⟨cg.val, cg.property, fun ⟨y, hy⟩ => ?_⟩
    simp only [T] at hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, _, rfl⟩ := hy
    change cg.val (x j) = f ⟨x j, hx_mem j⟩
    have step1 : (embed g).val.val (x j) = label j (embed g) := hx j (embed g)
    have step2 : label j (embed g) = g j := by
      simp only [label]
      rw [dif_pos ⟨g, rfl⟩, hembed_inj (⟨g, rfl⟩ : ∃ b, embed b = embed g).choose_spec]
    rw [step1, step2]
  exact ⟨T, hT_card, hT_shatters⟩

/-- **Assouad's dual VC bound**: if `VCDim(C) ≤ d`, then the VC dimension of
    the dual class is at most `2^(d+1) - 1`.

    This is tight: the class of all subsets of `{1,...,d}` achieves equality. -/
theorem dual_vcdim_le_pow {d : ℕ} (hd : VCDim X C ≤ ↑d) :
    VCDim ↥C (DualClass X C) ≤ ↑(2 ^ (d + 1) - 1) := by
  apply iSup₂_le
  intro S hS
  by_contra hlt
  push Not at hlt
  have hge : 2 ^ (d + 1) ≤ S.card := by
    by_contra hlt'
    push Not at hlt'
    have hle : S.card ≤ 2 ^ (d + 1) - 1 := by omega
    apply absurd _ (not_le.mpr hlt)
    change (↑S.card : WithTop ℕ) ≤ ↑(2 ^ (d + 1) - 1)
    exact WithTop.coe_le_coe.mpr hle
  obtain ⟨T, hTcard, hTshat⟩ := dual_shatters_imp_original_shatters S hS hge
  have hvc : (↑(d + 1) : WithTop ℕ) ≤ VCDim X C :=
    le_iSup₂_of_le T hTshat (by exact_mod_cast hTcard.ge)
  have : d + 1 ≤ d := by exact_mod_cast le_trans hvc hd
  omega

end DualVC
