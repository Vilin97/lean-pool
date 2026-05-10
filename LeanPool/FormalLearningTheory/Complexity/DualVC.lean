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
  -- Step 0: Get a bijection between (Fin (d+1) → Bool) and a subset of S
  -- Since |S| ≥ 2^(d+1) = |Fin (d+1) → Bool|, we can embed.
  have hcard_fun : Fintype.card (Fin (d + 1) → Bool) = 2 ^ (d + 1) := by
    simp [Fintype.card_bool, Fintype.card_fin]
  -- Get an equivalence S ≃ Fin S.card
  let eS := S.equivFin
  -- Get an embedding Fin (2^(d+1)) ↪ Fin S.card from 2^(d+1) ≤ S.card
  have h2le : 2 ^ (d + 1) ≤ S.card := hcard
  -- Get an embedding (Fin (d+1) → Bool) ↪ ↥S
  -- First: (Fin (d+1) → Bool) ≃ Fin (2^(d+1))
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_bool, Fintype.card_fin])
  -- Second: Fin (2^(d+1)) ↪ Fin S.card (order embedding from card bound)
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin S.card :=
    Fin.castLEEmb h2le
  -- Third: Fin S.card ≃ ↥S
  let eFinS : Fin S.card ≃ ↥S := eS.symm
  -- Compose: (Fin (d+1) → Bool) → ↥S
  let embed : (Fin (d + 1) → Bool) → ↥S := eFinS ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab
    simp only [embed, Function.comp] at hab
    have h1 := eFinS.injective hab
    have h2 := eFin.injective h1
    exact eFun.injective h2
  -- Step 1: For each coordinate j : Fin (d+1), define a labeling of S
  -- f_j(s) = (embed⁻¹(s))(j) if s is in the image, arbitrary otherwise.
  -- Better: f_j(s) = true iff s is in the "j-th half" of the embedded concepts.
  -- Precisely: T_j = {embed(b) | b(j) = true}
  -- Since S is shattered by DualClass, for T_j ⊆ S there exists a concept
  -- in DualClass realizing it. Since DualClass concepts are evaluation maps,
  -- this gives a point x_j.

  -- Define the labeling for coordinate j
  -- For each s : ↥S, we need a Bool value.
  -- If s is in the image of embed, assign the j-th bit of its preimage.
  -- If s is not in the image, assign false.
  let label (j : Fin (d + 1)) : ↥S → Bool := fun s =>
    if h : ∃ b, embed b = s then (h.choose) j else false
  -- Since DualClass shatters S, for each labeling there's a dual concept matching it
  -- A dual concept is evalConcept x for some x. So we get points x_j.
  have hpoints : ∀ j : Fin (d + 1), ∃ x : X, ∀ s : ↥S,
      (s : ↥C).val x = label j s := by
    intro j
    have := hS (label j)
    obtain ⟨f, hf_mem, hf_eq⟩ := this
    obtain ⟨x, hx⟩ := hf_mem
    exact ⟨x, fun s => by rw [← hx s, ← hf_eq s]⟩
  -- Choose the points
  choose x hx using hpoints
  -- Step 2: Build the set T = {x 0, x 1, ..., x d} as a Finset X
  let T : Finset X := Finset.univ.image x
  -- Step 3: Show T.card = d + 1 (the x_j are distinct)
  have hx_inj : Function.Injective x := by
    intro j k hjk
    -- If x j = x k, then for all s ∈ S, label j s = label k s
    -- But label j and label k differ on some element in the image of embed
    -- Specifically, on embed (fun i => if i = j then true else if i = k then false else false)
    -- Actually, consider the bitstring e_j that is 1 at j and 0 elsewhere
    by_contra hjk_ne
    have hlabel_eq : ∀ s : ↥S, label j s = label k s := by
      intro s
      have hj := hx j s
      have hk := hx k s
      rw [hjk] at hj
      rw [hj] at hk
      exact hk
    -- Construct a bitstring that distinguishes j and k
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    have hb0_in : ∃ b, embed b = embed b0 := ⟨b0, rfl⟩
    have hlabel_j_b0 : label j (embed b0) = true := by
      simp only [label]
      rw [dif_pos ⟨b0, rfl⟩]
      -- choose gives some b with embed b = embed b0, so b = b0 by injectivity
      have := (⟨b0, rfl⟩ : ∃ b, embed b = embed b0).choose_spec
      have := hembed_inj this
      rw [this]
      simp [b0]
    have hlabel_k_b0 : label k (embed b0) = false := by
      simp only [label]
      rw [dif_pos ⟨b0, rfl⟩]
      have := (⟨b0, rfl⟩ : ∃ b, embed b = embed b0).choose_spec
      have := hembed_inj this
      rw [this]
      simp only [b0]
      -- Goal: (k == j) = false
      cases hkj : (k == j)
      · rfl
      · exfalso; exact hjk_ne (beq_iff_eq.mp hkj).symm
    have := hlabel_eq (embed b0)
    rw [hlabel_j_b0, hlabel_k_b0] at this
    exact Bool.noConfusion this
  have hT_card : T.card = d + 1 := by
    simp only [T, card_image_of_injective _ hx_inj, card_univ, Fintype.card_fin]
  -- Step 4: Show C shatters T
  have hT_shatters : Shatters X C T := by
    intro f
    -- f : ↥T → Bool. We need to find c ∈ C with c x = f x for all x ∈ T.
    -- Construct the bitstring g : Fin (d+1) → Bool where g(j) = f(x j, ...)
    -- The concept embed(g) (as element of C) does the job.
    -- For each j, (embed g).val (x j) = label j (embed g) = g j
    -- And f(x j) = g j by construction.
    -- We need g(j) = f applied to (x j viewed as element of T).
    -- T = image x of univ, so x j ∈ T, and we need f ⟨x j, mem_image...⟩ = g j.
    -- Define g j = f ⟨x j, _⟩
    have hx_mem : ∀ j : Fin (d + 1), x j ∈ T := by
      intro j; simp only [T]; exact mem_image_of_mem _ (mem_univ _)
    let g : Fin (d + 1) → Bool := fun j => f ⟨x j, hx_mem j⟩
    -- The concept is embed(g), which is an element of S, hence of C
    let cg : ↥C := (embed g).val
    refine ⟨cg.val, cg.property, fun ⟨y, hy⟩ => ?_⟩
    -- y ∈ T means y = x j for some j
    simp only [T] at hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, _, rfl⟩ := hy
    -- Need: cg.val (x j) = f ⟨x j, hx_mem j⟩
    -- cg.val (x j) = (embed g).val.val (x j)
    change cg.val (x j) = f ⟨x j, hx_mem j⟩
    -- By hx j (embed g): (embed g).val.val (x j) = label j (embed g)
    have step1 : (embed g).val.val (x j) = label j (embed g) := hx j (embed g)
    -- label j (embed g) = g j (since embed g is in the image of embed)
    have step2 : label j (embed g) = g j := by
      simp only [label]
      rw [dif_pos ⟨g, rfl⟩]
      have := (⟨g, rfl⟩ : ∃ b, embed b = embed g).choose_spec
      have := hembed_inj this
      rw [this]
    -- g j = f ⟨x j, hx_mem j⟩ by definition
    have step3 : g j = f ⟨x j, hx_mem j⟩ := rfl
    rw [step1, step2, step3]
  exact ⟨T, hT_card, hT_shatters⟩

/-- **Assouad's dual VC bound**: if `VCDim(C) ≤ d`, then the VC dimension of
    the dual class is at most `2^(d+1) - 1`.

    This is tight: the class of all subsets of `{1,...,d}` achieves equality. -/
theorem dual_vcdim_le_pow {d : ℕ} (hd : VCDim X C ≤ ↑d) :
    VCDim ↥C (DualClass X C) ≤ ↑(2 ^ (d + 1) - 1) := by
  -- VCDim is ⨆ over shattered sets. Show each shattered set has card ≤ 2^(d+1) - 1.
  apply iSup₂_le
  intro S hS
  -- Show S.card ≤ 2^(d+1) - 1 in ℕ, then lift
  by_contra hlt
  push Not at hlt
  -- hlt : ↑(2^(d+1) - 1) < ↑S.card, which in WithTop means the nat inequality
  -- Work in ℕ: S.card ≥ 2^(d+1)
  have hge : 2 ^ (d + 1) ≤ S.card := by
    by_contra hlt'
    push Not at hlt'
    -- S.card ≤ 2^(d+1) - 1
    have hle : S.card ≤ 2 ^ (d + 1) - 1 := by omega
    -- Lift to WithTop: need ↑S.card ≤ ↑(2^(d+1) - 1)
    -- Since ↑(2^(d+1) - 1) = ↑(2^(d+1)) - 1 when 2^(d+1) ≥ 1, these are the same
    apply absurd _ (not_le.mpr hlt)
    change (↑S.card : WithTop ℕ) ≤ ↑(2 ^ (d + 1) - 1)
    exact WithTop.coe_le_coe.mpr hle
  obtain ⟨T, hTcard, hTshat⟩ := dual_shatters_imp_original_shatters S hS hge
  -- VCDim X C ≥ d + 1
  have hvc : (↑(d + 1) : WithTop ℕ) ≤ VCDim X C :=
    le_iSup₂_of_le T hTshat (by exact_mod_cast hTcard.ge)
  -- But VCDim X C ≤ d, and d + 1 > d
  have hle : (↑(d + 1) : WithTop ℕ) ≤ ↑d := le_trans hvc hd
  have : d + 1 ≤ d := by exact_mod_cast hle
  omega

end DualVC
