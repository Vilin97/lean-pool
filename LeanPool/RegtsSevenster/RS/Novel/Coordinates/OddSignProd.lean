/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionExists

/-!
# Product of odd signs over vertices equals product over outgoing flags
-/

@[expose] public section

namespace RS

open Finset
variable {α : Type} {W : Fragment α} {F : EdgeSubset W} {ℓ : ℕ}
  {κ : F.TransitionSystem}

/-! ### Helpers -/

/-- The oddSignFn lifted to bare flags using classical membership. -/
private noncomputable def EdgeSubset.oddSignFn' (F : EdgeSubset W)
    (κ : F.TransitionSystem) (φ : F.OddColouring ℓ)
    (f : W.Flag) : ℤ :=
  if h : f ∈ F.flags then F.oddSignFn κ φ ⟨f, h⟩ else 1

private theorem EdgeSubset.oddSignFn'_eq_of_mem
    (φ : F.OddColouring ℓ) {f : W.Flag} (hf : f ∈ F.flags) :
    F.oddSignFn' κ φ f = F.oddSignFn κ φ ⟨f, hf⟩ := by
  unfold EdgeSubset.oddSignFn'; exact dite_eq_left hf

/-- The attachWith-map list equals a plain map with classically
lifted function. -/
private theorem EdgeSubset.attachWith_map_oddSignFn_eq
    (φ : F.OddColouring ℓ) (l : List W.Flag)
    (H : ∀ x ∈ l, x ∈ F.flags) :
    (l.attachWith (· ∈ F.flags) H).map (F.oddSignFn κ φ) =
      l.map (F.oddSignFn' κ φ) := by
  rw [show l.attachWith (· ∈ F.flags) H =
    l.pmap Subtype.mk H from rfl, List.map_pmap]
  rw [show List.pmap (fun a (h : a ∈ F.flags) => F.oddSignFn κ φ ⟨a, h⟩)
        l H =
      List.pmap (fun a (_ : a ∈ F.flags) => F.oddSignFn' κ φ a) l H from
    List.pmap_congr_left _ (fun a _ h₁ _ =>
      (F.oddSignFn'_eq_of_mem φ h₁).symm)]
  exact List.pmap_eq_map H

open scoped Classical in
/-- `inFlagsAt` is a permutation of the filter's `toList`. -/
private theorem EdgeSubset.inFlagsAt_perm_filter_toList
    (o : κ.Orientation) (v : W.Vertex) :
    List.Perm (F.inFlagsAt o v)
      ((F.flags.filter
        (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false)).toList) := by
  unfold EdgeSubset.inFlagsAt
  let := W.flagOrder
  -- The unfolded LHS sort uses `fun a b => dec (a ≤ b)` from the
  -- `letI := Classical.dec` inside inFlagsAt, while the ambient
  -- instance is `LinearOrder.toDecidableLE`. Similarly, the filter
  -- uses `fun a => dec (...)` vs the ambient DecidablePred.
  -- Since Decidable is a Subsingleton, convert handles the gap.
  convert Finset.sort_perm_toList
    (F.flags.filter
      (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false))
    (· ≤ ·) using 2
  congr

/-! ### Step 1: oddSignAt as a Finset product -/

open scoped Classical in
/-- The list-based oddSignAt equals the finset product over the
filter of F.flags. -/
private theorem EdgeSubset.oddSignAt_eq_filter_prod
    (o : κ.Orientation) (φ : F.OddColouring ℓ) (v : W.Vertex) :
    F.oddSignAt o φ v =
      ∏ f ∈ F.flags.filter
        (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false),
        F.oddSignFn' κ φ f := by
  unfold EdgeSubset.oddSignAt
  rw [F.attachWith_map_oddSignFn_eq φ _ (fun f hf =>
    F.mem_of_mem_inFlagsAt hf)]
  rw [show (∏ f ∈ F.flags.filter
      (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false),
      F.oddSignFn' κ φ f) =
    ((F.flags.filter
      (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false)).toList.map
      (F.oddSignFn' κ φ)).prod from
    (Finset.prod_map_toList _ _).symm]
  exact ((F.inFlagsAt_perm_filter_toList o v).map _).prod_eq

/-! ### Step 2: product over vertices, then swap and collapse -/

/-- The product of oddSignAt over all vertices equals the product
of oddSignFn' over all participating flags with the incoming
condition. -/
private theorem EdgeSubset.prod_oddSignAt_eq_prod_flags_incoming
    (o : κ.Orientation) (φ : F.OddColouring ℓ) :
    (∏ v : W.Vertex, F.oddSignAt o φ v) =
      ∏ f ∈ F.flags,
        (if o.isOut f = false
         then F.oddSignFn' κ φ f else 1) := by
  classical
  simp_rw [F.oddSignAt_eq_filter_prod o φ, Finset.prod_filter]
  rw [show (∏ v : W.Vertex, ∏ f ∈ F.flags,
      if W.attach f = Sum.inl v ∧ o.isOut f = false then
        F.oddSignFn' κ φ f else 1) =
    ∏ f ∈ F.flags, ∏ v : W.Vertex,
      if W.attach f = Sum.inl v ∧ o.isOut f = false then
        F.oddSignFn' κ φ f else 1 from
    Finset.prod_comm]
  congr 1; ext f
  by_cases hf : f ∈ F.flags
  · obtain ⟨vf, hvf⟩ := κ.attach_internal f hf
    rw [Fintype.prod_eq_single vf]
    · simp [hvf]
    · intro v hv
      have : ¬(W.attach f = Sum.inl v ∧ o.isOut f = false) := by
        intro ⟨hatt, _⟩
        exact hv (Sum.inl.inj (hatt ▸ hvf))
      simp [this]
  · have hone : F.oddSignFn' κ φ f = 1 := by
      unfold EdgeSubset.oddSignFn'; rw [dite_eq_right hf]
    simp [hone]

/-! ### Step 3: incoming to subtype, then reindex -/

/-- Main theorem: the product over vertices of the Definition-5 odd
signs is the product of partner signs over the outgoing participating
flags. -/
theorem prod_oddSignAt (o : κ.Orientation) (φ : F.OddColouring ℓ) :
    (∏ v : W.Vertex, F.oddSignAt o φ v) =
      ∏ f : {f : W.Flag // f ∈ F.flags},
        (if o.isOut f.val = true then oddPartnerSign ℓ (φ.val f) else 1) := by
  rw [F.prod_oddSignAt_eq_prod_flags_incoming o φ]
  rw [show (∏ f ∈ F.flags,
      (if o.isOut f = false then F.oddSignFn' κ φ f else 1)) =
    ∏ f : {f : W.Flag // f ∈ F.flags},
      (if o.isOut f.val = false then F.oddSignFn κ φ f else 1) from by
    rw [← Finset.prod_attach]
    congr 1; ext ⟨f, hf⟩
    split <;> [exact F.oddSignFn'_eq_of_mem φ hf; rfl]]
  let e : {f : W.Flag // f ∈ F.flags} ≃ {f : W.Flag // f ∈ F.flags} :=
    ⟨fun f => ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩,
     fun f => ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩,
     fun f => Subtype.ext (κ.match_invol _ f.prop),
     fun f => Subtype.ext (κ.match_invol _ f.prop)⟩
  rw [← Equiv.prod_comp e]
  congr 1; ext f
  simp only [e, Equiv.coe_fn_mk]
  rw [o.match_flip _ f.prop]
  cases hb : o.isOut f.val <;> simp only [Bool.not_false, Bool.true_eq_false, ↓reduceIte,
    Bool.false_eq_true, Bool.not_true]
  · unfold EdgeSubset.oddSignFn
    congr 1
    exact congrArg φ.val (Subtype.ext (κ.match_invol _ f.prop))

end RS
