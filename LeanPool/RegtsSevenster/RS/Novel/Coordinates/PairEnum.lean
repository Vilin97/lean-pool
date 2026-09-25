/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionExists

/-!
# The pair enumeration

The Definition 5 odd list at a vertex is, order-exactly, the
per-flag value map over an explicit flag list: the incoming flags
in the fixed order, each followed by its match.
-/

namespace RS

open Finset

variable {α : Type} {W : Fragment α} {F : EdgeSubset W} {ℓ : ℕ}
  {κ : F.TransitionSystem}

open Classical in
/-- The Definition 5 per-flag odd value: outgoing flags carry the
partner of their colour, incoming flags the colour itself. -/
noncomputable def defFiveValue (o : κ.Orientation)
    (φ : F.OddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.flags}) : Fin (2 * ℓ) :=
  if o.isOut f.val = true then oddPartner ℓ (φ.val f)
  else φ.val f

/-- Incoming flags are incoming. -/
theorem isOut_of_mem_inFlagsAt (o : κ.Orientation)
    {v : W.Vertex} {f : W.Flag}
    (hf : f ∈ F.inFlagsAt o v) : o.isOut f = false := by
  let := W.flagOrder
  let := Classical.dec
  unfold EdgeSubset.inFlagsAt at hf
  exact (Finset.mem_filter.mp
    ((Finset.mem_sort _).mp hf)).2.2

private theorem map_flatMap' {γ δ ε : Type*} (l : List γ)
    (g : γ → List δ) (h : δ → ε) :
    (l.flatMap g).map h = l.flatMap (fun x => (g x).map h) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append,
      ih]

private theorem flatMap_congr' {γ δ : Type*} (l : List γ)
    (g₁ g₂ : γ → List δ) (h : ∀ x ∈ l, g₁ x = g₂ x) :
    l.flatMap g₁ = l.flatMap g₂ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.flatMap_cons, List.flatMap_cons,
      h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

open Classical in
/-- The flag list underlying the odd list at a vertex: the
incoming flags in the fixed order, each followed by its match. -/
noncomputable def pairFlagList (o : κ.Orientation)
    (v : W.Vertex) : List {f : W.Flag // f ∈ F.flags} :=
  ((F.inFlagsAt o v).attachWith (· ∈ F.flags)
    (fun _ hf => F.mem_of_mem_inFlagsAt hf)).flatMap
    (fun f => [f, ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩])

open Classical in
/-- **The odd list is the value map of the pair enumeration**,
order-exactly. -/
theorem oddListAt_eq_map (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W.Vertex) :
    F.oddListAt o φ v =
      (pairFlagList (F := F) o v).map (defFiveValue o φ) := by
  rw [EdgeSubset.oddListAt, pairFlagList, map_flatMap']
  refine flatMap_congr' _ _ _ ?_
  intro f hf
  have hfin : f.val ∈ F.inFlagsAt o v := by
    rw [show (F.inFlagsAt o v).attachWith (· ∈ F.flags)
        (fun _ hf' => F.mem_of_mem_inFlagsAt hf') =
      (F.inFlagsAt o v).pmap Subtype.mk
        (fun _ hf' => F.mem_of_mem_inFlagsAt hf') from rfl]
      at hf
    obtain ⟨a, ha, hfa⟩ := List.mem_pmap.mp hf
    rw [← hfa]
    exact ha
  have hin : o.isOut f.val = false :=
    isOut_of_mem_inFlagsAt o hfin
  have hout : o.isOut (κ.match_ f.val) = true := by
    rw [o.match_flip f.val f.prop, hin]
    rfl
  have h1 : defFiveValue o φ f = φ.val f := by
    rw [defFiveValue, hin]
    rw [ite_eq_right Bool.false_ne_true]
  have h2 : defFiveValue o φ
      ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩ =
      oddPartner ℓ (φ.val
        ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩) := by
    rw [defFiveValue, ite_eq_left hout]
  change F.oddPairFn κ φ f = _
  rw [EdgeSubset.oddPairFn, List.map_cons, List.map_cons,
    List.map_nil, h1, h2]

end RS
