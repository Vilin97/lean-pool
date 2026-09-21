/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.RelValue
import LeanPool.RegtsSevenster.RS.Novel.Skein.OpenCircuits

/-!
# Through-edges and the corrected constrained value

A participating edge of an open fragment both of whose flags are
boundary flags (a *through-edge*) carries no vertex data; its two
ends must take independent state colours, paired by the symplectic
copairing — full pairing-constancy of the odd colouring would
force the two ends equal, exactly where the symplectic weight
vanishes.  This file splits the participating flags into core and
through parts, restricts the odd colouring to the core, and
defines the corrected constrained summand: the core colouring sum
times an explicit symplectic factor per through-edge, oriented by
the label order.

Even colourings stay fully pairing-constant: the even gluing
weight is diagonal, which pairing-constancy implements already.
-/

namespace RS

variable {α : Type} {W : Fragment α}

namespace EdgeSubset

/-! ## Core and through flags -/

open scoped Classical in
/-- The through-flags: participating flags on boundary–boundary
edges. -/
noncomputable def throughFlags (F : EdgeSubset W) : Finset W.Flag :=
  F.flags.filter (fun f => (∃ i : α, W.attach f = Sum.inr i) ∧
    (∃ j : α, W.attach (W.pairing f) = Sum.inr j))

/-- The core flags: participating flags on edges with at least one
internal end. -/
noncomputable def coreFlags (F : EdgeSubset W) : Finset W.Flag :=
  F.flags \ F.throughFlags

/-- Core flags participate. -/
theorem coreFlags_subset (F : EdgeSubset W) :
    F.coreFlags ⊆ F.flags :=
  Finset.sdiff_subset

open scoped Classical in
/-- A participating flag is core when it or its edge partner meets
a vertex — through-edges, meeting none, are excluded. -/
theorem mem_coreFlags_iff (F : EdgeSubset W) {f : W.Flag} :
    f ∈ F.coreFlags ↔ f ∈ F.flags ∧
      ((∃ v : W.Vertex, W.attach f = Sum.inl v) ∨
        (∃ v : W.Vertex, W.attach (W.pairing f) = Sum.inl v)) := by
  unfold coreFlags throughFlags
  rw [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hf, hnot⟩
    refine ⟨hf, ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    refine hnot ⟨hf, ?_, ?_⟩
    · rcases hx : W.attach f with v | i
      · exact absurd hx (h1 v)
      · exact ⟨i, rfl⟩
    · rcases hx : W.attach (W.pairing f) with v | i
      · exact absurd hx (h2 v)
      · exact ⟨i, rfl⟩
  · rintro ⟨hf, hor⟩
    refine ⟨hf, fun hthr => ?_⟩
    obtain ⟨_, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hthr
    rcases hor with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [hv] at hi; cases hi
    · rw [hv] at hj; cases hj

/-- The pairing preserves the core flags. -/
theorem pairing_mem_coreFlags (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∈ F.coreFlags) : W.pairing f ∈ F.coreFlags := by
  rw [mem_coreFlags_iff] at hf ⊢
  refine ⟨F.pairing_mem _ hf.1, ?_⟩
  rcases hf.2 with h | h
  · right; rwa [W.pairing_invol]
  · left; exact h

/-- Internal flags are core flags. -/
theorem internalFlags_subset_coreFlags (F : EdgeSubset W) :
    F.internalFlags ⊆ F.coreFlags := by
  classical
  intro f hf
  rw [mem_coreFlags_iff]
  have h := Finset.mem_filter.mp hf
  exact ⟨h.1, Or.inl h.2⟩

/-! ## The core odd colouring -/

/-- Odd colourings of the core: pairing-constant colours on the
participating flags of edges with an internal end. -/
def CoreOddColouring (F : EdgeSubset W) (ℓ : ℕ) : Type :=
  {φ : {f : W.Flag // f ∈ F.coreFlags} → Fin (2 * ℓ) //
    ∀ f : {f : W.Flag // f ∈ F.coreFlags},
      φ ⟨W.pairing f.val, F.pairing_mem_coreFlags f.prop⟩ = φ f}

open scoped Classical in
/-- Core odd colourings are finite in number, so the summand's sum
over them is a finite sum. -/
noncomputable instance CoreOddColouring.instFintype
    (F : EdgeSubset W) (ℓ : ℕ) : Fintype (F.CoreOddColouring ℓ) := by
  unfold CoreOddColouring
  infer_instance

/-! ## Vertex-local data over the core colouring -/

open Classical in
/-- The odd pair contributed by an incoming internal flag, from the
core colouring. -/
noncomputable def coreOddPairFn (F : EdgeSubset W) {ℓ : ℕ}
    (κ : F.RelTransitionSystem) (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) :
    List (Fin (2 * ℓ)) :=
  [φ.val ⟨f.val, F.internalFlags_subset_coreFlags f.prop⟩,
    oddPartner ℓ (φ.val ⟨κ.match_ f.val,
      F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop)⟩)]

open Classical in
/-- The odd-pairing sign contributed by an incoming internal flag,
from the core colouring. -/
noncomputable def coreOddSignFn (F : EdgeSubset W) {ℓ : ℕ}
    (κ : F.RelTransitionSystem) (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) : ℤ :=
  oddPartnerSign ℓ (φ.val ⟨κ.match_ f.val,
    F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop)⟩)

open Classical in
/-- The odd-colour list at a vertex, from the core colouring. -/
noncomputable def coreOddListAt (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) :
    List (Fin (2 * ℓ)) :=
  ((F.relInFlagsAt o v).attachWith (· ∈ F.internalFlags)
      (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)).flatMap
    (F.coreOddPairFn κ φ)

open Classical in
/-- The odd-pairing sign at a vertex, from the core colouring. -/
noncomputable def coreOddSignAt (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) : ℤ :=
  (((F.relInFlagsAt o v).attachWith (· ∈ F.internalFlags)
      (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)).map
    (F.coreOddSignFn κ φ)).prod

end EdgeSubset

/-! ## The through-edge symplectic factor -/

/-- The symplectic copairing weight of an odd through-edge: nonzero
exactly on partner colours, with the partner sign of the
lower-label end.  (The sign convention is validated by the strand
identity in the gluing decomposition.) -/
noncomputable def oddThroughFactor (ℓ : ℕ)
    (c c' : Fin (2 * ℓ)) : ℂ :=
  if c' = oddPartner ℓ c then (oddPartnerSign ℓ c : ℂ) else 0

/-- The state weight of a through-edge, by the parity of its two
end states: diagonal on even colours, symplectic on odd colours,
zero on mixed parities. -/
noncomputable def throughStateFactor {k ℓ : ℕ}
    (c c' : Fin k ⊕ Fin (2 * ℓ)) : ℂ :=
  match c, c' with
  | Sum.inl a, Sum.inl a' => if a' = a then 1 else 0
  | Sum.inr b, Sum.inr b' => oddThroughFactor ℓ b b'
  | _, _ => 0

namespace EdgeSubset

open scoped Classical in
/-- The through-edge state weight of an edge subset: each
through-edge contributes its state factor exactly once, from its
lower-label flag. -/
noncomputable def throughProduct [LinearOrder α] {k ℓ : ℕ}
    (F : EdgeSubset W) (st : GenBoundaryState k ℓ α) : ℂ :=
  ∏ f ∈ F.throughFlags.attach,
    match W.attach f.val, W.attach (W.pairing f.val) with
    | Sum.inr i, Sum.inr j =>
        if i < j then throughStateFactor (st i) (st j) else 1
    | _, _ => 1

/-- The core odd boundary constraint: the state's odd colours are
imposed on the core boundary flags (through-edges are constrained
by the through factor instead). -/
def coreOddBoundaryMatch {k ℓ : ℕ} (F : EdgeSubset W)
    (st : GenBoundaryState k ℓ α)
    (φ : F.CoreOddColouring ℓ) : Prop :=
  ∀ (i : α) (c : Fin (2 * ℓ)) (_ : st i = Sum.inr c)
    (hcore : W.boundaryFlag i ∈ F.coreFlags),
    φ.val ⟨W.boundaryFlag i, hcore⟩ = c

open Classical in
/-- **The corrected constrained summand**: circuit sign, through
factor, and the core colouring sum. -/
noncomputable def throughSummand [LinearOrder α]
    (F : EdgeSubset W) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) (c : ℕ) : ℂ :=
  ((-1 : ℂ) ^ c) * F.throughProduct st *
    ∑ ψ : F.EvenColouring k,
      if genEvenBoundaryMatch F st hbnd ψ then
        ∑ φ : F.CoreOddColouring ℓ,
          if F.coreOddBoundaryMatch st φ then
            ∏ v : W.Vertex,
              ((F.coreOddSignAt o φ v : ℂ) *
                h.evalOdd (F.evenColoursAt ψ v)
                  (F.coreOddListAt o φ v))
          else 0
      else 0

end EdgeSubset

end RS
