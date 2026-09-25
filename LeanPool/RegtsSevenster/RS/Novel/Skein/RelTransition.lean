/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition

/-!
# Boundary-relative transition systems

For an open fragment `W : Fragment α` and an Eulerian edge
subset that may contain boundary-attached flags, the standard
`TransitionSystem` is too strong: it requires every participating
flag to be internally attached (`attach_internal`).  This file
defines a weaker notion.

## Design

A `RelTransitionSystem W F` for an edge subset `F : EdgeSubset W`
matches the *internal* participating flags pairwise at common
vertices, leaving boundary-attached flags unmatched (they are path
endpoints).

The walk permutation `κ ∘ σ` is well-defined only on internal flags.
Internal circuits are the orbits of this internal walk permutation.

Paths connect boundary flags in pairs: starting from a boundary flag
`b`, follow the edge pairing `σ` to the partner `σ b` (internal),
then apply matching `κ`, then `σ` again, alternating until reaching
another boundary flag.  The resulting pairing is `pathMatch`.

### Representation choice for the gluing theorem

The path matching is an involution on boundary s-flags.  For the
eventual gluing decomposition:

  `circuitCount(glued) = internalCircuitCount(F) +
     internalCircuitCount(G) + cycleCount(pathMatch_G ∘ pathMatch_F)`

the composition of two path matchings produces closed cycles that
become "cross-boundary" circuits.  Representing `pathMatch` as an
involution on boundary flags makes this composition natural.

For a closed fragment (no boundary flags), `RelTransitionSystem`
degenerates to `TransitionSystem` and `internalCircuitCount` equals
`circuitCount`.
-/

@[expose] public section

namespace RS



variable {α : Type}

namespace EdgeSubset

variable {W : Fragment α}

/-! ## Internal vs boundary flag classification -/

open scoped Classical in
/-- The internal flags of an edge subset: participating flags attached
to a vertex. -/
noncomputable def internalFlags (F : EdgeSubset W) : Finset W.Flag :=
  F.flags.filter (fun f => ∃ v : W.Vertex, W.attach f = Sum.inl v)

open scoped Classical in
/-- A flag is internal exactly when it is in the subset and attached
to a vertex. -/
theorem mem_internalFlags_iff {f : W.Flag} {F : EdgeSubset W} :
    f ∈ F.internalFlags ↔ f ∈ F.flags ∧
      ∃ v : W.Vertex, W.attach f = Sum.inl v :=
  Finset.mem_filter

open scoped Classical in
/-- The boundary flags of an edge subset: participating flags attached
to a boundary label. -/
noncomputable def boundaryFlags (F : EdgeSubset W) : Finset W.Flag :=
  F.flags.filter (fun f => ∃ i : α, W.attach f = Sum.inr i)

open scoped Classical in
/-- Every participating flag is either internal or boundary. -/
theorem mem_internalFlags_or_boundaryFlags (F : EdgeSubset W)
    {f : W.Flag} (hf : f ∈ F.flags) :
    f ∈ F.internalFlags ∨ f ∈ F.boundaryFlags := by
  rcases ha : W.attach f with v | i
  · left; exact Finset.mem_filter.mpr ⟨hf, v, ha⟩
  · right; exact Finset.mem_filter.mpr ⟨hf, i, ha⟩

/-- Internal and boundary flags are disjoint. -/
theorem internalFlags_disjoint_boundaryFlags (F : EdgeSubset W) :
    Disjoint F.internalFlags F.boundaryFlags := by
  classical
  unfold internalFlags boundaryFlags
  rw [Finset.disjoint_filter]
  intro f _ ⟨v, hv⟩ ⟨i, hi⟩
  rw [hv] at hi; cases hi

open scoped Classical in
/-- An internal flag is in the edge subset. -/
theorem mem_flags_of_internalFlags (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∈ F.internalFlags) : f ∈ F.flags :=
  (Finset.mem_filter.mp hf).1

open scoped Classical in
/-- A boundary flag is in the edge subset. -/
theorem mem_flags_of_boundaryFlags (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∈ F.boundaryFlags) : f ∈ F.flags :=
  (Finset.mem_filter.mp hf).1

open scoped Classical in
/-- An internal flag is attached to some vertex. -/
theorem attach_internal_of_mem (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∈ F.internalFlags) : ∃ v : W.Vertex, W.attach f = Sum.inl v :=
  (Finset.mem_filter.mp hf).2

open scoped Classical in
/-- A boundary flag is attached to some label. -/
theorem attach_boundary_of_mem (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∈ F.boundaryFlags) : ∃ i : α, W.attach f = Sum.inr i :=
  (Finset.mem_filter.mp hf).2

/-- A participating boundary flag lies in the boundary flags: it
attaches to a label, so it cannot be internal. -/
theorem boundaryFlag_mem_boundaryFlags {F : EdgeSubset W} {a : α}
    (hf : W.boundaryFlag a ∈ F.flags) :
    W.boundaryFlag a ∈ F.boundaryFlags := by
  rcases mem_internalFlags_or_boundaryFlags F hf with hint | hbd
  · obtain ⟨v, hv⟩ := attach_internal_of_mem F hint
    rw [W.attach_boundaryFlag a] at hv
    cases hv
  · exact hbd

/-- All participating flags are internal (no boundary flags). -/
def allInternal (F : EdgeSubset W) : Prop := F.boundaryFlags = ∅

/-- When all flags are internal, a participating flag is internal. -/
theorem mem_internalFlags_of_allInternal {F : EdgeSubset W}
    (hall : F.allInternal) {f : W.Flag} (hf : f ∈ F.flags) :
    f ∈ F.internalFlags := by
  rcases F.mem_internalFlags_or_boundaryFlags hf with h | h
  · exact h
  · exact absurd h (Finset.eq_empty_iff_forall_notMem.mp hall _)

/-! ## Boundary-relative transition system -/

/-- A boundary-relative transition system on an edge subset: a
fixed-point-free involution of its *internal* flags matching flags at
a common vertex.  Boundary flags are path endpoints and are not
matched.  This mirrors `TransitionSystem` but restricts the domain
from all participating flags to internal flags only. -/
structure RelTransitionSystem (F : EdgeSubset W) where
  /-- The matching, defined on all flags but only meaningful on
  internal participating flags. -/
  match_ : W.Flag → W.Flag
  /-- The matching is an involution on the internal flags. -/
  match_invol : ∀ f ∈ F.internalFlags, match_ (match_ f) = f
  /-- The matching has no fixed points on internal flags. -/
  match_ne : ∀ f ∈ F.internalFlags, match_ f ≠ f
  /-- The matching maps internal flags to internal flags. -/
  match_mem : ∀ f ∈ F.internalFlags, match_ f ∈ F.internalFlags
  /-- Matched flags share an internal vertex. -/
  match_vertex : ∀ f ∈ F.internalFlags, ∀ v : W.Vertex,
    W.attach f = Sum.inl v → W.attach (match_ f) = Sum.inl v

/-! ## Compatibility: conversions -/

open scoped Classical in
/-- A participating flag that is internally attached is an internal
flag. -/
theorem mem_internalFlags_of {F : EdgeSubset W} {f : W.Flag}
    (hf : f ∈ F.flags) (hv : ∃ v : W.Vertex, W.attach f = Sum.inl v) :
    f ∈ F.internalFlags := by
  exact Finset.mem_filter.mpr ⟨hf, hv⟩

open scoped Classical in
/-- Every `TransitionSystem` is a `RelTransitionSystem`. -/
def TransitionSystem.toRelTransitionSystem {F : EdgeSubset W}
    (κ : F.TransitionSystem) : F.RelTransitionSystem where
  match_ := κ.match_
  match_invol := fun f hf => κ.match_invol f (mem_flags_of_internalFlags F hf)
  match_ne := fun f hf => κ.match_ne f (mem_flags_of_internalFlags F hf)
  match_mem := fun f hf => by
    have hf' := mem_flags_of_internalFlags F hf
    refine Finset.mem_filter.mpr ⟨κ.match_mem f hf', ?_⟩
    obtain ⟨v, hv⟩ := attach_internal_of_mem F hf
    exact ⟨v, κ.match_vertex f hf' v hv⟩
  match_vertex := fun f hf => κ.match_vertex f (mem_flags_of_internalFlags F hf)

/-! ## Walk and circuit count on internal flags -/

/-- The walk map on flags via a relative transition: follow pairing
then matching. -/
noncomputable def RelTransitionSystem.internalWalk {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) (f : W.Flag) : W.Flag :=
  κ.match_ (W.pairing f)

/-- If a flag's pairing is internal, its walk successor is internal. -/
theorem RelTransitionSystem.internalWalk_mem {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) {f : W.Flag}
    (hp : W.pairing f ∈ F.internalFlags) :
    κ.internalWalk f ∈ F.internalFlags :=
  κ.match_mem _ hp

/-- The walk map is injective on flags whose pairings are internal. -/
theorem RelTransitionSystem.internalWalk_injOn {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) {f g : W.Flag}
    (hpf : W.pairing f ∈ F.internalFlags)
    (hpg : W.pairing g ∈ F.internalFlags)
    (h : κ.internalWalk f = κ.internalWalk g) : f = g := by
  have h' : κ.match_ (W.pairing f) = κ.match_ (W.pairing g) := h
  have h1 := κ.match_invol _ hpf
  have h2 := κ.match_invol _ hpg
  have hm : W.pairing f = W.pairing g :=
    calc W.pairing f = κ.match_ (κ.match_ (W.pairing f)) := h1.symm
      _ = κ.match_ (κ.match_ (W.pairing g)) := by rw [h']
      _ = W.pairing g := h2
  calc f = W.pairing (W.pairing f) := (W.pairing_invol f).symm
    _ = W.pairing (W.pairing g) := by rw [hm]
    _ = g := W.pairing_invol g

/-- When all flags are internal, the pairing of an internal flag is
internal. -/
theorem RelTransitionSystem.pairing_internal_of_allInternal
    {F : EdgeSubset W} (_κ : F.RelTransitionSystem)
    (hall : F.allInternal) {f : W.Flag} (hf : f ∈ F.internalFlags) :
    W.pairing f ∈ F.internalFlags :=
  mem_internalFlags_of_allInternal hall (F.pairing_mem f
    (mem_flags_of_internalFlags F hf))

/-- When all flags are internal, the walk preserves internal flags. -/
theorem RelTransitionSystem.internalWalk_mem_of_allInternal
    {F : EdgeSubset W} (κ : F.RelTransitionSystem)
    (hall : F.allInternal) {f : W.Flag} (hf : f ∈ F.internalFlags) :
    κ.internalWalk f ∈ F.internalFlags :=
  κ.internalWalk_mem (κ.pairing_internal_of_allInternal hall hf)

/-- When all flags are internal, the walk is injective. -/
theorem RelTransitionSystem.internalWalk_injOn_of_allInternal
    {F : EdgeSubset W} (κ : F.RelTransitionSystem)
    (hall : F.allInternal) {f g : W.Flag}
    (hf : f ∈ F.internalFlags) (hg : g ∈ F.internalFlags)
    (h : κ.internalWalk f = κ.internalWalk g) : f = g :=
  κ.internalWalk_injOn
    (κ.pairing_internal_of_allInternal hall hf)
    (κ.pairing_internal_of_allInternal hall hg) h

/-- The walk permutation on internal flags, when all flags are
internal. -/
noncomputable def RelTransitionSystem.walkPermInternal
    {F : EdgeSubset W} (κ : F.RelTransitionSystem)
    (hall : F.allInternal) :
    Equiv.Perm {f : W.Flag // f ∈ F.internalFlags} :=
  Equiv.ofBijective
    (fun f => ⟨κ.internalWalk f.val,
      κ.internalWalk_mem_of_allInternal hall f.prop⟩)
    (Finite.injective_iff_bijective.mp
      (fun f g h => Subtype.ext
        (κ.internalWalk_injOn_of_allInternal hall f.prop g.prop
          (congrArg Subtype.val h))))

/-- The internal circuit count when all flags are internal. -/
noncomputable def RelTransitionSystem.internalCircuitCount
    {F : EdgeSubset W} (κ : F.RelTransitionSystem)
    (hall : F.allInternal) : ℕ :=
  ((κ.walkPermInternal hall).cycleType.card +
    Fintype.card (Function.fixedPoints (κ.walkPermInternal hall))) / 2

/-! ## Compatibility: circuit-count agreement for closed subsets -/

open scoped Classical in
/-- When a `TransitionSystem` exists (all flags internal), the internal
flags equal the full flag set. -/
theorem internalFlags_eq_flags_of_transition {F : EdgeSubset W}
    (κ : F.TransitionSystem) : F.internalFlags = F.flags := by
  ext f; constructor
  · exact fun hf => mem_flags_of_internalFlags F hf
  · intro hf; exact Finset.mem_filter.mpr ⟨hf, κ.attach_internal f hf⟩

/-- A standard `TransitionSystem` implies all flags are internal. -/
theorem allInternal_of_transition {F : EdgeSubset W}
    (κ : F.TransitionSystem) : F.allInternal := by
  unfold allInternal
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  obtain ⟨i, hi⟩ := attach_boundary_of_mem F hf
  obtain ⟨v, hv⟩ := κ.attach_internal f (mem_flags_of_boundaryFlags F hf)
  rw [hv] at hi; cases hi

/-- The equivalence between full-flag and internal-flag subtypes when
all flags are internal. -/
noncomputable def flagsEquivInternal {F : EdgeSubset W}
    (κ : F.TransitionSystem) :
    {f : W.Flag // f ∈ F.flags} ≃
      {f : W.Flag // f ∈ F.internalFlags} where
  toFun f := ⟨f.val, by
    rw [internalFlags_eq_flags_of_transition κ]; exact f.prop⟩
  invFun f := ⟨f.val, mem_flags_of_internalFlags F f.prop⟩
  left_inv f := Subtype.ext rfl
  right_inv f := Subtype.ext rfl

/-- The walk permutations agree under the canonical equivalence. -/
theorem walkPerm_eq_of_transition {F : EdgeSubset W}
    (κ : F.TransitionSystem) :
    κ.toRelTransitionSystem.walkPermInternal (allInternal_of_transition κ) =
      (flagsEquivInternal κ).permCongr κ.walkPerm := by
  ext ⟨f, hf⟩
  show (κ.toRelTransitionSystem.walkPermInternal _ ⟨f, hf⟩).val =
    ((flagsEquivInternal κ).permCongr κ.walkPerm ⟨f, hf⟩).val
  simp only [RelTransitionSystem.walkPermInternal, Equiv.ofBijective_apply,
    Equiv.permCongr_apply, flagsEquivInternal]
  change κ.match_ (W.pairing f) = κ.walk f
  rfl

/-- **Compatibility**: for a closed-fragment transition system,
`internalCircuitCount` equals `circuitCount`. -/
theorem relTransition_circuitCount_eq {F : EdgeSubset W}
    (κ : F.TransitionSystem) :
    κ.toRelTransitionSystem.internalCircuitCount
      (allInternal_of_transition κ) = κ.circuitCount := by
  unfold RelTransitionSystem.internalCircuitCount
    TransitionSystem.circuitCount
  rw [walkPerm_eq_of_transition κ, cycleType_permCongr,
    card_fixedPoints_permCongr]

/-! ## Orientation for relative transition systems -/

/-- An orientation compatible with a boundary-relative transition
system: an in/out designation of the internal flags, flipped by the
matching and by the edge pairing (when both ends are internal). -/
structure RelTransitionSystem.Orientation {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) where
  /-- Whether a flag is outgoing. -/
  isOut : W.Flag → Bool
  /-- The matching flips orientation on internal flags. -/
  match_flip : ∀ f ∈ F.internalFlags, isOut (κ.match_ f) = !isOut f
  /-- The pairing flips orientation on internal flags whose partner is
  also internal. -/
  pairing_flip : ∀ f ∈ F.internalFlags,
    W.pairing f ∈ F.internalFlags →
    isOut (W.pairing f) = !isOut f

/-! ## Path chain tracing -/

/-- Follow the chain from a flag: apply pairing, check if boundary;
if internal, apply matching and recurse.  Returns `none` if the fuel
runs out. -/
noncomputable def traceChain {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) : ℕ → W.Flag → Option W.Flag
  | 0, _ => none
  | n + 1, f =>
    let f' := W.pairing f
    if f' ∈ F.boundaryFlags then some f'
    else if _hf' : f' ∈ F.internalFlags then
      traceChain κ n (κ.match_ f')
    else none

end EdgeSubset

end RS
