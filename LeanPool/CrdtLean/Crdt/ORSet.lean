/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import LeanPool.CrdtLean.Crdt.Defs
import LeanPool.CrdtLean.Crdt.Convergence
import LeanPool.CrdtLean.Crdt.Liveness


/-!
# The OR-Set (Observed-Remove Set) — an add-wins CRDT

`Crdt.Instances` discharges the *easy* CvRDT instances (G-Set, counters), where the
lattice carries everything and `merge` is plainly correct. This file does the **hard**
one: the **OR-Set**, the CRDT whose merge logic is genuinely subtle and where naive
designs (the 2P-Set) ship the wrong behaviour.

The classic failure: with a plain grow-only set you can never remove; with a 2P-Set
(add-set + remove-set of *elements*) a removed element can never be re-added — and a
*concurrent* add and remove resolves to absent, losing the add. The OR-Set fixes this by
tagging every add with a **unique token** and tombstoning *tokens*, not elements. A
remove only tombstones the tokens it has **observed**; a concurrent add mints a fresh
token the remove never saw, so the add **wins**.

## Model

State is a pair of grow-only sets: `adds : Finset (α × τ)` (element tagged with a unique
token) and `removed : Finset τ` (tombstoned tokens). As a product of two G-Sets it is a
`SemilatticeSup` with `OrderBot`, so `merge = ⊔` is componentwise union and the library's
Strong Eventual Consistency + liveness theorems apply **for free**. The content of this
file is the *semantic* layer on top: what `lookup` returns, and the add-wins guarantee.

## What is actually proved (the moat)

* `add_wins` — a fresh add merged with a concurrent remove of the same element leaves the
  element **present**. This is the defining OR-Set property and the one a 2P-Set gets
  wrong.
* `remove_lookup_false` — absent a concurrent add, remove genuinely removes.
* `add_lookup` — a fresh add makes the element present.
* SEC + eventual agreement, inherited unchanged from the abstract carrier.
-/

namespace Crdt.ORSet

variable {α τ : Type*} [DecidableEq α] [DecidableEq τ]

/-- OR-Set state: observed add-instances (each an element paired with a unique token)
and a grow-only tombstone set of removed tokens. A product of two grow-only sets. -/
abbrev State (α τ : Type*) := Finset (α × τ) × Finset τ

/-- The product carrier is a lawful CvRDT carrier with no extra work — so SEC and
liveness apply to the OR-Set unchanged. -/
example : SemilatticeSup (State α τ) := inferInstance
example : OrderBot (State α τ) := inferInstance
example : DecidableEq (State α τ) := inferInstance

/-- The tokens currently observed for element `a`: the second components of all
add-instances of `a`. -/
def observedTokens (s : State α τ) (a : α) : Finset τ :=
  (s.1.filter (fun p => p.1 = a)).image Prod.snd

/-- The elements currently in the set: those with at least one add-token that has not
been tombstoned. -/
def elements (s : State α τ) : Finset α :=
  (s.1.filter (fun p => p.2 ∉ s.2)).image Prod.fst

/-- Membership: `a` is in the set iff it has an un-tombstoned add-token. -/
def lookup (s : State α τ) (a : α) : Prop := a ∈ elements s

/-- Characterisation of membership in terms of tokens. -/
theorem mem_elements {s : State α τ} {a : α} :
    a ∈ elements s ↔ ∃ t, (a, t) ∈ s.1 ∧ t ∉ s.2 := by
  simp only [elements, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hp2⟩, rfl⟩; exact ⟨p.2, hp, hp2⟩
  · rintro ⟨t, ht, htr⟩; exact ⟨(a, t), ⟨ht, htr⟩, rfl⟩

theorem lookup_iff {s : State α τ} {a : α} :
    lookup s a ↔ ∃ t, (a, t) ∈ s.1 ∧ t ∉ s.2 := mem_elements

/-- Add element `a` with token `t`. The token is meant to be globally unique; freshness
is a hypothesis of the theorems below, not baked into the type. -/
def add (s : State α τ) (a : α) (t : τ) : State α τ := (insert (a, t) s.1, s.2)

/-- Remove element `a`: tombstone exactly the tokens currently observed for `a`. -/
def remove (s : State α τ) (a : α) : State α τ := (s.1, s.2 ∪ observedTokens s a)

/-- Merge is componentwise union of the two grow-only sets. -/
theorem merge_eq (s₁ s₂ : State α τ) :
    merge s₁ s₂ = (s₁.1 ∪ s₂.1, s₁.2 ∪ s₂.2) := by
  rw [merge_def]; rfl

theorem t_mem_observedTokens {s : State α τ} {a : α} {t : τ} :
    t ∈ observedTokens s a ↔ (a, t) ∈ s.1 := by
  simp only [observedTokens, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, rfl⟩, rfl⟩; exact hp
  · rintro h; exact ⟨(a, t), ⟨h, rfl⟩, rfl⟩

/-- **A fresh add makes the element present.** -/
theorem add_lookup (s : State α τ) (a : α) (t : τ) (htR : t ∉ s.2) :
    lookup (add s a t) a := by
  rw [lookup, mem_elements]
  exact ⟨t, Finset.mem_insert_self _ _, htR⟩

/-- **Remove genuinely removes** when there is no concurrent add: after removing `a`,
lookup fails, because every add-token for `a` is now tombstoned. -/
theorem remove_lookup_false (s : State α τ) (a : α) :
    ¬ lookup (remove s a) a := by
  rw [lookup, mem_elements]
  rintro ⟨t, htA, htR⟩
  exact htR (Finset.mem_union_right _ (t_mem_observedTokens.mpr htA))

/-- **Add-wins — the defining OR-Set property.** A concurrent add and remove of the same
element resolves to **present**: an add with a fresh token survives a concurrent remove,
because the remove can only tombstone tokens it has already observed, never the fresh
one. This is exactly the case a 2P-Set gets wrong (there the element would be lost). -/
theorem add_wins (s : State α τ) (a : α) (t : τ)
    (hfresh : (a, t) ∉ s.1) -- `t` is a fresh token for `a`, not yet observed
    (htR : t ∉ s.2) : -- and not already tombstoned
    lookup (merge (add s a t) (remove s a)) a := by
  rw [lookup, mem_elements, merge_eq]
  refine ⟨t, ?_, ?_⟩
  · -- (a, t) is in the merged add-set (it is in the fresh add)
    exact Finset.mem_union_left _ (by simp [add])
  · -- t is in neither tombstone set: not in s.2 (fresh) and not observed for a (fresh)
    simp only [add, remove, Finset.mem_union, not_or]
    refine ⟨htR, htR, ?_⟩
    rw [t_mem_observedTokens]
    exact hfresh

/-- **OR-Set inherits Strong Eventual Consistency** from the abstract carrier. -/
theorem strong_eventual_consistency (l₁ l₂ : List (State α τ))
    (h : l₁.toFinset = l₂.toFinset) :
    l₁.foldr merge ⊥ = l₂.foldr merge ⊥ :=
  Crdt.strong_eventual_consistency l₁ l₂ h

/-- **OR-Set inherits eventual agreement** under any fair delivery system. -/
theorem eventual_agreement {ι : Type*} (sys : DeliverySystem ι (State α τ)) (r₁ r₂ : ι) :
    ∃ T, ∀ t, T ≤ t →
      replicaState (sys.delivered r₁ t) = replicaState (sys.delivered r₂ t) :=
  sys.eventual_agreement r₁ r₂

end Crdt.ORSet
