/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import Mathlib.Data.Finset.Sort
import LeanPool.CrdtLean.Crdt.Defs
import LeanPool.CrdtLean.Crdt.Convergence
import LeanPool.CrdtLean.Crdt.Liveness


/-!
# Sequence CRDT (RGA-family) — convergence to an identical ordered sequence

The OR-Set (`Crdt.ORSet`) is the hard *unordered* CRDT. This file does the hard
*ordered* one: a **replicated sequence** (the RGA / Logoot / Treedoc family), where the
distinctive obligation is that every replica converges not just to the same *set* of
elements but to the same *ordered list*, and the relative order of any two surviving
elements is independent of the order in which operations were delivered.

## Model

Each inserted element carries a globally unique **position identifier** drawn from a
densely-ordered type `ι` with a `LinearOrder`. We abstract identifier *allocation* (the
insert-after-with-timestamp-tiebreak machinery RGA/Logoot use to mint a fresh position
between two neighbours) into "you are handed a fresh `ι`", exactly as `Crdt.ORSet`
abstracted unique add-tokens. What we prove is the convergence layer above allocation.

State is a pair of grow-only sets: `placed : Finset (ι × α)` (positioned elements) and
`tombstones : Finset ι` (deleted positions). As a product of two G-Sets it is a
`SemilatticeSup` with `OrderBot`, so `merge` is componentwise union and Strong Eventual
Consistency + liveness apply **for free** at the state level. The content here is the
**read**: the live position identifiers enumerated in order (each identifier carrying its
element value by lookup). Identifiers are totally ordered, so the enumeration is a
deterministic function of *which positions are live* — never of delivery history.

## What is proved (the moat)

* `read_sorted` — the read is sorted by identifier: the sequence order is a deterministic
  function of positions, never of history.
* `read_strong_eventual_consistency` — replicas that delivered the same set of operations
  produce the **identical ordered sequence** (sequence-level SEC, lifted from state SEC).
* `read_determined` — the read depends only on the live set, not on the delivery path.
* `read_nodup`, `mem_read` — the read is duplicate-free and exactly the live positions.
* `delete_not_read` / `insert_read` — tombstoning removes a position from the sequence; a
  fresh insert at a live position makes it appear.
-/

namespace Crdt.RGA

variable {ι α : Type*} [LinearOrder ι] [DecidableEq α]

/-- Sequence-CRDT state: positioned elements and a grow-only tombstone set of deleted
position identifiers. A product of two grow-only sets. -/
abbrev State (ι α : Type*) := Finset (ι × α) × Finset ι

/-- The product carrier is a lawful CvRDT carrier — SEC and liveness apply unchanged. -/
example : SemilatticeSup (State ι α) := inferInstance
example : OrderBot (State ι α) := inferInstance
example : DecidableEq (State ι α) := inferInstance

/-- The live elements: positioned pairs whose identifier has not been tombstoned. -/
def live (s : State ι α) : Finset (ι × α) := s.1.filter (fun p => p.1 ∉ s.2)

/-- The live position identifiers. -/
def positions (s : State ι α) : Finset ι := (live s).image Prod.fst

/-- The observable sequence: live position identifiers enumerated in order. Each
identifier carries its element value by lookup into `live`. -/
def read (s : State ι α) : List ι := (positions s).sort (· ≤ ·)

/-- Merge is componentwise union of the two grow-only sets. -/
theorem merge_eq (s₁ s₂ : State ι α) :
    merge s₁ s₂ = (s₁.1 ∪ s₂.1, s₁.2 ∪ s₂.2) := by
  rw [merge_def]; rfl

omit [DecidableEq α] in
/-- A position is live iff it has a placed, un-tombstoned element. -/
theorem mem_positions {s : State ι α} {p : ι} :
    p ∈ positions s ↔ ∃ v, (p, v) ∈ s.1 ∧ p ∉ s.2 := by
  simp only [positions, live, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hab, hb⟩, rfl⟩; exact ⟨b, hab, hb⟩
  · rintro ⟨v, hv, hp⟩; exact ⟨p, v, ⟨hv, hp⟩, rfl⟩

omit [DecidableEq α] in
/-- Membership in the read sequence is exactly being a live position. -/
theorem mem_read {s : State ι α} {p : ι} : p ∈ read s ↔ p ∈ positions s := by
  rw [read, Finset.mem_sort]

omit [DecidableEq α] in
/-- **The read is sorted by identifier.** The sequence order is a deterministic function
of the position identifiers, never of delivery history. -/
theorem read_sorted (s : State ι α) : (read s).Pairwise (· ≤ ·) := by
  rw [read]; exact Finset.pairwise_sort (positions s) (· ≤ ·)

omit [DecidableEq α] in
/-- The read is duplicate-free. -/
theorem read_nodup (s : State ι α) : (read s).Nodup := by
  rw [read]; exact Finset.sort_nodup (positions s) (· ≤ ·)

/-- Insert element `v` at a fresh position identifier `p`. -/
def insert (s : State ι α) (p : ι) (v : α) : State ι α := (Insert.insert (p, v) s.1, s.2)

/-- Delete the element at position `p` by tombstoning the identifier. -/
def delete (s : State ι α) (p : ι) : State ι α := (s.1, Insert.insert p s.2)

omit [DecidableEq α] in
/-- **Delete removes from the sequence.** A tombstoned position never appears in the
read. -/
theorem delete_not_read (s : State ι α) (p : ι) : p ∉ read (delete s p) := by
  rw [mem_read, mem_positions]
  rintro ⟨v, _, hp⟩
  exact hp (Finset.mem_insert_self p s.2)

/-- **Insert makes the position appear** when it is not already tombstoned. -/
theorem insert_read (s : State ι α) (p : ι) (v : α) (hp : p ∉ s.2) :
    p ∈ read (insert s p v) := by
  rw [mem_read, mem_positions]
  exact ⟨v, Finset.mem_insert_self _ _, hp⟩

/-- **Sequence-level Strong Eventual Consistency.** Replicas that have delivered the same
set of operation-states produce the **identical ordered sequence** — not merely the same
set of elements, but the same list, in the same order. Lifted from state-level SEC by the
fact that `read` is a pure function of state. -/
theorem read_strong_eventual_consistency (l₁ l₂ : List (State ι α))
    (h : l₁.toFinset = l₂.toFinset) :
    read (l₁.foldr merge ⊥) = read (l₂.foldr merge ⊥) :=
  congrArg read (Crdt.strong_eventual_consistency l₁ l₂ h)

omit [DecidableEq α] in
/-- **The read depends only on the live set, not on delivery history.** Two states with
the same live elements produce the identical sequence, regardless of how their tombstones
and placements were accumulated. Together with `read_sorted` this pins the order: it is a
function of *which positions are live*, full stop. -/
theorem read_determined {s₁ s₂ : State ι α} (h : live s₁ = live s₂) :
    read s₁ = read s₂ := by
  rw [read, read, positions, positions, h]

/-- **Eventual agreement** at the state level, inherited from the abstract carrier. -/
theorem eventual_agreement {κ : Type*} (sys : DeliverySystem κ (State ι α)) (r₁ r₂ : κ) :
    ∃ T, ∀ t, T ≤ t →
      replicaState (sys.delivered r₁ t) = replicaState (sys.delivered r₂ t) :=
  sys.eventual_agreement r₁ r₂

end Crdt.RGA
