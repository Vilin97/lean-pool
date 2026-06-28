/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanPool.CrdtLean.Crdt.Defs
import LeanPool.CrdtLean.Crdt.Convergence
import LeanPool.CrdtLean.Crdt.Liveness


/-!
# State-based CRDTs — concrete instances

`Crdt.Defs`/`Convergence`/`Liveness` prove Strong Eventual Consistency and conditional
liveness for *any* carrier that is a `SemilatticeSup` with `OrderBot` and decidable
equality. This file discharges that obligation for three textbook CRDTs, so each one
inherits SEC + liveness **for free** — no per-type re-proof:

* **G-Set** (grow-only set) — `Finset α`, merge = `∪`.
* **G-Counter** (grow-only counter) — `ι → ℕ`, merge = pointwise `max`, value = `∑`.
* **PN-Counter** (increment/decrement counter) — a pair of G-Counters, value = `P − N`.

For each we (a) confirm Mathlib already supplies the required lattice instances, (b)
state the concrete merge equation, (c) re-export SEC and eventual-agreement at the
concrete type, and (d) prove the *semantic read* (membership, counter value) is
**monotone** under delivery — the application-level statement an operator actually
cares about: replicas only ever move forward.

The honest boundary from `Crdt.Liveness` is unchanged: liveness is conditional on the
`DeliverySystem` fairness field. These instances make the abstract guarantee concrete,
they do not weaken it.
-/

namespace Crdt

/-! ## G-Set — grow-only set -/

section GSet

variable {α : Type*} [DecidableEq α]

/-- Mathlib already makes `Finset α` a `SemilatticeSup` with `OrderBot` and decidable
equality, so it is a lawful CvRDT carrier with no extra work. -/
example : SemilatticeSup (Finset α) := inferInstance
example : OrderBot (Finset α) := inferInstance
example : DecidableEq (Finset α) := inferInstance

/-- The G-Set merge is set union. -/
theorem gset_merge_eq_union (a b : Finset α) : merge a b = a ∪ b := by
  rw [merge_def, Finset.sup_eq_union]

/-- **G-Set inherits Strong Eventual Consistency.** Replicas delivered the same set of
element-states (each a `Finset α`) hold equal state, regardless of order/multiplicity. -/
theorem gset_strong_eventual_consistency (l₁ l₂ : List (Finset α))
    (h : l₁.toFinset = l₂.toFinset) :
    l₁.foldr merge ⊥ = l₂.foldr merge ⊥ :=
  strong_eventual_consistency l₁ l₂ h

/-- **G-Set inherits eventual agreement** under any fair delivery system. -/
theorem gset_eventual_agreement {ι : Type*}
    (sys : DeliverySystem ι (Finset α)) (r₁ r₂ : ι) :
    ∃ T, ∀ t, T ≤ t →
      replicaState (sys.delivered r₁ t) = replicaState (sys.delivered r₂ t) :=
  sys.eventual_agreement r₁ r₂

/-- **Semantic read is monotone.** As a replica delivers more element-states, the
observed G-Set only grows: membership is never revoked. -/
theorem gset_read_monotone {u v : Finset (Finset α)} (h : u ⊆ v) :
    replicaState u ⊆ replicaState v :=
  replicaState_mono h

end GSet

/-! ## G-Counter — grow-only counter -/

section GCounter

variable {ι : Type*}

/-- A G-Counter holds one grow-only tally per replica. -/
abbrev GCounter (ι : Type*) := ι → ℕ

variable [Fintype ι]

/-- Mathlib's `Pi` instances make `GCounter ι` a lawful CvRDT carrier. -/
example : SemilatticeSup (GCounter ι) := inferInstance
example : OrderBot (GCounter ι) := inferInstance
example : DecidableEq (GCounter ι) := inferInstance

omit [Fintype ι] in
/-- G-Counter merge is the pointwise maximum of the per-replica tallies. -/
theorem gcounter_merge_apply (a b : GCounter ι) (i : ι) :
    merge a b i = max (a i) (b i) := by
  rw [merge_def]; rfl

/-- The value of a G-Counter is the sum of its per-replica tallies. -/
def gcounterValue (a : GCounter ι) : ℕ := ∑ i, a i

/-- **G-Counter inherits Strong Eventual Consistency.** -/
theorem gcounter_strong_eventual_consistency (l₁ l₂ : List (GCounter ι))
    (h : l₁.toFinset = l₂.toFinset) :
    l₁.foldr merge ⊥ = l₂.foldr merge ⊥ :=
  strong_eventual_consistency l₁ l₂ h

/-- **G-Counter inherits eventual agreement** under any fair delivery system. -/
theorem gcounter_eventual_agreement (sys : DeliverySystem ι (GCounter ι)) (r₁ r₂ : ι) :
    ∃ T, ∀ t, T ≤ t →
      replicaState (sys.delivered r₁ t) = replicaState (sys.delivered r₂ t) :=
  sys.eventual_agreement r₁ r₂

/-- **The counter value never decreases under merge.** Merging in another replica's
state can only push each tally up (pointwise max), so the summed value is monotone —
the read an application makes only moves forward. -/
theorem gcounter_value_le_merge (a b : GCounter ι) :
    gcounterValue a ≤ gcounterValue (merge a b) := by
  apply Finset.sum_le_sum
  intro i _
  exact le_merge_left a b i

/-- The counter value is monotone in the lattice order on counters. -/
theorem gcounterValue_mono : Monotone (gcounterValue (ι := ι)) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro i _
  exact hab i

end GCounter

/-! ## PN-Counter — increment/decrement counter -/

section PNCounter

variable {ι : Type*}

/-- A PN-Counter is a pair of G-Counters: increments `P` and decrements `N`. -/
abbrev PNCounter (ι : Type*) := (ι → ℕ) × (ι → ℕ)

variable [Fintype ι]

/-- Mathlib's `Prod` instances make `PNCounter ι` a lawful CvRDT carrier. -/
example : SemilatticeSup (PNCounter ι) := inferInstance
example : OrderBot (PNCounter ι) := inferInstance
example : DecidableEq (PNCounter ι) := inferInstance

omit [Fintype ι] in
/-- PN-Counter merge is the componentwise G-Counter merge (pointwise max on each side). -/
theorem pncounter_merge_apply (a b : PNCounter ι) (i : ι) :
    (merge a b).1 i = max (a.1 i) (b.1 i) ∧
      (merge a b).2 i = max (a.2 i) (b.2 i) := by
  rw [merge_def]; exact ⟨rfl, rfl⟩

/-- The value of a PN-Counter is (sum of increments) − (sum of decrements), in `ℤ`. -/
def pncounterValue (a : PNCounter ι) : ℤ :=
  (∑ i, (a.1 i : ℤ)) - (∑ i, (a.2 i : ℤ))

/-- **PN-Counter inherits Strong Eventual Consistency.** -/
theorem pncounter_strong_eventual_consistency (l₁ l₂ : List (PNCounter ι))
    (h : l₁.toFinset = l₂.toFinset) :
    l₁.foldr merge ⊥ = l₂.foldr merge ⊥ :=
  strong_eventual_consistency l₁ l₂ h

/-- **PN-Counter inherits eventual agreement** under any fair delivery system. -/
theorem pncounter_eventual_agreement (sys : DeliverySystem ι (PNCounter ι)) (r₁ r₂ : ι) :
    ∃ T, ∀ t, T ≤ t →
      replicaState (sys.delivered r₁ t) = replicaState (sys.delivered r₂ t) :=
  sys.eventual_agreement r₁ r₂

end PNCounter

end Crdt
