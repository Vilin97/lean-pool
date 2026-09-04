/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.GapWitness
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Generic relation lemmas for the boundedness corollaries (issue #12, step 6 layer 1)

Pure order-theoretic consequences of the raw positive conclusion `RelPreserving`, with no
model extraction involved:

* `RelPreserving.injective_of_irreflexive` — the derived injectivity corollary (issue
  precision note: injectivity is **not** part of the raw theorem, it is a corollary under
  irreflexivity of the interpreted relation);
* `RelPreserving.descending` — the negative rationals give an infinite strictly descending
  sequence through the interpreted relation;
* `not_relPreserving_of_wellFounded` — hence no relation-preserving map from `ℚ` exists into
  a structure whose interpreted relation is well-founded (via `WellFounded.has_min`; no
  strict-order hypotheses, so `RelEmbedding.natGT` is deliberately not used).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {M : Type} [L.Structure M] {lt : L.Relations 2}

/-- **Derived injectivity**: a relation-preserving map from `ℚ` into a structure whose
interpreted relation is irreflexive is injective — if `q < r` collided, preservation would
put the collision point below itself. -/
theorem RelPreserving.injective_of_irreflexive {f : ℚ → M} (hf : RelPreserving lt f)
    (hirr : ∀ x : M, ¬ RelMap lt ![x, x]) : Function.Injective f := by
  intro q r hqr
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hf q r hlt
    rw [hqr] at h
    exact hirr (f r) h
  · have h := hf r q hgt
    rw [hqr] at h
    exact hirr (f r) h

/-- **The descending sequence**: the negative rationals turn a relation-preserving map into
an infinite strictly descending sequence for the interpreted relation. -/
theorem RelPreserving.descending {f : ℚ → M} (hf : RelPreserving lt f) (n : ℕ) :
    RelMap lt ![f (-(n + 1 : ℕ) : ℚ), f (-(n : ℕ) : ℚ)] :=
  hf _ _ (by push_cast; exact neg_lt_neg (lt_add_one _))

/-- A well-founded relation admits no infinite descending sequence (direct, via
`WellFounded.has_min` — no strict-order hypotheses on the relation). -/
private theorem not_descending_of_wellFounded {α : Type*} {r : α → α → Prop} (hwf : WellFounded r)
    (g : ℕ → α) : ¬ ∀ n, r (g (n + 1)) (g n) := by
  intro hg
  obtain ⟨x, hx, hmin⟩ := hwf.has_min (Set.range g) ⟨g 0, 0, rfl⟩
  obtain ⟨n, rfl⟩ := hx
  exact hmin (g (n + 1)) ⟨n + 1, rfl⟩ (hg n)

/-- **No relation-preserving map into a well-founded relation**: the target of the step-5
theorem can never have a well-founded interpreted relation. -/
theorem not_relPreserving_of_wellFounded
    (hwf : WellFounded fun x y : M => RelMap lt ![x, y]) (f : ℚ → M) :
    ¬ RelPreserving lt f := fun hf =>
  not_descending_of_wellFounded hwf (fun n => f (-(n : ℕ) : ℚ)) fun n => hf.descending n

end FirstOrder.Language
