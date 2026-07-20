/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# VC Dimension and Shattering

The foundational complexity measure for PAC learning.
Bridges to Mathlib's `Finset.vcDim` via `Bridge.lean`.
-/

universe u v

/-- A set S ⊆ X is shattered by concept class C if every labeling of S
    is realized by some concept in C. -/
def Shatters (X : Type u) (C : ConceptClass X Bool) (S : Finset X) : Prop :=
  ∀ f : S → Bool, ∃ c ∈ C, ∀ x : S, c (x : X) = f x

/-- VC dimension of a concept class: the size of the largest shattered set.
    Returns ℕ∞ = WithTop ℕ. -/
noncomputable def VCDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ)

/-- Growth function (shattering coefficient): π_C(m) = max_{|S|=m} |{c|_S : c ∈ C}|.
    For each m-element set S, counts the number of distinct restrictions of C to S,
    then takes the supremum over all such S. -/
noncomputable def GrowthFunction (X : Type u)
    (C : ConceptClass X Bool) : ℕ → ℕ :=
  fun m => sSup (Set.range fun (S : { S : Finset X // S.card = m }) =>
    ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard)

/-- Star number (dual VC dimension): the largest d such that there exists a set S
    of size d where for each x ∈ S, some concept in C separates x from the rest
    (i.e., ∃ c ∈ C, c x ≠ c y for all y ∈ S, y ≠ x in the appropriate sense).
    Formally: largest |S| where ∀ x ∈ S, ∃ c ∈ C, c(x) = true ∧ ∀ y ∈ S, y ≠ x → c(y) = false.
    Haussler-Welzl 1987: d*(C) = VCDim of the dual system. -/
noncomputable def StarNumber (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (S : Finset X)
    (_ : ∀ x ∈ S, ∃ c ∈ C, c x = true ∧ ∀ y ∈ S, y ≠ x → c y = false),
    (S.card : WithTop ℕ)

