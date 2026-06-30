/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

/-!
# Scott Information Systems

Following Dana Scott, *"Domains for Denotational Semantics"* (ICALP 1982) and the
compact presentation in Glynn Winskel, *The Formal Semantics of Programming
Languages*, Chapter 8.

Following Scott's **Definition 2.1**, an information system is a structure
`(P, Δ, Con, ⊢)` where

* `P` is a set of *data objects* / *propositions* (our token type `α`);
* `Δ ∈ P` is a distinguished *least informative* object (here the field `bot`);
* `Con` is a set of finite subsets of `P`, the *consistent* sets; and
* `⊢` (entailment, here `Ent`) relates a finite set to a token it forces.

Scott's six axioms (Def. 2.1) are, for finite `u, v ⊆ P` and `X ∈ P`:

* (i)   `u ∈ Con` whenever `u ⊆ v ∈ Con`              — `con_subset`
* (ii)  `{X} ∈ Con`                                    — `con_sing`
* (iii) `u ∪ {X} ∈ Con` whenever `u ⊢ X`               — `ent_con`
* (iv)  `u ⊢ Δ`                                         — `ent_bot`
* (v)   `u ⊢ X` whenever `X ∈ u`                        — `ent_refl`
* (vi)  if `v ⊢ Y` for all `Y ∈ u` and `u ⊢ X` then `v ⊢ X` — `ent_trans`

The **domain** determined by an information system is the poset of its *elements*
(a.k.a. *ideals*): sets of tokens that are consistent on every finite subset and
closed under entailment, ordered by inclusion. This file sets up the structure,
the
notion of element, and the partial order; later files build the function, product,
and sum spaces.

This is the **1982** presentation; the development is kept choice-free
(constructive),
matching Scott's emphasis on the constructive nature of the definitions.
-/

/-- A Scott information system on a type of tokens `α`, following Scott's
Definition 2.1
in *"Domains for Denotational Semantics"* (ICALP 1982).

`DecidableEq α` is required so that finite token sets support union (`X ∪ {a}`)
and the
other `Finset` operations the axioms mention. -/
structure InfoSys (α : Type*) [DecidableEq α] where
  /-- The distinguished least-informative object `Δ`. -/
  bot : α
  /-- The consistent finite sets of tokens. -/
  Con : Set (Finset α)
  /-- Entailment: `Ent u a` means the consistent set `u` forces the token `a`. -/
  Ent : Finset α → α → Prop
  /-- (i) Consistency is downward closed under `⊆`. -/
  con_subset : ∀ {u v : Finset α}, u ∈ Con → v ⊆ u → v ∈ Con
  /-- (ii) Every singleton is consistent. -/
  con_sing : ∀ a : α, {a} ∈ Con
  /-- (iii) A set entailing `a` stays consistent when `a` is added. Scott writes
  this as
  `u ∪ {a} ∈ Con`; we use the definitionally identical `insert a u`, because
  mathlib's
  `Finset` union instance (unlike `insert`) depends on `Classical.choice`, which
  would
  break the constructive development. -/
  ent_con : ∀ {u : Finset α} {a : α}, Ent u a → insert a u ∈ Con
  /-- (iv) The least token `Δ` is entailed by every consistent set. -/
  ent_bot : ∀ {u : Finset α}, u ∈ Con → Ent u bot
  /-- (v) Entailment is reflexive on members of a consistent set. -/
  ent_refl : ∀ {u : Finset α} {a : α}, u ∈ Con → a ∈ u → Ent u a
  /-- (vi) Entailment is transitive (cut): if a consistent `v` entails every
  member of a
  consistent `u`, and `u ⊢ c`, then `v ⊢ c`. -/
  ent_trans : ∀ {u v : Finset α} {c : α},
    v ∈ Con → u ∈ Con → (∀ y ∈ u, Ent v y) → Ent u c → Ent v c

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- An *element* (ideal) of the domain: a set of tokens that is consistent on
every
finite subset and closed under entailment. -/
structure Element where
  /-- The underlying set of tokens. -/
  carrier : Set α
  /-- Every finite subset of the element is consistent. -/
  consistent : ∀ Y : Finset α, (Y : Set α) ⊆ carrier → Y ∈ sys.Con
  /-- The element is closed under entailment. -/
  closed : ∀ (Y : Finset α) (a : α), (Y : Set α) ⊆ carrier → sys.Ent Y a → a ∈ carrier

/-- Elements are ordered by inclusion of their carriers; this is the Scott
ordering. -/
instance : PartialOrder sys.Element where
  le x y := x.carrier ⊆ y.carrier
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h1 h2 := Set.Subset.trans h1 h2
  le_antisymm x y h1 h2 := by
    -- Elements are determined by their carriers (the remaining fields are
    -- `Prop`s,
    -- closed by definitional proof irrelevance), so equality reduces to carrier
    -- antisymmetry. We avoid `congr` here because it pulls in `Classical.choice`;
    -- `subst` + `rfl` keeps the development constructive.
    have hc : x.carrier = y.carrier := Set.Subset.antisymm h1 h2
    cases x
    cases y
    subst hc
    rfl

end InfoSys
