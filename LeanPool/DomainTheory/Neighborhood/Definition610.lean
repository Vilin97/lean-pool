/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Basic

/-!
# Lecture VI — Definition 6.10 (Scott 1981, PRG-19): the subsystem relation `D ◁
E`

To explain why the *minimal* solutions of a domain equation exist, Scott
introduces a notion of
"subdomain". The functors `T` he has in mind are not merely continuous on maps
(Definition 6.8) but
also possess continuity properties *on domains*, and those are phrased in terms of
this relation.

**Definition 6.10.** For two neighbourhood systems `D` and `E` over the *same* set
of tokens `Δ`,
we write `D ◁ E` to mean that
* `D ⊆ E` (every neighbourhood of `D` is a neighbourhood of `E`), **and**
* whenever `X, Y ∈ D` and `X ∩ Y ∈ E`, then `X ∩ Y ∈ D`.

The second clause is the crucial one: it says the notion of *consistency* in `D`
is the **same** as
in `E`. A subdomain is a smaller family of neighbourhoods, but it must agree with
`E` about which
pairs are consistent.

This module formalizes the relation together with the elementary facts Scott
records in the prose:

* it is reflexive (`Subsystem.refl`) and transitive (`Subsystem.trans`);
* it is antisymmetric (`Subsystem.antisymm`): `D ◁ E` and `E ◁ D` force `D = E`;
* **Scott's remark.** If `D₀ ◁ E` and `D₁ ◁ E`, then `D₀ ◁ D₁ ↔ D₀ ⊆ D₁`
  (`Subsystem.subsystem_iff_subset_of_common`) — once both sit inside a common
  `E`, the
  subdomain relation collapses to plain inclusion of neighbourhood families.

Everything here is at the `Prop` level and **choice-free** (`#print axioms ⊆
{propext, Quot.sound}`).
Propositions 6.11 (the subsystems of `E` form a domain) and 6.12 (a `D ◁ E` yields
a projection
pair `i, j`) build on this relation and are formalized separately.
-/

namespace Domain.Neighborhood

variable {α : Type*}

/-- **Definition 6.10 (Scott 1981, PRG-19).** The *subsystem* (subdomain) relation
`D ◁ E` for two
neighbourhood systems over the same token type. It records that `D` and `E` are
systems over the
same `Δ` (`master_eq`), that `D` is a subfamily of `E` (`sub`), and — the
essential clause — that
consistency is inherited from `E`: an intersection of two `D`-neighbourhoods that
happens to be an
`E`-neighbourhood is already a `D`-neighbourhood (`inter_closed`). -/
structure Subsystem (D E : NeighborhoodSystem α) : Prop where
  /-- `D` and `E` are systems over the same set of tokens `Δ`. -/
  master_eq : D.master = E.master
  /-- `D ⊆ E`: every neighbourhood of `D` is a neighbourhood of `E`. -/
  sub : ∀ {X : Set α}, D.mem X → E.mem X
  /-- Consistency in `D` is the same as in `E`: if `X, Y ∈ D` and `X ∩ Y ∈ E`,
  then `X ∩ Y ∈ D`. -/
  inter_closed : ∀ {X Y : Set α}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)

@[inherit_doc] infix:50 " ◁ " => Subsystem

namespace Subsystem

/-- The subsystem relation is **reflexive**: `D ◁ D`. (The `inter_closed` clause
is trivial — the
hypothesis is already the conclusion.) -/
theorem refl (D : NeighborhoodSystem α) : D ◁ D where
  master_eq := rfl
  sub h := h
  inter_closed _ _ h := h

/-- The subsystem relation is **transitive**: `D ◁ E` and `E ◁ F` give `D ◁ F`.

The `inter_closed` clause threads through `E`: from `X, Y ∈ D ⊆ E` and `X ∩ Y ∈
F`, the relation
`E ◁ F` puts `X ∩ Y ∈ E`, and then `D ◁ E` puts `X ∩ Y ∈ D`. -/
theorem trans {D E F : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ F) : D ◁ F where
  master_eq := h₁.master_eq.trans h₂.master_eq
  sub h := h₂.sub (h₁.sub h)
  inter_closed hX hY hXY :=
    h₁.inter_closed hX hY (h₂.inter_closed (h₁.sub hX) (h₁.sub hY) hXY)

/-- Two neighbourhood systems with the same `mem` and the same `master` are equal
(the remaining
fields of `NeighborhoodSystem` are `Prop`s). -/
theorem _root_.Domain.Neighborhood.NeighborhoodSystem.ext {D E : NeighborhoodSystem α}
    (hmem : ∀ X, D.mem X ↔ E.mem X) (hmaster : D.master = E.master) : D = E := by
  rcases D with ⟨Dmem, Dmaster, _, _, _⟩
  rcases E with ⟨Emem, Emaster, _, _, _⟩
  have hm : Dmem = Emem := funext fun X => propext (hmem X)
  subst hm
  subst hmaster
  rfl

/-- The subsystem relation is **antisymmetric**: `D ◁ E` and `E ◁ D` force `D =
E`. (Mutual `sub`
gives equal `mem`, and `master_eq` gives equal masters.) -/
theorem antisymm {D E : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ D) : D = E :=
  NeighborhoodSystem.ext (fun _ => ⟨fun h => h₁.sub h, fun h => h₂.sub h⟩) h₁.master_eq

/-- **Scott's remark (the prose after Definition 6.10).** Once `D₀` and `D₁` both
sit inside a
common system `E` as subdomains, the subdomain relation between them is just
inclusion of
neighbourhood families: `D₀ ◁ D₁ ↔ D₀ ⊆ D₁`.

* `→` is the `sub` clause of `D₀ ◁ D₁`.
* `←` builds `D₀ ◁ D₁` from `D₀ ⊆ D₁`: the masters agree because both equal `E`'s
master, and
  the `inter_closed` clause routes through `E` — an intersection `X ∩ Y` of
  `D₀`-neighbourhoods
  lying in `D₁` lies in `E` (since `D₁ ⊆ E`), and `D₀ ◁ E` then returns it to
  `D₀`. -/
theorem subsystem_iff_subset_of_common {D₀ D₁ E : NeighborhoodSystem α}
    (h₀ : D₀ ◁ E) (h₁ : D₁ ◁ E) :
    D₀ ◁ D₁ ↔ ∀ {X : Set α}, D₀.mem X → D₁.mem X := by
  constructor
  · intro h _ hX; exact h.sub hX
  · intro hsub
    refine ⟨h₀.master_eq.trans h₁.master_eq.symm, hsub, ?_⟩
    intro X Y hX hY hXY
    exact h₀.inter_closed hX hY (h₁.sub hXY)

end Subsystem

end Domain.Neighborhood
