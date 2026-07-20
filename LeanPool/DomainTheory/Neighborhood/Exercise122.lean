/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Basic
import Mathlib.Topology.Inseparable

/-!
# Exercise 1.22 (Scott 1981, PRG-19, §1) — the topology on `|𝒟|`

> **EXERCISE 1.22.** (For topologists). Show that the neighbourhoods `[X]` for `X
∈ 𝒟` make
> `|𝒟|` into a topological space where the open subsets `𝒰 ⊆ |𝒟|` can be
characterized by the
> following two conditions:
>
> (i)  whenever `x ∈ 𝒰` and `x ⊑ y ∈ |𝒟|`, then `y ∈ 𝒰`; and
> (ii) whenever `x ∈ 𝒰`, then `[X] ⊆ 𝒰` for some `X ∈ x`.
>
> Prove also that the inclusion relation on `|𝒟|` can be defined topologically as:
>
> (iii) `x ⊑ y` iff for all open `𝒰 ⊆ |𝒟|`, if `x ∈ 𝒰` then `y ∈ 𝒰`.

Here `[X] = {x ∈ |𝒟| ∣ X ∈ x}` (Scott's notation from Theorem 1.10): the set of
elements
(filters) of which `X` is a member. We call it `basicOpen X`.

## What is proved

* `basicOpen` — Scott's `[X]`, with `mem_basicOpen` the membership unfolding.
* `instTopologicalSpaceElement` — the topology on `V.Element`: `𝒰` is open iff
every point of
  `𝒰` has a basic neighbourhood `[X]` (`X ∈ x`) contained in `𝒰`. This is
  condition (ii); the
  three topology axioms are verified directly (the basic opens are closed under
  finite `∩`, with
  `[Δ] = |𝒟|` the whole space, so they form a base).
* `isOpen_basicOpen` — each `[X]` is open.
* `isOpen_iff_upper_basic` — the characterization: `IsOpen 𝒰 ↔ (i) ∧ (ii)`. Note
(ii) already
  pins down openness; (i) (upward closure under `⊑`) is a *consequence* of (ii),
  recorded
  separately as `isOpen_isUpperSet`. We keep both to match Scott's statement.
* `le_iff_isOpen_imp` — condition (iii): `x ⊑ y ↔ ∀ 𝒰 open, x ∈ 𝒰 → y ∈ 𝒰`. This
says `⊑` is
  the (opposite of the) specialization preorder; `specializes_iff_le` makes the
  bridge to
  Mathlib's `⤳` explicit.

The space is **T₀** but not in general **T₁**/Hausdorff (the specialization order
`⊑` is a genuine
partial order, recoverable from the topology by (iii)); the open-ended limit-point
questions of the
exercise need Definition 1.7 (`↑X`) and are deferred.
-/

namespace Domain.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}` (Theorem 1.10 notation): the set of elements
of the domain
`|𝒟|` that contain the neighbourhood `X`. These sets are the basic opens of the
topology of
Exercise 1.22. -/
def basicOpen (X : Set α) : Set V.Element := {x | x.mem X}

@[simp] theorem mem_basicOpen {X : Set α} {x : V.Element} :
    x ∈ V.basicOpen X ↔ x.mem X := Iff.rfl

/-- `[X ∩ Y] ⊆ [X]` whenever `X ∈ 𝒟`: a filter containing `X ∩ Y` contains `X`
(upward closure).
This (with the symmetric version) is the closure of the basic opens under finite
intersection,
i.e. `[X] ∩ [Y] = [X ∩ Y]`, the base condition behind the topology. -/
theorem basicOpen_inter_subset_left {X Y : Set α} (hX : V.mem X) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen X :=
  fun z hz => z.up_mem hz hX Set.inter_subset_left

/-- `[X ∩ Y] ⊆ [Y]` whenever `Y ∈ 𝒟`. -/
theorem basicOpen_inter_subset_right {X Y : Set α} (hY : V.mem Y) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen Y :=
  fun z hz => z.up_mem hz hY Set.inter_subset_right

/-- A set `𝒰 ⊆ |𝒟|` is *open* (Exercise 1.22, condition (ii)) when every point `x
∈ 𝒰` has a
basic neighbourhood `[X]` with `X ∈ x` contained in `𝒰`. -/
def IsOpenFilter (U : Set V.Element) : Prop :=
  ∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U

/-- **Exercise 1.22 (the space).** The basic opens `[X]` (`X ∈ 𝒟`) generate a
topology on `|𝒟|`:
`𝒰` is open iff it is a union of basic opens (condition (ii)). The three axioms
hold because the
base is closed under finite intersection (`basicOpen_inter_subset_left/right`,
using that filters
are `∩`-closed and upward closed) with `[Δ] = |𝒟|` covering the space. -/
instance instTopologicalSpaceElement : TopologicalSpace V.Element where
  IsOpen := V.IsOpenFilter
  isOpen_univ := fun x _ => ⟨V.master, x.master_mem, Set.subset_univ _⟩
  isOpen_inter := by
    intro U W hU hW x hx
    obtain ⟨hxU, hxW⟩ := hx
    obtain ⟨X, hX, hXU⟩ := hU x hxU
    obtain ⟨Y, hY, hYW⟩ := hW x hxW
    refine ⟨X ∩ Y, x.inter_mem hX hY, fun z hz => ⟨hXU ?_, hYW ?_⟩⟩
    · exact V.basicOpen_inter_subset_left (x.sub hX) hz
    · exact V.basicOpen_inter_subset_right (x.sub hY) hz
  isOpen_sUnion := by
    intro S hS x hx
    obtain ⟨t, htS, hxt⟩ := hx
    obtain ⟨X, hX, hXt⟩ := hS t htS x hxt
    exact ⟨X, hX, hXt.trans fun _ ha => ⟨t, htS, ha⟩⟩

/-- `IsOpen` for `|𝒟|` is exactly Scott's condition (ii). -/
theorem isOpen_iff_isOpenFilter (U : Set V.Element) : IsOpen U ↔ V.IsOpenFilter U := Iff.rfl

/-- **Exercise 1.22.** Each basic neighbourhood `[X]` is open. -/
theorem isOpen_basicOpen (X : Set α) : IsOpen (V.basicOpen X) :=
  fun _ hx => ⟨X, hx, subset_rfl⟩

/-- **Exercise 1.22, condition (i).** Every open set is upward closed under the
approximation order
`⊑`: if `x ∈ 𝒰` and `x ⊑ y` then `y ∈ 𝒰`. (This is a *consequence* of (ii): the
basic
neighbourhood `[X] ⊆ 𝒰` witnessing `x ∈ 𝒰` also contains every `y ⊒ x`.) -/
theorem isOpen_isUpperSet {U : Set V.Element} (hU : IsOpen U) :
    ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U := by
  intro x y hxU hxy
  obtain ⟨X, hX, hXU⟩ := hU x hxU
  exact hXU (hxy X hX)

/-- **Exercise 1.22 (characterization of open sets).** A subset `𝒰 ⊆ |𝒟|` is open
iff
(i) it is upward closed under `⊑`, and (ii) every point of `𝒰` has a basic
neighbourhood `[X]`
(`X ∈ x`) contained in `𝒰`. -/
theorem isOpen_iff_upper_basic (U : Set V.Element) :
    IsOpen U ↔
      (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
        (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U) := by
  constructor
  · intro hU
    exact ⟨V.isOpen_isUpperSet hU, hU⟩
  · rintro ⟨_, h2⟩
    exact h2

/-- **Exercise 1.22, condition (iii).** The approximation order is recovered from
the topology:
`x ⊑ y` iff every open set containing `x` also contains `y`.

* `→` is upward closure of opens (`isOpen_isUpperSet`);
* `←` tests against the open basic neighbourhood `[X]` for each `X ∈ x`. -/
theorem le_iff_isOpen_imp (x y : V.Element) :
    x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U := by
  constructor
  · intro hxy U hU hxU
    exact V.isOpen_isUpperSet hU hxU hxy
  · intro h
    exact fun X hX => h (V.basicOpen X) (V.isOpen_basicOpen X) hX

/-- The approximation order `⊑` is the opposite of Mathlib's specialization
preorder `⤳`:
`y ⤳ x ↔ x ⊑ y`. (Scott's (iii) says exactly that `⊑` is the specialization order
of this
topology.) -/
theorem specializes_iff_le (x y : V.Element) : y ⤳ x ↔ x ≤ y := by
  rw [specializes_iff_forall_open]
  exact (V.le_iff_isOpen_imp x y).symm

end NeighborhoodSystem

end Domain.Neighborhood
