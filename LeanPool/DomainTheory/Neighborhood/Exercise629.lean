/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Product
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic

/-!
# Exercise 6.29 (Scott 1981, PRG-19, §6) — infinitary sum and product

> **EXERCISE 6.29.** Generalize `+` and `×` to infinitary operations on domains:
> `∑_{n=0}^∞ D_n` and `∏_{n=0}^∞ D_n`. Would a similar generalization be possible
for `⊕` and `⊗`?

We work with an arbitrary index type `ι` and a family of neighbourhood systems `D
: ∀ i, 𝒟ᵢ` over
token types `α i` (Scott's `D_n`, with `ℕ` the intended `ι`). Tokens of the
combined systems live in
`Σ i, α i` (for product-like operations) or `Option (Σ i, α i)` (for sum-like
operations, the
`none` being the fresh basepoint). This is the indexed analogue of the abstract
binary
`prod`/`sum` over `α ⊕ β` / `Option (α ⊕ β)`.

## The four operations and the answer

* **`∏_i D_i` (`iprod`)** — the indexed **product**. A neighbourhood is a tuple `X
i ∈ 𝒟ᵢ` that is
  the master in all but **finitely many** coordinates (a *cylinder*). The
  finite-support condition
  is *essential*: it is exactly what makes the compact elements of the product the
  finitely-presented
  ones, giving the headline result `iprodEquiv : |∏_i D_i| ≃o ∀ i, |D_i|` (the
  product order is
  pointwise) — the infinitary **Proposition 3.2**.
* **`∑_i D_i` (`isum`)** — the indexed **separated sum**. A neighbourhood is the
basepoint master or
  a single tagged copy `inj i X` of one summand (finite information — only one
  coordinate is
  constrained), so no finite-support condition is needed. Element trichotomy
  `isum_trichotomy`:
  every element is `⊥` or lives in exactly one summand.
* **`⊕_i D_i` (`ioplus`)** — the indexed **coalesced sum**, as `∑` but with the
improper tagged
  copies deleted (the bottoms identified). Single-coordinate, so it **generalizes
  fine**.
* **`⊗_i D_i` (`iotimes`)** — the indexed **smash product**. A proper
neighbourhood would need *every*
  coordinate proper (`≠` master), which over an infinite `ι` contradicts finite
  support. So the
  infinite smash **degenerates**: `iotimes_only_master`/`iotimes_subsingleton` —
  over an infinite
  index it has only the basepoint, a one-point domain.

**Answer to Scott's question.** `+`, `×`, `⊕` all generalize to infinitary
operations; `⊗` does
**not** — the infinite smash collapses to the trivial domain.

**Choice discipline.** Every *data* construction is choice-free
(`iprod`, `isum`, `ioplus`, `iotimes`, the order iso `iprodEquiv`, and
`isum_summand_unique` all have
`#print axioms ⊆ {propext, Quot.sound}`). The finite-support predicate is a `List`
of coordinates in
its *positive* form `∀ i, i ∉ l → X i = master`, which keeps intersection
(`FinSupp.inter`) and the
reconstruction (`z_mem_of_slices`) constructive. Only two genuinely classical
Prop-level results
remain: `isum_trichotomy` (an excluded-middle case split on whether an element
reaches a summand) and
the degeneracy `iotimes_only_master`/`iotimes_subsingleton` (a cardinality
argument through Mathlib's
classical `Set.Finite`). Both are flagged in their docstrings.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-! ## The product neighbourhood and its algebra -/

/-- A **product neighbourhood** `iprodNbhd X = {⟨i, a⟩ ∣ a ∈ X i}` over `Σ i, α
i`. -/
def iprodNbhd (X : ∀ i, Set (α i)) : Set (Σ i, α i) := {p | p.2 ∈ X p.1}

@[simp] theorem mem_iprodNbhd {X : ∀ i, Set (α i)} {i : ι} {a : α i} :
    (⟨i, a⟩ : Σ i, α i) ∈ iprodNbhd X ↔ a ∈ X i := Iff.rfl

/-- Product neighbourhoods intersect coordinatewise (Scott's (2)). -/
theorem iprodNbhd_inter (X X' : ∀ i, Set (α i)) :
    iprodNbhd X ∩ iprodNbhd X' = iprodNbhd (fun i => X i ∩ X' i) := by
  apply Set.ext; rintro ⟨i, a⟩; simp [iprodNbhd, Set.mem_inter_iff]

/-- Inclusion of product neighbourhoods is coordinatewise (Scott's (1)). -/
theorem iprodNbhd_subset_iff {X X' : ∀ i, Set (α i)} :
    iprodNbhd X ⊆ iprodNbhd X' ↔ ∀ i, X i ⊆ X' i := by
  constructor
  · intro h i a ha; exact h (show (⟨i, a⟩ : Σ i, α i) ∈ iprodNbhd X from ha)
  · rintro h ⟨i, a⟩ ha; exact h i ha

/-- The tuple representation of a product neighbourhood is unique. -/
theorem iprodNbhd_injective {X X' : ∀ i, Set (α i)} (h : iprodNbhd X = iprodNbhd X') : X = X' := by
  funext i; apply Set.ext; intro a
  simpa only [mem_iprodNbhd] using Set.ext_iff.mp h ⟨i, a⟩

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Choice-free finite support**: a *list* enumerating all coordinates where `X`
is non-master.
(Mathlib's `Set.Finite` is built on `Fintype` and pulls in `Classical.choice`; a
`List` witness keeps
the construction constructive, which is exactly what is needed for the cylinder.) -/
def FinSupp (D : ∀ i, NeighborhoodSystem (α i)) (X : ∀ i, Set (α i)) : Prop :=
  ∃ l : List ι, ∀ i, i ∉ l → X i = (D i).master

theorem FinSupp.master : FinSupp D (fun i => (D i).master) := ⟨[], fun _ _ => rfl⟩

theorem FinSupp.inter {X X' : ∀ i, Set (α i)}
    (hX : FinSupp D X) (hX' : FinSupp D X') : FinSupp D (fun i => X i ∩ X' i) := by
  obtain ⟨l, hl⟩ := hX; obtain ⟨l', hl'⟩ := hX'
  -- Outside `l ++ l'` both factors are the master, so the intersection is too —
  -- fully constructive,
  -- no case split on the undecidable proposition `X i = master`.
  refine ⟨l ++ l', fun i hi => ?_⟩
  rw [List.mem_append, not_or] at hi
  simp only [hl i hi.1, hl' i hi.2, Set.inter_self]

variable (D) in
/-- **Exercise 6.29 — the indexed product `∏_i D_i`.** Neighbourhoods are
cylinders: tuples
`X i ∈ 𝒟ᵢ` that are the master in all but finitely many coordinates. -/
def iprod : NeighborhoodSystem (Σ i, α i) where
  mem W := ∃ X : ∀ i, Set (α i), (∀ i, (D i).mem (X i)) ∧ FinSupp D X ∧ W = iprodNbhd X
  master := iprodNbhd (fun i => (D i).master)
  master_mem := ⟨fun i => (D i).master, fun i => (D i).master_mem, FinSupp.master, rfl⟩
  sub_master := by
    rintro W ⟨X, hX, _, rfl⟩
    exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i)
  inter_mem := by
    rintro W W' Z ⟨X, hX, hXf, rfl⟩ ⟨X', hX', hX'f, rfl⟩ ⟨ZZ, hZZ, _, rfl⟩ hsub
    rw [iprodNbhd_inter] at hsub ⊢
    refine ⟨fun i => X i ∩ X' i, fun i => ?_, hXf.inter hX'f, rfl⟩
    have : ZZ i ⊆ X i ∩ X' i := iprodNbhd_subset_iff.mp hsub i
    exact (D i).inter_mem (hX i) (hX' i) (hZZ i) this

theorem iprod_mem_iprodNbhd {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i))
    (hXf : FinSupp D X) : (iprod D).mem (iprodNbhd X) :=
  ⟨X, hX, hXf, rfl⟩

/-! ## The element isomorphism `|∏_i D_i| ≃o ∀ i, |D_i|`

Throughout we use the *slices* `slice i U` — the cylinder that is `U` at
coordinate `i` and the
master elsewhere. -/

section Iso

variable [DecidableEq ι]

/-- The tuple that is `U` at coordinate `i` and the master elsewhere. -/
def updTuple (D : ∀ i, NeighborhoodSystem (α i)) (i : ι) (U : Set (α i)) : ∀ j, Set (α j) :=
  Function.update (fun j => (D j).master) i U

@[simp] theorem updTuple_apply_self (i : ι) (U : Set (α i)) : updTuple D i U i = U := by
  simp [updTuple]

theorem updTuple_apply_ne {i j : ι} (U : Set (α i)) (h : j ≠ i) :
    updTuple D i U j = (D j).master := by
  simp [updTuple, Function.update_of_ne h]

/-- The slice cylinder: `U` at coordinate `i`, master elsewhere. -/
def slice (D : ∀ i, NeighborhoodSystem (α i)) (i : ι) (U : Set (α i)) : Set (Σ i, α i) :=
  iprodNbhd (updTuple D i U)

theorem slice_eq (i : ι) (U : Set (α i)) : slice D i U = iprodNbhd (updTuple D i U) := rfl

/-- A slice has support `⊆ {i}`, hence is a neighbourhood of the product when `U ∈
𝒟ᵢ`. -/
theorem iprod_mem_slice {i : ι} {U : Set (α i)} (hU : (D i).mem U) :
    (iprod D).mem (slice D i U) := by
  refine ⟨updTuple D i U, fun j => ?_, ⟨[i], fun j hj => ?_⟩, rfl⟩
  · by_cases h : j = i
    · subst h; rw [updTuple_apply_self]; exact hU
    · rw [updTuple_apply_ne U h]; exact (D j).master_mem
  · exact updTuple_apply_ne U fun h => hj (List.mem_singleton.mpr h)

/-- Recovering the coordinate from a slice neighbourhood. -/
theorem iprod_mem_slice_inv {i : ι} {U : Set (α i)} (h : (iprod D).mem (slice D i U)) :
    (D i).mem U := by
  obtain ⟨X, hX, _, heq⟩ := h
  have hXeq : updTuple D i U = X := iprodNbhd_injective heq
  have hi := hX i
  rwa [← hXeq, updTuple_apply_self] at hi

/-- Slices at the same coordinate intersect by intersecting their data. -/
theorem slice_inter (i : ι) (U U' : Set (α i)) :
    slice D i U ∩ slice D i U' = slice D i (U ∩ U') := by
  rw [slice_eq, slice_eq, slice_eq, iprodNbhd_inter]
  congr 1; funext j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self, updTuple_apply_self, updTuple_apply_self]
  · rw [updTuple_apply_ne U h, updTuple_apply_ne U' h, updTuple_apply_ne (U ∩ U') h,
      Set.inter_self]

/-- Slices are monotone in their data. -/
theorem slice_subset (i : ι) {U U' : Set (α i)} (hUU' : U ⊆ U') : slice D i U ⊆ slice D i U' := by
  rw [slice_eq, slice_eq, iprodNbhd_subset_iff]
  intro j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self, updTuple_apply_self]; exact hUU'
  · rw [updTuple_apply_ne U h, updTuple_apply_ne U' h]

/-- A cylinder is contained in each of its own slices. -/
theorem iprodNbhd_subset_slice {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i)) (i : ι) :
    iprodNbhd X ⊆ slice D i (X i) := by
  rw [slice_eq, iprodNbhd_subset_iff]
  intro j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self]
  · rw [updTuple_apply_ne (X i) h]; exact (D j).sub_master (hX j)

/-- **The `i`-th component of a product element** (Scott's `z_i`). -/
def proj (z : (iprod D).Element) (i : ι) : (D i).Element where
  mem U := (D i).mem U ∧ z.mem (slice D i U)
  sub h := h.1
  master_mem := ⟨(D i).master_mem, by
    have : slice D i (D i).master = (iprod D).master := by
      change iprodNbhd (updTuple D i (D i).master) = iprodNbhd (fun j => (D j).master)
      congr 1; funext j
      by_cases h : j = i
      · subst h; rw [updTuple_apply_self]
      · rw [updTuple_apply_ne (D i).master h]
    rw [this]; exact z.master_mem⟩
  inter_mem := by
    rintro U U' ⟨_, hzU⟩ ⟨_, hzU'⟩
    have hz := z.inter_mem hzU hzU'
    rw [slice_inter] at hz
    exact ⟨iprod_mem_slice_inv (z.sub hz), hz⟩
  up_mem := by
    rintro U U' ⟨_, hzU⟩ hU' hUU'
    exact ⟨hU', z.up_mem hzU (iprod_mem_slice hU') (slice_subset i hUU')⟩

/-- **The element of `∏_i D_i` assembled from a tuple of components.** -/
def fromPi (D : ∀ i, NeighborhoodSystem (α i)) (x : ∀ i, (D i).Element) : (iprod D).Element where
  mem W := ∃ X : ∀ i, Set (α i), (∀ i, (x i).mem (X i)) ∧ FinSupp D X ∧ W = iprodNbhd X
  sub := by rintro W ⟨X, hX, hXf, rfl⟩; exact ⟨X, fun i => (x i).sub (hX i), hXf, rfl⟩
  master_mem := ⟨fun i => (D i).master, fun i => (x i).master_mem, FinSupp.master, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, hX, hXf, rfl⟩ ⟨X', hX', hX'f, rfl⟩
    exact ⟨fun i => X i ∩ X' i, fun i => (x i).inter_mem (hX i) (hX' i), hXf.inter hX'f,
      iprodNbhd_inter X X'⟩
  up_mem := by
    rintro W W' ⟨X, hX, _, rfl⟩ hW' hsub
    obtain ⟨X', hX'mem, hX'f, rfl⟩ := hW'
    rw [iprodNbhd_subset_iff] at hsub
    exact ⟨X', fun i => (x i).up_mem (hX i) (hX'mem i) (hsub i), hX'f, rfl⟩

theorem fromPi_mem_slice (x : ∀ i, (D i).Element) (i : ι) (U : Set (α i)) :
    (fromPi D x).mem (slice D i U) ↔ (x i).mem U := by
  constructor
  · rintro ⟨X, hX, _, heq⟩
    have hXeq : updTuple D i U = X := iprodNbhd_injective heq
    have hi := hX i
    rwa [← hXeq, updTuple_apply_self] at hi
  · intro hU
    refine ⟨updTuple D i U, fun j => ?_, ⟨[i], fun j hj => ?_⟩, rfl⟩
    · by_cases h : j = i
      · subst h; rw [updTuple_apply_self]; exact hU
      · rw [updTuple_apply_ne U h]; exact (x j).master_mem
    · exact updTuple_apply_ne U fun h => hj (List.mem_singleton.mpr h)

/-- The cylinder restricted to a list of coordinates `l` (master outside `l`). -/
def restrictTo (D : ∀ i, NeighborhoodSystem (α i)) (l : List ι) (X : ∀ i, Set (α i)) :
    ∀ j, Set (α j) := fun j => if j ∈ l then X j else (D j).master

theorem iprodNbhd_restrictTo_cons {X : ∀ i, Set (α i)} (hXsub : ∀ i, X i ⊆ (D i).master)
    (a : ι) (l : List ι) :
    iprodNbhd (restrictTo D (a :: l) X) = slice D a (X a) ∩ iprodNbhd (restrictTo D l X) := by
  rw [slice_eq, iprodNbhd_inter]
  congr 1; funext j
  change (if j ∈ a :: l then X j else (D j).master)
      = updTuple D a (X a) j ∩ (if j ∈ l then X j else (D j).master)
  by_cases hja : j = a
  · subst hja
    rw [updTuple_apply_self]
    by_cases hjl : j ∈ l
    · rw [if_pos List.mem_cons_self, if_pos hjl, Set.inter_self]
    · rw [if_pos List.mem_cons_self, if_neg hjl, Set.inter_eq_left.mpr (hXsub j)]
  · rw [updTuple_apply_ne (X a) hja]
    by_cases hjl : j ∈ l
    · rw [if_pos (List.mem_cons_of_mem a hjl), if_pos hjl, Set.inter_eq_right.mpr (hXsub j)]
    · rw [if_neg fun h => (List.mem_cons.mp h).elim hja hjl, if_neg hjl, Set.inter_self]

/-- An element contains the restricted cylinder once it contains each listed
slice. -/
theorem z_mem_iprodNbhd_restrictTo (z : (iprod D).Element) {X : ∀ i, Set (α i)}
    (hXsub : ∀ i, X i ⊆ (D i).master) (hslice : ∀ i, z.mem (slice D i (X i))) (l : List ι) :
    z.mem (iprodNbhd (restrictTo D l X)) := by
  induction l with
  | nil =>
    have : restrictTo D [] X = fun j => (D j).master := by
      funext j; rw [restrictTo]; exact if_neg List.not_mem_nil
    rw [this]; exact z.master_mem
  | cons a l ih =>
    rw [iprodNbhd_restrictTo_cons hXsub a l]
    exact z.inter_mem (hslice a) ih

/-- **Reconstruction.** A product element containing each of a cylinder's slices
contains the
cylinder. The finite support (a *list* of coordinates) lets the only finitely many
non-trivial slices
be intersected inside the element — entirely choice-free. -/
theorem z_mem_of_slices (z : (iprod D).Element) {X : ∀ i, Set (α i)}
    (hXmem : ∀ i, (D i).mem (X i)) (hXf : FinSupp D X)
    (hslice : ∀ i, z.mem (slice D i (X i))) : z.mem (iprodNbhd X) := by
  obtain ⟨l, hl⟩ := hXf
  have hsub : ∀ i, X i ⊆ (D i).master := fun i => (D i).sub_master (hXmem i)
  have key := z_mem_iprodNbhd_restrictTo z hsub hslice l
  have heq : restrictTo D l X = X := by
    funext j
    rw [restrictTo]
    by_cases h : j ∈ l
    · rw [if_pos h]
    · rw [if_neg h]; exact (hl j h).symm
  rwa [heq] at key

theorem fromPi_toPi (z : (iprod D).Element) : fromPi D (fun i => proj z i) = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, hX, hXf, rfl⟩
    exact z_mem_of_slices z (fun i => (hX i).1) hXf (fun i => (hX i).2)
  · intro hW
    obtain ⟨X, hXmem, hXf, rfl⟩ := z.sub hW
    exact ⟨X, fun i => ⟨hXmem i, z.up_mem hW (iprod_mem_slice (hXmem i))
      (iprodNbhd_subset_slice hXmem i)⟩, hXf, rfl⟩

theorem proj_fromPi (x : ∀ i, (D i).Element) (i : ι) : proj (fromPi D x) i = x i := by
  apply Element.ext
  intro U
  constructor
  · rintro ⟨_, hz⟩; exact (fromPi_mem_slice x i U).mp hz
  · intro hU; exact ⟨(x i).sub hU, (fromPi_mem_slice x i U).mpr hU⟩

/-- **Exercise 6.29 — `×` generalizes to `∏`, correct up to isomorphism.** The
domain of the
indexed product is the pointwise product of the factor domains: `|∏_i D_i| ≃o ∀ i,
|D_i|`. This is
the infinitary **Proposition 3.2** (`prodEquiv`). -/
def iprodEquiv (D : ∀ i, NeighborhoodSystem (α i)) :
    (iprod D).Element ≃o (∀ i, (D i).Element) where
  toFun z := fun i => proj z i
  invFun x := fromPi D x
  left_inv z := fromPi_toPi z
  right_inv x := funext fun i => proj_fromPi x i
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hzW
      obtain ⟨X, hXmem, hXf, rfl⟩ := z.sub hzW
      refine z_mem_of_slices z' hXmem hXf fun i => ?_
      have hzi : (proj z i).mem (X i) :=
        ⟨hXmem i, z.up_mem hzW (iprod_mem_slice (hXmem i)) (iprodNbhd_subset_slice hXmem i)⟩
      exact ((h i) (X i) hzi).2
    · intro h i U hU
      exact ⟨hU.1, h _ hU.2⟩

end Iso

/-! ## `+` generalizes to `∑`: the indexed separated sum

Tokens live in `Option (Σ i, α i)`: the `none` basepoint plus tagged copies `inj i
X` of the
summands. A neighbourhood constrains only a single coordinate, so — unlike the
product — no
finite-support condition is needed. We need `∅ ∉ 𝒟ᵢ` (`hne`) to keep distinct
tagged copies
disjoint. -/

/-- A tagged copy `inj i X = {some ⟨i, a⟩ ∣ a ∈ X}` of summand `i`. -/
def injI (i : ι) (X : Set (α i)) : Set (Option (Σ i, α i)) :=
  (fun a => (some ⟨i, a⟩ : Option (Σ i, α i))) '' X

theorem none_not_mem_injI {i : ι} {X : Set (α i)} : (none : Option (Σ i, α i)) ∉ injI i X := by
  rintro ⟨a, _, heq⟩; simp at heq

@[simp] theorem some_mem_injI {i : ι} {a : α i} {X : Set (α i)} :
    (some ⟨i, a⟩ : Option (Σ i, α i)) ∈ injI i X ↔ a ∈ X := by
  constructor
  · rintro ⟨b, hb, heq⟩
    simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at heq
    rwa [heq] at hb
  · intro ha; exact ⟨a, ha, rfl⟩

/-- A tagged token determines its summand index. -/
theorem index_of_some_mem_injI {i k : ι} {a : α k} {X : Set (α i)}
    (hmem : (some ⟨k, a⟩ : Option (Σ i, α i)) ∈ injI i X) : k = i := by
  obtain ⟨b, _, heq⟩ := hmem
  simp only [Option.some.injEq] at heq
  exact (congrArg Sigma.fst heq).symm

theorem injI_nonempty {i : ι} {X : Set (α i)} (hX : X.Nonempty) : (injI i X).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨some ⟨i, a⟩, some_mem_injI.mpr ha⟩

theorem injI_subset_iff {i : ι} {X Y : Set (α i)} : injI i X ⊆ injI i Y ↔ X ⊆ Y := by
  constructor
  · intro h a ha; exact some_mem_injI.mp (h (some_mem_injI.mpr ha))
  · intro h; rintro w ⟨a, ha, rfl⟩; exact ⟨a, h ha, rfl⟩

theorem injI_inter_same (i : ι) (X Y : Set (α i)) : injI i X ∩ injI i Y = injI i (X ∩ Y) := by
  apply Set.ext
  rintro (_ | ⟨k, a⟩)
  · constructor
    · rintro ⟨h, _⟩; exact absurd h none_not_mem_injI
    · intro h; exact absurd h none_not_mem_injI
  · constructor
    · rintro ⟨hx, hy⟩
      obtain rfl := index_of_some_mem_injI hx
      exact some_mem_injI.mpr ⟨some_mem_injI.mp hx, some_mem_injI.mp hy⟩
    · intro h
      obtain rfl := index_of_some_mem_injI h
      have h' := some_mem_injI.mp h
      exact ⟨some_mem_injI.mpr h'.1, some_mem_injI.mpr h'.2⟩

theorem injI_inter_ne {i j : ι} (h : i ≠ j) (X : Set (α i)) (Y : Set (α j)) :
    injI i X ∩ injI j Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro (_ | ⟨k, a⟩) ⟨hw1, hw2⟩
  · exact none_not_mem_injI hw1
  · exact h ((index_of_some_mem_injI hw1).symm.trans (index_of_some_mem_injI hw2))

/-- The basepoint master of the indexed sum: `{none} ∪ {some ⟨i, a⟩ ∣ a ∈ Δᵢ}`. -/
def sumMasterI (D : ∀ i, NeighborhoodSystem (α i)) : Set (Option (Σ i, α i)) :=
  insert none ((fun p => (some p : Option (Σ i, α i))) '' iprodNbhd (fun i => (D i).master))

theorem none_mem_sumMasterI : (none : Option (Σ i, α i)) ∈ sumMasterI D := Set.mem_insert _ _

theorem injI_subset_sumMasterI {i : ι} {X : Set (α i)} (hX : (D i).mem X) :
    injI i X ⊆ sumMasterI D := by
  rintro w ⟨a, ha, rfl⟩
  exact Set.mem_insert_iff.mpr (Or.inr ⟨⟨i, a⟩, (D i).sub_master hX ha, rfl⟩)

/-- **Exercise 6.29 — the indexed separated sum `∑_i D_i`.** -/
def isum (D : ∀ i, NeighborhoodSystem (α i))
    (hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty) :
    NeighborhoodSystem (Option (Σ i, α i)) where
  mem W := W = sumMasterI D ∨ ∃ i, ∃ X : Set (α i), (D i).mem X ∧ W = injI i X
  master := sumMasterI D
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨i, X, hX, rfl⟩)
    · exact subset_rfl
    · exact injI_subset_sumMasterI hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨i, X, hX, rfl⟩
    · have hsub' : W' ⊆ sumMasterI D := by
        rcases hW' with rfl | ⟨j, Y, hY, rfl⟩
        · exact subset_rfl
        · exact injI_subset_sumMasterI hY
      rw [Set.inter_eq_right.mpr hsub']; exact hW'
    · rcases hW' with rfl | ⟨j, Y, hY, rfl⟩
      · rw [Set.inter_eq_left.mpr (injI_subset_sumMasterI hX)]
        exact Or.inr ⟨i, X, hX, rfl⟩
      · -- both proper: the consistency witness `Z` forces `i = j` constructively.
        rcases hZ with rfl | ⟨k, Wk, hWk, rfl⟩
        · exact absurd (hsub none_mem_sumMasterI).1 none_not_mem_injI
        · obtain ⟨w, hw⟩ := hne k Wk hWk
          have hmemZ := hsub (some_mem_injI.mpr hw)
          obtain rfl := index_of_some_mem_injI hmemZ.1
          obtain rfl := index_of_some_mem_injI hmemZ.2
          rw [injI_inter_same] at hsub ⊢
          exact Or.inr ⟨k, X ∩ Y, (D k).inter_mem hX hY hWk (injI_subset_iff.mp hsub), rfl⟩

/-- **Exercise 6.29 — sum trichotomy.** Every element of `∑_i D_i` either reaches
into some summand
or is the basepoint `⊥`. (Prop-level and genuinely classical: the case split is
excluded middle on
whether `z` reaches a summand, so this depends on `Classical.choice`.) -/
theorem isum_trichotomy {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) :
    (∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)) ∨
      (∀ W, z.mem W → W = (isum D hne).master) := by
  by_cases h : ∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)
  · exact Or.inl h
  · refine Or.inr fun W hW => ?_
    rcases z.sub hW with rfl | ⟨i, X, hX, rfl⟩
    · rfl
    · exact absurd ⟨i, X, hX, hW⟩ h

/-- **Exercise 6.29 — a sum element reaches at most one summand.** -/
theorem isum_summand_unique {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) {i j : ι} {X : Set (α i)} {Y : Set (α j)}
    (hX : z.mem (injI i X)) (hY : z.mem (injI j Y)) : i = j := by
  -- The filter element `z` contains the consistent intersection; its
  -- representative carries a
  -- token whose index is forced to be both `i` and `j` — no excluded middle on `i
  -- = j`.
  have hz := z.inter_mem hX hY
  rcases z.sub hz with h0 | ⟨k, W, hWmem, hWeq⟩
  · rw [Set.ext_iff] at h0
    exact absurd ((h0 none).mpr none_mem_sumMasterI).1 none_not_mem_injI
  · obtain ⟨w, hw⟩ := hne k W hWmem
    rw [Set.ext_iff] at hWeq
    have hmem := (hWeq (some ⟨k, w⟩)).mpr (some_mem_injI.mpr hw)
    obtain rfl := index_of_some_mem_injI hmem.1
    obtain rfl := index_of_some_mem_injI hmem.2
    rfl

/-! ## `⊕` generalizes: the indexed coalesced sum

As `∑`, but the *improper* tagged copies `inj i Δᵢ` are deleted (the per-summand
bottoms are
identified with the basepoint). Single-coordinate, so it generalizes with no
finite-support issue. -/

/-- **Exercise 6.29 — the indexed coalesced sum `⊕_i D_i`.** -/
def ioplus (D : ∀ i, NeighborhoodSystem (α i))
    (hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty) :
    NeighborhoodSystem (Option (Σ i, α i)) where
  mem W := W = sumMasterI D ∨ ∃ i, ∃ X : Set (α i), (D i).mem X ∧ X ≠ (D i).master ∧ W = injI i X
  master := sumMasterI D
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨i, X, hX, _, rfl⟩)
    · exact subset_rfl
    · exact injI_subset_sumMasterI hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨i, X, hX, hXne, rfl⟩
    · have hsub' : W' ⊆ sumMasterI D := by
        rcases hW' with rfl | ⟨j, Y, hY, _, rfl⟩
        · exact subset_rfl
        · exact injI_subset_sumMasterI hY
      rw [Set.inter_eq_right.mpr hsub']; exact hW'
    · rcases hW' with rfl | ⟨j, Y, hY, hYne, rfl⟩
      · rw [Set.inter_eq_left.mpr (injI_subset_sumMasterI hX)]
        exact Or.inr ⟨i, X, hX, hXne, rfl⟩
      · rcases hZ with rfl | ⟨k, Wk, hWk, _, rfl⟩
        · exact absurd (hsub none_mem_sumMasterI).1 none_not_mem_injI
        · obtain ⟨w, hw⟩ := hne k Wk hWk
          have hmemZ := hsub (some_mem_injI.mpr hw)
          obtain rfl := index_of_some_mem_injI hmemZ.1
          obtain rfl := index_of_some_mem_injI hmemZ.2
          rw [injI_inter_same] at hsub ⊢
          exact Or.inr ⟨k, X ∩ Y, (D k).inter_mem hX hY hWk (injI_subset_iff.mp hsub),
            fun heq => hXne (Set.Subset.antisymm ((D k).sub_master hX)
              (heq ▸ Set.inter_subset_left)), rfl⟩

/-! ## `⊗` does **not** generalize: the infinite smash degenerates

The smash product keeps only those tuples that are *proper* (`≠` master) in
**every** coordinate
(plus the basepoint master). Over an infinite index this collides with the
finite-support
requirement that any neighbourhood imposes — there are no proper neighbourhoods at
all, so the
infinite smash collapses to the one-point domain. -/

/-- **Exercise 6.29 — the indexed smash product `⊗_i D_i`.** A proper
neighbourhood is a cylinder
proper in *every* coordinate; closure under intersection is as for `iprod` plus
the observation that
`X i ∩ X' i ⊆ X i ≠` master stays proper. -/
def iotimes (D : ∀ i, NeighborhoodSystem (α i)) : NeighborhoodSystem (Σ i, α i) where
  mem W := W = iprodNbhd (fun i => (D i).master) ∨
    ∃ X : ∀ i, Set (α i), (∀ i, (D i).mem (X i)) ∧ (∀ i, X i ≠ (D i).master) ∧
      FinSupp D X ∧ W = iprodNbhd X
  master := iprodNbhd (fun i => (D i).master)
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, _, _, rfl⟩)
    · exact subset_rfl
    · exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i)
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨X, hX, hXne, hXf, rfl⟩
    · have hW'sub : W' ⊆ iprodNbhd (fun i => (D i).master) := by
        rcases hW' with rfl | ⟨X', hX', _, _, rfl⟩
        · exact subset_rfl
        · exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX' i)
      rw [Set.inter_eq_right.mpr hW'sub]; exact hW'
    · rcases hW' with rfl | ⟨X', hX', hX'ne, hX'f, rfl⟩
      · rw [Set.inter_eq_left.mpr (iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i))]
        exact Or.inr ⟨X, hX, hXne, hXf, rfl⟩
      · rw [iprodNbhd_inter] at hsub ⊢
        obtain ⟨ZZ, hZZmem, rfl⟩ : ∃ ZZ, (∀ i, (D i).mem (ZZ i)) ∧ Z = iprodNbhd ZZ := by
          rcases hZ with rfl | ⟨ZZ, hZZ, _, _, rfl⟩
          · exact ⟨fun i => (D i).master, fun i => (D i).master_mem, rfl⟩
          · exact ⟨ZZ, hZZ, rfl⟩
        refine Or.inr ⟨fun i => X i ∩ X' i, fun i => ?_, fun i => ?_, ?_, rfl⟩
        · exact (D i).inter_mem (hX i) (hX' i) (hZZmem i) (iprodNbhd_subset_iff.mp hsub i)
        · intro heq
          exact hXne i (Set.Subset.antisymm ((D i).sub_master (hX i))
            (by rw [← heq]; exact Set.inter_subset_left))
        · exact hXf.inter hX'f

/-- **Exercise 6.29 — `⊗` does not generalize.** Over an infinite index, the smash
product has only
its basepoint: an all-coordinates-proper cylinder has support `Set.univ`, which
cannot be finite. -/
theorem iotimes_only_master [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    ∀ W, (iotimes D).mem W → W = (iotimes D).master := by
  rintro W (rfl | ⟨X, _, hXne, ⟨l, hl⟩, rfl⟩)
  · rfl
  · -- Every coordinate is proper, so the finite support list `l` would have to contain
    -- *all* of `ι`,
    -- impossible for an infinite index. This is a cardinality argument:
    -- Prop-level and unavoidably
    -- classical (Mathlib's `Set.Finite`/`Fintype` API is built on
    -- `Classical.choice`).
    refine absurd ((List.finite_toSet l).subset (fun i _ => ?_)) Set.infinite_univ
    exact not_not.mp fun hni => hXne i (hl i hni)

/-- **Exercise 6.29 — the infinite smash collapses to one point.** Its element
domain is a
singleton (`⊥` only), so `⊗` has no sensible infinitary generalization. -/
theorem iotimes_subsingleton [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    Subsingleton (iotimes D).Element := by
  refine ⟨fun x y => ?_⟩
  apply Element.ext
  intro W
  constructor
  · intro hx; rw [iotimes_only_master D W (x.sub hx)]; exact y.master_mem
  · intro hy; rw [iotimes_only_master D W (y.sub hy)]; exact x.master_mem

end Exercise629

end Domain.Neighborhood
