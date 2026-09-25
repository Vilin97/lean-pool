/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ContractionForestCensusGeneral
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSeparator

/-!
# Rigidity of the representative map on a forest face

A `DegSpec` carries its vertex identification as a *chosen function*
`rep : Fin n → Fin n`, not as a partition, and its `forest` field is a
cardinality equation rather than the assertion that the vanishing slots
generate `rep`.  Two consequences, both recorded in
`Utilities/Subdivision/DegenerateSpec.lean`'s own header and in
the corresponding closed-row proof module §4:

* a `DegSpec` on a **non-forest** vanishing set may merge blocks that no
  metric degeneration merges — the cardinality equation lets an unrelated
  extra identification balance a redundant zero slot; and
* even on a forest face, `rep` may pick different *representatives* of the
  right classes than the union-find map `compFold` does, so `DegSpec.ext'`
  (which compares `rep` as a function) cannot identify the two.

This file removes both obstacles for the forest case.

## What is proved

`rep_eq_of_compFold_eq` — `rep` always coarsens the census partition; this is
just `rep_zero` propagated along a `ReachIn` chain, and needs no hypothesis.

`compFold_eq_of_rep_eq` — **the sharpening.**  On a forest face the coarsening
is an equality.  `forest` gives `|image rep| + |zeroSlots| = n` and `IsForest`
gives `|image compFold| + |zeroSlots| = n`, so a coarsening between partitions
of equal class count is the identity.  Together: `rep_iff_compFold`.

`repEquiv` — **representative independence.**  Two closed faces on the same
core and lengths that induce the *same partition* have `LaplacianEquiv`
graphs, matching core vertex for core vertex (`repEquiv_coreVertex`).  No new
combinatorics: `d₁` is exhibited as a `Contraction` onto `d₂`'s canonical
positive quotient `d₂.contractedSpec`, and the equivalence is that datum
composed with `d₂.canonicalContraction`.

`censusFace` / `censusFaceEquiv` — the payoff.  Every forest face of a closed
orthant is `LaplacianEquiv`, mark for mark, to the face a *census*-facing
producer speaks about (`rep := compFold` of the vanishing slots — literally
the corresponding closed-row proof module's `rep`).  Note that `censusFace` needs no
`¬ IsLoopy` hypothesis: its `rep_loopless` field is inherited from `d`'s
through `rep_eq_of_compFold_eq`.

## What is *not* proved here

Nothing about non-forest faces.  On those `rep` genuinely is not determined
by the length vector, and the enumeration in
the accompanying analysis measures how many such
faces a genus-five legged row has.
-/

@[expose] public section

-- `Certificate` is a structure inside a namespace already ending in `Certificate`.
namespace Utilities.Certificate.DegenerateSpec.DegSpec

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Finset ExplicitPotential

variable {n p : ℕ}

/-! ## The class of a core vertex on the canonical positive quotient

These two live here rather than beside their first consumer because they are
pure `DegSpec` bookkeeping and both the legged reduction and the rigidity
statement below need them. -/

/-- The class of a core vertex, as a core vertex index of the canonical
contracted core.  This is the mark-carrying half of the legged reduction: a
pinned mark on a closed face is again a pinned *core* mark on the canonical
positive quotient. -/
noncomputable def contractedClass (d : DegSpec n p) (v : Fin n) :
    Fin d.classCard :=
  d.classIndex ⟨d.rep v, d.rep_idem v⟩

/-- The canonical Laplacian equivalence carries the contracted class of a core
vertex back to that core vertex's class on the closed face. -/
theorem canonicalContraction_coreVertex_contractedClass (d : DegSpec n p)
    (v : Fin n) :
    d.canonicalContraction.laplacianEquiv.toEquiv
        (d.contractedSpec.coreVertex (d.contractedClass v))
      = d.coreVertex v := by
  have hvtx : d.canonicalContraction.vtx (d.contractedClass v) = d.rep v := by
    show (d.classIndex.symm (d.contractedClass v)).val = d.rep v
    rw [contractedClass, Equiv.symm_apply_apply]
  show d.canonicalContraction.vertexEquiv
      (d.contractedSpec.coreVertex (d.contractedClass v)) = d.coreVertex v
  rw [Contraction.vertexEquiv_coreVertex, hvtx]
  exact (d.coreVertex_eq_iff (d.rep v) v).mpr (d.rep_idem v)

/-! ## Representative independence -/

section RepIndependence

variable (d₁ d₂ : DegSpec n p)

/-- Two closed faces on the same core and lengths that induce the same vertex
partition: `d₁` is a `Contraction` onto `d₂`'s canonical positive quotient.

Every field is index bookkeeping through `d₂.classIndex`/`d₂.slotIndex`; the
only mathematical input is `hiff`, used three times to move a `d₂.rep` inside
a `d₁.rep`. -/
noncomputable def contractionOfRepIff
    (hcore : d₁.core = d₂.core) (hlength : d₁.length = d₂.length)
    (hiff : ∀ u v : Fin n, d₁.rep u = d₁.rep v ↔ d₂.rep u = d₂.rep v) :
    Contraction d₁ d₂.contractedSpec where
  vtx := fun v' => d₁.rep (d₂.classIndex.symm v').val
  vtx_rep := fun v' => d₁.rep_idem _
  vtx_inj := by
    intro a b h
    have h2 : d₂.rep (d₂.classIndex.symm a).val = d₂.rep (d₂.classIndex.symm b).val :=
      (hiff _ _).mp h
    rw [(d₂.classIndex.symm a).property, (d₂.classIndex.symm b).property] at h2
    exact d₂.classIndex.symm.injective (Subtype.ext h2)
  vtx_surj := by
    intro v
    refine ⟨d₂.classIndex ⟨d₂.rep v, d₂.rep_idem v⟩, ?_⟩
    show d₁.rep (d₂.classIndex.symm (d₂.classIndex ⟨d₂.rep v, _⟩)).val = d₁.rep v
    rw [Equiv.symm_apply_apply]
    exact (hiff _ _).mpr (d₂.rep_idem v)
  slot := fun e' => (d₂.slotIndex.symm e').val
  slot_inj := by
    intro a b h
    exact d₂.slotIndex.symm.injective (Subtype.ext h)
  slot_surj := by
    intro e he
    refine ⟨d₂.slotIndex ⟨e, ?_⟩, ?_⟩
    · rw [← hlength]; exact he
    · rw [Equiv.symm_apply_apply]
  length_eq := by
    intro e'
    show d₂.length _ = d₁.length _
    rw [hlength]
  tail_eq := by
    intro e'
    show d₁.rep (d₂.classIndex.symm
        (d₂.classIndex ⟨d₂.rep (d₂.core.tail _), _⟩)).val = _
    rw [Equiv.symm_apply_apply, hcore]
    exact (hiff _ _).mpr (d₂.rep_idem _)
  head_eq := by
    intro e'
    show d₁.rep (d₂.classIndex.symm
        (d₂.classIndex ⟨d₂.rep (d₂.core.head _), _⟩)).val = _
    rw [Equiv.symm_apply_apply, hcore]
    exact (hiff _ _).mpr (d₂.rep_idem _)

variable (hcore : d₁.core = d₂.core) (hlength : d₁.length = d₂.length)
  (hiff : ∀ u v : Fin n, d₁.rep u = d₁.rep v ↔ d₂.rep u = d₂.rep v)

/-- **Representative independence.**  Two closed faces on the same core and
lengths with the same vertex partition carry the same Laplacian. -/
noncomputable def repEquiv : LaplacianEquiv d₁.graph d₂.graph :=
  ((contractionOfRepIff d₁ d₂ hcore hlength hiff).laplacianEquiv).symm.trans
    d₂.canonicalContraction.laplacianEquiv

/-- The equivalence matches core vertex for core vertex — so a pinned mark
survives the change of representatives. -/
theorem repEquiv_coreVertex (v : Fin n) :
    repEquiv d₁ d₂ hcore hlength hiff (d₁.coreVertex v) = d₂.coreVertex v := by
  set c := contractionOfRepIff d₁ d₂ hcore hlength hiff with hc
  have hvtx : c.vtx (d₂.contractedClass v) = d₁.rep v := by
    show d₁.rep (d₂.classIndex.symm (d₂.contractedClass v)).val = d₁.rep v
    rw [contractedClass, Equiv.symm_apply_apply]
    exact (hiff _ _).mpr (d₂.rep_idem v)
  have hforward : c.laplacianEquiv.toEquiv
      (d₂.contractedSpec.coreVertex (d₂.contractedClass v)) = d₁.coreVertex v := by
    show c.vertexEquiv (d₂.contractedSpec.coreVertex (d₂.contractedClass v))
        = d₁.coreVertex v
    rw [Contraction.vertexEquiv_coreVertex, hvtx]
    exact (d₁.coreVertex_eq_iff (d₁.rep v) v).mpr (d₁.rep_idem v)
  have hback : c.laplacianEquiv.toEquiv.symm (d₁.coreVertex v)
      = d₂.contractedSpec.coreVertex (d₂.contractedClass v) := by
    rw [← hforward, Equiv.symm_apply_apply]
  show d₂.canonicalContraction.laplacianEquiv.toEquiv
      (c.laplacianEquiv.toEquiv.symm (d₁.coreVertex v)) = d₂.coreVertex v
  rw [hback]
  exact d₂.canonicalContraction_coreVertex_contractedClass v

end RepIndependence

/-! ## The vanishing-slot set and the census partition -/

/-- The vanishing slots of a degenerate spec.  Syntactically the `Finset`
appearing in the `forest` field. -/
def zeroSlotSet (d : DegSpec n p) : Finset (Fin p) :=
  Finset.univ.filter (fun e => d.length e = 0)

@[simp] theorem mem_zeroSlotSet (d : DegSpec n p) (e : Fin p) :
    e ∈ d.zeroSlotSet ↔ d.length e = 0 := by
  simp [zeroSlotSet]

theorem forest' (d : DegSpec n p) :
    (Finset.univ.image d.rep).card + d.zeroSlotSet.card = n := d.forest

/-- **The classes of `rep` are generated by the vanishing slots.**  `rep_zero`
is the easy direction; this is the converse, which a bare `DegSpec` does not
carry.  It holds by definition for every `rep` built as a `compFold`. -/
def RepIsContraction (d : DegSpec n p) : Prop :=
  ∀ u v : Fin n, d.rep u = d.rep v → ReachIn d.core d.zeroSlotSet u v

/-- `rep` is constant along vanishing-slot reachability: the direction every
`DegSpec` has, packaged for `ReflTransGen`. -/
theorem rep_eq_of_reachIn (d : DegSpec n p) {x y : Fin n}
    (h : ReachIn d.core d.zeroSlotSet x y) : d.rep x = d.rep y := by
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
      obtain ⟨e, he, hcase⟩ := hbc
      have hzero : d.length e = 0 :=
        (d.mem_zeroSlotSet e).mp ((mem_edgeList _ e).mp he)
      have hrep := d.rep_zero e hzero
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans hrep
      · exact ih.trans hrep.symm

/-- **`rep` coarsens the census partition.**  No hypothesis: this is
`rep_zero` propagated along a reachability chain through the vanishing
slots. -/
theorem rep_eq_of_compFold_eq (d : DegSpec n p) {u v : Fin n}
    (h : compFold d.core d.zeroSlotSet u = compFold d.core d.zeroSlotSet v) :
    d.rep u = d.rep v :=
  d.rep_eq_of_reachIn ((compFold_iff d.core d.zeroSlotSet u v).mp h)

/-- **An honest face has a forest vanishing set.**  If `rep`'s classes really
are generated by the vanishing slots — which is what every metric degeneration
gives, and what `RepIsContraction` names — then the two partitions coincide,
so their class counts agree, and the `forest` *cardinality* field upgrades to
`IsForest`.

Contrapositively: the faces the `forest` field admits but no degeneration
produces are exactly the **non-forest** ones.  That is the precise content of
the corresponding closed-row proof module §4's counterexample. -/
theorem isForest_of_repIsContraction (d : DegSpec n p)
    (h : d.RepIsContraction) : IsForest d.core d.zeroSlotSet := by
  have hiff : ∀ x y : Fin n, d.rep x = d.rep y ↔
      compFold d.core d.zeroSlotSet x = compFold d.core d.zeroSlotSet y :=
    fun x y => ⟨fun hxy => (compFold_iff d.core d.zeroSlotSet x y).mpr (h x y hxy),
      d.rep_eq_of_compFold_eq⟩
  have hle : (Finset.univ.image d.rep).card
      ≤ (Finset.univ.image (compFold d.core d.zeroSlotSet)).card :=
    card_image_le_of_rep_iff d.rep_idem hiff
  have hge : (Finset.univ.image (compFold d.core d.zeroSlotSet)).card
      ≤ (Finset.univ.image d.rep).card :=
    card_image_le_of_rep_iff (compFold_idem d.core d.zeroSlotSet)
      (fun x y => (hiff x y).symm)
  have hforest := d.forest'
  unfold IsForest
  omega

/-- **A closed face is never loopy.**  `rep_loopless` plus the coarsening of
`rep_eq_of_compFold_eq` rules out a semantic loop on the *census* partition,
with no hypothesis at all — so the second census check a row-proof leaf asks
for is free once one has a `DegSpec` in hand. -/
theorem not_isLoopy_zeroSlotSet (d : DegSpec n p) :
    ¬ IsLoopy d.core d.zeroSlotSet := by
  rintro ⟨e, he, hEq⟩
  have hpos : 0 < d.length e := by
    rcases Nat.eq_zero_or_pos (d.length e) with h | h
    · exact absurd ((d.mem_zeroSlotSet e).mpr h) he
    · exact h
  exact d.rep_loopless e hpos (d.rep_eq_of_compFold_eq hEq)

/-- **The sharpening.**  On a forest face the coarsening of
`rep_eq_of_compFold_eq` is an equality: `rep` and `compFold` induce the *same*
partition.

Both partitions have `n - |zeroSlots|` classes — one by the `forest` field,
the other by `IsForest` — and a coarsening between partitions of equal class
count is the identity. -/
theorem compFold_eq_of_rep_eq (d : DegSpec n p)
    (hForest : IsForest d.core d.zeroSlotSet) {u v : Fin n}
    (h : d.rep u = d.rep v) :
    compFold d.core d.zeroSlotSet u = compFold d.core d.zeroSlotSet v := by
  classical
  have hcoarse : ∀ x : Fin n,
      d.rep (compFold d.core d.zeroSlotSet x) = d.rep x := fun x =>
    d.rep_eq_of_compFold_eq (compFold_idem d.core d.zeroSlotSet x)
  have himg : (Finset.univ.image (compFold d.core d.zeroSlotSet)).image d.rep
      = Finset.univ.image d.rep := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨z, ⟨x, hx⟩, hz⟩
      exact ⟨x, by rw [← hz, ← hx, hcoarse x]⟩
    · rintro ⟨x, hx⟩
      exact ⟨compFold d.core d.zeroSlotSet x, ⟨x, rfl⟩, by rw [hcoarse x]; exact hx⟩
  have hcard : (Finset.univ.image d.rep).card
      = (Finset.univ.image (compFold d.core d.zeroSlotSet)).card := by
    have h1 : (Finset.univ.image (compFold d.core d.zeroSlotSet)).card
        + d.zeroSlotSet.card = n := forest_image_add_card_eq d.core hForest
    have h2 : (Finset.univ.image d.rep).card + d.zeroSlotSet.card = n := d.forest
    omega
  have hinj : Set.InjOn d.rep
      ↑(Finset.univ.image (compFold d.core d.zeroSlotSet)) := by
    refine Finset.injOn_of_card_image_eq ?_
    rw [himg, hcard]
  refine hinj ?_ ?_ ?_
  · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  · rw [hcoarse u, hcoarse v]; exact h

/-- The sharpening, as the partition identity. -/
theorem rep_iff_compFold (d : DegSpec n p)
    (hForest : IsForest d.core d.zeroSlotSet) (u v : Fin n) :
    d.rep u = d.rep v ↔
      compFold d.core d.zeroSlotSet u = compFold d.core d.zeroSlotSet v :=
  ⟨d.compFold_eq_of_rep_eq hForest, d.rep_eq_of_compFold_eq⟩

/-! ## The census face -/

/-- The **census face** of a forest face: the same core and the same lengths,
with `rep` replaced by the union-find component map of the vanishing slots —
that is, by exactly the `rep` a census-facing producer builds
(the corresponding closed-row proof module).

No `¬ IsLoopy` hypothesis is needed: `rep_loopless` is inherited from `d`
through `rep_eq_of_compFold_eq`. -/
def censusFace (d : DegSpec n p) (hForest : IsForest d.core d.zeroSlotSet) :
    DegSpec n p where
  core := d.core
  length := d.length
  core_nonempty := d.core_nonempty
  rep := compFold d.core d.zeroSlotSet
  rep_idem := compFold_idem d.core d.zeroSlotSet
  rep_zero := fun e he =>
    compFold_tail_eq_head_of_mem d.core ((d.mem_zeroSlotSet e).mpr he)
  rep_loopless := fun e he hEq =>
    d.rep_loopless e he (d.rep_eq_of_compFold_eq hEq)
  forest := forest_image_add_card_eq d.core hForest

@[simp] theorem censusFace_core (d : DegSpec n p)
    (hForest : IsForest d.core d.zeroSlotSet) :
    (d.censusFace hForest).core = d.core := rfl

@[simp] theorem censusFace_length (d : DegSpec n p)
    (hForest : IsForest d.core d.zeroSlotSet) :
    (d.censusFace hForest).length = d.length := rfl

@[simp] theorem censusFace_rep (d : DegSpec n p)
    (hForest : IsForest d.core d.zeroSlotSet) :
    (d.censusFace hForest).rep = compFold d.core d.zeroSlotSet := rfl

/-- **The payoff.**  Every forest face is `LaplacianEquiv` to its census
face. -/
noncomputable def censusFaceEquiv (d : DegSpec n p)
    (hForest : IsForest d.core d.zeroSlotSet) :
    LaplacianEquiv d.graph (d.censusFace hForest).graph :=
  repEquiv d (d.censusFace hForest) rfl rfl (d.rep_iff_compFold hForest)

/-- …matching core vertex for core vertex, so a pinned mark survives. -/
theorem censusFaceEquiv_coreVertex (d : DegSpec n p)
    (hForest : IsForest d.core d.zeroSlotSet) (v : Fin n) :
    d.censusFaceEquiv hForest (d.coreVertex v)
      = (d.censusFace hForest).coreVertex v :=
  repEquiv_coreVertex d (d.censusFace hForest) rfl rfl
    (d.rep_iff_compFold hForest) v

end Utilities.Certificate.DegenerateSpec.DegSpec
