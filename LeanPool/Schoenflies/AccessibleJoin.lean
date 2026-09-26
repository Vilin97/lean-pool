/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SimpleArc
public import LeanPool.Schoenflies.Accessible
public import LeanPool.Schoenflies.LocallyPolygonal

/-!
# Joining accessible boundary points

Two boundary points of a region that are each reachable by a polygonal arc from inside can be
joined by a *single* simple polygonal arc whose interior stays inside the region. This is
`lem:accessible-endpoints`, and the same extraction — applied to a finite polygonal skeleton
rather than to a pair of access arcs — is `lem:skeleton-crosscuts`.

## The predicate

`Schoenflies.PolyAccessible Ω a` says that `a` admits a *polygonal access arc* from `Ω`: a
vertex list starting at `a`, ending inside `Ω`, all of whose points other than `a` lie in `Ω`.

The definition deliberately does **not** ask the access arc to be simple. A consumer that has
only a self-crossing approach path can still supply the hypothesis, and nothing is lost: the
extraction below re-runs `lem:finite-polygonal-union` on the whole union anyway, so simplicity
of the input is never used. `PolyAccessible.exists_simple` recovers the blueprint's literal
phrasing (*a simple polygonal arc from `a` to a point of `Ω`*) for a point off `Ω`, so the two
readings agree where the blueprint uses them.

Note also that neither the definition nor the theorems below mention `frontier Ω`. The
blueprint states `lem:accessible-endpoints` for `a, b ∈ ∂Ω`, but boundary membership plays no
role in the proof — only `a ≠ b` does — so the statements here are the stronger ones with the
hypothesis dropped. A consumer holding `a, b ∈ ∂Ω` simply does not pass it.

## The method, and where the difficulty actually is

Take an access arc from `a` and one from `b`, join their far ends inside `Ω` by
`lem:polygonal-connected` (`Schoenflies.exists_poly_of_isPreconnected`), and extract a simple
arc from the resulting three-piece polygonal union by `lem:finite-polygonal-union`
(`Schoenflies.exists_simple_poly_of_union`).

The whole content is that the extraction must keep the two endpoints and must keep everything
else inside `Ω`. Both are free from the interface actually on `main`:
`Schoenflies.exists_simple_poly_of_union` already returns a vertex list whose `head` is `a` and
whose `getLast` is `b`, together with `IsArcBetween _ a b`, so the endpoints are pinned; and it
returns the arc as a *subset of the union it was extracted from*, so `poly ws \ {a, b} ⊆ Ω`
follows from the same inclusion for the union. No endpoint-pinning lemma had to be added.

What *was* missing is a version of the extraction indexed by an arbitrary finite family rather
than by a `List (Set Plane)`: a skeleton arrives as a finite set of edges, and turning it into a
list at the call site is noise. `Schoenflies.exists_simple_poly_of_biUnion_finite` is that
version and belongs beside `Schoenflies.exists_simple_poly_of_union` in
`Schoenflies/SimpleArc.lean`.

## Blueprint

* `Schoenflies.PolyAccessible` — "admitting a polygonal access arc from `Ω`", the hypothesis of
  `lem:accessible-endpoints`.
* `Schoenflies.PolyAccessible.of_openSegment`, `Schoenflies.StronglyAccessible.polyAccessible`,
  `Schoenflies.polyAccessible_of_poly`, `Schoenflies.polyAccessible_of_poly'` — the ways the
  construction produces the hypothesis: a straight access segment, Definition 8.1 (strong
  accessibility), and a chain already known to run into `Ω` from either of its ends.
* `Schoenflies.PolyAccessible.exists_simple` — the blueprint's literal reading of the
  hypothesis, for a point off `Ω`.
* `Schoenflies.exists_simple_poly_of_biUnion_finite`,
  `Schoenflies.exists_simple_arc_of_biUnion_finite`, `Schoenflies.exists_simple_poly_pinned`,
  `Schoenflies.exists_simple_poly_of_isPolygonal_pinned` — `lem:finite-polygonal-union` over a
  finite family, and with the "off the endpoints, stay in the region" clause attached. These
  four belong in `Schoenflies/SimpleArc.lean`.
* `Graph.pointSet_eq_biUnion`, `Graph.exists_simple_poly_of_pointSet` — the same extraction on
  the point set of a finite plane graph with polygonal edges, which is the shape a skeleton
  stage arrives in. Root `Graph` namespace, per the convention of `Schoenflies/Graph/*`.
* `Schoenflies.exists_simple_poly_of_polyAccessible`,
  `Schoenflies.exists_simple_arc_of_polyAccessible` — `lem:accessible-endpoints`.
* `Schoenflies.exists_crosscut_of_polyAccessible` — `lem:accessible-endpoints` in crosscut form:
  when `Ω` misses a set `C` carrying `a` and `b`, the arc meets `C` exactly at its endpoints.
* `Schoenflies.exists_crosscut_of_biUnion_finite`,
  `Schoenflies.exists_crosscut_arc_of_biUnion_finite` — `lem:skeleton-crosscuts`, the extraction
  step: a connected finite polygonal union meeting `C` in exactly two points carries a simple
  polygonal crosscut between them.

`lem:skeleton-crosscuts` has two further halves that are **not** here, because the objects they
speak about are not yet in Lean: the construction of the connected union `Y = e_a ∪ |Λ| ∪ e_b`
from a finite stage of the skeleton, and the transport of the crosscut through the finite
skeleton homeomorphism. Both need the stage/anchor machinery of §"Continuity at the Jordan
curve"; the extraction between them is what this module supplies.
-/

public section

open Metric Set

namespace Schoenflies

variable {Ω C D S : Set Plane} {a b z : Plane}

/-! ### Polygonal accessibility -/

/-- `a` is **polygonally accessible from `Ω`**: some polygonal chain starts at `a`, ends at a
point of `Ω`, and has all of its points except `a` inside `Ω`.

Stated for a chain rather than for a simple arc; see the module docstring. -/
def PolyAccessible (Ω : Set Plane) (a : Plane) : Prop :=
  ∃ (vs : List Plane) (h : vs ≠ []), vs.head h = a ∧ vs.getLast h ∈ Ω ∧ poly vs \ {a} ⊆ Ω

/-- A point of `Ω` is accessible from it, by the constant chain. -/
theorem polyAccessible_of_mem (ha : a ∈ Ω) : PolyAccessible Ω a :=
  ⟨[a], by simp, rfl, by simpa using ha, by simp⟩

/-- Accessibility passes to a larger set. -/
theorem PolyAccessible.mono (h : PolyAccessible Ω a) (hsub : Ω ⊆ S) : PolyAccessible S a := by
  obtain ⟨vs, hvs, hhead, hlast, hint⟩ := h
  exact ⟨vs, hvs, hhead, hsub hlast, hint.trans hsub⟩

/-- A straight access segment gives accessibility. This is the form the construction meets:
`z` is an interior point seen from `a` along a segment that only touches the boundary at `a`. -/
theorem PolyAccessible.of_openSegment (hz : z ∈ Ω) (hseg : openSegment ℝ a z ⊆ Ω) :
    PolyAccessible Ω a := by
  refine ⟨[a, z], by simp, rfl, by simpa using hz, ?_⟩
  rw [poly_pair]
  rintro x ⟨hxseg, hxa⟩
  rw [mem_singleton_iff] at hxa
  -- Off the near endpoint, a point of the segment is either the far endpoint or interior to it.
  rcases eq_or_ne x z with rfl | hxz
  · exact hz
  · exact hseg (mem_openSegment_of_ne_left_right (Ne.symm hxa) (Ne.symm hxz) hxseg)

/-- **A strongly accessible point is polygonally accessible.** The straight segment to the
centre of the tangent disk is the access arc. -/
theorem StronglyAccessible.polyAccessible (h : StronglyAccessible Ω a) : PolyAccessible Ω a := by
  obtain ⟨z, hz, -, hseg⟩ := h.openSegment_subset
  exact PolyAccessible.of_openSegment hz hseg

/-- **The constructor a consumer holding an arc should use.** A chain that starts at `a`, ends
somewhere else, and has all of its other points in `Ω` is an access arc.

This is the converse direction of `lem:accessible-endpoints`: the arc that lemma produces makes
both of its endpoints accessible again, which is what an induction that extends a partial
construction one crosscut at a time needs. -/
theorem polyAccessible_of_poly {vs : List Plane} (h : vs ≠ []) (hhead : vs.head h = a)
    (hlast : vs.getLast h ≠ a) (hsub : poly vs \ {a} ⊆ Ω) : PolyAccessible Ω a :=
  ⟨vs, h, hhead, hsub ⟨getLast_mem_poly h, hlast⟩, hsub⟩

/-- `Schoenflies.polyAccessible_of_poly` read from the far end: reversing the chain moves the
distinguished endpoint from the head to the last vertex. -/
theorem polyAccessible_of_poly' {vs : List Plane} (h : vs ≠ []) (hlast : vs.getLast h = a)
    (hhead : vs.head h ≠ a) (hsub : poly vs \ {a} ⊆ Ω) : PolyAccessible Ω a := by
  have hrev : vs.reverse ≠ [] := by simpa using h
  refine polyAccessible_of_poly hrev ?_ ?_ ?_
  · rw [List.head_reverse]; exact hlast
  · rw [List.getLast_reverse]; exact hhead
  · rw [poly_reverse]; exact hsub

/-- The blueprint's literal reading of the hypothesis: for a point *off* `Ω`, a polygonal access
chain can be taken to be a simple polygonal arc.

The far endpoint is returned, so a consumer that needs to know where the arc lands still has
it. -/
theorem PolyAccessible.exists_simple (h : PolyAccessible Ω a) (ha : a ∉ Ω) :
    ∃ z ∈ Ω, a ≠ z ∧ ∃ (vs : List Plane) (hv : vs ≠ []),
      vs.head hv = a ∧ vs.getLast hv = z ∧ poly vs \ {a} ⊆ Ω ∧ IsArcBetween (poly vs) a z := by
  obtain ⟨vs, hvs, hhead, hlast, hint⟩ := h
  set z := vs.getLast hvs with hz
  have hne : a ≠ z := fun hcon => ha (hcon ▸ hlast)
  obtain ⟨ws, hws, hwhead, hwlast, hwsub, hwarc⟩ :=
    exists_simple_poly_of_poly (isConnected_poly hvs).2 hne
      (hhead ▸ head_mem_poly hvs) (getLast_mem_poly hvs)
  exact ⟨z, hlast, hne, ws, hws, hwhead, hwlast,
    fun x hx => hint ⟨hwsub hx.1, hx.2⟩, hwarc⟩

/-! ### `lem:finite-polygonal-union` over a finite family

`Schoenflies.exists_simple_poly_of_union` takes the union as a `List (Set Plane)`. A skeleton
arrives as a finite *set* of edges, so the list is pure friction at the call site. This
paragraph removes it; it belongs in `Schoenflies/SimpleArc.lean`. -/

/-- A union indexed by a list of sets, rewritten as a union indexed by the list of their
indices. -/
theorem biUnion_list_map {ι : Type*} (f : ι → Set Plane) (l : List ι) :
    (⋃ A ∈ l.map f, A) = ⋃ i ∈ l, f i := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, biUnion_list_cons (fun A : Set Plane => A),
      biUnion_list_cons f, ih]

/-- **`lem:finite-polygonal-union` for an arbitrary finite family.** If the union of finitely
many polygonal sets is connected, any two of its distinct points are joined inside it by a
simple polygonal arc.

Same conclusion as `Schoenflies.exists_simple_poly_of_union`, with the index a finite set
instead of a list. -/
theorem exists_simple_poly_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ i ∈ s, A i) ∧ IsArcBetween (poly ws) a b := by
  classical
  -- Enumerate the index set; the enumeration is only used to feed the list-indexed form.
  set l : List ι := hs.toFinset.toList with hl
  have hlmem : ∀ i, i ∈ l ↔ i ∈ s := by
    intro i; rw [hl, Finset.mem_toList, hs.mem_toFinset]
  have hU : (⋃ B ∈ l.map A, B) = ⋃ i ∈ s, A i := by
    rw [biUnion_list_map]
    exact iUnion_congr fun i => iUnion_congr_Prop (hlmem i) fun _ => rfl
  have hpoly : ∀ B ∈ l.map A, IsPolygonal B := by
    intro B hB
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hB
    exact hA i ((hlmem i).1 hi)
  have := exists_simple_poly_of_union hpoly (hU ▸ hconn) hab (hU ▸ ha) (hU ▸ hb)
  rwa [hU] at this

/-- **The endpoint-pinned extraction, in the most general form this development needs.** From a
connected finite family of polygonal sets, a simple polygonal arc between two prescribed points
of the union, staying inside the union — and, off a prescribed set `E` of exceptional points,
inside any `S` that already contains the union off `E`.

The last clause is the one the consumers of `lem:accessible-endpoints` and
`lem:skeleton-crosscuts` actually use, with `E = {a, b}` the two endpoints and `S` the region:
the extracted arc must keep its endpoints *and* keep everything else inside the region. It is a
one-line consequence of the arc being a subset of the union, but stating it here means no
consumer has to rediscover that the extraction is inclusion-preserving. -/
theorem exists_simple_poly_pinned {ι : Type*} {s : Set ι} {A : ι → Set Plane} {E : Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i)
    (hS : (⋃ i ∈ s, A i) \ E ⊆ S) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ i ∈ s, A i) ∧ poly ws \ E ⊆ S ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_biUnion_finite hs hA hconn hab ha hb
  exact ⟨ws, hws, hhead, hlast, hsub, fun x hx => hS ⟨hsub hx.1, hx.2⟩, harc⟩

/-- `Schoenflies.exists_simple_poly_pinned` for a union presented as one polygonal set. -/
theorem exists_simple_poly_of_isPolygonal_pinned {Y E : Set Plane} (hY : IsPolygonal Y)
    (hconn : IsPreconnected Y) (hab : a ≠ b) (ha : a ∈ Y) (hb : b ∈ Y) (hS : Y \ E ⊆ S) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ Y ∧ poly ws \ E ⊆ S ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_isPolygonal hY hconn hab ha hb
  exact ⟨ws, hws, hhead, hlast, hsub, fun x hx => hS ⟨hsub hx.1, hx.2⟩, harc⟩

/-- `Schoenflies.exists_simple_poly_of_biUnion_finite`, at the level of sets. -/
theorem exists_simple_arc_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i) :
    ∃ P ⊆ (⋃ i ∈ s, A i), IsPolygonal P ∧ IsArcBetween P a b := by
  obtain ⟨ws, -, -, -, hsub, harc⟩ :=
    exists_simple_poly_of_biUnion_finite hs hA hconn hab ha hb
  exact ⟨poly ws, hsub, ⟨ws, rfl⟩, harc⟩

/-! ### `lem:skeleton-crosscuts`: the extraction step

The blueprint's proof of `lem:skeleton-crosscuts` builds, from a finite stage of the skeleton, a
connected finite union `Y = e_a ∪ |Λ| ∪ e_b` of polygonal arcs with `Y ∩ C = {a, b}`, and then
says: *subdivide `Y` at its finitely many vertices; the resulting finite graph is connected, so
it contains a simple graph path `P` from `a` to `b`, as in the proof of
`lem:finite-polygonal-union`; this path meets `C` only at its endpoints and is therefore a
polygonal crosscut.* That last step is what this paragraph is. The construction of `Y` from the
skeleton needs the stage machinery and is not here. -/

/-- **`lem:skeleton-crosscuts`, extraction step.** A connected finite union of polygonal sets
which meets `C` in exactly the two distinct points `a, b` carries a simple polygonal arc from
`a` to `b` meeting `C` only at its endpoints — a polygonal crosscut.

The last conclusion, `poly ws \ {a, b} ⊆ D`, is the crosscut condition relative to a region `D`
containing the part of the union off `C`; for `D = Cᶜ` it is automatic, and the skeleton
consumer instantiates it with the interior of the Jordan curve. -/
theorem exists_crosscut_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (haC : a ∈ C) (hbC : b ∈ C)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i)
    (hmeet : (⋃ i ∈ s, A i) ∩ C ⊆ {a, b}) (hD : (⋃ i ∈ s, A i) \ C ⊆ D) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ i ∈ s, A i) ∧ IsArcBetween (poly ws) a b ∧
      poly ws ∩ C = {a, b} ∧ poly ws \ {a, b} ⊆ D := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_biUnion_finite hs hA hconn hab ha hb
  have haw : a ∈ poly ws := hhead ▸ head_mem_poly hws
  have hbw : b ∈ poly ws := hlast ▸ getLast_mem_poly hws
  refine ⟨ws, hws, hhead, hlast, hsub, harc, ?_, ?_⟩
  · refine subset_antisymm (fun x hx => hmeet ⟨hsub hx.1, hx.2⟩) ?_
    rintro x (rfl | rfl)
    exacts [⟨haw, haC⟩, ⟨hbw, hbC⟩]
  · -- Off its two endpoints the arc misses `C`, since the union meets `C` only there.
    rintro x ⟨hx, hxab⟩
    exact hD ⟨hsub hx, fun hxC => hxab (hmeet ⟨hsub hx, hxC⟩)⟩

/-- `Schoenflies.exists_crosscut_of_biUnion_finite`, at the level of sets: the crosscut as a
polygonal arc rather than as a vertex list. -/
theorem exists_crosscut_arc_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (haC : a ∈ C) (hbC : b ∈ C)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i)
    (hmeet : (⋃ i ∈ s, A i) ∩ C ⊆ {a, b}) (hD : (⋃ i ∈ s, A i) \ C ⊆ D) :
    ∃ P ⊆ (⋃ i ∈ s, A i), IsPolygonal P ∧ IsArcBetween P a b ∧
      P ∩ C = {a, b} ∧ P \ {a, b} ⊆ D := by
  obtain ⟨ws, -, -, -, hsub, harc, hcut, hint⟩ :=
    exists_crosscut_of_biUnion_finite hs hA hconn hab haC hbC ha hb hmeet hD
  exact ⟨poly ws, hsub, ⟨ws, rfl⟩, harc, hcut, hint⟩

/-! ### `lem:accessible-endpoints` -/

/-- **`lem:accessible-endpoints`: accessible endpoints can be joined.** Let `Ω` be a region and
`a ≠ b` two points each admitting a polygonal access arc from `Ω`. Then there is a simple
polygonal arc from `a` to `b` whose remaining points lie in `Ω`.

The arc is returned as a vertex list with its two ends displayed, matching
`Schoenflies.exists_simple_poly_of_union`: the consumers that overlay this arc with another
polygonal object need the vertices, not merely the set.

`a` and `b` are *not* required to lie on `frontier Ω`; the proof never uses it. -/
theorem exists_simple_poly_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hab : a ≠ b) (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws \ {a, b} ⊆ Ω ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨as, has, hahead, halast, haint⟩ := ha
  obtain ⟨bs, hbs, hbhead, hblast, hbint⟩ := hb
  -- Join the two far ends inside the region.
  obtain ⟨ms, hms, hmsub, hmhead, hmlast⟩ :=
    exists_poly_of_isPreconnected hΩ hconn halast hblast
  -- The three chains form a connected union: consecutive ones share a far end.
  set U : Set Plane := poly as ∪ (poly ms ∪ poly bs) with hU
  have hlist : (⋃ vs ∈ [as, ms, bs], poly vs) = U := by
    rw [biUnion_list_cons (fun vs : List Plane => poly vs),
      biUnion_list_cons (fun vs : List Plane => poly vs),
      biUnion_list_cons (fun vs : List Plane => poly vs), hU]
    simp
  have hconnU : IsPreconnected U := by
    refine (IsConnected.union ?_ (isConnected_poly has) (IsConnected.union ?_
      (isConnected_poly hms) (isConnected_poly hbs))).2
    · exact ⟨as.getLast has, getLast_mem_poly has,
        Or.inl (hmhead ▸ head_mem_poly hms)⟩
    · exact ⟨ms.getLast hms, getLast_mem_poly hms, hmlast ▸ getLast_mem_poly hbs⟩
  -- Off `{a, b}` the union is inside `Ω`, one piece at a time.
  have hUΩ : U \ {a, b} ⊆ Ω := by
    rintro x ⟨hx, hxab⟩
    rcases hx with hx | hx | hx
    · exact haint ⟨hx, fun hxa => hxab (Or.inl (hahead ▸ hxa))⟩
    · exact hmsub hx
    · exact hbint ⟨hx, fun hxb => hxab (Or.inr (hbhead ▸ hxb))⟩
  have haU : a ∈ U := Or.inl (hahead ▸ head_mem_poly has)
  have hbU : b ∈ U := Or.inr (Or.inr (hbhead ▸ head_mem_poly hbs))
  obtain ⟨ws, hws, hwhead, hwlast, hwsub, hwarc⟩ :=
    exists_simple_poly_of_biUnion (L := [as, ms, bs]) (hlist ▸ hconnU) hab
      (hlist ▸ haU) (hlist ▸ hbU)
  rw [hlist] at hwsub
  exact ⟨ws, hws, hwhead, hwlast, fun x hx => hUΩ ⟨hwsub hx.1, hx.2⟩, hwarc⟩

/-- **`lem:accessible-endpoints`**, at the level of sets. -/
theorem exists_simple_arc_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hab : a ≠ b) (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P a b ∧ P \ {a, b} ⊆ Ω := by
  obtain ⟨ws, -, -, -, hsub, harc⟩ :=
    exists_simple_poly_of_polyAccessible hΩ hconn hab ha hb
  exact ⟨poly ws, ⟨ws, rfl⟩, harc, hsub⟩

/-- **`lem:accessible-endpoints` in crosscut form.** If the region `Ω` misses a set `C` that
carries the two accessible points, the joining arc meets `C` exactly at its endpoints. With `C`
a Jordan curve and `Ω` its interior this says the arc is a polygonal crosscut. -/
theorem exists_crosscut_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hdisj : Disjoint Ω C) (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws \ {a, b} ⊆ Ω ∧ IsArcBetween (poly ws) a b ∧ poly ws ∩ C = {a, b} := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_polyAccessible hΩ hconn hab ha hb
  refine ⟨ws, hws, hhead, hlast, hsub, harc, subset_antisymm ?_ ?_⟩
  · -- A point of the arc off `{a, b}` lies in `Ω`, which misses `C`.
    rintro x ⟨hxw, hxC⟩
    by_contra hxab
    exact (hdisj.ne_of_mem (hsub ⟨hxw, hxab⟩) hxC) rfl
  · rintro x (rfl | rfl)
    exacts [⟨hhead ▸ head_mem_poly hws, haC⟩, ⟨hlast ▸ getLast_mem_poly hws, hbC⟩]

end Schoenflies

/-! ### The extraction on the point set of a finite polygonal plane graph

A skeleton stage arrives as a plane graph, and what the crosscut is extracted from is its point
set. Splitting that into "one singleton per vertex, one arc per edge" is the only step between
`Schoenflies.exists_simple_poly_of_biUnion_finite` and the graph, so it is done once here.

Following the convention of `Schoenflies/Graph/*`, these live in the root `Graph` namespace. -/

namespace Graph

open Schoenflies Set

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {a b : Plane}

/-- The point set of a plane graph, written as a union indexed by "a vertex or an edge". Each
piece is polygonal as soon as the edge arcs are: a vertex contributes a singleton. -/
theorem pointSet_eq_biUnion (G : Graph Plane β) (drawing : β → ℝ → Plane) :
    pointSet G drawing =
      ⋃ i ∈ (Sum.inl '' V(G) ∪ Sum.inr '' E(G) : Set (Plane ⊕ β)),
        Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing) i := by
  rw [biUnion_union, biUnion_image, biUnion_image]
  simp only [Sum.elim_inl, Sum.elim_inr, biUnion_of_singleton]
  rfl

/-- **The endpoint-pinned extraction on a plane graph.** If a finite plane graph has polygonal
edges and a connected point set, any two distinct points of that set are joined inside it by a
simple polygonal arc.

No drawing condition is needed: the extraction re-subdivides everything anyway, so the edges may
cross each other freely. -/
theorem exists_simple_poly_of_pointSet [G.Finite]
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hconn : IsPreconnected (pointSet G drawing)) (hab : a ≠ b)
    (ha : a ∈ pointSet G drawing) (hb : b ∈ pointSet G drawing) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ pointSet G drawing ∧ IsArcBetween (poly ws) a b := by
  have hfin : (Sum.inl '' V(G) ∪ Sum.inr '' E(G) : Set (Plane ⊕ β)).Finite :=
    ((G.finite_vertexSet).image _).union ((G.finite_edgeSet).image _)
  have hA : ∀ i ∈ (Sum.inl '' V(G) ∪ Sum.inr '' E(G) : Set (Plane ⊕ β)),
      IsPolygonal (Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing) i) := by
    rintro (v | e) hi
    · exact ⟨[v], rfl⟩
    · refine hpoly e ?_
      rcases hi with ⟨x, -, hx⟩ | ⟨x, hx, hx'⟩
      · exact absurd hx (by simp)
      · exact (Sum.inr_injective hx') ▸ hx
  rw [pointSet_eq_biUnion G drawing] at hconn ha hb ⊢
  exact exists_simple_poly_of_biUnion_finite hfin hA hconn hab ha hb

end Graph
