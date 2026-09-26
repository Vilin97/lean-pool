/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Accessible
public import LeanPool.Schoenflies.AccessibleJoin
public import LeanPool.Schoenflies.SkeletonAccess

/-!
# Access from a fresh anchor, for `thm:finite-transfer`(b)

Direction (b) of `thm:finite-transfer` transfers a target refinement back to the source. Every
step of its induction is the same as direction (a)'s except one: when the target ear starts at
a point of `S`, that point is by hypothesis a fresh image `u(a)` of an anchor `a ∈ 𝒜`, and the
*source* endpoint `a` lies on the wild curve `C`, where no polygonal skeleton reaches it and
`lem:polygonal-side-accessibility` says nothing. The blueprint's paragraph is:

> The union `K` of all old closed nonboundary edges and the finitely many source ears already
> inserted is compact and does not contain `a`. By `lem:tangent-cone`, a tangent disk at `a`
> contains an open cone of access segments. By `lem:compact-separation`(c), shrink that cone
> until it misses `K`. Its punctured part is connected, lies in the complement of the current
> skeleton, and accumulates at `a`; therefore it lies in the unique current source 2-cell just
> identified. It supplies the required access arc.

That paragraph is proved here, end to end, as `Schoenflies.polyAccessible_of_stronglyAccessible`.

## The three facts about the cone that the paragraph needs

`Schoenflies.accessCone` is on `main` (`Schoenflies/Accessible.lean`) with its openness, its
truncation, and `StronglyAccessible.exists_cone` — a cone of *any* radius below the radius of
the tangent disk lies in the domain, which is exactly the shrinking the paragraph performs.
What was missing is the three properties that make it usable as the connected set of
`lem:cellulation-invariants`(i):

* it is **convex**, hence preconnected (`convex_accessCone`, `isPreconnected_accessCone`) —
  the condition `‖x - p‖/2 < ⟪v, x - p⟫` is the superlevel set of a concave function and the
  truncation is a ball;
* the apex is in its **closure** (`mem_closure_accessCone`) — this is "accumulates at `a`",
  and it is what identifies the cell;
* it contains a straight **access segment** from the apex (`polyAccessible_accessCone`), which
  is `Schoenflies.PolyAccessible` in the shape `lem:accessible-endpoints` consumes.

Note that no *puncturing* is needed: `Schoenflies.notMem_accessCone` says the apex is not in the
cone to begin with, so the blueprint's "its punctured part" is the cone itself.

## Which 2-cell, and why that is a hypothesis

"Therefore it lies in the unique current source 2-cell just identified" has two halves. That the
cone lies in *some* 2-cell is proved here, from `Schoenflies.CellsAbsorb` — the same single
hypothesis `Schoenflies/SkeletonAccess.lean` carries, discharged by
`Schoenflies.cellsAbsorb_of_isComponent` or `.cellsAbsorb_of_isComponent_in` — together with a
covering clause. That the cell is the *prescribed* one is the separate combinatorial paragraph
of the blueprint ("each of the resulting outer subedges is incident with exactly one source
2-cell … hence exactly one descendant 2-cell remains incident with `a`"), an induction over the
ear sequence, and it enters here as the hypothesis `hunique`: *the only cell whose closure
contains `a` is `F`*. That is a statement about the ear induction, not about the geometry of the
cone, and the induction is what will discharge it.

## Blueprint

* `Schoenflies.convex_accessCone`, `Schoenflies.isPreconnected_accessCone`,
  `Schoenflies.mem_closure_accessCone`, `Schoenflies.polyAccessible_accessCone` — the three
  properties of the cone of `lem:tangent-cone` that `thm:finite-transfer`(b) uses.
* `Schoenflies.exists_accessCone_disjoint` — "by `lem:compact-separation`(c), shrink that cone
  until it misses `K`", combining `lem:tangent-cone` with `lem:compact-separation`(c).
* `Schoenflies.accessCone_subset_cell` — "its punctured part is connected, lies in the
  complement of the current skeleton, and accumulates at `a`; therefore it lies in the unique
  current source 2-cell", from `lem:cellulation-invariants`(i) in the `CellsAbsorb` reading.
* `Schoenflies.CellsAbsorbIn`, `Schoenflies.accessCone_subset_cell_in` — the domain-restricted
  form actually used in direction (b): the access cone already lies in the Jordan domain, so
  absorption is needed only for connected subsets of that domain.
* `Schoenflies.polyAccessible_of_stronglyAccessible` — the whole paragraph: a strongly
  accessible point of the wild curve is polygonally accessible from the current source 2-cell
  incident with it. This is the one input direction (b) needs beyond direction (a).
* `Schoenflies.polyAccessible_of_stronglyAccessible_in` — the same conclusion from the
  domain-restricted absorption interface.
-/

public section

open Metric Set

namespace Schoenflies

variable {D K F N : Set Plane} {cells : Set (Set Plane)} {p v a z : Plane} {r s t ε : ℝ}

/-! ### The cone is convex

`accessCone p v s` is cut out of the ball `B(p, s)` by `‖x - p‖/2 < ⟪v, x - p⟫`. Both halves
are convex — the second because `y ↦ ⟪v, y⟫ - ‖y‖/2` is concave — so the cone is, and in
particular it is connected, which is what `lem:cellulation-invariants`(i) asks of it. -/

/-- The truncated access cone is convex. -/
theorem convex_accessCone (p v : Plane) (s : ℝ) : Convex ℝ (accessCone p v s) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ α β hα hβ hαβ
  have hβ' : β = 1 - α := by linarith
  subst hβ'
  -- Abbreviations for the two distances and the two inner products.
  set A := ‖x - p‖ with hA
  set B := ‖y - p‖ with hB
  set Ix := inner ℝ v (x - p) with hIx
  set Iy := inner ℝ v (y - p) with hIy
  -- Everything happens in the translated coordinates.
  have hshift : α • x + (1 - α) • y - p = α • (x - p) + (1 - α) • (y - p) := by module
  have hnorm : ‖α • x + (1 - α) • y - p‖ ≤ α * A + (1 - α) * B := by
    rw [hshift]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα,
      abs_of_nonneg hβ]
  have hinner : inner ℝ v (α • x + (1 - α) • y - p) = α * Ix + (1 - α) * Iy := by
    rw [hshift, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  -- A convex combination lies between the minimum and the maximum of its two arguments.
  have hcomb : ∀ c d : ℝ, min c d ≤ α * c + (1 - α) * d ∧ α * c + (1 - α) * d ≤ max c d := by
    intro c d
    have h1 : α * min c d ≤ α * c := mul_le_mul_of_nonneg_left (min_le_left _ _) hα
    have h2 : (1 - α) * min c d ≤ (1 - α) * d := mul_le_mul_of_nonneg_left (min_le_right _ _) hβ
    have h3 : α * c ≤ α * max c d := mul_le_mul_of_nonneg_left (le_max_left _ _) hα
    have h4 : (1 - α) * d ≤ (1 - α) * max c d := mul_le_mul_of_nonneg_left (le_max_right _ _) hβ
    constructor <;> nlinarith
  refine ⟨hnorm.trans_lt (lt_of_le_of_lt (hcomb A B).2 (max_lt hx1 hy1)), ?_⟩
  -- The cone defect `⟪v, z⟫ - ‖z‖/2` is at least the minimum of the two defects, so positive.
  rw [hinner]
  have hdef : min (Ix - A / 2) (Iy - B / 2) ≤ α * (Ix - A / 2) + (1 - α) * (Iy - B / 2) :=
    (hcomb (Ix - A / 2) (Iy - B / 2)).1
  have hminpos : 0 < min (Ix - A / 2) (Iy - B / 2) :=
    lt_min (by linarith) (by linarith)
  nlinarith

/-- The truncated access cone is preconnected: it is convex. -/
theorem isPreconnected_accessCone (p v : Plane) (s : ℝ) :
    IsPreconnected (accessCone p v s) := (convex_accessCone p v s).isPreconnected

/-! ### The cone accumulates at its apex

`Schoenflies.notMem_accessCone` says the apex is *not* a point of the cone; this says it is a
limit of points of it. That is the blueprint's "accumulates at `a`", and it is what turns
"the cone lies in some 2-cell" into "the cone lies in a 2-cell incident with `a`". -/

/-- The inner product of a unit vector with itself clears the cone condition. Used three times
below, always to point the access segment along the axis of the cone. -/
private theorem half_lt_inner_self (hv : ‖v‖ = 1) : 1 / 2 < inner ℝ v v := by
  rw [real_inner_self_eq_norm_sq, hv]
  norm_num

/-- The distance from the apex to a point of the axis. -/
private theorem dist_apex_axis (hv : ‖v‖ = 1) (ht : 0 < t) : dist p (p + t • v) = t := by
  have hshift : p + t • v - p = t • v := by module
  rw [dist_comm, dist_eq_norm, hshift, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one]

/-- The apex lies in the closure of its own access cone. -/
theorem mem_closure_accessCone (hv : ‖v‖ = 1) (hs : 0 < s) : p ∈ closure (accessCone p v s) := by
  refine Metric.mem_closure_iff.2 fun ε hε => ⟨p + (min ε s / 2) • v, ?_, ?_⟩
  · have hpos : 0 < min ε s / 2 := by positivity
    have hlt : min ε s / 2 < s := by
      have := min_le_right ε s
      linarith
    exact mem_accessCone hv (half_lt_inner_self hv) hpos hlt
  · have hpos : 0 < min ε s / 2 := by positivity
    rw [dist_apex_axis hv hpos]
    have := min_le_left ε s
    linarith

/-- **The straight access segment.** The cone contains an open segment leaving the apex, so the
apex is polygonally accessible from anything containing the cone. This is `PolyAccessible` in
the shape `lem:accessible-endpoints` consumes. -/
theorem polyAccessible_accessCone (hv : ‖v‖ = 1) (hs : 0 < s) (hsub : accessCone p v s ⊆ N) :
    PolyAccessible N p := by
  have hhalf : (0:ℝ) < s / 2 := by linarith
  have hmono : accessCone p v (s / 2) ⊆ accessCone p v s := accessCone_mono (by linarith)
  have hz : p + (s / 2) • v ∈ accessCone p v s :=
    mem_accessCone hv (half_lt_inner_self hv) hhalf (by linarith)
  refine PolyAccessible.of_openSegment (hsub hz) ?_
  exact ((openSegment_subset_accessCone hv (half_lt_inner_self hv) hhalf).trans hmono).trans hsub

/-! ### Shrinking the cone off the compact part already built -/

/-- **"Shrink that cone until it misses `K`."** A strongly accessible point off a compact set
has an access cone into the domain that is disjoint from that set. `lem:tangent-cone` supplies
the cone and `lem:compact-separation`(c) the radius. -/
theorem exists_accessCone_disjoint (h : StronglyAccessible D a) (hK : IsCompact K) (ha : a ∉ K) :
    ∃ (v : Plane) (s : ℝ), ‖v‖ = 1 ∧ 0 < s ∧ accessCone a v s ⊆ D ∧
      Disjoint (accessCone a v s) K := by
  obtain ⟨v, hv, r, hr, hcone⟩ := h.exists_cone
  obtain ⟨ρ, hρ, hball⟩ := Plane.exists_ball_subset_diff isOpen_univ hK ⟨mem_univ a, ha⟩
  refine ⟨v, min r ρ, hv, lt_min hr hρ, hcone _ (min_le_left _ _), ?_⟩
  refine Set.disjoint_left.2 fun x hx hxK => ?_
  exact (hball (accessCone_subset_ball_self (accessCone_mono (min_le_right r ρ) hx))).2 hxK

/-! ### Which cell the cone lies in -/

/-- Absorption by cells for connected sets already known to lie in an ambient domain.  This is
the precise form needed for a tangent cone inside a Jordan domain when `K` contains only the
closed nonboundary edges and not the wild boundary itself. -/
def CellsAbsorbIn (D K : Set Plane) (cells : Set (Set Plane)) : Prop :=
  ∀ N : Set Plane, N ⊆ D → IsPreconnected N → Disjoint N K →
    ∀ R ∈ cells, (N ∩ R).Nonempty → N ⊆ R

/-- Global absorption implies its domain-restricted form. -/
theorem CellsAbsorb.cellsAbsorbIn (h : CellsAbsorb K cells) : CellsAbsorbIn D K cells :=
  fun N _ hN hdisj R hR hmeet => h N hN hdisj R hR hmeet

/-- **"Therefore it lies in the unique current source 2-cell just identified."** A connected set
disjoint from the current skeleton, contained in a region the cells cover, lies in a single
cell; the closure clause then names it.

`hcover` is the covering half of `lem:cellulation-invariants`(i) — every point of the region off
the skeleton is in an open cell — and `habs` is the absorption half, `Schoenflies.CellsAbsorb`.
`hunique` is the combinatorial paragraph of `thm:finite-transfer`(b), not a geometric fact: it
says that exactly one current 2-cell is incident with `a`. -/
theorem accessCone_subset_cell (habs : CellsAbsorb K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F)
    (hv : ‖v‖ = 1) (hs : 0 < s) (hD : accessCone a v s ⊆ D)
    (hdisj : Disjoint (accessCone a v s) K) :
    accessCone a v s ⊆ F := by
  -- Some point of the cone lies in some cell, and absorption carries the whole cone into it.
  obtain ⟨x, hx⟩ := accessCone_nonempty hv hs
  obtain ⟨R, hR, hxR⟩ := hcover x (hD hx) (Set.disjoint_left.1 hdisj hx)
  have hsub : accessCone a v s ⊆ R :=
    habs _ (isPreconnected_accessCone a v s) hdisj R hR ⟨x, hx, hxR⟩
  -- The cone accumulates at `a`, so `R` is incident with `a`, so `R` is the prescribed cell.
  rw [← hunique R hR (closure_mono hsub (mem_closure_accessCone hv hs))]
  exact hsub

/-- The unique-cell argument with absorption required only inside the ambient domain. -/
theorem accessCone_subset_cell_in (habs : CellsAbsorbIn D K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F)
    (hv : ‖v‖ = 1) (hs : 0 < s) (hD : accessCone a v s ⊆ D)
    (hdisj : Disjoint (accessCone a v s) K) :
    accessCone a v s ⊆ F := by
  obtain ⟨x, hx⟩ := accessCone_nonempty hv hs
  obtain ⟨R, hR, hxR⟩ := hcover x (hD hx) (Set.disjoint_left.1 hdisj hx)
  have hsub : accessCone a v s ⊆ R :=
    habs _ hD (isPreconnected_accessCone a v s) hdisj R hR ⟨x, hx, hxR⟩
  rw [← hunique R hR (closure_mono hsub (mem_closure_accessCone hv hs))]
  exact hsub

/-! ### The paragraph -/

/-- **The source access arc at a fresh anchor** — the one input `thm:finite-transfer`(b) needs
beyond direction (a).

A strongly accessible point `a` of the wild curve, off the compact set `K` of everything already
drawn, is polygonally accessible from the current source 2-cell `F` incident with it. Compare
`lem:polygonal-side-accessibility`, which does the same job at every point *off* `C` and is
useless here precisely because `a ∈ C`.

`lem:accessible-endpoints` (`Schoenflies.exists_crosscut_of_polyAccessible`) turns this, together
with the accessibility of the other endpoint, into the polygonal crosscut the ear needs. -/
theorem polyAccessible_of_stronglyAccessible (h : StronglyAccessible D a) (hK : IsCompact K)
    (ha : a ∉ K) (habs : CellsAbsorb K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F) :
    PolyAccessible F a := by
  obtain ⟨v, s, hv, hs, hD, hdisj⟩ := exists_accessCone_disjoint h hK ha
  exact polyAccessible_accessCone hv hs
    (accessCone_subset_cell habs hcover hunique hv hs hD hdisj)

/-- The fresh-anchor paragraph with the absorption invariant stated only inside the Jordan
domain, where the tangent cone is already known to lie. -/
theorem polyAccessible_of_stronglyAccessible_in (h : StronglyAccessible D a)
    (hK : IsCompact K) (ha : a ∉ K) (habs : CellsAbsorbIn D K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F) :
    PolyAccessible F a := by
  obtain ⟨v, s, hv, hs, hD, hdisj⟩ := exists_accessCone_disjoint h hK ha
  exact polyAccessible_accessCone hv hs
    (accessCone_subset_cell_in habs hcover hunique hv hs hD hdisj)

end Schoenflies
