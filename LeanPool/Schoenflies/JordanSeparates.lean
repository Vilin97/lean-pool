/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Graph.K33Land
public import LeanPool.Schoenflies.Graph.OuterFace
public import LeanPool.Schoenflies.TwoArcs
public import LeanPool.Schoenflies.SimpleArc
public import LeanPool.Schoenflies.SegmentCut
public import LeanPool.Schoenflies.SegmentOrder

/-!
# A Jordan curve separates the plane

Half of the Jordan curve theorem: the complement of a Jordan curve `C` is disconnected. The
proof is the blueprint's — build a subdivision of `K(3,3)` out of the curve, a chord of it, a
detour above it, and a connecting arc, and appeal to `Graph.IsArcK33.elim`.

## The configuration

Fix a coordinate `i` in which `C` has nonzero width, and let `j` be the other one. Write `m`
and `M` for the extreme `i`-coordinates on `C`, and let `p₁`, `p₂` be the points of `C` on the
two supporting lines `{z | z i = m}`, `{z | z i = M}` with the largest `j`-coordinate. Two
points of a Jordan curve cut it into two arcs `C₁`, `C₂` (`IsJordanCurve.two_arcs`). Both meet
the middle line `{z | z i = (m + M) / 2}`, by the intermediate value theorem; a closest pair
`a ∈ C₁`, `b ∈ C₂` on that line spans a segment `L₄` whose interior misses `C`. Running up the
two supporting lines and across above the curve gives a polygonal set meeting `C` exactly in
`{p₁, p₂}` and missing `L₄`; a simple arc `L₅` inside it (`exists_simple_poly_of_poly`) is the
blueprint's detour.

The blueprint argues inside the unbounded component: it supposes `L₄ \ {a, b}` to lie there,
and concludes that it does not. Here the contradiction hypothesis is the statement being
negated — that the whole complement is preconnected — which is weaker to assume and gives the
same `K(3,3)`. Nothing about the unbounded component is needed, so nothing about it is proved;
`exists_unique_unbounded_connectedComponentIn_compl` at the end is the separate cheap fact.

*If* the complement were preconnected, a simple polygonal arc `R` inside it would join an
interior point of `L₄` to an interior point of `L₅`. Its last parameter on `L₄` and the first
one after that on `L₅` cut out a piece `L₆` meeting `L₄ ∪ L₅` only at its two ends — this is
why the blueprint takes such care over the order in which `c'` and `d'` are chosen. Cutting
`C₁` at `a`, `C₂` at `b`, `L₅` at the far end `d'` of `L₆` and `L₄` at its near end `c'`
produces nine arcs on the six points `{p₁, p₂, c'}`, `{a, b, d'}`, meeting only where a
`K(3,3)` forces them to. That is impossible, so the complement is not preconnected.

## Coordinates instead of a rotation

The blueprint rotates so that the direction of nonzero width becomes horizontal. Here the two
coordinate indices are carried as parameters `i ≠ j` of `not_isPreconnected_compl_of_coord`
instead, and the headline theorem picks whichever pair works. No rotation, no trigonometry and
no coordinate-swap symmetry lemma is needed: every step is symmetric in the two indices except
for which one is named.

The blueprint's opening step — a Jordan curve is not contained in a line — is not needed in
this form. All it is used for is a direction of nonzero width, and that follows from the curve
having two distinct points (`IsJordanCurve.exists_ne`). The degenerate configurations the
blueprint's step rules out are excluded downstream instead, by `C₁ ∩ C₂ = {p₁, p₂}`.

## Blueprint

* `Schoenflies.not_isPreconnected_compl_of_coord`,
  `Schoenflies.IsJordanCurve.not_isPreconnected_compl`,
  `Schoenflies.IsJordanCurve.exists_connectedComponentIn_ne` — `prop:jordan-disconnected`.
* `Schoenflies.exists_unique_unbounded_connectedComponentIn_compl` — the opening sentence of
  the blueprint's Jordan section: the complement of a compact set has exactly one unbounded
  component.
* `Graph.isArcK33_of_pieces` — the packaging of `cor:k33-subdivision` (through
  `Graph.IsArcK33.elim`) that this configuration fits.
* `Schoenflies.IsArcBetween.exists_split` — an arc cut at an interior point; the arc analogue
  of the second clause of `lem:jordan-circle`, which `Schoenflies.IsJordanCurve.two_arcs` is.

## For the integrator

Three groups of declarations here are general and have no home yet on `main`:

* `Schoenflies.Plane.coord_ext`, `axisVec`, `setCoord`, `coord_eq_of_mem_segment`,
  `le_coord_of_mem_segment`, `coord_le_of_mem_segment` belong beside the coordinate
  half-planes in `Schoenflies/Square.lean`.
* `Schoenflies.IsArcBetween.exists_split` belongs in `Schoenflies/Subarc.lean`, next to
  `IsArc.exists_isArcBetween_subset`; `Schoenflies.injective_three` is a `Fin 3` triviality.
* `Graph.isArcK33_of_pieces` belongs in `Schoenflies/Graph/K33Planar.lean`, next to
  `Graph.IsArcK33`.
-/

@[expose] public section

open Metric Set unitInterval

namespace Schoenflies

namespace Plane

/-- Two points of the plane agreeing in two distinct coordinates are equal. -/
theorem coord_ext {i j : Fin 2} (hij : i ≠ j) {z w : Plane} (hi : z i = w i) (hj : z j = w j) :
    z = w := by
  ext k
  have hk : k = i ∨ k = j := by
    revert hij; fin_cases i <;> fin_cases j <;> intro hij <;> fin_cases k <;> simp_all
  rcases hk with rfl | rfl
  · exact hi
  · exact hj

/-- The unit vector along the coordinate axis `j`. -/
noncomputable def axisVec (j : Fin 2) : Plane :=
  mk (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)

@[simp] theorem axisVec_self (j : Fin 2) : axisVec j j = 1 := by
  fin_cases j <;> simp [axisVec]

theorem axisVec_of_ne {i j : Fin 2} (h : i ≠ j) : axisVec j i = 0 := by
  revert h; fin_cases i <;> fin_cases j <;> intro h <;> simp_all [axisVec]

/-- The point obtained from `z` by moving its `j`-th coordinate to `t` and leaving the other
coordinate where it was. This is how the two upper corners of the polygonal detour above the
curve are named without committing to which of the two coordinates is the horizontal one. -/
noncomputable def setCoord (z : Plane) (j : Fin 2) (t : ℝ) : Plane :=
  z + (t - z j) • axisVec j

@[simp] theorem setCoord_self (z : Plane) (j : Fin 2) (t : ℝ) : setCoord z j t j = t := by
  simp [setCoord]

theorem setCoord_of_ne {i j : Fin 2} (h : i ≠ j) (z : Plane) (t : ℝ) :
    setCoord z j t i = z i := by
  simp [setCoord, axisVec_of_ne h]

/-! ### Coordinates along a segment -/

variable {k : Fin 2} {r : ℝ} {s t z : Plane}

/-- A coordinate constant at both ends of a segment is constant along it. -/
theorem coord_eq_of_mem_segment (hs : s k = r) (ht : t k = r) (hz : z ∈ segment ℝ s t) :
    z k = r :=
  le_antisymm ((convex_coord_le k r).segment_subset hs.le ht.le hz)
    ((convex_coord_ge k r).segment_subset hs.ge ht.ge hz)

/-- A lower bound on a coordinate at both ends of a segment holds along it. -/
theorem le_coord_of_mem_segment (hs : r ≤ s k) (ht : r ≤ t k) (hz : z ∈ segment ℝ s t) :
    r ≤ z k :=
  (convex_coord_ge k r).segment_subset hs ht hz

/-- An upper bound on a coordinate at both ends of a segment holds along it. -/
theorem coord_le_of_mem_segment (hs : s k ≤ r) (ht : t k ≤ r) (hz : z ∈ segment ℝ s t) :
    z k ≤ r :=
  (convex_coord_le k r).segment_subset hs ht hz

end Plane

/-- Injectivity of a three-element vector, from the three distinctness facts. -/
theorem injective_three {α : Type*} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all

/-! ### Cutting an arc at an interior point -/

/-- **An arc splits at any of its interior points** into two arcs which cover it and meet
exactly there. This is the arc analogue of `IsJordanCurve.two_arcs`, and is what turns each
branch of the configuration below into two branch paths of the `K(3,3)`. -/
theorem IsArcBetween.exists_split {A : Set Plane} {p q z : Plane} (h : IsArcBetween A p q)
    (hz : z ∈ A) (hzp : z ≠ p) (hzq : z ≠ q) :
    ∃ A₁ A₂, IsArcBetween A₁ p z ∧ IsArcBetween A₂ z q ∧ A₁ ∪ A₂ = A ∧ A₁ ∩ A₂ = {z} := by
  obtain ⟨f, hc, hi, rfl, rfl, rfl⟩ := h
  obtain ⟨r, hr, rfl⟩ := hz
  have hr0 : (0 : ℝ) ≠ r := fun hc => hzp (by rw [hc])
  have hr1 : r ≠ (1 : ℝ) := fun hc => hzq (by rw [hc])
  have hsub₁ : Icc (0 : ℝ) r ⊆ I := Icc_subset_Icc le_rfl hr.2
  have hsub₂ : Icc r (1 : ℝ) ⊆ I := Icc_subset_Icc hr.1 le_rfl
  refine ⟨f '' Icc 0 r, f '' Icc r 1, ?_, ?_, ?_, ?_⟩
  · have := isArcBetween_subarc_of_injOn_I hc hi zero_mem_I hr hr0
    rwa [uIcc_of_le hr.1] at this
  · have := isArcBetween_subarc_of_injOn_I hc hi hr one_mem_I hr1
    rwa [uIcc_of_le hr.2] at this
  · rw [← image_union, Icc_union_Icc_eq_Icc hr.1 hr.2]
  · rw [← hi.image_inter hsub₁ hsub₂, Icc_inter_Icc, max_eq_right hr.1, min_eq_left hr.2,
      Icc_self, image_singleton]

end Schoenflies

namespace Graph

open Schoenflies

/-- **Nine arcs assembled from three chains, two bridges of a fourth, and a ninth arc.**

This is a packaging lemma: it repackages the `meet` clause of `Graph.IsArcK33` as the five
containment facts that a `K(3,3)` subdivision found inside a plane configuration actually
produces. The rows `0` and `1` of `P` are the two halves of three chains `Ch 0, Ch 1, Ch 2`
running from `x 0` to `x 1`, each cut at the point `y j`; row `2` holds three further pieces,
carried by sets `Sg j`, that all issue from `x 2`.

The hypotheses are exactly what the separation proof below has to hand, and nothing about
their geometry is used: only the listed intersections. -/
theorem isArcK33_of_pieces {x y : Fin 3 → Plane} {P : Fin 3 → Fin 3 → Set Plane}
    {Ch Sg : Fin 3 → Set Plane}
    (harc : ∀ i j, IsArcBetween (P i j) (x i) (y j))
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j)
    (hsubCh₀ : ∀ j, P 0 j ⊆ Ch j) (hsubCh₁ : ∀ j, P 1 j ⊆ Ch j) (hsubSg : ∀ j, P 2 j ⊆ Sg j)
    (hsplit : ∀ j, P 0 j ∩ P 1 j ⊆ {y j})
    (hChCh : ∀ j l, j ≠ l → Ch j ∩ Ch l ⊆ {x 0, x 1})
    (hChSg : ∀ j l, Ch j ∩ Sg l ⊆ {y j})
    (hSgSg : ∀ j l, j ≠ l → P 2 j ∩ P 2 l ⊆ {x 2}) :
    IsArcK33 x y P := by
  -- `x 0` is an endpoint of every piece in row `0`; were it also on a piece of row `1` it would
  -- be the cut point `y j` the two share, and the six points are distinct.
  have hx0 : ∀ j, x 0 ∉ P 1 j := fun j hmem =>
    hxy 0 j (hsplit j ⟨(harc 0 j).left_mem, hmem⟩)
  have hx1 : ∀ j, x 1 ∉ P 0 j := fun j hmem =>
    hxy 1 j (hsplit j ⟨hmem, (harc 1 j).left_mem⟩)
  have hrow : ∀ m : Fin 3, m ≠ 2 → m = 0 ∨ m = 1 := by decide
  have hsubCh : ∀ i j, i ≠ 2 → P i j ⊆ Ch j := by
    intro i j hi
    rcases hrow i hi with rfl | rfl
    exacts [hsubCh₀ j, hsubCh₁ j]
  -- Half of the `meet` clause; the other half is this one with the two index pairs exchanged.
  have key : ∀ i j k l : Fin 3, (i, j) ≠ (k, l) → P i j ∩ P k l ⊆ ({x i, y j} : Set Plane) := by
    rintro i j k l hne z ⟨hz1, hz2⟩
    rcases eq_or_ne i 2 with rfl | hi2
    · rcases eq_or_ne k 2 with rfl | hk2
      · -- Two pieces of the bottom row: they meet only at `x 2`.
        exact Or.inl (hSgSg j l (fun h => hne (by rw [h])) ⟨hz1, hz2⟩)
      · -- A bottom-row piece against a piece of the chain `Ch l`.
        have hzl : z = y l := hChSg l j ⟨hsubCh k l hk2 hz2, hsubSg j hz1⟩
        rcases eq_or_ne j l with rfl | hjl
        · exact Or.inr hzl
        · -- `y l` is an endpoint of `P 2 l` too, so it is on two bottom-row pieces: it is `x 2`.
          exact Or.inl (hSgSg l j (Ne.symm hjl)
            ⟨by rw [hzl]; exact (harc 2 l).right_mem, hz1⟩)
    · rcases eq_or_ne k 2 with rfl | hk2
      · exact Or.inr (hChSg j l ⟨hsubCh i j hi2 hz1, hsubSg l hz2⟩)
      · rcases eq_or_ne j l with rfl | hjl
        · -- Same chain, the two halves: they meet at the cut point.
          have hik : i ≠ k := fun h => hne (by rw [h])
          rcases hrow i hi2 with rfl | rfl <;> rcases hrow k hk2 with rfl | rfl
          · exact absurd rfl hik
          · exact Or.inr (hsplit j ⟨hz1, hz2⟩)
          · exact Or.inr (hsplit j ⟨hz2, hz1⟩)
          · exact absurd rfl hik
        · -- Distinct chains: their common points are the two ends `x 0`, `x 1`.
          rcases hChCh j l hjl ⟨hsubCh i j hi2 hz1, hsubCh k l hk2 hz2⟩ with rfl | rfl
          · rcases hrow i hi2 with rfl | rfl
            · exact Or.inl rfl
            · exact absurd hz1 (hx0 j)
          · rcases hrow i hi2 with rfl | rfl
            · exact absurd hz1 (hx1 j)
            · exact Or.inl rfl
  exact { arc := harc, x_injective := hx, y_injective := hy, ne := hxy,
          meet := fun i j k l hne => subset_inter (key i j k l hne)
            (by rw [inter_comm]; exact key k l i j (Ne.symm hne)) }

end Graph

namespace Schoenflies

open Plane

/-! ### The separation proof -/

/-- A chord and an exterior detour across the two arcs force a planar `K(3,3)`
configuration if the complement were connected. -/
theorem not_isPreconnected_of_arc_chord_detour
    {C C₁ C₂ L₅ : Set Plane} {p₁ p₂ a b : Plane}
    (hCopen : IsOpen Cᶜ) (harc₁ : IsArcBetween C₁ p₁ p₂)
    (harc₂ : IsArcBetween C₂ p₁ p₂) (hL₅arc : IsArcBetween L₅ p₁ p₂)
    (hcover : C₁ ∪ C₂ = C) (hCmeet : C₁ ∩ C₂ = {p₁, p₂})
    (haC₁ : a ∈ C₁) (hbC₂ : b ∈ C₂)
    (ha_ne : a ≠ p₁ ∧ a ≠ p₂) (hb_ne : b ≠ p₁ ∧ b ≠ p₂) (hab_ne : a ≠ b)
    (hopenSeg : ∀ z ∈ openSegment ℝ a b, z ∉ C)
    (hL₅C : ∀ z ∈ L₅, z ∈ C → z = p₁ ∨ z = p₂)
    (hL₅L₄ : ∀ z ∈ L₅, z ∉ segment ℝ a b) : ¬ IsPreconnected Cᶜ := by
  intro hconn
  have hC₁sub : C₁ ⊆ C := by rw [← hcover]; exact subset_union_left
  have hC₂sub : C₂ ⊆ C := by rw [← hcover]; exact subset_union_right
  have hp₁C : p₁ ∈ C := hC₁sub harc₁.left_mem
  have hp₂C : p₂ ∈ C := hC₁sub harc₁.right_mem
  have hp₁p₂ : p₁ ≠ p₂ := harc₁.ne
  have hsegC : ∀ z ∈ segment ℝ a b, z ∈ C → z = a ∨ z = b := by
    intro z hz hzC
    rw [← insert_endpoints_openSegment] at hz
    rcases hz with rfl | rfl | hz
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hzC (hopenSeg z hz)
  -- ## Interior points of the two crossings
  obtain ⟨d, hdL₅, hdp₁, hdp₂⟩ : ∃ d ∈ L₅, d ≠ p₁ ∧ d ≠ p₂ := by
    obtain ⟨g, -, hgi, hgim, hg0, hg1⟩ := hL₅arc
    have hhalf : (1 / 2 : ℝ) ∈ I := ⟨by norm_num, by norm_num⟩
    refine ⟨g (1 / 2), by rw [← hgim]; exact mem_image_of_mem g hhalf, ?_, ?_⟩
    · rw [← hg0]; intro hcon; have := hgi hhalf zero_mem_I hcon; norm_num at this
    · rw [← hg1]; intro hcon; have := hgi hhalf one_mem_I hcon; norm_num at this
  obtain ⟨cpt, hcptOpen⟩ : ∃ c : Plane, c ∈ openSegment ℝ a b :=
    ⟨_, ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, rfl⟩⟩
  have hcptSeg : cpt ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hcptOpen
  have hcptCc : cpt ∈ Cᶜ := hopenSeg cpt hcptOpen
  have hdCc : d ∈ Cᶜ := fun hcon => by
    rcases hL₅C d hdL₅ hcon with h | h
    exacts [hdp₁ h, hdp₂ h]
  have hcd : cpt ≠ d := fun h => hL₅L₄ d hdL₅ (h ▸ hcptSeg)
  -- ## A simple polygonal arc joining them in the complement
  obtain ⟨R, hRsub, -, hRarc⟩ := exists_simple_arc_of_isPreconnected hCopen hconn hcptCc hdCc hcd
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hRarc
  have hL₄closed : IsClosed (segment ℝ a b) := (isCompact_segment a b).isClosed
  have hL₅closed : IsClosed L₅ := hL₅arc.isArc.isClosed
  -- The last parameter at which the arc is on the closest-pair segment ...
  obtain ⟨sp, hspI, hspSeg, hspmax⟩ :
      ∃ s ∈ I, f s ∈ segment ℝ a b ∧ ∀ t ∈ I, f t ∈ segment ℝ a b → t ≤ s := by
    have hcl : IsClosed (I ∩ f ⁻¹' segment ℝ a b) :=
      hfc.preimage_isClosed_of_isClosed isClosed_Icc hL₄closed
    have h0 : (0 : ℝ) ∈ I ∩ f ⁻¹' segment ℝ a b :=
      ⟨zero_mem_I, by rw [mem_preimage, hf0]; exact hcptSeg⟩
    have hbdd : BddAbove (I ∩ f ⁻¹' segment ℝ a b) := ⟨1, fun t ht => ht.1.2⟩
    obtain ⟨h1, h2⟩ := hcl.csSup_mem ⟨0, h0⟩ hbdd
    exact ⟨_, h1, h2, fun t ht hmem => le_csSup hbdd ⟨ht, hmem⟩⟩
  -- ... and the first parameter after it at which the arc is on the detour.
  obtain ⟨tp, htpmem, htpL₅, htpmin⟩ :
      ∃ t ∈ Icc sp 1, f t ∈ L₅ ∧ ∀ r ∈ Icc sp 1, f r ∈ L₅ → t ≤ r := by
    have hcl : IsClosed (Icc sp 1 ∩ f ⁻¹' L₅) :=
      (hfc.mono (Icc_subset_Icc hspI.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc hL₅closed
    have h1mem : (1 : ℝ) ∈ Icc sp 1 ∩ f ⁻¹' L₅ :=
      ⟨⟨hspI.2, le_rfl⟩, by rw [mem_preimage, hf1]; exact hdL₅⟩
    have hbdd : BddBelow (Icc sp 1 ∩ f ⁻¹' L₅) := ⟨sp, fun t ht => ht.1.1⟩
    obtain ⟨h1, h2⟩ := hcl.csInf_mem ⟨1, h1mem⟩ hbdd
    exact ⟨_, h1, h2, fun r hr hmem => csInf_le hbdd ⟨hr, hmem⟩⟩
  have htpI : tp ∈ I := ⟨hspI.1.trans htpmem.1, htpmem.2⟩
  have hsptp : sp ≠ tp := fun hcon => hL₅L₄ (f tp) htpL₅ (hcon ▸ hspSeg)
  -- ## The last branch arc: the piece of `R` between those two parameters
  obtain ⟨L₆, hL₆arc, hL₆C, hL₆L₄, hL₆L₅⟩ :
      ∃ L₆, IsArcBetween L₆ (f sp) (f tp) ∧ (∀ z ∈ L₆, z ∉ C) ∧
        (∀ z ∈ L₆, z ∈ segment ℝ a b → z = f sp) ∧ (∀ z ∈ L₆, z ∈ L₅ → z = f tp) := by
    refine ⟨f '' Icc sp tp, ?_, ?_, ?_, ?_⟩
    · have := isArcBetween_subarc_of_injOn_I hfc hfi hspI htpI hsptp
      rwa [uIcc_of_le (lt_of_le_of_ne htpmem.1 hsptp).le] at this
    · rintro _ ⟨r, hr, rfl⟩
      exact hRsub (by rw [← hfim]; exact mem_image_of_mem f ⟨hspI.1.trans hr.1, hr.2.trans htpI.2⟩)
    · rintro _ ⟨r, hr, rfl⟩ hmem
      rw [le_antisymm (hspmax r ⟨hspI.1.trans hr.1, hr.2.trans htpI.2⟩ hmem) hr.1]
    · rintro _ ⟨r, hr, rfl⟩ hmem
      rw [le_antisymm hr.2 (htpmin r ⟨hr.1, hr.2.trans htpI.2⟩ hmem)]
  have hcpC : f sp ∉ C := hL₆C _ hL₆arc.left_mem
  have hdpC : f tp ∉ C := hL₆C _ hL₆arc.right_mem
  -- ## The six branch vertices are six distinct points
  have hp₁a : p₁ ≠ a := fun h => ha_ne.1 h.symm
  have hp₁b : p₁ ≠ b := fun h => hb_ne.1 h.symm
  have hp₂a : p₂ ≠ a := fun h => ha_ne.2 h.symm
  have hp₂b : p₂ ≠ b := fun h => hb_ne.2 h.symm
  have hp₁dp : p₁ ≠ f tp := fun h => hdpC (h ▸ hp₁C)
  have hp₂dp : p₂ ≠ f tp := fun h => hdpC (h ▸ hp₂C)
  have hp₁cp : p₁ ≠ f sp := fun h => hcpC (h ▸ hp₁C)
  have hp₂cp : p₂ ≠ f sp := fun h => hcpC (h ▸ hp₂C)
  have hcpa : f sp ≠ a := fun h => hcpC (h ▸ hC₁sub haC₁)
  have hcpb : f sp ≠ b := fun h => hcpC (h ▸ hC₂sub hbC₂)
  have hdpa : f tp ≠ a := fun h => hdpC (h ▸ hC₁sub haC₁)
  have hdpb : f tp ≠ b := fun h => hdpC (h ▸ hC₂sub hbC₂)
  have hcpdp : f sp ≠ f tp := fun h => hL₅L₄ (f tp) htpL₅ (h ▸ hspSeg)
  -- ## Cutting the four branches
  obtain ⟨A₁, A₂, hA₁, hA₂, hAcov, hAmeet⟩ :=
    harc₁.exists_split haC₁ ha_ne.1 ha_ne.2
  obtain ⟨B₁, B₂, hB₁, hB₂, hBcov, hBmeet⟩ :=
    harc₂.exists_split hbC₂ hb_ne.1 hb_ne.2
  obtain ⟨E₁, E₂, hE₁, hE₂, hEcov, hEmeet⟩ := hL₅arc.exists_split htpL₅ hp₁dp.symm hp₂dp.symm
  obtain ⟨D₁, D₂, hD₁, hD₂, hDcov, hDmeet⟩ :=
    (isArcBetween_segment hab_ne).exists_split hspSeg hcpa hcpb
  have hA₁sub : A₁ ⊆ C₁ := by rw [← hAcov]; exact subset_union_left
  have hA₂sub : A₂ ⊆ C₁ := by rw [← hAcov]; exact subset_union_right
  have hB₁sub : B₁ ⊆ C₂ := by rw [← hBcov]; exact subset_union_left
  have hB₂sub : B₂ ⊆ C₂ := by rw [← hBcov]; exact subset_union_right
  have hE₁sub : E₁ ⊆ L₅ := by rw [← hEcov]; exact subset_union_left
  have hE₂sub : E₂ ⊆ L₅ := by rw [← hEcov]; exact subset_union_right
  have hD₁sub : D₁ ⊆ segment ℝ a b := by rw [← hDcov]; exact subset_union_left
  have hD₂sub : D₂ ⊆ segment ℝ a b := by rw [← hDcov]; exact subset_union_right
  -- ## The remaining pairwise intersections
  have hbC₁ : b ∉ C₁ := by
    intro hcon
    have hmem : b ∈ C₁ ∩ C₂ := ⟨hcon, hbC₂⟩
    rw [hCmeet] at hmem
    rcases hmem with h | h
    exacts [hb_ne.1 h, hb_ne.2 h]
  have haC₂ : a ∉ C₂ := by
    intro hcon
    have hmem : a ∈ C₁ ∩ C₂ := ⟨haC₁, hcon⟩
    rw [hCmeet] at hmem
    rcases hmem with h | h
    exacts [ha_ne.1 h, ha_ne.2 h]
  have hC₁L₄ : ∀ z ∈ C₁, z ∈ segment ℝ a b → z = a := by
    intro z h1 h2
    rcases hsegC z h2 (hC₁sub h1) with h | h
    exacts [h, absurd (h ▸ h1) hbC₁]
  have hC₂L₄ : ∀ z ∈ C₂, z ∈ segment ℝ a b → z = b := by
    intro z h1 h2
    rcases hsegC z h2 (hC₂sub h1) with h | h
    exacts [absurd (h ▸ h1) haC₂, h]
  -- ## The configuration is a subdivision of `K(3,3)`, which the plane cannot carry
  -- The bipartition is `{p₁, p₂, c'}` against `{a, b, d'}`, with `c' = f sp` and `d' = f tp`.
  -- Row `i`, column `j` of `P` is the branch path from the `i`-th point of the first side to
  -- the `j`-th point of the second: the halves of `C₁`, `C₂` and `L₅` in rows `0` and `1`, the
  -- two halves of the chord `L₄` and the connecting arc `L₆` in row `2`.
  refine (Graph.isArcK33_of_pieces (x := ![p₁, p₂, f sp]) (y := ![a, b, f tp])
    (P := ![![A₁, B₁, E₁], ![A₂, B₂, E₂], ![D₁, D₂, L₆]])
    (Ch := ![C₁, C₂, L₅]) (Sg := ![segment ℝ a b, segment ℝ a b, L₆])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).elim
  · intro r c
    fin_cases r <;> fin_cases c
    exacts [hA₁, hB₁, hE₁, hA₂.reverse, hB₂.reverse, hE₂.reverse, hD₁.reverse, hD₂, hL₆arc]
  · exact injective_three hp₁p₂ hp₁cp hp₂cp
  · exact injective_three hab_ne hdpa.symm hdpb.symm
  · intro r c
    fin_cases r <;> fin_cases c
    exacts [hp₁a, hp₁b, hp₁dp, hp₂a, hp₂b, hp₂dp, hcpa, hcpb, hcpdp]
  · intro c; fin_cases c
    exacts [hA₁sub, hB₁sub, hE₁sub]
  · intro c; fin_cases c
    exacts [hA₂sub, hB₂sub, hE₂sub]
  · intro c; fin_cases c
    exacts [hD₁sub, hD₂sub, subset_rfl]
  · intro c; fin_cases c
    exacts [hAmeet.subset, hBmeet.subset, hEmeet.subset]
  · intro c e hne
    fin_cases c <;> fin_cases e
    · exact absurd rfl hne
    · exact hCmeet.subset
    · rintro z ⟨h1, h2⟩; exact hL₅C z h2 (hC₁sub h1)
    · rintro z ⟨h1, h2⟩; exact hCmeet.subset ⟨h2, h1⟩
    · exact absurd rfl hne
    · rintro z ⟨h1, h2⟩; exact hL₅C z h2 (hC₂sub h1)
    · rintro z ⟨h1, h2⟩; exact hL₅C z h1 (hC₁sub h2)
    · rintro z ⟨h1, h2⟩; exact hL₅C z h1 (hC₂sub h2)
    · exact absurd rfl hne
  · intro c e
    fin_cases c <;> fin_cases e
    · rintro z ⟨h1, h2⟩; exact hC₁L₄ z h1 h2
    · rintro z ⟨h1, h2⟩; exact hC₁L₄ z h1 h2
    · rintro z ⟨h1, h2⟩; exact absurd (hC₁sub h1) (hL₆C z h2)
    · rintro z ⟨h1, h2⟩; exact hC₂L₄ z h1 h2
    · rintro z ⟨h1, h2⟩; exact hC₂L₄ z h1 h2
    · rintro z ⟨h1, h2⟩; exact absurd (hC₂sub h1) (hL₆C z h2)
    · rintro z ⟨h1, h2⟩; exact absurd h2 (hL₅L₄ z h1)
    · rintro z ⟨h1, h2⟩; exact absurd h2 (hL₅L₄ z h1)
    · rintro z ⟨h1, h2⟩; exact hL₆L₅ z h2 h1
  · intro c e hne
    fin_cases c <;> fin_cases e
    · exact absurd rfl hne
    · exact hDmeet.subset
    · rintro z ⟨h1, h2⟩; exact hL₆L₄ z h2 (hD₁sub h1)
    · rintro z ⟨h1, h2⟩; exact hDmeet.subset ⟨h2, h1⟩
    · exact absurd rfl hne
    · rintro z ⟨h1, h2⟩; exact hL₆L₄ z h2 (hD₂sub h1)
    · rintro z ⟨h1, h2⟩; exact hL₆L₄ z h1 (hD₁sub h2)
    · rintro z ⟨h1, h2⟩; exact hL₆L₄ z h1 (hD₂sub h2)
    · exact absurd rfl hne


/-- **Proposition 3.2 (a Jordan curve separates)**, with the coordinate direction named.

`i` is the blueprint's horizontal direction and `j` its vertical one; the hypothesis on `u`
and `v` is that the projection of `C` to the `i`-th coordinate has nonzero width, which is all
the blueprint's rotation achieves. `IsJordanCurve.not_isPreconnected_compl` discharges it. -/
theorem not_isPreconnected_compl_of_coord {C : Set Plane} (hC : IsJordanCurve C)
    {i j : Fin 2} (hij : i ≠ j) {u v : Plane} (hu : u ∈ C) (hv : v ∈ C) (huv : u i ≠ v i) :
    ¬ IsPreconnected Cᶜ := by
  intro hconn
  have hCcomp : IsCompact C := hC.isCompact
  have hCopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hCne : C.Nonempty := ⟨u, hu⟩
  have hlineClosed : ∀ r : ℝ, IsClosed {z : Plane | z i = r} := fun r =>
    isClosed_eq (continuous_coord i) continuous_const
  -- ## The two supporting lines
  obtain ⟨z₁, hz₁C, hz₁min⟩ := hCcomp.exists_isMinOn hCne (continuous_coord i).continuousOn
  obtain ⟨z₂, hz₂C, hz₂max⟩ := hCcomp.exists_isMaxOn hCne (continuous_coord i).continuousOn
  have hmin : ∀ z ∈ C, z₁ i ≤ z i := isMinOn_iff.mp hz₁min
  have hmax : ∀ z ∈ C, z i ≤ z₂ i := isMaxOn_iff.mp hz₂max
  set m : ℝ := z₁ i
  set M : ℝ := z₂ i
  -- The curve has two points with different `i`-coordinates, so the strip between the two
  -- supporting lines is nondegenerate: were the two extremes equal, every point of `C` would
  -- be squeezed onto that one value.
  have hmM : m < M := by
    rcases eq_or_lt_of_le (hmin z₂ hz₂C) with h | h
    · refine absurd ?_ huv
      rw [le_antisymm (by rw [h]; exact hmax u hu) (hmin u hu),
        le_antisymm (by rw [h]; exact hmax v hv) (hmin v hv)]
    · exact h
  -- ## The highest point of the curve on each supporting line
  obtain ⟨p₁, hp₁mem, hp₁max⟩ := (hCcomp.inter_right (hlineClosed m)).exists_isMaxOn
    ⟨z₁, hz₁C, rfl⟩ (continuous_coord j).continuousOn
  obtain ⟨p₂, hp₂mem, hp₂max⟩ := (hCcomp.inter_right (hlineClosed M)).exists_isMaxOn
    ⟨z₂, hz₂C, rfl⟩ (continuous_coord j).continuousOn
  have hp₁C : p₁ ∈ C := hp₁mem.1
  have hp₂C : p₂ ∈ C := hp₂mem.1
  have hp₁i : p₁ i = m := hp₁mem.2
  have hp₂i : p₂ i = M := hp₂mem.2
  have hp₁top : ∀ z ∈ C, z i = m → z j ≤ p₁ j := fun z hz hzi => isMaxOn_iff.mp hp₁max z ⟨hz, hzi⟩
  have hp₂top : ∀ z ∈ C, z i = M → z j ≤ p₂ j := fun z hz hzi => isMaxOn_iff.mp hp₂max z ⟨hz, hzi⟩
  have hp₁p₂ : p₁ ≠ p₂ := by
    intro h; rw [h, hp₂i] at hp₁i; exact hmM.ne' hp₁i
  -- ## The two arcs of the curve between them
  obtain ⟨C₁, C₂, harc₁, harc₂, hcover, hCmeet⟩ := hC.two_arcs hp₁C hp₂C hp₁p₂
  have hC₁sub : C₁ ⊆ C := by rw [← hcover]; exact subset_union_left
  have hC₂sub : C₂ ⊆ C := by rw [← hcover]; exact subset_union_right
  -- ## A line strictly between the two supporting lines
  set mid : ℝ := (m + M) / 2 with hmid
  have hmmid : m < mid := by rw [hmid]; linarith
  have hmidM : mid < M := by rw [hmid]; linarith
  -- A point on that line is neither of the two chosen curve points.
  have hne_mid : ∀ z : Plane, z i = mid → z ≠ p₁ ∧ z ≠ p₂ := by
    refine fun z hz => ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, hp₁i] at hz; exact hmmid.ne hz
    · rw [h, hp₂i] at hz; exact hmidM.ne' hz
  -- Both arcs meet the middle line, by the intermediate value theorem on the `i`-coordinate.
  have hmeets : ∀ A : Set Plane, IsArcBetween A p₁ p₂ → ∃ z ∈ A, z i = mid := by
    intro A hA
    have hIVT := hA.isArc.isConnected.isPreconnected.intermediate_value hA.left_mem hA.right_mem
      (continuous_coord i).continuousOn
    exact hIVT (show mid ∈ Icc (p₁ i) (p₂ i) by rw [hp₁i, hp₂i]; exact ⟨hmmid.le, hmidM.le⟩)
  obtain ⟨w₁, hw₁A, hw₁i⟩ := hmeets C₁ harc₁
  obtain ⟨w₂, hw₂A, hw₂i⟩ := hmeets C₂ harc₂
  -- ## The closest pair on the middle line
  obtain ⟨⟨a, b⟩, hab, habmin⟩ :=
    ((harc₁.isArc.isCompact.inter_right (hlineClosed mid)).prod
      (harc₂.isArc.isCompact.inter_right (hlineClosed mid))).exists_isMinOn
      ⟨(w₁, w₂), ⟨⟨hw₁A, hw₁i⟩, ⟨hw₂A, hw₂i⟩⟩⟩ continuous_dist.continuousOn
  obtain ⟨haC₁, hai⟩ := hab.1
  obtain ⟨hbC₂, hbi⟩ := hab.2
  have hminab : ∀ s ∈ C₁ ∩ {z : Plane | z i = mid}, ∀ t ∈ C₂ ∩ {z : Plane | z i = mid},
      dist a b ≤ dist s t := fun s hs t ht => isMinOn_iff.mp habmin (s, t) ⟨hs, ht⟩
  have hab_ne : a ≠ b := by
    intro h
    have hmem : a ∈ C₁ ∩ C₂ := ⟨haC₁, h ▸ hbC₂⟩
    rw [hCmeet] at hmem
    rcases hmem with h₁ | h₁
    · exact (hne_mid a hai).1 h₁
    · exact (hne_mid a hai).2 h₁
  -- The open segment between the closest pair misses the curve.
  have hopenSeg : ∀ z ∈ openSegment ℝ a b, z ∉ C := by
    intro z hz hzC
    have hzseg : z ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hz
    have hzi : z i = mid := coord_eq_of_mem_segment hai hbi hzseg
    have hlt : dist a z < dist a b :=
      (dist_lt_of_mem_openSegment hab_ne (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
        hab_ne (by simp) hz).2
    have hgt : dist b z < dist b a :=
      (dist_lt_of_mem_openSegment hab_ne.symm (left_mem_segment ℝ b a) (right_mem_segment ℝ b a)
        hab_ne.symm (by simp) (by rwa [openSegment_symm] at hz)).2
    rw [← hcover] at hzC
    rcases hzC with h | h
    · exact absurd (hminab z ⟨h, hzi⟩ b ⟨hbC₂, hbi⟩)
        (not_le.mpr (by rw [dist_comm z b, dist_comm a b]; exact hgt))
    · exact absurd (hminab a ⟨haC₁, hai⟩ z ⟨h, hzi⟩) (not_le.mpr hlt)
  -- ## The detour above the curve
  obtain ⟨z₃, hz₃C, hz₃max⟩ := hCcomp.exists_isMaxOn hCne (continuous_coord j).continuousOn
  set top : ℝ := z₃ j + 1 with htop
  have hCtop : ∀ z ∈ C, z j < top := by
    intro z hz; have := isMaxOn_iff.mp hz₃max z hz; rw [htop]; linarith
  set q₁ : Plane := setCoord p₁ j top with hq₁
  set q₂ : Plane := setCoord p₂ j top with hq₂
  have hq₁i : q₁ i = m := by rw [hq₁, setCoord_of_ne hij, hp₁i]
  have hq₂i : q₂ i = M := by rw [hq₂, setCoord_of_ne hij, hp₂i]
  have hq₁j : q₁ j = top := by rw [hq₁, setCoord_self]
  have hq₂j : q₂ j = top := by rw [hq₂, setCoord_self]
  have hWeq : poly [p₁, q₁, q₂, p₂] =
      segment ℝ p₁ q₁ ∪ (segment ℝ q₁ q₂ ∪ segment ℝ q₂ p₂) := by
    rw [poly_cons_cons, poly_cons_cons, poly_pair]
  -- The detour meets the curve exactly at its two endpoints ...
  have hWsubC : ∀ z ∈ poly [p₁, q₁, q₂, p₂], z ∈ C → z = p₁ ∨ z = p₂ := by
    intro z hzW hzC
    rw [hWeq] at hzW
    rcases hzW with h | h | h
    · refine Or.inl (coord_ext hij ?_ ?_)
      · rw [coord_eq_of_mem_segment hp₁i hq₁i h, hp₁i]
      · exact le_antisymm (hp₁top z hzC (coord_eq_of_mem_segment hp₁i hq₁i h))
          (le_coord_of_mem_segment le_rfl (by rw [hq₁j]; exact (hCtop p₁ hp₁C).le) h)
    · exact absurd (hCtop z hzC) (by rw [coord_eq_of_mem_segment hq₁j hq₂j h]; exact lt_irrefl top)
    · refine Or.inr (coord_ext hij ?_ ?_)
      · rw [coord_eq_of_mem_segment hq₂i hp₂i h, hp₂i]
      · exact le_antisymm (hp₂top z hzC (coord_eq_of_mem_segment hq₂i hp₂i h))
          (le_coord_of_mem_segment (by rw [hq₂j]; exact (hCtop p₂ hp₂C).le) le_rfl h)
  -- ... and misses the closest-pair segment altogether.
  have hWL₄ : ∀ z ∈ poly [p₁, q₁, q₂, p₂], z ∉ segment ℝ a b := by
    intro z hzW hzL₄
    have hzmid : z i = mid := coord_eq_of_mem_segment hai hbi hzL₄
    rw [hWeq] at hzW
    rcases hzW with h | h | h
    · rw [coord_eq_of_mem_segment hp₁i hq₁i h] at hzmid; exact hmmid.ne hzmid
    · have hzj : z j ≤ z₃ j := coord_le_of_mem_segment
        (isMaxOn_iff.mp hz₃max a (hC₁sub haC₁)) (isMaxOn_iff.mp hz₃max b (hC₂sub hbC₂)) hzL₄
      rw [coord_eq_of_mem_segment hq₁j hq₂j h, htop] at hzj; linarith
    · rw [coord_eq_of_mem_segment hq₂i hp₂i h] at hzmid; exact hmidM.ne' hzmid
  -- ## The detour, made into a simple arc
  obtain ⟨L₅, hL₅sub, hL₅arc⟩ : ∃ A ⊆ poly [p₁, q₁, q₂, p₂], IsArcBetween A p₁ p₂ := by
    have hlne : ([p₁, q₁, q₂, p₂] : List Plane) ≠ [] := by simp
    obtain ⟨ws, -, -, -, hsub, harc⟩ := exists_simple_poly_of_poly
      (vs := [p₁, q₁, q₂, p₂]) (isConnected_poly hlne).isPreconnected hp₁p₂
      (mem_poly_of_mem (by simp)) (mem_poly_of_mem (by simp))
    exact ⟨poly ws, hsub, harc⟩
  have hL₅C : ∀ z ∈ L₅, z ∈ C → z = p₁ ∨ z = p₂ := fun z hz => hWsubC z (hL₅sub hz)
  have hL₅L₄ : ∀ z ∈ L₅, z ∉ segment ℝ a b := fun z hz => hWL₄ z (hL₅sub hz)
  exact not_isPreconnected_of_arc_chord_detour hCopen harc₁ harc₂ hL₅arc hcover hCmeet
    haC₁ hbC₂ (hne_mid a hai) (hne_mid b hbi) hab_ne hopenSeg hL₅C hL₅L₄ hconn

/-! ### The headline -/

/-- A Jordan curve carries two distinct points: the loop parametrising it is injective on
`[0, 1)`, which has two distinct points. -/
theorem IsJordanCurve.exists_ne {C : Set Plane} (hC : IsJordanCurve C) :
    ∃ u ∈ C, ∃ v ∈ C, u ≠ v := by
  obtain ⟨g, hg, rfl⟩ := hC
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hh : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨g 0, mem_image_of_mem g zero_mem_I, g (1 / 2),
    mem_image_of_mem g ⟨by norm_num, by norm_num⟩, fun hcon => ?_⟩
  have := hg.injOn h0 hh hcon
  norm_num at this

/-- **Proposition 3.2 (a Jordan curve separates the plane).** The complement of a Jordan curve
is not preconnected.

The direction hypothesis of `not_isPreconnected_compl_of_coord` is discharged here: the curve
has two distinct points, so they differ in one of the two coordinates, and that coordinate
plays the role of the blueprint's horizontal one. No rotation is performed — the proof is run
for whichever coordinate projection has nonzero width, with the two coordinate indices carried
as parameters. -/
theorem IsJordanCurve.not_isPreconnected_compl {C : Set Plane} (hC : IsJordanCurve C) :
    ¬ IsPreconnected Cᶜ := by
  obtain ⟨u, hu, v, hv, huv⟩ := hC.exists_ne
  have hk : ∃ k : Fin 2, u k ≠ v k := by
    by_contra hcon
    push Not at hcon
    exact huv (by ext k; exact hcon k)
  obtain ⟨k, hk⟩ := hk
  fin_cases k
  · exact not_isPreconnected_compl_of_coord hC (i := 0) (j := 1) (by decide) hu hv hk
  · exact not_isPreconnected_compl_of_coord hC (i := 1) (j := 0) (by decide) hu hv hk

/-- **Proposition 3.2, in the form the Jordan curve theorem consumes**: the complement of a
Jordan curve has at least two connected components. Stated as two of its points lying in
different components, since that is what `thm:jordan` starts from.

It is genuinely the same statement: a set all of whose points share one component *is* that
component, and a component is preconnected. -/
theorem IsJordanCurve.exists_connectedComponentIn_ne {C : Set Plane} (hC : IsJordanCurve C) :
    ∃ u ∈ Cᶜ, ∃ v ∈ Cᶜ, connectedComponentIn Cᶜ u ≠ connectedComponentIn Cᶜ v := by
  by_contra hcon
  push Not at hcon
  -- The complement is nonempty: the empty set is preconnected, and this one is not.
  rcases eq_empty_or_nonempty Cᶜ with hempty | ⟨u, hu⟩
  · exact hC.not_isPreconnected_compl (hempty ▸ isPreconnected_empty)
  · have heq : Cᶜ = connectedComponentIn Cᶜ u := by
      refine subset_antisymm (fun v hv => ?_) (connectedComponentIn_subset _ _)
      rw [← hcon v hv u hu]
      exact mem_connectedComponentIn hv
    exact hC.not_isPreconnected_compl (by rw [heq]; exact isPreconnected_connectedComponentIn)

/-! ### The unbounded component

Cheap, and what `thm:jordan` needs to name the exterior: a compact set sits inside a square,
the outside of that square is connected and misses it, so the whole outside lies in one
component of the complement — the only unbounded one. -/

/-- **The unbounded component of the complement of a compact set.** It exists, it swallows the
outside of any square containing the set, and it is the only unbounded component. -/
theorem exists_unique_unbounded_connectedComponentIn_compl {C : Set Plane} (hC : IsCompact C) :
    ∃ base ∈ Cᶜ, ¬ Bornology.IsBounded (connectedComponentIn Cᶜ base) ∧
      ∀ z ∈ Cᶜ, ¬ Bornology.IsBounded (connectedComponentIn Cᶜ z) →
        connectedComponentIn Cᶜ z = connectedComponentIn Cᶜ base := by
  obtain ⟨r, -, hr⟩ := hC.exists_closedSquare
  have hbeyond : beyondSquare r ⊆ Cᶜ := by
    rw [beyondSquare_eq_compl]; exact compl_subset_compl.mpr hr
  obtain ⟨base, hbase⟩ : (beyondSquare r).Nonempty := (isConnected_beyondSquare r).nonempty
  -- The outside of the square is preconnected and inside the complement, so it lies in the
  -- single component named by any of its points.
  have hsub : beyondSquare r ⊆ connectedComponentIn Cᶜ base :=
    (isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn hbase hbeyond
  refine ⟨base, hbeyond hbase, fun hb => Graph.not_isBounded_beyondSquare r (hb.subset hsub), ?_⟩
  intro z hz hzu
  -- An unbounded component escapes the square, so it meets the outside, so it is that one.
  obtain ⟨w, hw1, hw2⟩ : ∃ w, w ∈ connectedComponentIn Cᶜ z ∧ w ∈ beyondSquare r := by
    by_contra hcon
    push Not at hcon
    refine hzu ((Graph.isBounded_closedSquare r).subset fun w hw => ?_)
    by_contra hout
    exact hcon w hw (by rw [beyondSquare_eq_compl]; exact hout)
  rw [connectedComponentIn_eq hw1, connectedComponentIn_eq (hsub hw2)]

end Schoenflies

