/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.BoundaryContinuity
public import LeanPool.Schoenflies.Endgame

/-!
# Continuity at the Jordan curve, and `thm:square-extension`

The last three statements of the manuscript: `lem:crosscut-side-correspondence`,
`prop:boundary-continuity`, and the assembly of `thm:square-extension` from them.

`Schoenflies/BoundaryContinuity.lean` proves the statement with the real combinatorial content,
`lem:skeleton-crosscuts` (`Graph.IsStageOn.exists_crosscut`), for one finite
plane graph. This module takes the crosscuts as given and finishes the section.

## The construction inputs

This module isolates the construction-dependent data as explicit hypotheses. They are supplied
for the quantitative stage recursion in `Schoenflies/InteriorHomeomorphism.lean` and
`Schoenflies/BoundaryAnchors.lean`. Nothing else is assumed: `thm:jordan` and
`thm:general-crosscut` are used through `Schoenflies/JordanClosed.lean`, where their hypotheses
are supplied.

* **`prop:interior-homeomorphism`** enters as `IsHomeoOn F F' (inside C) (Plane.openSquare 0 1)`
  — the `Schoenflies.IsHomeoOn` shape of `Schoenflies/Inversion.lean`: a map, a named inverse,
  and the continuity and inverse laws on the two sets.
* **`lem:skeleton-crosscuts` + `prop:skeleton-agreement`** enter as
  `Schoenflies.HasAnchorCrosscuts`: for two distinct anchors `a, b` a crosscut `P` of `C` from
  `a` to `b`, a crosscut `P'` of `Q°` from `u a` to `u b`, and the agreement
  `F '' (P ∖ {a,b}) = P' ∖ {u a, u b}`. This is exactly what the finite skeleton homeomorphism
  produces once `Graph.IsStageOn.exists_crosscut` has been run in the stage containing `a`
  and `b` (see `Graph.IsStageOn.exists_isCrosscut` below, which does the packaging).
* **`lem:anchor-density`** enters as the two clauses `𝒜 ⊆ C` and `C ⊆ closure 𝒜`, plus its
  "incident with a nonboundary edge" clause in the germ form `Schoenflies.HasSpokes`: at an
  anchor `c`, arbitrarily small connected pieces `J` of the Jordan domain which cling to `c`
  and whose `F`-images cling to `u c`. That is the initial subarc of the spoke at `c`, and its
  image, which is the initial subarc of the target spoke — the *only* use the blueprint makes
  of the spokes, in the paragraph of `lem:crosscut-side-correspondence` beginning "Choose
  `c ∈ 𝒜` in the relative interior of `Aᵢ`".

`Schoenflies.HasLimitHomeomorphism` bundles the four over all curves, and
`Schoenflies.squareExtension_of_hasLimitHomeomorphism` derives
`Schoenflies.SquareExtension` — the exact `def` of
`Schoenflies/Endgame.lean` — from it. The proof of `HasLimitHomeomorphism` assembled in
`Schoenflies/JordanSchoenflies.lean` closes the full theorem.

## The two arguments

*Which side maps to which side* is `Schoenflies.crosscut_side_correspondence`. The homeomorphism
of the interiors carries `Int(C) ∖ P` onto `Q° ∖ P'` (`Schoenflies.image_inside_sdiff`), hence
carries each of the two components onto one of the two; the labels are pinned by a spoke germ
`J` at an anchor `c` in the relative interior of `A₁`. `J` is connected, misses `P` because it
is small and `c ∉ P`, so it lies in one side; `c ∈ closure J` and `closure(Uᵢ) ∩ C = Aᵢ` force
that side to be `U₁`. The same two facts on the target, applied to `F '' J`, force `F '' U₁` to
be `U'₁`.

*Boundary continuity* is `Schoenflies.tendsto_nhdsWithin_inside`. The blueprint argues on a
subsequence; the filter form of the same argument avoids extracting one. If `F` does not tend
to `u p` along `𝓝[Int C] p`, then `l' = 𝓝[Int C] p ⊓ 𝓟 (F⁻¹ Wᶜ)` is a nonzero filter for some
open `W ∋ u p`, and compactness of `Q` gives a cluster point `q ∈ Wᶜ` of `F` along `l'`. If
`q ∈ Q°` then pushing `l'` through `F'` shows `p = F' q ∈ Int(C)`, impossible. Otherwise
`q ∈ S`; anchors `a, b` separating `p` from `r = u⁻¹ q` give a crosscut whose `p`-side contains
every point of `Int(C)` near `p`, so `l'` sits on that side, so `q` lies in the closure of the
corresponding target side, whose trace on `S` is `u(A₁)` — and `r ∉ A₁`.

## Blueprint

* `Graph.IsStageOn.exists_isCrosscut` — **`lem:skeleton-crosscuts`** repackaged as
  `Schoenflies.IsCrosscut`, the form `thm:general-crosscut` consumes.
* `Schoenflies.IsCutPair.separates`, `Schoenflies.exists_separating_anchors` — the selection
  step of `prop:boundary-continuity`: two anchors putting two prescribed points of the curve on
  opposite arcs. Uses **`lem:anchor-density`** through the density hypothesis alone.
* `Schoenflies.IsCrosscut.image_of_injOn`, `Schoenflies.image_sdiff_eq_of_eqOn` — the two
  steps a consumer performs to discharge `Schoenflies.HasAnchorCrosscuts` from a finite skeleton
  homeomorphism. No blueprint statement of their own; they are the second paragraph of the
  proof of **`lem:skeleton-crosscuts`**, "the finite skeleton homeomorphism sends `P` to a
  simple path `P'`".
* `Schoenflies.crosscut_side_correspondence` — **`lem:crosscut-side-correspondence`**.
* `Schoenflies.extendByBoundary`, `Schoenflies.tendsto_nhdsWithin_inside`,
  `Schoenflies.boundary_continuity` — **`prop:boundary-continuity`**.
* `Schoenflies.isHomeoOn_extendByBoundary`,
  `Schoenflies.squareExtension_of_hasLimitHomeomorphism` —
  **`thm:square-extension`**.
-/

public section

open Bornology Filter Metric Schoenflies Set Topology
open scoped Graph

namespace Graph

/-- **`lem:skeleton-crosscuts`, packaged for `thm:general-crosscut`.** The crosscut that
`Graph.IsStageOn.exists_crosscut` extracts from a stage drawn in the closed Jordan domain is a
`Schoenflies.IsCrosscut` of `C`, which is the configuration every consumer downstream takes.

This is only a repackaging; all the work is in `Schoenflies/BoundaryContinuity.lean`. -/
theorem IsStageOn.exists_isCrosscut {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {C : Set Plane} [G.Finite] (h : IsStageOn G drawing C (Schoenflies.inside C))
    (hC : Schoenflies.IsJordanCurve C) {a b : Plane} (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : ∃ e, G.Inc e a ∧ Nonboundary drawing C e)
    (hb : ∃ e, G.Inc e b ∧ Nonboundary drawing C e) :
    ∃ P ⊆ pointSet G drawing, Schoenflies.IsCrosscut C P a b := by
  obtain ⟨P, hPsub, hPpoly, hParc, -, hPD⟩ := h.exists_crosscut hab haC hbC ha hb
  exact ⟨P, hPsub, ⟨hC, hParc, hPpoly, haC, hbC, hPD⟩⟩

end Graph

namespace Schoenflies

variable {C 𝒜 A₁ A₂ B₁ B₂ P P' : Set Plane} {u v F F' : Plane → Plane} {a b p r : Plane}

/-! ### Two elementary facts about the model square

`Q° = Int(S)`: the open square is the Jordan domain of the model curve. This is the bridge
between the shape `prop:interior-homeomorphism` is stated in (a homeomorphism onto
`Plane.openSquare 0 1`) and the shape `thm:general-crosscut` speaks in (`inside modelCurve`). -/

/-- The Jordan domain of the model curve is the open square. -/
theorem inside_modelCurve : inside modelCurve = Plane.openSquare 0 1 := by
  rw [modelCurve_eq_frontier]
  exact inside_frontier_closedSquare 0 1

/-- The closed square is compact. -/
theorem isCompact_closedSquare (c : Plane) (r : ℝ) : IsCompact (Plane.closedSquare c r) :=
  Metric.isCompact_of_isClosed_isBounded (Plane.isClosed_closedSquare c r)
    (Plane.isBounded_closedSquare c r)

/-! ### Pushing arcs forward

`lem:crosscut-side-correspondence` labels the target sides by `u(A₁)` and `u(A₂)`, so the two
target arcs have to be produced as images. Nothing here is specific to the square. -/

/-- The image of an arc under a map continuous and injective on a set containing it. -/
theorem IsArcBetween.image_of_injOn {A S : Set Plane} {p q : Plane} {f : Plane → Plane}
    (h : IsArcBetween A p q) (hAS : A ⊆ S) (hcont : ContinuousOn f S) (hinj : InjOn f S) :
    IsArcBetween (f '' A) (f p) (f q) := by
  obtain ⟨g, hg, hgi, hgim, hg0, hg1⟩ := h
  have hmem : ∀ t ∈ unitInterval, g t ∈ S := by
    intro t ht
    exact hAS (hgim ▸ mem_image_of_mem g ht)
  refine ⟨f ∘ g, hcont.comp hg hmem, ?_, ?_, by simp [hg0], by simp [hg1]⟩
  · intro s hs t ht hst
    exact hgi hs ht (hinj (hmem s hs) (hmem t ht) hst)
  · rw [← hgim, image_comp]

/-- The image of a cut pair. -/
theorem IsCutPair.image {f : Plane → Plane} (h : IsCutPair C a b A₁ A₂)
    (hcont : ContinuousOn f C) (hinj : InjOn f C) :
    IsCutPair (f '' C) (f a) (f b) (f '' A₁) (f '' A₂) where
  fst := h.fst.image_of_injOn h.fst_subset hcont hinj
  snd := h.snd.image_of_injOn h.snd_subset hcont hinj
  union_eq := by rw [← image_union, h.union_eq]
  inter_eq := by
    rw [← hinj.image_inter h.fst_subset h.snd_subset, h.inter_eq, image_pair]

/-- The image of a cut pair under a restricted homeomorphism, in the form the target side of
`lem:crosscut-side-correspondence` needs it. -/
theorem IsCutPair.image_of_isHomeoOn {T : Set Plane} (h : IsCutPair C a b A₁ A₂)
    (hu : IsHomeoOn u v C T) : IsCutPair T (u a) (u b) (u '' A₁) (u '' A₂) := by
  have h' := h.image hu.continuousOn hu.injOn
  rwa [hu.image_eq] at h'

/-! ### Anchors that separate

The selection step of `prop:boundary-continuity`. Given two distinct points `p, r` of the curve
and a dense set `𝒜` of anchors, we need anchors `a, b` with `p` and `r` on opposite arcs of `C`
from `a` to `b`. Density produces one anchor on each of the two open arcs of `C` from `p` to
`r`; the separation is then automatic, because an arc from `a` to `b` avoiding `p` and `r`
would be a connected subset of `C ∖ {p, r}` meeting both of its two (relatively open) halves. -/

/-- **A dense set meets the relative interior of either arc of a cut pair.** The one use
`lem:anchor-density` is put to. -/
theorem exists_anchor_mem_arc (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcut : IsCutPair C a b A₁ A₂) : ∃ c ∈ 𝒜, c ∈ A₁ ∧ c ∉ A₂ := by
  -- an arc is more than its two endpoints, and the two endpoints are all that `A₂` shares
  obtain ⟨z, hzA, hz⟩ := not_subset.1 hcut.fst.not_subset_pair
  have hzA2 : z ∉ A₂ := fun h => hz (by rw [← hcut.inter_eq]; exact ⟨hzA, h⟩)
  have hA2closed : IsClosed A₂ := hcut.snd.isArc.isClosed
  obtain ⟨c, hcmem, hc⟩ :=
    mem_closure_iff.1 (hdense (hcut.fst_subset hzA)) _ hA2closed.isOpen_compl hzA2
  have hcC : c ∈ A₁ ∪ A₂ := by rw [hcut.union_eq]; exact hsub hc
  exact ⟨c, hc, hcC.resolve_right hcmem, hcmem⟩

/-- **Two anchors on opposite open arcs separate.** If `a` lies on the open arc `B₁ ∖ {p, r}`
and `b` on the opposite one, then any pair of arcs cutting `C` at `a` and `b` puts `p` and `r`
on different arcs.

The proof is the one separation argument of the section: an arc from `a` to `b` missing both
`p` and `r` is a connected subset of `C ∖ {p, r} = (C ∖ B₂) ∪ (C ∖ B₁)`, a union of two
relatively open pieces, and it meets both — because `a` is in the first and `b` in the
second. -/
theorem IsCutPair.separates (hB : IsCutPair C p r B₁ B₂) (hA : IsCutPair C a b A₁ A₂)
    (ha' : a ∉ B₂) (hb' : b ∉ B₁) :
    (p ∈ A₁ ∧ r ∈ A₂) ∨ (p ∈ A₂ ∧ r ∈ A₁) := by
  have hpB : p ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inl rfl
  have hrB : r ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inr rfl
  -- no arc of the pair can hold both `p` and `r`
  have key : ∀ A : Set Plane, IsArcBetween A a b → A ⊆ C → p ∉ A → r ∉ A → False := by
    intro A hAarc hAC hpA hrA
    have hcov : A ⊆ B₂ᶜ ∪ B₁ᶜ := by
      intro z hz
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      have : z ∈ ({p, r} : Set Plane) := by rw [← hB.inter_eq]; exact ⟨hcon.2, hcon.1⟩
      rcases this with rfl | rfl
      · exact hpA hz
      · exact hrA hz
    have hempty : ∀ z ∈ A, z ∈ B₂ᶜ → z ∉ B₁ᶜ := by
      intro z hz hz2 hz1
      have : z ∈ B₁ ∪ B₂ := by rw [hB.union_eq]; exact hAC hz
      exact this.elim hz1 hz2
    obtain ⟨z, hzA, hz2, hz1⟩ :=
      hAarc.isArc.isConnected.2 _ _ (hB.snd.isArc.isClosed.isOpen_compl)
        (hB.fst.isArc.isClosed.isOpen_compl) hcov ⟨a, hAarc.left_mem, ha'⟩
        ⟨b, hAarc.right_mem, hb'⟩
    exact hempty z hzA hz2 hz1
  -- `p` and `r` are each on exactly one of the two arcs
  have hpne : p ≠ a ∧ p ≠ b := ⟨fun h => ha' (h ▸ hpB.2), fun h => hb' (h ▸ hpB.1)⟩
  have hrne : r ≠ a ∧ r ≠ b := ⟨fun h => ha' (h ▸ hrB.2), fun h => hb' (h ▸ hrB.1)⟩
  have hone : ∀ z : Plane, z ∈ C → z ≠ a → z ≠ b → (z ∈ A₁ ∧ z ∉ A₂) ∨ (z ∈ A₂ ∧ z ∉ A₁) := by
    intro z hzC hza hzb
    have hboth : ¬ (z ∈ A₁ ∧ z ∈ A₂) := by
      intro h
      have : z ∈ ({a, b} : Set Plane) := by rw [← hA.inter_eq]; exact h
      rcases this with h' | h'
      · exact hza h'
      · exact hzb h'
    have : z ∈ A₁ ∪ A₂ := by rw [hA.union_eq]; exact hzC
    rcases this with h | h
    · exact Or.inl ⟨h, fun h' => hboth ⟨h, h'⟩⟩
    · exact Or.inr ⟨h, fun h' => hboth ⟨h', h⟩⟩
  have hpC : p ∈ C := by rw [← hB.union_eq]; exact Or.inl hpB.1
  have hrC : r ∈ C := by rw [← hB.union_eq]; exact Or.inl hrB.1
  rcases hone p hpC hpne.1 hpne.2 with ⟨hp1, hp2⟩ | ⟨hp2, hp1⟩ <;>
    rcases hone r hrC hrne.1 hrne.2 with ⟨hr1, hr2⟩ | ⟨hr2, hr1⟩
  · exact absurd (key A₂ hA.snd hA.snd_subset hp2 hr2) not_false
  · exact Or.inl ⟨hp1, hr2⟩
  · exact Or.inr ⟨hp2, hr1⟩
  · exact absurd (key A₁ hA.fst hA.fst_subset hp1 hr1) not_false

/-- **The selection step of `prop:boundary-continuity`.** Two distinct points of the curve are
separated by two anchors of any dense set of anchors. -/
theorem exists_separating_anchors (hC : IsJordanCurve C) (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hp : p ∈ C) (hr : r ∈ C) (hpr : p ≠ r) :
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ A₁ A₂ : Set Plane, a ≠ b ∧ IsCutPair C a b A₁ A₂ ∧
      p ∈ A₁ ∧ p ∉ A₂ ∧ r ∈ A₂ ∧ r ∉ A₁ := by
  obtain ⟨B₁, B₂, hB⟩ := exists_isCutPair hC hp hr hpr
  obtain ⟨a, ha𝒜, haB, haB'⟩ := exists_anchor_mem_arc hsub hdense hB
  obtain ⟨b, hb𝒜, hbB, hbB'⟩ := exists_anchor_mem_arc hsub hdense hB.symm
  have hab : a ≠ b := fun h => haB' (h ▸ hbB)
  obtain ⟨A₁, A₂, hA⟩ := exists_isCutPair hC (hsub ha𝒜) (hsub hb𝒜) hab
  -- the two points are not the anchors, so each lies on exactly one arc
  have hpB : p ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inl rfl
  have hrB : r ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inr rfl
  have hsplit : ∀ (D₁ D₂ : Set Plane), IsCutPair C a b D₁ D₂ → ∀ z : Plane,
      z ∈ B₁ ∩ B₂ → z ∈ D₁ → z ∉ D₂ := by
    intro D₁ D₂ hD z hz hzD hzD'
    have : z ∈ ({a, b} : Set Plane) := by rw [← hD.inter_eq]; exact ⟨hzD, hzD'⟩
    rcases this with rfl | rfl
    · exact haB' hz.2
    · exact hbB' hz.1
  rcases hB.separates hA haB' hbB' with ⟨hp1, hr2⟩ | ⟨hp2, hr1⟩
  · exact ⟨a, ha𝒜, b, hb𝒜, A₁, A₂, hab, hA, hp1, hsplit A₁ A₂ hA p hpB hp1, hr2,
      hsplit A₂ A₁ hA.symm r hrB hr2⟩
  · exact ⟨a, ha𝒜, b, hb𝒜, A₂, A₁, hab, hA.symm, hp2, hsplit A₂ A₁ hA.symm p hpB hp2, hr1,
      hsplit A₁ A₂ hA r hrB hr1⟩

/-! ### The hypotheses

Two predicates, one for each thing that is still being built. Both are *statements about one
curve*, so a consumer can discharge them curve by curve. -/

/-- **`lem:skeleton-crosscuts` together with `prop:skeleton-agreement`**, as
`lem:crosscut-side-correspondence` consumes them: any two distinct anchors are joined by a
crosscut `P` of `C`, whose image under the limit map is a crosscut `P'` of the open square from
`u a` to `u b`.

The agreement clause is stated on `P ∖ {a, b}`, which by `IsCrosscut.inter_eq` is exactly
`P ∩ Int(C)` — the part of the crosscut on which `F` is defined at all. -/
def HasAnchorCrosscuts (C 𝒜 : Set Plane) (u F : Plane → Plane) : Prop :=
  ∀ ⦃a b : Plane⦄, a ∈ 𝒜 → b ∈ 𝒜 → a ≠ b → ∃ P P' : Set Plane,
    IsCrosscut C P a b ∧ IsCrosscut modelCurve P' (u a) (u b) ∧
      F '' (P \ {a, b}) = P' \ {u a, u b}

/-- **The spokes at the anchors.** At an anchor `c` there are arbitrarily small connected
pieces `J` of the Jordan domain clinging to `c` whose `F`-images cling to `u c`.

This is the germ of the nonboundary edge that `lem:anchor-density` attaches to `c`: `J` is an
initial subarc of that edge with the endpoint `c` removed, and `F '' J` is the corresponding
initial subarc of the target edge, which ends at `u c` because the finite skeleton
homeomorphism sends `c` to `u c`. Nothing else about the spokes is used anywhere. -/
def HasSpokes (C 𝒜 : Set Plane) (u F : Plane → Plane) : Prop :=
  ∀ c ∈ 𝒜, ∀ ε > 0, ∃ J : Set Plane, J ⊆ inside C ∧ IsPreconnected J ∧ J ⊆ ball c ε ∧
    c ∈ closure J ∧ u c ∈ closure (F '' J)

/-! ### Discharging `HasAnchorCrosscuts` from a skeleton homeomorphism

The two steps a consumer has to perform, isolated so that they need not be reinvented: the
image of a crosscut under the finite skeleton homeomorphism is again a crosscut, and the
agreement clause follows from agreement of the limit map with that homeomorphism on the
crosscut. Neither says anything about the square, so both apply to the source and the target
side of any of the stages. -/

/-- **The image of a crosscut is a crosscut.** All that is asked of the map is continuity and
injectivity on a set containing the crosscut, plus the two clauses that are genuinely about the
target configuration: the image is polygonal, and everything but its two endpoints lies in the
target Jordan domain. -/
theorem IsCrosscut.image_of_injOn {C' Sk : Set Plane} {g : Plane → Plane}
    (hP : IsCrosscut C P a b) (hPSk : P ⊆ Sk) (hcont : ContinuousOn g Sk) (hinj : InjOn g Sk)
    (hC' : IsJordanCurve C') (hpoly : IsPolygonal (g '' P)) (ha : g a ∈ C') (hb : g b ∈ C')
    (hint : g '' (P \ {a, b}) ⊆ inside C') : IsCrosscut C' (g '' P) (g a) (g b) := by
  refine ⟨hC', hP.arc.image_of_injOn hPSk hcont hinj, hpoly, ha, hb, ?_⟩
  rintro z ⟨⟨w, hwP, rfl⟩, hz⟩
  refine hint ⟨w, ⟨hwP, ?_⟩, rfl⟩
  rintro (rfl | rfl)
  · exact hz (Or.inl rfl)
  · exact hz (Or.inr rfl)

/-- **The agreement clause of `Schoenflies.HasAnchorCrosscuts`**, from agreement of the limit
map with the skeleton homeomorphism on the part of the crosscut that lies in the domain. -/
theorem image_sdiff_eq_of_eqOn {Sk : Set Plane} {g : Plane → Plane} (hPSk : P ⊆ Sk)
    (hinj : InjOn g Sk) (ha : a ∈ P) (hb : b ∈ P) (hFg : EqOn F g (P \ {a, b})) :
    F '' (P \ {a, b}) = g '' P \ {g a, g b} := by
  rw [hFg.image_eq, (hinj.mono hPSk).image_sdiff_subset (pair_subset ha hb), image_pair]

/-! ### `lem:crosscut-side-correspondence` -/

/-- Removing a crosscut from the Jordan domain is the same as removing its interior: the two
endpoints are on the curve and so are not in the domain to begin with. -/
theorem inside_sdiff_crosscut (h : IsCrosscut C P a b) :
    inside C \ P = inside C \ (P \ {a, b}) := by
  refine Set.ext fun z => ⟨fun hz => ⟨hz.1, fun h' => hz.2 h'.1⟩, fun hz => ⟨hz.1, fun h' => ?_⟩⟩
  have hzab : z ∈ ({a, b} : Set Plane) := by
    by_contra hcon
    exact hz.2 ⟨h', hcon⟩
  rcases hzab with rfl | rfl
  · exact inside_subset_compl hz.1 h.left_mem
  · exact inside_subset_compl hz.1 h.right_mem

/-- **The limit map carries `Int(C) ∖ P` onto `Q° ∖ P'`.** This is the whole use made of
`prop:skeleton-agreement`: it turns a homeomorphism of the interiors into a homeomorphism of
the cut interiors. -/
theorem image_inside_sdiff (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hP : IsCrosscut C P a b) (hP' : IsCrosscut modelCurve P' (u a) (u b))
    (hagree : F '' (P \ {a, b}) = P' \ {u a, u b}) :
    F '' (inside C \ P) = inside modelCurve \ P' := by
  have hFin : F '' inside C = inside modelCurve := by rw [hF.image_eq, inside_modelCurve]
  rw [inside_sdiff_crosscut hP, hF.injOn.image_sdiff_subset hP.sdiff_subset, hagree, hFin,
    ← inside_sdiff_crosscut hP']

/-- **`lem:crosscut-side-correspondence`, one inclusion.** The side of the crosscut whose
closure meets `C` in `A₁` is carried into the side of the target crosscut whose closure meets
`S` in `u(A₁)`.

This is where the spokes are used, and the only place. -/
theorem image_crosscut_side_subset (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜) (hspoke : HasSpokes C 𝒜 u F)
    (hcut : IsCutPair C a b A₁ A₂) (hP : IsCrosscut C P a b)
    (hP' : IsCrosscut modelCurve P' (u a) (u b)) (hagree : F '' (P \ {a, b}) = P' \ {u a, u b}) :
    F '' inside (A₁ ∪ P) ⊆ inside (u '' A₁ ∪ P') := by
  classical
  have hcut' : IsCutPair modelCurve (u a) (u b) (u '' A₁) (u '' A₂) :=
    hcut.image_of_isHomeoOn hu
  obtain ⟨hsrc1, hsrc2, -, -, -, -, -, -, hsrc9, hsrc10⟩ := crosscut_theorem hP hcut
  obtain ⟨htgt1, htgt2, -, -, -, -, -, -, htgt9, htgt10⟩ := crosscut_theorem hP' hcut'
  have hdiff := image_inside_sdiff hF hP hP' hagree
  -- the four sides, and their openness
  have hopenS : ∀ A : Set Plane, IsArcBetween A a b → IsOpen (inside (A ∪ P)) := fun A hA =>
    isOpen_inside (hA.isArc.isCompact.union hP.arc.isArc.isCompact).isClosed
  have hopenT : ∀ A : Set Plane, IsArcBetween A (u a) (u b) → IsOpen (inside (A ∪ P')) :=
    fun A hA => isOpen_inside (hA.isArc.isCompact.union hP'.arc.isArc.isCompact).isClosed
  have hS1 := hopenS A₁ hcut.fst
  have hS2 := hopenS A₂ hcut.snd
  have hT1 := hopenT _ hcut'.fst
  have hT2 := hopenT _ hcut'.snd
  -- the image of the first side is connected and lands in the union of the two target sides
  have hW1sub : inside (A₁ ∪ P) ⊆ inside C \ P := by rw [hsrc1]; exact subset_union_left
  have hconn : IsPreconnected (F '' inside (A₁ ∪ P)) := by
    refine IsPreconnected.image ?_ F (hF.continuousOn.mono fun z hz => (hW1sub hz).1)
    exact ((jordan_curve_theorem (hP.isJordanCurve_union hcut)).isConnected_inside).2
  have himsub : F '' inside (A₁ ∪ P) ⊆ inside (u '' A₁ ∪ P') ∪ inside (u '' A₂ ∪ P') := by
    rw [← htgt1, ← hdiff]
    exact image_mono hW1sub
  -- it therefore lands in one of the two; the spoke germ says which
  by_cases hmeet : (F '' inside (A₁ ∪ P) ∩ inside (u '' A₁ ∪ P')).Nonempty
  · exact hconn.subset_left_of_subset_union hT1 hT2 htgt2 himsub hmeet
  rw [not_nonempty_iff_eq_empty] at hmeet
  exfalso
  have hother : F '' inside (A₁ ∪ P) ⊆ inside (u '' A₂ ∪ P') := by
    intro w hw
    refine (himsub hw).resolve_left fun h' => ?_
    exact (eq_empty_iff_forall_notMem.1 hmeet w) ⟨hw, h'⟩
  -- an anchor in the relative interior of `A₁`
  obtain ⟨c, hc𝒜, hcA1, hcA2⟩ := exists_anchor_mem_arc hsub hdense hcut
  have hcC : c ∈ C := hsub hc𝒜
  have hca : c ≠ a := fun h => hcA2 (h ▸ hcut.snd.left_mem)
  have hcb : c ≠ b := fun h => hcA2 (h ▸ hcut.snd.right_mem)
  -- the anchor is off the crosscut, so a small ball around it misses the crosscut
  have hcP : c ∉ P := by
    intro h
    have : c ∈ ({a, b} : Set Plane) := by rw [← hP.inter_eq]; exact ⟨h, hcC⟩
    rcases this with h' | h'
    · exact hca h'
    · exact hcb h'
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 hP.arc.isArc.isClosed.isOpen_compl c hcP
  obtain ⟨J, hJin, hJconn, hJball, hJc, hJuc⟩ := hspoke c hc𝒜 ε hε
  have hJsub : J ⊆ inside C \ P := fun z hz => ⟨hJin hz, hball (hJball hz)⟩
  have hJcov : J ⊆ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by rw [← hsrc1]; exact hJsub
  -- the germ lies on the `A₁` side, because it clings to `c ∈ A₁ ∖ A₂`
  have hJ1 : J ⊆ inside (A₁ ∪ P) := by
    by_cases hJ1 : (J ∩ inside (A₁ ∪ P)).Nonempty
    · exact hJconn.subset_left_of_subset_union hS1 hS2 hsrc2 hJcov hJ1
    · rw [not_nonempty_iff_eq_empty] at hJ1
      have hJ2 : J ⊆ inside (A₂ ∪ P) := fun z hz =>
        (hJcov hz).resolve_left fun h' => (eq_empty_iff_forall_notMem.1 hJ1 z) ⟨hz, h'⟩
      have : c ∈ A₂ := by
        rw [← hsrc10]
        exact ⟨closure_mono hJ2 hJc, hcC⟩
      exact absurd this hcA2
  -- so its image lies on the `u(A₁)` side, contradicting `hother`
  have : u c ∈ u '' A₂ := by
    rw [← htgt10]
    refine ⟨closure_mono (subset_trans (image_mono hJ1) hother) hJuc, hu.mapsTo hcC⟩
  obtain ⟨w, hwA2, hw⟩ := this
  exact hcA2 (hu.injOn (hcut.snd_subset hwA2) hcC hw ▸ hwA2)

/-- **`lem:crosscut-side-correspondence`.** The limit map carries each side of a crosscut onto
the side of the target crosscut carrying the corresponding boundary arc.

The sides are named the way `Schoenflies.crosscut_theorem` names them: `inside (Aᵢ ∪ P)` is the
component of `Int(C) ∖ P` whose closure meets `C` exactly in `Aᵢ`. -/
theorem crosscut_side_correspondence (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜) (hspoke : HasSpokes C 𝒜 u F)
    (hcut : IsCutPair C a b A₁ A₂) (hP : IsCrosscut C P a b)
    (hP' : IsCrosscut modelCurve P' (u a) (u b)) (hagree : F '' (P \ {a, b}) = P' \ {u a, u b}) :
    F '' inside (A₁ ∪ P) = inside (u '' A₁ ∪ P') ∧
      F '' inside (A₂ ∪ P) = inside (u '' A₂ ∪ P') := by
  have hcut' : IsCutPair modelCurve (u a) (u b) (u '' A₁) (u '' A₂) :=
    hcut.image_of_isHomeoOn hu
  have h1 := image_crosscut_side_subset hu hF hsub hdense hspoke hcut hP hP' hagree
  have h2 := image_crosscut_side_subset hu hF hsub hdense hspoke hcut.symm hP hP' hagree
  obtain ⟨hsrc1, -⟩ := crosscut_theorem hP hcut
  obtain ⟨htgt1, htgt2, -⟩ := crosscut_theorem hP' hcut'
  have hdiff := image_inside_sdiff hF hP hP' hagree
  -- the two images cover the two target sides, so each inclusion is an equality
  have hcover : F '' inside (A₁ ∪ P) ∪ F '' inside (A₂ ∪ P) =
      inside (u '' A₁ ∪ P') ∪ inside (u '' A₂ ∪ P') := by
    rw [← image_union, ← hsrc1, hdiff, htgt1]
  constructor
  · refine subset_antisymm h1 fun w hw => ?_
    have : w ∈ F '' inside (A₁ ∪ P) ∪ F '' inside (A₂ ∪ P) := by
      rw [hcover]; exact Or.inl hw
    exact this.resolve_right fun h' => Set.disjoint_left.1 htgt2 hw (h2 h')
  · refine subset_antisymm h2 fun w hw => ?_
    have : w ∈ F '' inside (A₁ ∪ P) ∪ F '' inside (A₂ ∪ P) := by
      rw [hcover]; exact Or.inr hw
    exact this.resolve_left fun h' => Set.disjoint_left.1 htgt2 (h1 h') hw

/-! ### `prop:boundary-continuity` -/

/-- The blueprint's `Fbar`: the limit map on the Jordan domain and the boundary homeomorphism on
the curve. It is `Schoenflies.paste`, which comes with its two evaluation lemmas. -/
noncomputable def extendByBoundary (C : Set Plane) (u F : Plane → Plane) : Plane → Plane :=
  paste C u F

theorem extendByBoundary_of_mem {z : Plane} (hz : z ∈ C) : extendByBoundary C u F z = u z :=
  paste_of_mem hz

theorem extendByBoundary_of_notMem {z : Plane} (hz : z ∉ C) : extendByBoundary C u F z = F z :=
  paste_of_notMem hz

/-- **`prop:boundary-continuity`, the substance.** Approaching a point `p` of the curve from
inside, the limit map tends to `u p`.

The blueprint extracts a subsequence; the same argument runs on the filter
`l' = 𝓝[Int C] p ⊓ 𝓟 (F⁻¹ Wᶜ)` without extracting one. -/
theorem tendsto_nhdsWithin_inside (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) (hp : p ∈ C) :
    Tendsto F (𝓝[inside C] p) (𝓝 (u p)) := by
  classical
  by_contra hcon
  rw [Filter.tendsto_def] at hcon
  push Not at hcon
  obtain ⟨s, hs, hsnot⟩ := hcon
  obtain ⟨W, hWs, hWopen, hWmem⟩ := _root_.mem_nhds_iff.1 hs
  have hWnot : F ⁻¹' W ∉ 𝓝[inside C] p := fun h =>
    hsnot (mem_of_superset h (preimage_mono hWs))
  -- the filter of approach that stays away from `W`
  set l' : Filter Plane := 𝓝[inside C] p ⊓ 𝓟 (F ⁻¹' Wᶜ) with hl'
  let _ : l'.NeBot := by
    refine ⟨fun h => hWnot ?_⟩
    rw [hl', Filter.inf_principal_eq_bot] at h
    simpa using h
  have hl'in : inside C ∈ l' := mem_inf_of_left self_mem_nhdsWithin
  have hl'W : F ⁻¹' Wᶜ ∈ l' := mem_inf_of_right (mem_principal_self _)
  have hl'p : l' ≤ 𝓝 p := le_trans inf_le_left nhdsWithin_le_nhds
  -- compactness of the square gives a cluster point of the image
  have hmapK : map F l' ≤ 𝓟 (Plane.closedSquare 0 1) := by
    rw [le_principal_iff, mem_map]
    filter_upwards [hl'in] with z hz using Plane.openSquare_subset_closedSquare 0 1 (hF.mapsTo hz)
  obtain ⟨q, hqK, hqcl⟩ := (isCompact_closedSquare 0 1).exists_clusterPt hmapK
  have hqW : q ∈ Wᶜ := by
    have hle : map F l' ≤ 𝓟 Wᶜ := by rw [le_principal_iff]; exact hl'W
    have := mem_closure_iff_clusterPt.2 (hqcl.mono hle)
    rwa [hWopen.isClosed_compl.closure_eq] at this
  have hqne : q ≠ u p := fun h => hqW (h ▸ hWmem)
  -- the cluster point lies on the boundary of the square: otherwise the inverse map would
  -- send it back to `p`, which is not an interior point
  have hqcurve : q ∈ modelCurve := by
    by_contra hq
    have hqopen : q ∈ Plane.openSquare 0 1 := by
      rw [← closedSquare_sdiff_modelCurve]; exact ⟨hqK, hq⟩
    have hmapO : map F l' ≤ 𝓟 (Plane.openSquare 0 1) := by
      rw [le_principal_iff, mem_map]
      filter_upwards [hl'in] with z hz using hF.mapsTo hz
    set m : Filter Plane := 𝓝 q ⊓ map F l' with hm
    let _ : m.NeBot := hqcl
    have hm1 : m ≤ 𝓝[Plane.openSquare 0 1] q :=
      le_inf inf_le_left (le_trans inf_le_right hmapO)
    have h1 : Tendsto F' m (𝓝 (F' q)) := (hF.continuousOn_inv q hqopen).mono_left hm1
    have h2 : Tendsto F' m (𝓝 p) := by
      refine le_trans (map_mono (inf_le_right : m ≤ map F l')) ?_
      rw [Filter.map_map]
      have heq : (F' ∘ F) =ᶠ[l'] id := by
        filter_upwards [hl'in] with z hz using hF.invOn.1 hz
      rw [Filter.map_congr heq, Filter.map_id]
      exact hl'p
    have hpin : p ∈ inside C := tendsto_nhds_unique h1 h2 ▸ hF.mapsTo_inv hqopen
    exact inside_subset_compl hpin hp
  -- the boundary case: separate `p` from the preimage of `q` by two anchors
  have hrC : v q ∈ C := hu.mapsTo_inv hqcurve
  have hur : u (v q) = q := hu.invOn.2 hqcurve
  have hpr : p ≠ v q := fun h => hqne (by rw [← hur, ← h])
  obtain ⟨a, ha𝒜, b, hb𝒜, A₁, A₂, hab, hcut, hpA1, hpA2, hrA2, hrA1⟩ :=
    exists_separating_anchors hC hsub hdense hp hrC hpr
  obtain ⟨P, P', hP, hP', hagree⟩ := hcross ha𝒜 hb𝒜 hab
  have hcut' : IsCutPair modelCurve (u a) (u b) (u '' A₁) (u '' A₂) :=
    hcut.image_of_isHomeoOn hu
  have hside := image_crosscut_side_subset hu hF hsub hdense hspoke hcut hP hP' hagree
  obtain ⟨hsrc1, -, -, -, -, -, -, -, -, hsrc10⟩ := crosscut_theorem hP hcut
  obtain ⟨-, -, -, -, -, -, -, -, htgt9, -⟩ := crosscut_theorem hP' hcut'
  -- `p` is off the crosscut and off the closure of the far side
  have hpa : p ≠ a := fun h => hpA2 (h ▸ hcut.snd.left_mem)
  have hpb : p ≠ b := fun h => hpA2 (h ▸ hcut.snd.right_mem)
  have hpP : p ∉ P := by
    intro h
    have : p ∈ ({a, b} : Set Plane) := by rw [← hP.inter_eq]; exact ⟨h, hp⟩
    rcases this with h' | h'
    · exact hpa h'
    · exact hpb h'
  have hpfar : p ∉ closure (inside (A₂ ∪ P)) := fun h => hpA2 (hsrc10 ▸ ⟨h, hp⟩)
  -- hence every nearby point of the domain is on the `p` side
  have hV : IsOpen (Pᶜ ∩ (closure (inside (A₂ ∪ P)))ᶜ) :=
    hP.arc.isArc.isClosed.isOpen_compl.inter isClosed_closure.isOpen_compl
  have hnear : inside (A₁ ∪ P) ∈ 𝓝[inside C] p := by
    refine mem_nhdsWithin.2 ⟨_, hV, ⟨hpP, hpfar⟩, ?_⟩
    rintro z ⟨⟨hz1, hz2⟩, hzin⟩
    have : z ∈ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by rw [← hsrc1]; exact ⟨hzin, hz1⟩
    exact this.resolve_right fun h' => hz2 (subset_closure h')
  -- so the cluster point sits in the closure of the corresponding target side
  have hmapW : map F l' ≤ 𝓟 (inside (u '' A₁ ∪ P')) := by
    rw [le_principal_iff, mem_map]
    filter_upwards [mem_inf_of_left hnear] with z hz using hside ⟨z, hz, rfl⟩
  have hqclos : q ∈ closure (inside (u '' A₁ ∪ P')) :=
    mem_closure_iff_clusterPt.2 (hqcl.mono hmapW)
  have hqA1 : q ∈ u '' A₁ := by rw [← htgt9]; exact ⟨hqclos, hqcurve⟩
  obtain ⟨w, hwA1, hw⟩ := hqA1
  have : v q = w := by
    rw [← hw, hu.invOn.1 (hcut.fst_subset hwA1)]
  exact hrA1 (this ▸ hwA1)

/-- **`prop:boundary-continuity`.** The glued map is continuous on the closed Jordan domain. -/
theorem boundary_continuity (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) :
    ContinuousOn (extendByBoundary C u F) (C ∪ inside C) := by
  have heqC : EqOn (extendByBoundary C u F) u C := fun _ hz => extendByBoundary_of_mem hz
  have heqD : EqOn (extendByBoundary C u F) F (inside C) := fun _ hz =>
    extendByBoundary_of_notMem (inside_subset_compl hz)
  intro z hz
  rcases hz with hzC | hzin
  · -- at a point of the curve: split the approach into the boundary part and the inner part
    rw [ContinuousWithinAt, extendByBoundary_of_mem hzC, nhdsWithin_union, Filter.tendsto_sup]
    constructor
    · exact Tendsto.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqC).symm
        (hu.continuousOn z hzC)
    · exact Tendsto.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqD).symm
        (tendsto_nhdsWithin_inside hC hu hF hsub hdense hcross hspoke hzC)
  · -- at an interior point the map is `F` on a neighbourhood
    have hopen : IsOpen (inside C) := isOpen_inside hC.isClosed
    have hmem : inside C ∈ 𝓝 z := hopen.mem_nhds hzin
    have hFat : ContinuousAt F z := hF.continuousOn.continuousAt hmem
    exact (hFat.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hmem heqD)).continuousWithinAt

/-! ### `thm:square-extension` -/

/-- **`thm:square-extension`, for one curve.** The glued map restricts to a homeomorphism of the
closed Jordan domain onto the closed square, and extends `u`.

Continuity of the inverse is not proved directly: the domain is compact and the square is
Hausdorff, so the continuous bijection `Fbar` is a closed map, which is exactly what
`continuousOn_iff_isClosed` asks of the inverse. -/
theorem isHomeoOn_extendByBoundary (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) :
    IsHomeoOn (extendByBoundary C u F) (extendByBoundary modelCurve v F')
      (C ∪ inside C) (Plane.closedSquare 0 1) := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  have hcont : ContinuousOn (extendByBoundary C u F) (C ∪ inside C) :=
    boundary_continuity hC hu hF hsub hdense hcross hspoke
  have hK : IsCompact (C ∪ inside C) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_union_inside hsep)
      (hC.isCompact.isBounded.union hsep.isBounded_inside)
  -- the two `MapsTo` clauses
  have hmaps : MapsTo (extendByBoundary C u F) (C ∪ inside C) (Plane.closedSquare 0 1) := by
    rintro z (hz | hz)
    · rw [extendByBoundary_of_mem hz]
      exact modelCurve_subset_closedSquare (hu.mapsTo hz)
    · rw [extendByBoundary_of_notMem (inside_subset_compl hz)]
      exact Plane.openSquare_subset_closedSquare 0 1 (hF.mapsTo hz)
  have hmaps' : MapsTo (extendByBoundary modelCurve v F') (Plane.closedSquare 0 1)
      (C ∪ inside C) := by
    intro w hw
    by_cases hwc : w ∈ modelCurve
    · rw [extendByBoundary_of_mem hwc]
      exact Or.inl (hu.mapsTo_inv hwc)
    · have hwo : w ∈ Plane.openSquare 0 1 := by
        rw [← closedSquare_sdiff_modelCurve]; exact ⟨hw, hwc⟩
      rw [extendByBoundary_of_notMem hwc]
      exact Or.inr (hF.mapsTo_inv hwo)
  -- the two inverse laws
  have hleft : LeftInvOn (extendByBoundary modelCurve v F') (extendByBoundary C u F)
      (C ∪ inside C) := by
    rintro z (hz | hz)
    · rw [extendByBoundary_of_mem hz, extendByBoundary_of_mem (hu.mapsTo hz)]
      exact hu.invOn.1 hz
    · have hFz : F z ∈ Plane.openSquare 0 1 := hF.mapsTo hz
      have : F z ∉ modelCurve := by
        rw [← inside_modelCurve] at hFz
        exact inside_subset_compl hFz
      rw [extendByBoundary_of_notMem (inside_subset_compl hz),
        extendByBoundary_of_notMem this]
      exact hF.invOn.1 hz
  have hright : RightInvOn (extendByBoundary modelCurve v F') (extendByBoundary C u F)
      (Plane.closedSquare 0 1) := by
    intro w hw
    by_cases hwc : w ∈ modelCurve
    · rw [extendByBoundary_of_mem hwc, extendByBoundary_of_mem (hu.mapsTo_inv hwc)]
      exact hu.invOn.2 hwc
    · have hwo : w ∈ Plane.openSquare 0 1 := by
        rw [← closedSquare_sdiff_modelCurve]; exact ⟨hw, hwc⟩
      have : F' w ∉ C := inside_subset_compl (hF.mapsTo_inv hwo)
      rw [extendByBoundary_of_notMem hwc, extendByBoundary_of_notMem this]
      exact hF.invOn.2 hwo
  -- continuity of the inverse, by compactness
  refine ⟨hmaps, hmaps', hcont, ?_, hleft, hright⟩
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨extendByBoundary C u F '' (t ∩ (C ∪ inside C)), ?_, ?_⟩
  · exact ((hK.inter_left ht).image_of_continuousOn
      (hcont.mono inter_subset_right)).isClosed
  · ext w
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hwt, hw⟩
      exact ⟨⟨_, ⟨hwt, hmaps' hw⟩, hright hw⟩, hw⟩
    · rintro ⟨⟨z, ⟨hzt, hzK⟩, rfl⟩, hw⟩
      exact ⟨by rw [hleft hzK]; exact hzt, hw⟩

/-! ### The assembled hypothesis, and `Schoenflies.SquareExtension` -/

/-- **Everything this section assumes**, for every Jordan curve and every boundary
homeomorphism onto the model square: a dense set of anchors, the limit homeomorphism of the
interiors (`prop:interior-homeomorphism`), the anchor crosscuts with their target images
(`lem:skeleton-crosscuts` and `prop:skeleton-agreement`), and the spokes at the anchors
(`lem:anchor-density`).

`Schoenflies.squareExtension_of_hasLimitHomeomorphism` turns this into
`Schoenflies.SquareExtension`, which is the input required by the final reduction. -/
def HasLimitHomeomorphism : Prop :=
  ∀ (C : Set Plane) (u v : Plane → Plane), IsJordanCurve C → IsHomeoOn u v C modelCurve →
    ∃ (𝒜 : Set Plane) (F F' : Plane → Plane), 𝒜 ⊆ C ∧ C ⊆ closure 𝒜 ∧
      IsHomeoOn F F' (inside C) (Plane.openSquare 0 1) ∧
      HasAnchorCrosscuts C 𝒜 u F ∧ HasSpokes C 𝒜 u F

/-- **`thm:square-extension`.** Every homeomorphism of a Jordan curve onto the model square
boundary extends to a homeomorphism of the closed Jordan domain onto the closed square. -/
theorem squareExtension_of_hasLimitHomeomorphism (h : HasLimitHomeomorphism) :
    SquareExtension := by
  intro C u v hC hu
  obtain ⟨𝒜, F, F', hsub, hdense, hF, hcross, hspoke⟩ := h C u v hC hu
  exact ⟨extendByBoundary C u F, extendByBoundary modelCurve v F',
    isHomeoOn_extendByBoundary hC hu hF hsub hdense hcross hspoke,
    fun _ hz => extendByBoundary_of_mem hz⟩

end Schoenflies
