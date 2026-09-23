/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SkeletonLocal

/-!
# The sector decomposition of a local disk, and the branches that cut it

`Schoenflies/SkeletonLocal.lean` proves the *radial* half of Lemma "Local structure of a
polygonal skeleton" (`lem:local-skeleton-structure`): a point `x` of a finite polygonal plane
graph has a radius `r` at which the closed disk meets the point set exactly in `x` together with
the radii in the *local directions* `Schoenflies.localDirs`. Two things the blueprint proves are
missing there, and this module supplies them.

## 1. The sectors

"Consequently `B(x,r) \ |G|` is a finite union of open circular sectors" is proved here, in the
form the blueprint states it: the punctured disk is the union, over the **consecutive pairs** of
local directions, of the open sectors between them
(`Schoenflies.IsLocalRadius.ball_diff_eq_iUnion_cone`), each of which is open, connected,
nonempty and disjoint from the graph. The sector is `Plane.cone x (Plane.arcCCW d w) r`, the
object `Schoenflies/Strip.lean` already builds; nothing new is defined for it. The union is
disjoint (`Schoenflies.cone_disjoint_of_isSectorPair`), so each sector is exactly a connected
component of the punctured disk
(`Schoenflies.IsLocalRadius.connectedComponentIn_eq_cone`).

"Consecutive" is `Plane.IsSectorPair D d w`: both are in `D`, they are distinct, and no member
of `D` lies strictly inside `arcCCW d w`. **No angle and no sorting is visible in that
definition**, and none is used at a call site. The existence proof does sort, and this is the
piece with no analogue on `main`: read as a *ternary cyclic order*, `Plane.arcCCW` obeys
rotation (`Plane.mem_arcCCW_rotate`), asymmetry (`Plane.notMem_arcCCW_swap`,
`Plane.notMem_arcCCW_asymm`), two transitivity laws (`Plane.arcCCW_trans`,
`Plane.arcCCW_trans'`) and — for genuine directions — totality (`Plane.mem_arcCCW_total`). All
of them are pure sign-of-`det` facts, and the two transitivity laws are one instance each of the
Grassmann identity `Plane.det_mul_det_add`; none of them needs a nondegeneracy hypothesis. Cut
at any direction outside `D` and the cyclic order becomes a linear order; the greatest and the
least element of `D` in it bound the sector containing the cut (`Plane.exists_isSectorPair`).

## 2. The branches

On `main` nothing links `localDirs` to the edges of the graph, so "with pairwise distinct
directions" holds only because a *set* has distinct members. The blueprint derives it, and that
derivation is the mathematical content of the lemma. It is here:

* `Graph.IsDrawing.exists_edge_radial` and `Graph.IsDrawing.edge_radial_unique` — each radial
  segment lies inside exactly one edge arc. The relative interior of the segment is connected
  and contains no vertex, so `Graph.IsDrawing.unique_edge_at` makes "the edge through this
  point" locally constant on it, and the edge arcs being closed and finitely many makes it
  constant.
* `Graph.IsDrawing.not_three_localDirs_on_edge` — one edge carries at most two of them. The
  parametrization of an edge is a continuous injection of a compact interval, hence a closed
  map, so each radial segment pulls back to an *interval* of parameters; three such intervals
  all contain the parameter of `x`, all reach beyond it, and meet pairwise nowhere else, which
  is impossible on a line.
* `Graph.IsDrawing.localDirs_ncard_le` — the two together, counted: there are at most twice as
  many local directions as edges. This is what makes `localDirs` a count of *branches*.

Both steps need a radius at which the disk contains no vertex other than `x`, which
`Schoenflies.IsLocalRadius` does not record and does not imply — a local radius may perfectly
well contain other vertices, sitting out along the radial segments. `Graph.IsLocalDisk` adds
that clause and `Graph.IsDrawing.exists_isLocalDisk` produces it.

## What the consumer gets

`lem:polygonal-side-accessibility` wants, at once: the finitely many sectors, that each is
connected and misses the skeleton, one that meets the prescribed face, and a short straight
segment from `x` into it. `Graph.exists_access_sector` hands over all four about one named
sector, so nothing has to be composed at the call site. The straight segment needs no
shortening: a sector is star-shaped about its apex
(`Schoenflies.openSegment_subset_cone_arcCCW`), so `(x, y)` lies in the very sector `y` is in.

## The two-branch hypothesis

The sector decomposition and `Graph.exists_access_sector` assume that `x` has **at least two**
local directions. That is not cosmetic: with one local direction the complement of the ray in
the disk is a genuine sector of full turn, and `arcCCW d d` is empty, so it is not of the form
`arcCCW d w` for `d, w ∈ localDirs`; with none it is the punctured disk. The
consumer form is `Graph.IsDrawing.exists_access_region`, which returns the connected component
of `y` in the punctured disk — a set with every property of a sector that the accessibility
argument uses, but with no claim that it is bounded by two local directions. Whether the two
degenerate punctured disks are connected is not settled here; it is not needed, because the
component is connected by construction.

## Blueprint

* `Schoenflies.IsLocalRadius.ball_diff_eq_iUnion_cone`,
  `Schoenflies.IsLocalRadius.cone_subset_ball_diff`,
  `Schoenflies.IsLocalRadius.isConnected_cone`, `Schoenflies.isOpen_cone_arcCCW`,
  `Schoenflies.cone_disjoint_of_isSectorPair`,
  `Schoenflies.IsLocalRadius.connectedComponentIn_eq_cone` — "consequently `B(x,r) \ |G|` is a
  finite union of open circular sectors" of `lem:local-skeleton-structure`.
* `Graph.IsDrawing.exists_edge_radial`, `Graph.IsDrawing.edge_radial_unique`,
  `Graph.IsDrawing.not_three_localDirs_on_edge`, `Graph.IsDrawing.localDirs_ncard_le` — "two of
  these radial segments with a common direction would have overlapping relative interiors,
  which is impossible", the distinct-directions step of the same lemma.
* `Graph.IsLocalDisk`, `Graph.IsDrawing.exists_isLocalDisk` — the radius `r₀` of the same lemma,
  with the vertex clause the drawing axioms need.
* `Graph.exists_access_sector`, `Graph.IsDrawing.exists_access_region` — "each sector is
  connected and disjoint from the skeleton … at least one sector lies in `F` … a short straight
  segment from `x` into that sector is a polygonal access arc" of
  `lem:polygonal-side-accessibility`.
* `Plane.mem_arcCCW_rotate`, `Plane.notMem_arcCCW_swap`, `Plane.arcCCW_trans`,
  `Plane.arcCCW_trans'`, `Plane.mem_arcCCW_total`, `Plane.exists_isSectorPair`,
  `Plane.IsSectorPair.unique` — the cyclic order of finitely many directions.
  `app:background`, item 1 lists the two arcs bounded by two directions but not their cyclic
  order; this is the part of "pairwise distinct directions" that the background package does
  not cover.
-/

@[expose] public section

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ### An extreme element of a finite set

The counterclockwise order of directions is a bare relation, not an order instance, so the
sorting step is stated for a relation that is total and transitive *on the set in question*. -/

/-- A finite nonempty set on which a relation is total and transitive has a greatest element. -/
theorem exists_greatest_of_finite {α : Type*} {R : α → α → Prop} {D : Set α}
    (hfin : D.Finite) (hne : D.Nonempty)
    (htot : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → R a b ∨ R b a)
    (htr : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, R a b → R b c → R a c) :
    ∃ m ∈ D, ∀ a ∈ D, a ≠ m → R a m := by
  classical
  -- Induct over finite subsets of `D`, so that the two hypotheses stay attached to `D`.
  suffices H : ∀ T : Finset α, ↑T ⊆ D → T.Nonempty → ∃ m ∈ T, ∀ a ∈ T, a ≠ m → R a m by
    obtain ⟨m, hm, hmax⟩ := H hfin.toFinset (by simp) (by simpa using hne)
    exact ⟨m, by simpa using hm, fun a ha hane => hmax a (by simpa using ha) hane⟩
  intro T
  induction T using Finset.induction_on with
  | empty => intro _ h; simp at h
  | @insert a T ha ih =>
    intro hsub _
    have haD : a ∈ D := hsub (by simp)
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · exact ⟨a, by simp, by intro b hb hbne; simp only [Finset.mem_insert,
        Finset.notMem_empty, or_false] at hb; exact absurd hb hbne⟩
    obtain ⟨m, hm, hmax⟩ := ih (fun x hx => hsub (by simp [hx])) hTne
    have hmD : m ∈ D := hsub (by simp [hm])
    have ham : a ≠ m := fun h => ha (h ▸ hm)
    rcases htot a haD m hmD ham with h | h
    · refine ⟨m, Finset.mem_insert_of_mem hm, fun b hb hbm => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact h
      · exact hmax b hb hbm
    · refine ⟨a, Finset.mem_insert_self _ _, fun b hb hba => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact absurd rfl hba
      · rcases eq_or_ne b m with rfl | hbm
        · exact h
        · exact htr b (hsub (by simp [hb])) m hmD a haD (hmax b hb hbm) h

namespace Plane

variable {u v w d z : Plane} {ρ : ℝ}

/-! ### The cyclic order of directions

`Plane.arcCCW u w` is, by definition, the set of `d` for which at least two of the three
consecutive orientation forms of the triple `(u, d, w)` are positive — Sedgewick's `ccw`
predicate on that triple. Reading it as a *ternary cyclic order* rather than as an arc is what
makes a finite set of directions sortable without an angle: the three lemmas below are exactly
the axioms of a cyclic order (rotation, asymmetry, transitivity), and they hold with no
nondegeneracy hypothesis at all. -/

/-- The Grassmann identity for four vectors of the plane: any three of them are linearly
dependent, and expanding that dependence against the fourth gives this relation among the six
orientation forms. Every transitivity below is one instance of it. -/
theorem det_mul_det_add (a b c e : Plane) :
    det a b * det c e - det a c * det b e + det a e * det b c = 0 := by
  simp only [det]; ring

/-- **Rotation.** The cyclic order is invariant under rotating its triple: `d` lies on the arc
counterclockwise from `u` to `w` exactly when `w` lies on the arc counterclockwise from `d` to
`u`. -/
theorem mem_arcCCW_rotate : d ∈ arcCCW u w ↔ w ∈ arcCCW d u := by
  simp only [arcCCW, Set.mem_ofPred_eq]
  tauto

/-- A bounding ray is not on its own arc. -/
theorem left_notMem_arcCCW (u w : Plane) : u ∉ arcCCW u w := by
  have h : det w u = -det u w := det_comm w u
  simp only [arcCCW, Set.mem_ofPred_eq, det_self, h]
  rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩) <;> linarith

/-- The other bounding ray is not on the arc either. -/
theorem right_notMem_arcCCW (u w : Plane) : w ∉ arcCCW u w := by
  have h : det w u = -det u w := det_comm w u
  simp only [arcCCW, Set.mem_ofPred_eq, det_self, h]
  rintro (⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩) <;> linarith

/-- **Asymmetry.** Transposing the first two entries of the triple negates the cyclic order:
if `v` is counterclockwise of `u` before `w`, then `u` is not counterclockwise of `v` before
`w`. Two of the three orientation forms would have to be positive and two negative. -/
theorem notMem_arcCCW_swap (h : v ∈ arcCCW u w) : u ∉ arcCCW v w := by
  have e1 : det v u = -det u v := det_comm v u
  have e2 : det u w = -det w u := det_comm u w
  have e3 : det w v = -det v w := det_comm w v
  simp only [arcCCW, Set.mem_ofPred_eq] at h ⊢
  rw [e1, e3]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rintro (⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2⟩) <;> linarith

/-! #### The two transitivity laws

Both are the same real-arithmetic fact, extracted so that the `det` bookkeeping happens once.
Write `p₁ = det u w`, `p₂ = det w v`, `p₃ = det v u` for the triple `(u, w, v)`, and
`q₂ = det v d`, `q₃ = det d u` for the missing entries of `(u, v, d)`; note `det u v = -p₃`.
The Grassmann identity turns into `p₃ * s₂ = q₃ * p₂ - p₁ * q₂` with `s₂ = det w d`. -/

private theorem trans_aux₁ {p₁ p₂ p₃ q₂ q₃ s₂ : ℝ}
    (hid : p₃ * s₂ = q₃ * p₂ - p₁ * q₂)
    (h1 : (0 < p₁ ∧ 0 < p₂) ∨ (0 < p₂ ∧ 0 < p₃) ∨ (0 < p₃ ∧ 0 < p₁))
    (h2 : (0 < -p₃ ∧ 0 < q₂) ∨ (0 < q₂ ∧ 0 < q₃) ∨ (0 < q₃ ∧ 0 < -p₃)) :
    (0 < p₁ ∧ 0 < s₂) ∨ (0 < s₂ ∧ 0 < q₃) ∨ (0 < q₃ ∧ 0 < p₁) := by
  rcases le_or_gt p₃ 0 with hp₃ | hp₃
  · -- `p₃ ≤ 0` forces the first pair of `h1`, so `p₁` and `p₂` are both positive.
    have hp₁ : 0 < p₁ := by rcases h1 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> linarith
    have hp₂ : 0 < p₂ := by rcases h1 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
    rcases lt_or_ge 0 q₃ with hq₃ | hq₃
    · exact Or.inr (Or.inr ⟨hq₃, hp₁⟩)
    · -- `q₃ ≤ 0` forces the first pair of `h2`, and then the identity signs `s₂`.
      have hq₂ : 0 < q₂ := by rcases h2 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
      have hp₃' : p₃ < 0 := by rcases h2 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
      have : 0 < s₂ := by nlinarith
      exact Or.inl ⟨hp₁, this⟩
  · -- `0 < p₃` forces the middle pair of `h2`.
    have hq₂ : 0 < q₂ := by rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
    have hq₃ : 0 < q₃ := by rcases h2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> linarith
    rcases lt_or_ge 0 p₁ with hp₁ | hp₁
    · exact Or.inr (Or.inr ⟨hq₃, hp₁⟩)
    · have hp₂ : 0 < p₂ := by rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
      have : 0 < s₂ := by nlinarith
      exact Or.inr (Or.inl ⟨this, hq₃⟩)

private theorem trans_aux₂ {p₁ p₂ p₃ q₂ q₃ s₂ : ℝ}
    (hid : p₃ * s₂ = q₃ * p₂ - p₁ * q₂)
    (h1 : (0 < p₁ ∧ 0 < p₂) ∨ (0 < p₂ ∧ 0 < p₃) ∨ (0 < p₃ ∧ 0 < p₁))
    (h2 : (0 < -p₃ ∧ 0 < q₂) ∨ (0 < q₂ ∧ 0 < q₃) ∨ (0 < q₃ ∧ 0 < -p₃)) :
    (0 < p₂ ∧ 0 < q₂) ∨ (0 < q₂ ∧ 0 < -s₂) ∨ (0 < -s₂ ∧ 0 < p₂) := by
  rcases le_or_gt p₃ 0 with hp₃ | hp₃
  · have hp₁ : 0 < p₁ := by rcases h1 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> linarith
    have hp₂ : 0 < p₂ := by rcases h1 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
    rcases lt_or_ge 0 q₂ with hq₂ | hq₂
    · exact Or.inl ⟨hp₂, hq₂⟩
    · have hq₃ : 0 < q₃ := by rcases h2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> linarith
      have hp₃' : p₃ < 0 := by rcases h2 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
      have : s₂ < 0 := by nlinarith
      exact Or.inr (Or.inr ⟨by linarith, hp₂⟩)
  · have hq₂ : 0 < q₂ := by rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
    have hq₃ : 0 < q₃ := by rcases h2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> linarith
    rcases lt_or_ge 0 p₂ with hp₂ | hp₂
    · exact Or.inl ⟨hp₂, hq₂⟩
    · have hp₁ : 0 < p₁ := by rcases h1 with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
      have : s₂ < 0 := by nlinarith
      exact Or.inr (Or.inl ⟨hq₂, by linarith⟩)

/-- The instance of `Plane.det_mul_det_add` that both transitivity laws run on. -/
private theorem grassmann (u w v d : Plane) :
    det v u * det w d = det d u * det w v - det u w * det v d := by
  simp only [det]; ring

/-- **Transitivity, first form.** Counterclockwise order seen from a fixed ray `u` is
transitive: if `w` comes before `v` and `v` before `d`, then `w` comes before `d`. This is what
makes a finite set of directions linearly ordered once a ray to cut at has been chosen. -/
theorem arcCCW_trans (h₁ : w ∈ arcCCW u v) (h₂ : v ∈ arcCCW u d) : w ∈ arcCCW u d := by
  simp only [arcCCW, Set.mem_ofPred_eq] at h₁ h₂ ⊢
  have hv : det u v = -det v u := det_comm u v
  rw [hv] at h₂
  exact trans_aux₁ (grassmann u w v d) h₁ h₂

/-- **Transitivity, second form.** The same three rays, read from `w` instead of from `u`: if
`w` comes before `v` and `v` before `d` as seen from `u`, then `v` lies on the arc
counterclockwise from `w` to `d`. This is the step that turns "nothing of the finite set lies
between `u` and the extreme rays" into "nothing lies inside the sector". -/
theorem arcCCW_trans' (h₁ : w ∈ arcCCW u v) (h₂ : v ∈ arcCCW u d) : v ∈ arcCCW w d := by
  simp only [arcCCW, Set.mem_ofPred_eq] at h₁ h₂ ⊢
  have hv : det u v = -det v u := det_comm u v
  have hd : det d w = -det w d := det_comm d w
  rw [hv] at h₂
  rw [hd]
  exact trans_aux₂ (grassmann u w v d) h₁ h₂

/-! #### Totality

Totality is the only one of the four order axioms that needs a hypothesis: the two rays being
compared must be genuine directions, distinct from each other and from the ray cut at. -/

/-- A unit vector parallel to `u` is one of the two unit vectors along the line of `u`. -/
theorem eq_dir_or_eq_neg_dir (hu : u ≠ 0) (hv : IsDirection v) (h : det u v = 0) :
    v = dir u ∨ v = -dir u := by
  obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u v hu).1 h
  have hn : |c| * ‖u‖ = 1 := by
    have := hv.norm
    rwa [norm_smul, Real.norm_eq_abs] at this
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hc : c = ‖u‖⁻¹ ∨ c = -‖u‖⁻¹ := by
    rcases abs_cases c with ⟨he, _⟩ | ⟨he, _⟩
    · left; rw [he] at hn; field_simp; linarith
    · right; rw [he] at hn; field_simp; linarith
  rcases hc with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by rw [dir]; module)

private theorem total_aux {A B C : ℝ} (hA : A = 0 → 0 < B * C) (hB : B = 0 → 0 < A * C)
    (hC : C = 0 → 0 < A * B) :
    ((0 < A ∧ 0 < B) ∨ (0 < B ∧ 0 < C) ∨ (0 < C ∧ 0 < A)) ∨
      ((0 < -C ∧ 0 < -B) ∨ (0 < -B ∧ 0 < -A) ∨ (0 < -A ∧ 0 < -C)) := by
  rcases eq_or_ne A 0 with rfl | hA0
  · have h := hA rfl
    rcases lt_trichotomy B 0 with hb | rfl | hb
    · exact Or.inr (Or.inl ⟨by nlinarith, by linarith⟩)
    · simp at h
    · exact Or.inl (Or.inr (Or.inl ⟨hb, by nlinarith⟩))
  rcases eq_or_ne B 0 with rfl | hB0
  · have h := hB rfl
    rcases lt_trichotomy A 0 with ha | rfl | ha
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by nlinarith⟩))
    · exact absurd rfl hA0
    · exact Or.inl (Or.inr (Or.inr ⟨by nlinarith, ha⟩))
  rcases eq_or_ne C 0 with rfl | hC0
  · have h := hC rfl
    rcases lt_trichotomy A 0 with ha | rfl | ha
    · exact Or.inr (Or.inr (Or.inl ⟨by nlinarith, by linarith⟩))
    · exact absurd rfl hA0
    · exact Or.inl (Or.inl ⟨ha, by nlinarith⟩)
  -- All three nonzero: whatever the signs, one of the two triples has two positives.
  rcases lt_or_gt_of_ne hA0 with ha | ha <;> rcases lt_or_gt_of_ne hB0 with hb | hb <;>
    rcases lt_or_gt_of_ne hC0 with hc | hc
  all_goals first
    | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-- **Totality.** Two distinct directions, neither of them the direction of `u`, are comparable
in the counterclockwise order seen from `u`. The three degenerate configurations — one of them
opposite to `u`, or the two opposite to each other — are exactly the three hypotheses of
`total_aux`. -/
theorem mem_arcCCW_total (hu : u ≠ 0) (hv : IsDirection v) (hw : IsDirection w) (hvw : v ≠ w)
    (hvu : v ≠ dir u) (hwu : w ≠ dir u) : v ∈ arcCCW u w ∨ w ∈ arcCCW u v := by
  have hupos : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu
  have hdu : dir u = ‖u‖⁻¹ • u := rfl
  -- `A = det u v`, `B = det v w`, `C = det w u`.
  have hAB : det v u = -det u v := det_comm v u
  have hCB : det u w = -det w u := det_comm u w
  have hWV : det w v = -det v w := det_comm w v
  have key : ((0 < det u v ∧ 0 < det v w) ∨ (0 < det v w ∧ 0 < det w u) ∨
      (0 < det w u ∧ 0 < det u v)) ∨
      ((0 < -det w u ∧ 0 < -det v w) ∨ (0 < -det v w ∧ 0 < -det u v) ∨
        (0 < -det u v ∧ 0 < -det w u)) := by
    refine total_aux ?_ ?_ ?_
    · -- `det u v = 0`: then `v = -dir u`, so `det v w` and `det w u` agree up to `‖u‖ > 0`.
      intro h
      have hv' : v = -dir u := (eq_dir_or_eq_neg_dir hu hv h).resolve_left hvu
      have hne : det w u ≠ 0 := by
        intro h0
        have : det u w = 0 := by linarith [det_comm u w]
        rcases eq_dir_or_eq_neg_dir hu hw this with h1 | h1
        · exact hwu h1
        · exact hvw (by rw [hv', h1])
      have hsm : (-(‖u‖⁻¹ • u) : Plane) = (-‖u‖⁻¹) • u := by module
      have he : det v w = ‖u‖⁻¹ * det w u := by
        rw [hv', hdu, hsm, det_smul_left, det_comm u w]
        ring
      rw [he, mul_assoc]
      exact mul_pos (inv_pos.2 hupos) (mul_self_pos.2 hne)
    · -- `det v w = 0`: then `w = -v`, so `det w u = det u v`.
      intro h
      have hw' : w = -v := by
        have hvne : v ≠ 0 := hv.ne_zero
        rcases eq_dir_or_eq_neg_dir hvne hw h with h1 | h1
        · rw [dir, hv.norm] at h1; simp at h1; exact absurd h1.symm hvw
        · rw [dir, hv.norm] at h1; simpa using h1
      have hne : det u v ≠ 0 := by
        intro h0
        have hv' : v = -dir u := (eq_dir_or_eq_neg_dir hu hv h0).resolve_left hvu
        exact hwu (by rw [hw', hv']; module)
      have hsm : (-v : Plane) = (-1 : ℝ) • v := by module
      have he : det w u = det u v := by
        rw [hw', hsm, det_smul_left, det_comm v u]; ring
      rw [he]
      exact mul_self_pos.2 hne
    · -- `det w u = 0`: then `w = -dir u`, so `det v w` and `det u v` agree up to `‖u‖ > 0`.
      intro h
      have h' : det u w = 0 := by linarith [det_comm u w]
      have hw' : w = -dir u := (eq_dir_or_eq_neg_dir hu hw h').resolve_left hwu
      have hne : det u v ≠ 0 := by
        intro h0
        have hv' : v = -dir u := (eq_dir_or_eq_neg_dir hu hv h0).resolve_left hvu
        exact hvw (by rw [hv', hw'])
      have hsm : (-(‖u‖⁻¹ • u) : Plane) = (-‖u‖⁻¹) • u := by module
      have he : det v w = ‖u‖⁻¹ * det u v := by
        rw [hw', hdu, hsm, det_smul_right, det_comm v u]
        ring
      rw [he, mul_comm, mul_assoc]
      exact mul_pos (inv_pos.2 hupos) (mul_self_pos.2 hne)
  simp only [arcCCW, Set.mem_ofPred_eq]
  rw [hAB, hCB, hWV]
  rcases key with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-! ### Consecutive directions, and the sector they bound

A finite set `D` of directions cuts the circle of directions into arcs. A pair `(d, w)` of
members of `D` is *consecutive* when nothing of `D` lies strictly between them: that is the
whole of `Plane.IsSectorPair`, and it is stated with no reference to a sorting of `D`.

The existence proof does sort, but only relative to a *free* direction `u` — one that is not in
`D`. Seen from `u` the cyclic order becomes the linear order `v ≺ w ↔ v ∈ arcCCW u w`, whose
greatest and least elements are the two rays bounding the sector `u` lies in. -/

/-- **Asymmetry, transposing the last two entries.** -/
theorem notMem_arcCCW_asymm (h : v ∈ arcCCW u w) : w ∉ arcCCW u v := by
  rw [mem_arcCCW_rotate] at h
  rw [mem_arcCCW_rotate]
  exact notMem_arcCCW_swap h

/-- A unit vector is its own direction. -/
theorem dir_self (hu : IsDirection u) : dir u = u := by
  rw [dir, hu.norm, inv_one, one_smul]

/-- Two distinct directions killed by the orientation form are opposite. -/
theorem eq_neg_of_det_eq_zero (hu : IsDirection u) (hw : IsDirection w) (hne : u ≠ w)
    (h : det u w = 0) : w = -u := by
  rcases eq_dir_or_eq_neg_dir hu.ne_zero hw h with h1 | h1
  · rw [dir_self hu] at h1; exact absurd h1.symm hne
  · rwa [dir_self hu] at h1

/-- The arc counterclockwise from a ray to its opposite is the open half-plane on its left.
This is the sector of a point with exactly two local branches, in a straight line. -/
theorem arcCCW_neg (u : Plane) : arcCCW u (-u) = {v | 0 < det u v} := by
  have hsm : (-u : Plane) = (-1 : ℝ) • u := by module
  have e1 : ∀ v : Plane, det v (-u) = det u v := by
    intro v; rw [hsm, det_smul_right, det_comm v u]; ring
  have e2 : det (-u) u = 0 := by rw [hsm, det_smul_left, det_self, mul_zero]
  ext v
  simp only [arcCCW, Set.mem_ofPred_eq, e1, e2]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> linarith
  · exact fun h => Or.inl ⟨h, h⟩

/-- **The sector between two distinct directions is connected**, whether or not they are
opposite. `Plane.isConnected_arcCCW_ball` assumes `det u w ≠ 0`, which excludes the straight
case; there the arc is a half-plane, and convex. -/
theorem isConnected_arcCCW_ball_of_ne (hu : IsDirection u) (hw : IsDirection w) (hne : u ≠ w)
    (hρ : 0 < ρ) : IsConnected (arcCCW u w ∩ ball (0 : Plane) ρ) := by
  rcases eq_or_ne (det u w) 0 with h | h
  · rw [eq_neg_of_det_eq_zero hu hw hne h, arcCCW_neg]
    have hhalf : (0 : ℝ) < ρ / 2 := by linarith
    refine ⟨⟨(ρ / 2) • perp u, ?_, ?_⟩,
      ((convex_det_right_pos u).inter (convex_ball _ _)).isPreconnected⟩
    · simp only [Set.mem_ofPred_eq, det_smul_right, det_perp_self, hu.norm, one_pow, mul_one]
      exact hhalf
    · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, norm_perp, hu.norm, mul_one,
        abs_of_pos hhalf]
      linarith
  · exact isConnected_arcCCW_ball h hρ

/-- The sector of radius `ρ` at `x` between two distinct directions is connected. -/
theorem isConnected_cone_arcCCW_of_ne (x : Plane) (hu : IsDirection u) (hw : IsDirection w)
    (hne : u ≠ w) (hρ : 0 < ρ) : IsConnected (cone x (arcCCW u w) ρ) := by
  rw [cone_eq_image]
  exact (isConnected_arcCCW_ball_of_ne hu hw hne hρ).image _
    ((continuous_const.add continuous_id).continuousOn)

/-- **`d` and `w` are consecutive in `D`**: both belong to `D`, they are distinct, and no member
of `D` lies strictly inside the arc counterclockwise from `d` to `w`. That arc is then a sector
of the complement of `D`. -/
def IsSectorPair (D : Set Plane) (d w : Plane) : Prop :=
  d ∈ D ∧ w ∈ D ∧ d ≠ w ∧ ∀ v ∈ D, v ∉ arcCCW d w

/-- The consecutive pairs of a finite set of directions, as a set. Indexing the sectors by this
set rather than by a chosen cyclic successor keeps the construction choice-free. -/
def sectorPairs (D : Set Plane) : Set (Plane × Plane) := {p | IsSectorPair D p.1 p.2}

theorem mem_sectorPairs_iff {D : Set Plane} {p : Plane × Plane} :
    p ∈ sectorPairs D ↔ IsSectorPair D p.1 p.2 := Iff.rfl

theorem sectorPairs_finite {D : Set Plane} (hfin : D.Finite) : (sectorPairs D).Finite :=
  (hfin.prod hfin).subset fun _ hp => ⟨hp.1, hp.2.1⟩

/-- **Every free direction lies in a sector.** Given a finite set `D` of at least two
directions and a direction not in `D`, there is a consecutive pair of `D` whose arc contains
it. The two bounding rays are the greatest and the least element of `D` in the counterclockwise
order seen from the free direction. -/
theorem exists_isSectorPair {D : Set Plane} (hfin : D.Finite) (hdir : ∀ v ∈ D, IsDirection v)
    (h2 : ∃ a ∈ D, ∃ b ∈ D, a ≠ b) (hu : u ≠ 0) (hud : dir u ∉ D) :
    ∃ d w, IsSectorPair D d w ∧ u ∈ arcCCW d w := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := h2
  have hne : D.Nonempty := ⟨a₀, ha₀⟩
  have hnotdir : ∀ v ∈ D, v ≠ dir u := fun v hv h => hud (h ▸ hv)
  -- Totality and transitivity of `v ≺ w ↔ v ∈ arcCCW u w` on `D`.
  have htot : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → a ∈ arcCCW u b ∨ b ∈ arcCCW u a := fun a ha b hb hab =>
    mem_arcCCW_total hu (hdir a ha) (hdir b hb) hab (hnotdir a ha) (hnotdir b hb)
  obtain ⟨m, hm, hmax⟩ := exists_greatest_of_finite (R := fun a b => a ∈ arcCCW u b) hfin hne
    htot (fun _ _ _ _ _ _ h₁ h₂ => arcCCW_trans h₁ h₂)
  obtain ⟨n, hn, hmin⟩ := exists_greatest_of_finite (R := fun a b => b ∈ arcCCW u a) hfin hne
    (fun a ha b hb hab => (htot a ha b hb hab).symm)
    (fun _ _ _ _ _ _ h₁ h₂ => arcCCW_trans h₂ h₁)
  -- With two distinct members, the greatest and the least are distinct.
  have hmn : m ≠ n := by
    rintro rfl
    rcases eq_or_ne a₀ m with rfl | h
    · exact notMem_arcCCW_asymm (hmax b₀ hb₀ (Ne.symm hab)) (hmin b₀ hb₀ (Ne.symm hab))
    · exact notMem_arcCCW_asymm (hmax a₀ ha₀ h) (hmin a₀ ha₀ h)
  refine ⟨m, n, ⟨hm, hn, hmn, fun v hv => ?_⟩, ?_⟩
  · rcases eq_or_ne v m with rfl | hvm
    · exact left_notMem_arcCCW _ _
    rcases eq_or_ne v n with rfl | hvn
    · exact right_notMem_arcCCW _ _
    -- `v` is between the least and the greatest, hence outside the sector.
    rw [mem_arcCCW_rotate]
    exact notMem_arcCCW_swap (arcCCW_trans' (hmin v hv hvn) (hmax v hv hvm))
  · -- The least is inside the arc from the greatest back to it, so the free ray is too.
    have h := hmin m hm hmn
    rw [mem_arcCCW_rotate, mem_arcCCW_rotate] at h
    exact h


/-! #### The sector a direction lies in is unique

Distinct consecutive pairs bound disjoint arcs, so the sectors are a *partition* of the free
directions and not merely a cover. The proof is the same cyclic-order calculation as the
existence proof, run backwards: a free direction inside `arcCCW d w` forces `d` to be the
greatest and `w` the least element of `D` in the order seen from it. -/

/-- A positive multiple of a direction which is itself a direction is that direction. -/
private theorem eq_of_smul {c : ℝ} (hc : 0 < c) (hd : IsDirection d) (hz : IsDirection z)
    (h : z = c • d) : z = d := by
  have hc1 : c = 1 := by
    have hn := hz.norm
    rwa [h, norm_smul, Real.norm_eq_abs, abs_of_pos hc, hd.norm, mul_one] at hn
  rw [h, hc1, one_smul]

/-- A direction that is neither bounding ray of an arc and is not on it lies on the
complementary arc. Both the generic case and the straight case `w = -d` are covered. -/
theorem mem_arcCCW_rev_of_notMem {d w z : Plane} (hd : IsDirection d) (hw : IsDirection w)
    (hdw : d ≠ w) (hz : IsDirection z) (hzd : z ≠ d) (hzw : z ≠ w) (h : z ∉ arcCCW d w) :
    z ∈ arcCCW w d := by
  rcases eq_or_ne (det d w) 0 with hdet | hdet
  · -- Straight: the two arcs are the two open half-planes bounded by the line of `d`.
    have hwd : w = -d := eq_neg_of_det_eq_zero hd hw hdw hdet
    have harc : arcCCW d w = {v | 0 < det d v} := by rw [hwd]; exact arcCCW_neg d
    have harc' : arcCCW w d = {v | 0 < det w v} := by
      have hne := arcCCW_neg w
      rw [hwd, neg_neg] at hne
      rw [hwd]
      exact hne
    rw [harc, Set.mem_ofPred_eq, not_lt] at h
    rw [harc', Set.mem_ofPred_eq, hwd]
    have hdz : det d z ≠ 0 := by
      intro hzero
      rcases eq_dir_or_eq_neg_dir hd.ne_zero hz hzero with h1 | h1
      · exact hzd (by rwa [dir_self hd] at h1)
      · exact hzw (by rw [hwd]; rwa [dir_self hd] at h1)
    have hsm : (-d : Plane) = (-1 : ℝ) • d := by module
    rw [hsm, det_smul_left]
    have : det d z < 0 := lt_of_le_of_ne h hdz
    linarith
  · rcases mem_ray_or_mem_arcCCW' hdet hz.ne_zero with ⟨c, hc, hcz⟩ | ⟨c, hc, hcz⟩ | harc | harc
    · exact absurd (eq_of_smul hc hd hz hcz) hzd
    · exact absurd (eq_of_smul hc hw hz hcz) hzw
    · exact absurd harc h
    · exact harc

/-- **`d` is the greatest element of `D` seen from a direction of its sector.** -/
theorem IsSectorPair.mem_arcCCW_left {D : Set Plane} {d w v z : Plane} (hp : IsSectorPair D d w)
    (hdir : ∀ y ∈ D, IsDirection y) (hv : v ∈ arcCCW d w) (hz : z ∈ D) (hzd : z ≠ d) :
    z ∈ arcCCW v d := by
  have hrot : w ∈ arcCCW v d := mem_arcCCW_rotate.1 hv
  rcases eq_or_ne z w with rfl | hzw
  · exact hrot
  have hzarc : z ∈ arcCCW w d := mem_arcCCW_rev_of_notMem (hdir d hp.1) (hdir w hp.2.1)
    hp.2.2.1 (hdir z hz) hzd hzw (hp.2.2.2 z hz)
  rw [mem_arcCCW_rotate]
  exact arcCCW_trans' hzarc (mem_arcCCW_rotate.1 hrot)

/-- **`w` is the least element of `D` seen from a direction of its sector.** -/
theorem IsSectorPair.mem_arcCCW_right {D : Set Plane} {d w v z : Plane} (hp : IsSectorPair D d w)
    (hdir : ∀ y ∈ D, IsDirection y) (hv : v ∈ arcCCW d w) (hz : z ∈ D) (hzw : z ≠ w) :
    w ∈ arcCCW v z := by
  rcases eq_or_ne z d with rfl | hzd
  · exact mem_arcCCW_rotate.1 hv
  have hzarc : z ∈ arcCCW w d := mem_arcCCW_rev_of_notMem (hdir d hp.1) (hdir w hp.2.1)
    hp.2.2.1 (hdir z hz) hzd hzw (hp.2.2.2 z hz)
  exact arcCCW_trans' hv (mem_arcCCW_rotate.1 (mem_arcCCW_rotate.1 hzarc))

/-- **The sector containing a free direction is unique.** -/
theorem IsSectorPair.unique {D : Set Plane} {d w d' w' v : Plane} (hdir : ∀ y ∈ D, IsDirection y)
    (hp : IsSectorPair D d w) (hp' : IsSectorPair D d' w') (hv : v ∈ arcCCW d w)
    (hv' : v ∈ arcCCW d' w') : d = d' ∧ w = w' := by
  refine ⟨?_, ?_⟩
  · by_contra hne
    exact notMem_arcCCW_asymm (hp.mem_arcCCW_left hdir hv hp'.1 (Ne.symm hne))
      (hp'.mem_arcCCW_left hdir hv' hp.1 hne)
  · by_contra hne
    exact notMem_arcCCW_asymm (hp.mem_arcCCW_right hdir hv hp'.2.1 (Ne.symm hne))
      (hp'.mem_arcCCW_right hdir hv' hp.2.1 hne)

/-- **Distinct consecutive pairs bound disjoint arcs.** -/
theorem arcCCW_disjoint_of_isSectorPair {D : Set Plane} {d w d' w' : Plane}
    (hdir : ∀ y ∈ D, IsDirection y) (hp : IsSectorPair D d w) (hp' : IsSectorPair D d' w')
    (hne : d ≠ d' ∨ w ≠ w') : Disjoint (arcCCW d w) (arcCCW d' w') := by
  rw [Set.disjoint_left]
  intro v hv hv'
  obtain ⟨h1, h2⟩ := IsSectorPair.unique hdir hp hp' hv hv'
  exact hne.elim (fun h => h h1) fun h => h h2


end Plane

/-! ### The punctured local disk is a finite union of open sectors

This is the last clause of `lem:local-skeleton-structure`, "consequently `B(x,r) \ |G|` is a
finite union of open circular sectors". The sectors are indexed by the consecutive pairs of
local directions, and there are finitely many of them because there are finitely many local
directions. -/

variable {S : Set Plane} {x y z : Plane} {r : ℝ}

/-- A sector between two consecutive local directions misses `S` entirely: no point of it is
`x`, because the origin lies on no arc, and no point of it points along a local direction. -/
theorem IsLocalRadius.cone_subset_ball_diff (h : IsLocalRadius S x r) {d w : Plane}
    (hp : Plane.IsSectorPair (localDirs S x) d w) :
    Plane.cone x (Plane.arcCCW d w) r ⊆ ball x r \ S := by
  intro z hz
  obtain ⟨harc, hball⟩ := Plane.mem_cone_iff.1 hz
  -- The origin lies on no arc, so a point of a sector is never the apex.
  have h0 : (0 : Plane) ∉ Plane.arcCCW d w := by
    have := (Plane.notMem_arcCCW_smul d w (le_refl (0 : ℝ))).1
    rwa [zero_smul] at this
  have hne : z - x ≠ 0 := fun hzero => h0 (hzero ▸ harc)
  refine ⟨mem_ball.2 hball, fun hzS => ?_⟩
  rcases (h.2 z hball.le).1 hzS with hzx | hd
  · exact hne (by rw [hzx, sub_self])
  · exact hp.2.2.2 _ hd ((Plane.dir_mem_arcCCW_iff hne).2 harc)

/-- Each sector is connected — and in particular nonempty. -/
theorem IsLocalRadius.isConnected_cone (h : IsLocalRadius S x r) {d w : Plane}
    (hp : Plane.IsSectorPair (localDirs S x) d w) :
    IsConnected (Plane.cone x (Plane.arcCCW d w) r) :=
  Plane.isConnected_cone_arcCCW_of_ne x (isDirection_of_mem_localDirs hp.1)
    (isDirection_of_mem_localDirs hp.2.1) hp.2.2.1 h.pos

/-- Each sector is open. -/
theorem isOpen_cone_arcCCW (x d w : Plane) (r : ℝ) :
    IsOpen (Plane.cone x (Plane.arcCCW d w) r) :=
  Plane.isOpen_cone (Plane.isOpen_arcCCW d w)

/-- **A sector is star-shaped about the apex.** A straight segment from `x` towards a point of
a sector stays in that sector: this is the blueprint's "a short straight segment from `x` into
that sector is a polygonal access arc", with no shortening needed. -/
theorem openSegment_subset_cone_arcCCW {d w : Plane}
    (hz : z ∈ Plane.cone x (Plane.arcCCW d w) r) :
    openSegment ℝ x z ⊆ Plane.cone x (Plane.arcCCW d w) r := by
  obtain ⟨harc, hball⟩ := Plane.mem_cone_iff.1 hz
  intro v hv
  rw [openSegment_eq_image'] at hv
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hv
  have hsub : x + θ • (z - x) - x = θ • (z - x) := by module
  refine Plane.mem_cone_iff.2 ⟨?_, ?_⟩
  · rw [hsub]
    exact (Plane.smul_mem_arcCCW hθ0).2 harc
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hθ0, ← dist_eq_norm]
    nlinarith [dist_nonneg (x := z) (y := x)]

/-- **The punctured local disk is the union of the sectors between consecutive local
directions.** The last clause of `lem:local-skeleton-structure`. The hypothesis is that `x` has
at least two local branches; with fewer, `B(x,r) \ S` is connected and is not an arc sector
(see the module note). -/
theorem IsLocalRadius.ball_diff_eq_iUnion_cone (h : IsLocalRadius S x r)
    (hfin : (localDirs S x).Finite)
    (h2 : ∃ a ∈ localDirs S x, ∃ b ∈ localDirs S x, a ≠ b) :
    ball x r \ S =
      ⋃ p ∈ Plane.sectorPairs (localDirs S x), Plane.cone x (Plane.arcCCW p.1 p.2) r := by
  ext z
  constructor
  · rintro ⟨hzb, hzS⟩
    have hzx : z ≠ x := fun hh =>
      hzS ((h.2 z (by rw [hh, dist_self]; exact h.pos.le)).2 (Or.inl hh))
    have hne : z - x ≠ 0 := sub_ne_zero.2 hzx
    have hd : Plane.dir (z - x) ∉ localDirs S x := fun hd =>
      hzS ((h.2 z (mem_ball.1 hzb).le).2 (Or.inr hd))
    obtain ⟨d, w, hp, hmem⟩ := Plane.exists_isSectorPair hfin
      (fun _ hv => isDirection_of_mem_localDirs hv) h2 hne hd
    exact Set.mem_biUnion (show (d, w) ∈ Plane.sectorPairs _ from hp)
      (Plane.mem_cone_iff.2 ⟨hmem, mem_ball.1 hzb⟩)
  · intro hz
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.1 hz
    exact h.cone_subset_ball_diff hp hzp


/-- **The sectors are pairwise disjoint**, so the decomposition of the punctured disk is a
partition and not merely a cover. -/
theorem cone_disjoint_of_isSectorPair {d w d' w' : Plane}
    (hp : Plane.IsSectorPair (localDirs S x) d w)
    (hp' : Plane.IsSectorPair (localDirs S x) d' w') (hne : d ≠ d' ∨ w ≠ w') :
    Disjoint (Plane.cone x (Plane.arcCCW d w) r) (Plane.cone x (Plane.arcCCW d' w') r) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact Set.disjoint_left.1 (Plane.arcCCW_disjoint_of_isSectorPair
    (fun _ hv => isDirection_of_mem_localDirs hv) hp hp' hne)
    (Plane.mem_cone_iff.1 hz).1 (Plane.mem_cone_iff.1 hz').1


/-- **Each sector is a connected component of the punctured disk.** The sectors are open,
connected, pairwise disjoint and cover, so each is exactly the component of any of its points.
This is what makes "the sector `y` lies in" and "the component of `y`" the same set, and hence
`Graph.exists_access_region` and `Graph.exists_access_sector` two readings of one theorem. -/
theorem IsLocalRadius.connectedComponentIn_eq_cone (h : IsLocalRadius S x r)
    (hfin : (localDirs S x).Finite)
    (h2 : ∃ a ∈ localDirs S x, ∃ b ∈ localDirs S x, a ≠ b) {d w : Plane}
    (hp : Plane.IsSectorPair (localDirs S x) d w) (hz : z ∈ Plane.cone x (Plane.arcCCW d w) r) :
    connectedComponentIn (ball x r \ S) z = Plane.cone x (Plane.arcCCW d w) r := by
  classical
  set U := Plane.cone x (Plane.arcCCW d w) r with hU
  -- The union of all the *other* sectors.
  set V := ⋃ p ∈ Plane.sectorPairs (localDirs S x) \ {(d, w)},
    Plane.cone x (Plane.arcCCW p.1 p.2) r with hV
  have hVopen : IsOpen V := isOpen_biUnion fun p _ => isOpen_cone_arcCCW _ _ _ _
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro y hyU hyV
    obtain ⟨p, hp', hyp⟩ := Set.mem_iUnion₂.1 hyV
    have hne : d ≠ p.1 ∨ w ≠ p.2 := by
      by_contra hcon
      push Not at hcon
      exact hp'.2 (by simpa [Prod.ext_iff] using ⟨hcon.1.symm, hcon.2.symm⟩)
    exact Set.disjoint_left.1 (cone_disjoint_of_isSectorPair hp hp'.1 hne) hyU hyp
  have hcover : ball x r \ S ⊆ U ∪ V := by
    intro y hy
    obtain ⟨p, hp', hyp⟩ := Set.mem_iUnion₂.1 ((h.ball_diff_eq_iUnion_cone hfin h2) ▸ hy)
    rcases eq_or_ne p (d, w) with rfl | hpne
    · exact Or.inl hyp
    · exact Or.inr (Set.mem_biUnion ⟨hp', hpne⟩ hyp)
  refine subset_antisymm ?_ ?_
  · rcases (isPreconnected_connectedComponentIn (F := ball x r \ S) (x := z)).subset_or_subset
      (isOpen_cone_arcCCW _ _ _ _) hVopen hdisj
      ((connectedComponentIn_subset _ _).trans hcover) with hsub | hsub
    · exact hsub
    · exact absurd (hsub (mem_connectedComponentIn (h.cone_subset_ball_diff hp hz)))
        (Set.disjoint_left.1 hdisj hz)
  · exact (h.isConnected_cone hp).isPreconnected.subset_connectedComponentIn hz
      (h.cone_subset_ball_diff hp)


/-! ### Radial segments, two at a time

Two radial segments with distinct directions meet only at the centre, and the relative interior
of a radial segment stays strictly inside the disk and off the centre. These are the two facts
that turn the drawing axioms into the distinct-directions clause of
`lem:local-skeleton-structure`. -/

/-- A radius in a local direction lies in the set. -/
theorem IsLocalRadius.radial_subset (h : IsLocalRadius S x r) {d : Plane}
    (hd : d ∈ localDirs S x) : segment ℝ x (x + r • d) ⊆ S := by
  intro z hz
  obtain ⟨hdist, hcase⟩ := (mem_radial_iff (isDirection_of_mem_localDirs hd) h.pos).1 hz
  refine (h.2 z hdist).2 ?_
  rcases hcase with hzx | hdir
  · exact Or.inl hzx
  · exact Or.inr (hdir ▸ hd)

/-- **Two radial segments with distinct directions meet only at the centre.** -/
theorem radial_inter_radial {d₁ d₂ : Plane} (hd₁ : Plane.IsDirection d₁)
    (hd₂ : Plane.IsDirection d₂) (hne : d₁ ≠ d₂) (hr : 0 < r) :
    segment ℝ x (x + r • d₁) ∩ segment ℝ x (x + r • d₂) ⊆ {x} := by
  rintro z ⟨h₁, h₂⟩
  obtain ⟨-, hc₁⟩ := (mem_radial_iff hd₁ hr).1 h₁
  obtain ⟨-, hc₂⟩ := (mem_radial_iff hd₂ hr).1 h₂
  rcases hc₁ with hzx | hdir₁
  · exact hzx
  rcases hc₂ with hzx | hdir₂
  · exact hzx
  exact absurd (hdir₁ ▸ hdir₂) hne

/-- The relative interior of a radius avoids the centre and stays strictly inside the disk. -/
theorem mem_openSegment_radial {d : Plane} (hd : Plane.IsDirection d) (hr : 0 < r)
    (hz : z ∈ openSegment ℝ x (x + r • d)) : z ≠ x ∧ dist z x < r := by
  rw [openSegment_eq_image'] at hz
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
  have hsub : x + θ • (x + r • d - x) - x = (θ * r) • d := by module
  have hdist : dist (x + θ • (x + r • d - x)) x = θ * r := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hd.norm,
      mul_one]
  refine ⟨fun hh => ?_, by rw [hdist]; nlinarith⟩
  rw [← sub_eq_zero, hsub] at hh
  rcases smul_eq_zero.1 hh with h' | h'
  · nlinarith
  · exact hd.ne_zero h'


end Schoenflies

/-! ## Finite polygonal plane graphs

`Schoenflies/SkeletonLocal.lean` produces a local radius from the *point set* of the graph, and
never looks at the edges. The blueprint's proof does: it derives the pairwise distinctness of
the branch directions from the drawing axioms. That derivation is what follows, and it needs
one more thing from the radius than `IsLocalRadius` records — that the disk contains no vertex
other than `x` — because the drawing axioms only control edges away from the vertices. -/

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {x d : Plane} {r : ℝ}

/-- **A local disk of a plane graph at `x`**: a local radius for the point set whose closed disk
contains no vertex but possibly `x` itself.

The second clause is not a consequence of the first — a local radius may well contain other
vertices, sitting on the radial segments — and it is exactly what makes the relative interior of
each radial segment a set of *non-vertex* points, where `IsDrawing.unique_edge_at` applies. -/
structure IsLocalDisk (G : Graph Plane β) (drawing : β → ℝ → Plane) (x : Plane) (r : ℝ) :
    Prop where
  /-- The disk meets the point set exactly in the radial segments. -/
  isLocalRadius : IsLocalRadius (pointSet G drawing) x r
  /-- No vertex other than `x` is within `r` of `x`. -/
  vertex_eq : ∀ v ∈ V(G), dist v x ≤ r → v = x

theorem IsLocalDisk.pos (h : IsLocalDisk G drawing x r) : 0 < r := h.isLocalRadius.pos

theorem IsLocalDisk.mono (h : IsLocalDisk G drawing x r) {ε : ℝ} (hε : 0 < ε) (hle : ε ≤ r) :
    IsLocalDisk G drawing x ε :=
  ⟨h.isLocalRadius.mono hε hle, fun v hv hd => h.vertex_eq v hv (hd.trans hle)⟩

/-- **A local disk exists**, by shrinking a local radius below the distance to the other
vertices. -/
theorem IsDrawing.exists_isLocalDisk [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (hx : x ∈ pointSet G drawing) :
    ∃ r, IsLocalDisk G drawing x r := by
  obtain ⟨r₀, hr₀⟩ := h.exists_isLocalRadius hpoly hx
  have hfinV : (V(G) \ {x}).Finite := (Graph.finite_vertexSet G).sdiff
  have hdisj : Disjoint ({x} : Set Plane) (V(G) \ {x}) :=
    Set.disjoint_singleton_left.2 (fun hmem => hmem.2 rfl)
  obtain ⟨ρ, hρ, hsep⟩ :=
    Schoenflies.Plane.exists_dist_pos isCompact_singleton hfinV.isCompact hdisj
  refine ⟨min r₀ (ρ / 2), hr₀.mono (lt_min hr₀.pos (by linarith)) (min_le_left _ _),
    fun v hv hdv => ?_⟩
  by_contra hne
  have hmem : v ∈ V(G) \ {x} := ⟨hv, by simpa using hne⟩
  have := hsep x rfl v hmem
  rw [dist_comm] at this
  have h2 : dist v x ≤ ρ / 2 := hdv.trans (min_le_right _ _)
  linarith

/-! ### Each radial segment lies on exactly one edge

The relative interior of a radial segment is connected and meets no vertex, so
`IsDrawing.unique_edge_at` makes "the edge through this point" a locally constant function on
it; the edge arcs being closed and finitely many turns local constancy into global constancy. -/

/-- **Existence.** At a local disk radius, a radial segment lies inside a single edge arc. -/
theorem IsDrawing.exists_edge_radial [G.Finite] (h : IsDrawing G drawing)
    (hr : IsLocalDisk G drawing x r) (hd : d ∈ localDirs (pointSet G drawing) x) :
    ∃ e ∈ E(G), segment ℝ x (x + r • d) ⊆ edgeArc drawing e := by
  classical
  have hdir : Plane.IsDirection d := isDirection_of_mem_localDirs hd
  have hpos : 0 < r := hr.pos
  set O := openSegment ℝ x (x + r • d) with hO
  -- The relative interior of the radius lies in the point set and misses every vertex.
  have hOS : O ⊆ pointSet G drawing :=
    (openSegment_subset_segment ℝ _ _).trans (hr.isLocalRadius.radial_subset hd)
  have hOV : ∀ z ∈ O, z ∉ V(G) := by
    intro z hz hzV
    obtain ⟨hzx, hzr⟩ := mem_openSegment_radial hdir hpos hz
    exact hzx (hr.vertex_eq z hzV hzr.le)
  have hOedge : ∀ z ∈ O, ∃ e ∈ E(G), z ∈ edgeArc drawing e := by
    intro z hz
    rcases hOS hz with hzV | hzE
    · exact absurd hzV (hOV z hz)
    · simpa only [mem_iUnion, exists_prop] using hzE
  -- A point to start from, and the edge through it.
  have hmid : x + (1 / 2 : ℝ) • (x + r • d - x) ∈ O := by
    rw [hO, openSegment_eq_image']
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  obtain ⟨e₀, he₀, hp₀⟩ := hOedge _ hmid
  refine ⟨e₀, he₀, ?_⟩
  -- The interior is covered by the arc of `e₀` and by the union of all the other arcs, two
  -- closed sets that cannot both meet it.
  have hrest : IsClosed (⋃ e ∈ E(G) \ {e₀}, edgeArc drawing e) :=
    ((Graph.finite_edgeSet G).sdiff (t := {e₀})).isClosed_biUnion
      fun e he => (h.isCompact_edgeArc he.1).isClosed
  have hcover : O ⊆ edgeArc drawing e₀ ∪ ⋃ e ∈ E(G) \ {e₀}, edgeArc drawing e := by
    intro z hz
    obtain ⟨e, he, hze⟩ := hOedge z hz
    rcases eq_or_ne e e₀ with rfl | hee
    · exact Or.inl hze
    · exact Or.inr (mem_biUnion ⟨he, by simpa using hee⟩ hze)
  have hOsub : O ⊆ edgeArc drawing e₀ := by
    by_contra hcon
    obtain ⟨z, hz, hzn⟩ := Set.not_subset.1 hcon
    have hz2 : z ∈ ⋃ e ∈ E(G) \ {e₀}, edgeArc drawing e := (hcover hz).resolve_left hzn
    obtain ⟨p, hpO, hp1, hp2⟩ :=
      isPreconnected_closed_iff.1 (convex_openSegment (𝕜 := ℝ) x (x + r • d)).isPreconnected
        (edgeArc drawing e₀) (⋃ e ∈ E(G) \ {e₀}, edgeArc drawing e)
        (h.isCompact_edgeArc he₀).isClosed hrest hcover ⟨_, hmid, hp₀⟩ ⟨z, hz, hz2⟩
    obtain ⟨e, he, hpe⟩ := mem_iUnion₂.1 hp2
    exact hOV p hpO (h.arcs_meet_at_vertex he₀ he.1 (Ne.symm (by simpa using he.2)) hp1 hpe)
  -- The arc is closed, so it also carries the two endpoints.
  exact (segment_subset_closure_openSegment).trans
    (closure_minimal hOsub (h.isCompact_edgeArc he₀).isClosed)

/-- **Uniqueness.** Two edges carrying the same radial segment are the same edge: the relative
interior of the segment is off the vertex set, and there a point lies on only one edge. -/
theorem IsDrawing.edge_radial_unique (h : IsDrawing G drawing)
    (hr : IsLocalDisk G drawing x r) (hdir : Plane.IsDirection d) {e f : β}
    (he : e ∈ E(G)) (hf : f ∈ E(G)) (hse : segment ℝ x (x + r • d) ⊆ edgeArc drawing e)
    (hsf : segment ℝ x (x + r • d) ⊆ edgeArc drawing f) : e = f := by
  set p := x + (1 / 2 : ℝ) • (x + r • d - x) with hp
  have hmid : p ∈ openSegment ℝ x (x + r • d) := by
    rw [hp, openSegment_eq_image']
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  obtain ⟨hpx, hpr⟩ := mem_openSegment_radial hdir hr.pos hmid
  have hpV : p ∉ V(G) := fun hV => hpx (hr.vertex_eq p hV hpr.le)
  exact h.unique_edge_at he hf hpV (hse (openSegment_subset_segment ℝ _ _ hmid))
    (hsf (openSegment_subset_segment ℝ _ _ hmid))

/-! ### An edge carries at most two local branches

The parametrization of an edge is a continuous injection of a compact interval, hence a closed
map, so the preimage of a connected subset of its arc is connected
(`IsPreconnected.preimage_of_isClosedMap`). Three radial segments inside one edge arc therefore
pull back to three intervals of parameters, each containing the parameter of `x` and a point
other than it, and meeting pairwise in nothing else. Two of the three lie on the same side of
the parameter of `x`, and then the smaller of the two extra points belongs to both intervals. -/

/-- Two intervals through `t₀` reaching out on the same side must overlap beyond `t₀`. -/
private theorem two_same_side {J J' : Set ℝ} {t₀ a b : ℝ} (hc : IsPreconnected J)
    (hc' : IsPreconnected J') (h₀ : t₀ ∈ J) (h₀' : t₀ ∈ J') (ha : a ∈ J) (hb : b ∈ J')
    (hane : a ≠ t₀) (hbne : b ≠ t₀) (hi : J ∩ J' ⊆ {t₀})
    (hside : (t₀ < a ∧ t₀ < b) ∨ (a < t₀ ∧ b < t₀)) : False := by
  rcases hside with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · rcases le_total a b with hab | hab
    · exact hane (hi ⟨ha, hc'.Icc_subset h₀' hb ⟨hA.le, hab⟩⟩)
    · exact hbne (hi ⟨hc.Icc_subset h₀ ha ⟨hB.le, hab⟩, hb⟩)
  · rcases le_total a b with hab | hab
    · exact hbne (hi ⟨hc.Icc_subset ha h₀ ⟨hab, hB.le⟩, hb⟩)
    · exact hane (hi ⟨ha, hc'.Icc_subset hb h₀' ⟨hab, hA.le⟩⟩)

/-- Three such intervals are impossible: two of them reach out on the same side. -/
private theorem three_intervals {J₁ J₂ J₃ : Set ℝ} {t₀ t₁ t₂ t₃ : ℝ}
    (hc₁ : IsPreconnected J₁) (hc₂ : IsPreconnected J₂) (hc₃ : IsPreconnected J₃)
    (h₀₁ : t₀ ∈ J₁) (h₀₂ : t₀ ∈ J₂) (h₀₃ : t₀ ∈ J₃)
    (h₁ : t₁ ∈ J₁) (h₂ : t₂ ∈ J₂) (h₃ : t₃ ∈ J₃)
    (n₁ : t₁ ≠ t₀) (n₂ : t₂ ≠ t₀) (n₃ : t₃ ≠ t₀)
    (i₁₂ : J₁ ∩ J₂ ⊆ {t₀}) (i₁₃ : J₁ ∩ J₃ ⊆ {t₀}) (i₂₃ : J₂ ∩ J₃ ⊆ {t₀}) : False := by
  rcases lt_or_gt_of_ne n₁ with s₁ | s₁ <;> rcases lt_or_gt_of_ne n₂ with s₂ | s₂ <;>
    rcases lt_or_gt_of_ne n₃ with s₃ | s₃ <;>
  first
    | exact two_same_side hc₁ hc₂ h₀₁ h₀₂ h₁ h₂ n₁ n₂ i₁₂ (by tauto)
    | exact two_same_side hc₁ hc₃ h₀₁ h₀₃ h₁ h₃ n₁ n₃ i₁₃ (by tauto)
    | exact two_same_side hc₂ hc₃ h₀₂ h₀₃ h₂ h₃ n₂ n₃ i₂₃ (by tauto)

/-- **An edge carries at most two local branches at `x`** — the blueprint's "two of these radial
segments with a common direction would have overlapping relative interiors, which is
impossible", in the shape it is actually used: three distinct directions cannot all be carried
by one edge. Together with `IsDrawing.exists_edge_radial` and `IsDrawing.edge_radial_unique`
this says that the local directions at `x` are in bijection with the local branches, so the
radial segments of `lem:local-skeleton-structure` really do have pairwise distinct
directions. -/
theorem IsDrawing.not_three_localDirs_on_edge (h : IsDrawing G drawing)
    (hr : IsLocalDisk G drawing x r) {e : β} (he : e ∈ E(G)) {d₁ d₂ d₃ : Plane}
    (hd₁ : Plane.IsDirection d₁) (hd₂ : Plane.IsDirection d₂) (hd₃ : Plane.IsDirection d₃)
    (h₁₂ : d₁ ≠ d₂) (h₁₃ : d₁ ≠ d₃) (h₂₃ : d₂ ≠ d₃)
    (hs₁ : segment ℝ x (x + r • d₁) ⊆ edgeArc drawing e)
    (hs₂ : segment ℝ x (x + r • d₂) ⊆ edgeArc drawing e)
    (hs₃ : segment ℝ x (x + r • d₃) ⊆ edgeArc drawing e) : False := by
  obtain ⟨hcont, hinj, -⟩ := h.edge_param he
  let _ : CompactSpace ↥(I : Set ℝ) := isCompact_iff_compactSpace.1 isCompact_I
  set φ : ↥(I : Set ℝ) → Plane := Set.domRestrict I (drawing e) with hφdef
  have hφi : Function.Injective φ := Set.injOn_iff_injective.1 hinj
  have hcm : IsClosedMap φ := (hcont.domRestrict).isClosedMap
  have hrange : Set.range φ = edgeArc drawing e := Set.range_domRestrict _ _
  -- The preimage of a radial segment is a connected set of parameters.
  have hpre : ∀ dd : Plane, segment ℝ x (x + r • dd) ⊆ edgeArc drawing e →
      IsPreconnected (Subtype.val '' (φ ⁻¹' segment ℝ x (x + r • dd))) := by
    intro dd hsub
    refine IsPreconnected.image ?_ _ continuous_subtype_val.continuousOn
    exact ((convex_segment x (x + r • dd)).isPreconnected).preimage_of_isClosedMap hφi hcm
      (by rw [hrange]; exact hsub)
  -- The parameter of `x`, and one parameter on each of the three branches.
  have hxr : x ∈ Set.range φ := by rw [hrange]; exact hs₁ (left_mem_segment ℝ _ _)
  obtain ⟨τ₀, hτ₀⟩ := hxr
  have hend : ∀ dd : Plane, Plane.IsDirection dd →
      segment ℝ x (x + r • dd) ⊆ edgeArc drawing e →
      ∃ τ : ↥(I : Set ℝ), φ τ = x + r • dd ∧ (τ : ℝ) ≠ (τ₀ : ℝ) := by
    intro dd hdd hsub
    have hmem : x + r • dd ∈ Set.range φ := by rw [hrange]; exact hsub (right_mem_segment ℝ _ _)
    obtain ⟨τ, hτ⟩ := hmem
    refine ⟨τ, hτ, fun hval => ?_⟩
    have : τ = τ₀ := Subtype.ext hval
    rw [this, hτ₀] at hτ
    have hz : r • dd = 0 := by
      have := sub_eq_zero.2 hτ.symm
      rwa [show x + r • dd - x = r • dd by module] at this
    rcases smul_eq_zero.1 hz with h' | h'
    · exact absurd h' hr.pos.ne'
    · exact hdd.ne_zero h'
  obtain ⟨τ₁, hτ₁, n₁⟩ := hend d₁ hd₁ hs₁
  obtain ⟨τ₂, hτ₂, n₂⟩ := hend d₂ hd₂ hs₂
  obtain ⟨τ₃, hτ₃, n₃⟩ := hend d₃ hd₃ hs₃
  -- Two branches share only the parameter of `x`.
  have hinter : ∀ dd dd' : Plane, Plane.IsDirection dd → Plane.IsDirection dd' → dd ≠ dd' →
      (Subtype.val '' (φ ⁻¹' segment ℝ x (x + r • dd))) ∩
        (Subtype.val '' (φ ⁻¹' segment ℝ x (x + r • dd'))) ⊆ {(τ₀ : ℝ)} := by
    rintro dd dd' hdd hdd' hne s ⟨⟨τ, hτ, rfl⟩, ⟨τ', hτ', hval⟩⟩
    have hττ : τ' = τ := Subtype.ext hval
    subst hττ
    have hx : φ τ' = x :=
      Set.mem_singleton_iff.1 (radial_inter_radial hdd hdd' hne hr.pos ⟨hτ, hτ'⟩)
    have hτ₀' : τ' = τ₀ := hφi (by rw [hx, hτ₀])
    exact Set.mem_singleton_iff.2 (by rw [hτ₀'])
  refine three_intervals (hpre d₁ hs₁) (hpre d₂ hs₂) (hpre d₃ hs₃)
    ⟨τ₀, by simpa [hτ₀] using left_mem_segment ℝ x (x + r • d₁), rfl⟩
    ⟨τ₀, by simpa [hτ₀] using left_mem_segment ℝ x (x + r • d₂), rfl⟩
    ⟨τ₀, by simpa [hτ₀] using left_mem_segment ℝ x (x + r • d₃), rfl⟩
    ⟨τ₁, by simpa [hτ₁] using right_mem_segment ℝ x (x + r • d₁), rfl⟩
    ⟨τ₂, by simpa [hτ₂] using right_mem_segment ℝ x (x + r • d₂), rfl⟩
    ⟨τ₃, by simpa [hτ₃] using right_mem_segment ℝ x (x + r • d₃), rfl⟩
    n₁ n₂ n₃ (hinter d₁ d₂ hd₁ hd₂ h₁₂) (hinter d₁ d₃ hd₁ hd₃ h₁₃) (hinter d₂ d₃ hd₂ hd₃ h₂₃)

/-- **The local directions are the local branches, counted.** Each local direction is carried by
exactly one edge and each edge carries at most two of them, so there are at most twice as many
local directions as edges. This is the quantitative packaging of the blueprint's
"finitely many straight segments from `x` with pairwise distinct directions": the count is a
count of *branches*, not of an unrelated set of rays. -/
theorem IsDrawing.localDirs_ncard_le [G.Finite] (h : IsDrawing G drawing)
    (hr : IsLocalDisk G drawing x r) (hfin : (localDirs (pointSet G drawing) x).Finite) :
    (localDirs (pointSet G drawing) x).ncard ≤ 2 * E(G).ncard := by
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · -- With no edges at all there is no local direction either.
    have hempty : localDirs (pointSet G drawing) x = ∅ := by
      ext d
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hd
      obtain ⟨e, -, -⟩ := h.exists_edge_radial hr hd
      exact hβ.false e
    simp [hempty]
  have hex : ∀ d : Plane, ∃ e, d ∈ localDirs (pointSet G drawing) x →
      e ∈ E(G) ∧ segment ℝ x (x + r • d) ⊆ edgeArc drawing e := by
    intro d
    by_cases hd : d ∈ localDirs (pointSet G drawing) x
    · obtain ⟨e, he, hs⟩ := h.exists_edge_radial hr hd
      exact ⟨e, fun _ => ⟨he, hs⟩⟩
    · exact ⟨Classical.arbitrary β, fun hc => absurd hc hd⟩
  choose f hf using hex
  have hmaps : ∀ d ∈ hfin.toFinset, f d ∈ G.edgeFinset := fun d hd =>
    Graph.mem_edgeFinset.2 (hf d (hfin.mem_toFinset.1 hd)).1
  have hfib : ∀ e ∈ G.edgeFinset,
      (Finset.filter (fun d => f d = e) hfin.toFinset).card ≤ 2 := by
    intro e he
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hcon
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at ha hb hc
    exact h.not_three_localDirs_on_edge hr (Graph.mem_edgeFinset.1 he)
      (isDirection_of_mem_localDirs ha.1) (isDirection_of_mem_localDirs hb.1)
      (isDirection_of_mem_localDirs hc.1) hab hac hbc
      (ha.2 ▸ (hf a ha.1).2) (hb.2 ▸ (hf b hb.1).2) (hc.2 ▸ (hf c hc.1).2)
  have hcard := Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib
  have hE : E(G).ncard = (G.edgeFinset).card :=
    Set.ncard_eq_toFinset_card _ (Graph.finite_edgeSet G)
  have hD : (localDirs (pointSet G drawing) x).ncard = (hfin.toFinset).card :=
    Set.ncard_eq_toFinset_card _ hfin
  rw [hD, hE]
  exact hcard

/-! ### The access sector

`lem:polygonal-side-accessibility` needs four things at once: the finitely many sectors, that
each is connected and misses the skeleton, one that meets the prescribed face, and a short
straight segment from `x` into it. `IsDrawing.exists_access_sector` delivers all four about a
single named sector, so that the consumer never has to compose three lemmas. -/

/-- **The access sector** (`lem:polygonal-side-accessibility`, the local step). A point `y` of
the exterior inside a local disk about `x` lies in one of the sectors between consecutive local
directions, and that sector is open, connected, nonempty, disjoint from the graph, contained in
`y`'s own face, and reached from `x` by the straight segment `(x, y)`. -/
theorem exists_access_sector {y : Plane}
    (hr : IsLocalRadius (pointSet G drawing) x r)
    (hfin : (localDirs (pointSet G drawing) x).Finite)
    (h2 : ∃ a ∈ localDirs (pointSet G drawing) x,
      ∃ b ∈ localDirs (pointSet G drawing) x, a ≠ b)
    (hy : y ∈ ball x r) (hyE : y ∈ exterior G drawing) :
    ∃ d w, Plane.IsSectorPair (localDirs (pointSet G drawing) x) d w ∧
      y ∈ Plane.cone x (Plane.arcCCW d w) r ∧
      IsOpen (Plane.cone x (Plane.arcCCW d w) r) ∧
      IsConnected (Plane.cone x (Plane.arcCCW d w) r) ∧
      Plane.cone x (Plane.arcCCW d w) r ⊆ ball x r \ pointSet G drawing ∧
      Plane.cone x (Plane.arcCCW d w) r ⊆ face G drawing y ∧
      openSegment ℝ x y ⊆ Plane.cone x (Plane.arcCCW d w) r := by
  have hyS : y ∉ pointSet G drawing := hyE
  have hyx : y ≠ x := fun hh =>
    hyS ((hr.2 y (by rw [hh, dist_self]; exact hr.pos.le)).2 (Or.inl hh))
  have hne : y - x ≠ 0 := sub_ne_zero.2 hyx
  have hdy : Plane.dir (y - x) ∉ localDirs (pointSet G drawing) x := fun hd =>
    hyS ((hr.2 y (mem_ball.1 hy).le).2 (Or.inr hd))
  obtain ⟨d, w, hp, hmem⟩ := Plane.exists_isSectorPair hfin
    (fun _ hv => isDirection_of_mem_localDirs hv) h2 hne hdy
  have hycone : y ∈ Plane.cone x (Plane.arcCCW d w) r :=
    Plane.mem_cone_iff.2 ⟨hmem, mem_ball.1 hy⟩
  have hsub : Plane.cone x (Plane.arcCCW d w) r ⊆ ball x r \ pointSet G drawing :=
    hr.cone_subset_ball_diff hp
  refine ⟨d, w, hp, hycone, isOpen_cone_arcCCW _ _ _ _, hr.isConnected_cone hp, hsub, ?_,
    openSegment_subset_cone_arcCCW hycone⟩
  -- A connected subset of the exterior through `y` lies in `y`'s face.
  exact (hr.isConnected_cone hp).isPreconnected.subset_connectedComponentIn hycone
    (fun z hz => (hsub hz).2)

/-- **The access region, with no hypothesis on the number of branches.** The connected component
of `y` in the punctured disk has every property `lem:polygonal-side-accessibility` asks of the
sector: it is open, connected, misses the graph, lies in `y`'s face, and contains the straight
segment from `x` to `y`. When `x` has at least two local branches it *is* a sector, by
`Graph.exists_access_sector`; with fewer it is the whole punctured disk, which is not an arc
sector, and this is the form to use. -/
theorem IsDrawing.exists_access_region [G.Finite] (h : IsDrawing G drawing) {y : Plane}
    (hr : IsLocalRadius (pointSet G drawing) x r) (hy : y ∈ ball x r)
    (hyE : y ∈ exterior G drawing) :
    ∃ N : Set Plane, y ∈ N ∧ IsOpen N ∧ IsConnected N ∧
      N ⊆ ball x r \ pointSet G drawing ∧ N ⊆ face G drawing y ∧ openSegment ℝ x y ⊆ N := by
  have hyS : y ∉ pointSet G drawing := hyE
  have hyd : y ∈ ball x r \ pointSet G drawing := ⟨hy, hyS⟩
  have hopen : IsOpen (ball x r \ pointSet G drawing) := isOpen_ball.sdiff h.isClosed_pointSet
  refine ⟨connectedComponentIn (ball x r \ pointSet G drawing) y, mem_connectedComponentIn hyd,
    Schoenflies.Plane.isOpen_connectedComponentIn hopen,
    ⟨⟨y, mem_connectedComponentIn hyd⟩, isPreconnected_connectedComponentIn⟩,
    connectedComponentIn_subset _ _, ?_, ?_⟩
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hyd) fun z hz => (connectedComponentIn_subset _ _ hz).2
  · -- The half-open segment `(x, y]` is connected, misses the graph and contains `y`.
    have hTsub : AffineMap.lineMap x y '' Ioc (0 : ℝ) 1 ⊆ ball x r \ pointSet G drawing := by
      rintro w ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
      rcases eq_or_lt_of_le hθ1 with rfl | hlt
      · rwa [AffineMap.lineMap_apply_one]
      · exact hr.openSegment_subset_ball_diff hy hyS
          (by rw [openSegment_eq_image_lineMap]; exact ⟨θ, ⟨hθ0, hlt⟩, rfl⟩)
    have hconn : IsPreconnected (AffineMap.lineMap x y '' Ioc (0 : ℝ) 1) :=
      ((convex_Ioc (0 : ℝ) 1).affine_image (AffineMap.lineMap x y)).isPreconnected
    have hyT : y ∈ AffineMap.lineMap x y '' Ioc (0 : ℝ) 1 :=
      ⟨1, ⟨zero_lt_one, le_refl 1⟩, AffineMap.lineMap_apply_one x y⟩
    refine subset_trans ?_ (hconn.subset_connectedComponentIn hyT hTsub)
    rw [openSegment_eq_image_lineMap]
    exact Set.image_mono Ioo_subset_Ioc_self

end Graph
