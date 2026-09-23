/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Subarc
public import LeanPool.Schoenflies.Topology
public import LeanPool.Schoenflies.Polygonal
public import LeanPool.Schoenflies.Strip

/-!
# A crosscut cuts a region into at most two pieces

Lemma "At most two sides": if `D` is a region and `P` is a simple polygonal arc whose endpoints
lie *outside* `D` and whose remaining points lie in `D`, then `D ∖ P` has at most two
components. This is the missing half of the crosscut theorem — the crosscut-cells lemma
(`Schoenflies.crosscut_cells`) already exhibits two components, and this says there are no
others.

## "At most two" as a covering statement

Nothing here talks about the *set* of components. What is proved, and what the crosscut theorem
consumes, is the constructive form: two points `z_L, z_R` of `D ∖ P` such that every point of
`D ∖ P` lies in the component of one of them (`crosscut_at_most_two`). Handed two components
that are known to be distinct — which is exactly what the crosscut-cells lemma supplies — that
turns into "every point lies in one of *those* two" (`crosscut_components_exhaust`), which is
the sentence the crosscut theorem actually needs.

## The proof is a clopen argument, not the blueprint's path argument

The blueprint traces a polygonal arc `γ` from an arbitrary `x ∈ D ∖ P` to a reference point
`z₀ ∈ P`, takes the first point `z` of `γ` on `P`, and pushes `x` into a track of a strip around
the subarc of `P` from `z` to `z₀`. The first-hitting-point step is only there to *find* a point
of `D ∖ P` next to `P`; once one knows that a whole neighbourhood of every point of `P ∩ D` is
covered by the two components, the statement is a connectedness argument and no path is needed:

* `T`, the set of points of `D ∖ P` in neither of the two components, is open, because a
  component of an open subset of the plane is open and two components are equal or disjoint
  (`isOpen_notMem_two_components`);
* `U`, the union of the two components with every open piece of `D` whose complement of `P` is
  covered, is open and contains all of `P ∩ D`;
* `U` and `T` are disjoint, cover `D`, and `U` meets `D`; so `T = ∅` because `D` is connected.

That is `covered_by_two_of_local`, and it is where "at most two" really comes from. The arc, the
polygonality and the endpoint hypotheses enter only through the collar.

## The collar is a hypothesis: `Schoenflies/Strip.lean` is stated for a closed curve

The local input the argument needs is blueprint Lemma 1.8 (b) — a two-sided collar of a compact
subarc of `P ∖ ∂P`. `Schoenflies/Strip.lean`, `Schoenflies/StripLocal.lean` and
`Schoenflies/Compose.lean` build the collar of a `ClosedPolygon`, a *closed* curve, and the note
at the end of `StripLocal.lean` says in as many words that the arc case "is not formalised".
There is no way to get it from the closed case: the two tracks of a closed collar are connected
because they run all the way round the curve, and intersecting them with `D` destroys exactly
that.

So `HasArcCollars D P` is an explicit hypothesis of every theorem below. It is blueprint
Lemma 1.8 (b) with the prescribed open set taken to be `D`, together with the "local sides"
clause of that lemma in the form `StripLocal.lean` already proves in the closed case
(`StripData.carrier_subset_closure_sideL`): every point of the subarc is in the closure of both
tracks. `ArcCollar` is the bundled datum, so a discharger returns a construction rather than an
existential.

## Blueprint

* `Schoenflies.ArcCollar`, `Schoenflies.HasArcCollars` — Lemma 1.8 (b) (two-sided polygonal
  strips, the arc case) as an interface: the collar of one compact subarc as data, and the
  hypothesis that every compact subarc has one.
* `Schoenflies.isOpen_notMem_two_components`, `Schoenflies.covered_by_two_of_local` — the clopen
  step, which is the whole of the lemma once the collar is available.
* `Schoenflies.crosscut_at_most_two` — Lemma "At most two sides".
* `Schoenflies.crosscut_components_exhaust` — the same, applied to two components already known
  to be distinct; this is the form Theorem "Crosscut theorem" cites.
* `Schoenflies.Plane.mem_segment_iff_coord`, `Schoenflies.hasArcCollars_segment` — Lemma 1.8 (b)
  for a straight crosscut, which is the blueprint's edge block and nothing else. With it,
  `Schoenflies.segment_crosscut_at_most_two` is Lemma "At most two sides" for a straight
  crosscut with no hypothesis left standing, and certifies that `HasArcCollars` is satisfiable.
-/

@[expose] public section

open Metric Set unitInterval

namespace Schoenflies

variable {D P K K' : Set Plane}

/-! ### The collar of a compact subarc, as data

Blueprint Lemma 1.8 (b). `nbhd` is the neighbourhood `N`, `left` and `right` are the two tracks
`N_L, N_R`. The prescribed open set of the blueprint is `D`, which is all this development ever
prescribes.

Two clauses of the blueprint are dropped because nothing here uses them: that the tracks are
open and that they are disjoint. Two are kept and are essential: that each track is *connected*
— that is the whole point of a collar, and it is what ties the local picture at one point of the
arc to the local picture at another — and that every point of the subarc is in the closure of
both tracks, which is the blueprint's "the two sets `N_L, N_R` are the two local sides of the
curve" in the form `StripLocal.lean` proves it for a closed polygon. -/

/-- A **two-sided collar** of the compact subarc `K` of `P`, inside the region `D`: an open
neighbourhood `nbhd` of `K` contained in `D`, whose complement of `P` splits into two connected
tracks, each of which approaches every point of `K`.

Note that the splitting clause is stated for `nbhd ∖ P` and not for `nbhd ∖ K`: an open
neighbourhood of `K` necessarily contains points of `P` beyond the ends of `K`, and it is the
*whole* of `P` that has to be removed for the tracks to lie in `D ∖ P`. That is how the
blueprint states it too. -/
structure ArcCollar (D P K : Set Plane) where
  /-- the neighbourhood `N` of the subarc -/
  nbhd : Set Plane
  /-- the left track `N_L` -/
  left : Set Plane
  /-- the right track `N_R` -/
  right : Set Plane
  isOpen_nbhd : IsOpen nbhd
  subset_nbhd : K ⊆ nbhd
  nbhd_subset : nbhd ⊆ D
  nbhd_diff : nbhd \ P = left ∪ right
  isConnected_left : IsConnected left
  isConnected_right : IsConnected right
  subset_closure_left : K ⊆ closure left
  subset_closure_right : K ⊆ closure right

/-- **Blueprint Lemma 1.8 (b) as a hypothesis.** Every nondegenerate compact connected piece of
`P` lying inside `D` has a two-sided collar inside `D`.

A compact connected subset of an arc is a compact subarc, so this is the blueprint's "if `P` is
an arc and `K` is a compact subarc of `P ∖ ∂P`" — the condition `K ⊆ D ∩ P` is what "`K` avoids
the endpoints" amounts to here, since the endpoints of a crosscut are outside `D`.

Nondegeneracy is asked for because the blueprint's proof builds the collar out of edge blocks
and vertex disks along `K`, which needs `K` to contain an edge; a consumer that has a genuine
subarc always has it. -/
def HasArcCollars (D P : Set Plane) : Prop :=
  ∀ K : Set Plane, K ⊆ D ∩ P → IsCompact K → IsPreconnected K → K.Nontrivial →
    Nonempty (ArcCollar D P K)

namespace ArcCollar

theorem left_subset_nbhd_diff (C : ArcCollar D P K) : C.left ⊆ C.nbhd \ P := by
  rw [C.nbhd_diff]; exact subset_union_left

theorem right_subset_nbhd_diff (C : ArcCollar D P K) : C.right ⊆ C.nbhd \ P := by
  rw [C.nbhd_diff]; exact subset_union_right

theorem nbhd_diff_subset_diff (C : ArcCollar D P K) : C.nbhd \ P ⊆ D \ P :=
  fun _ hy => ⟨C.nbhd_subset hy.1, hy.2⟩

theorem left_subset_diff (C : ArcCollar D P K) : C.left ⊆ D \ P :=
  C.left_subset_nbhd_diff.trans C.nbhd_diff_subset_diff

theorem right_subset_diff (C : ArcCollar D P K) : C.right ⊆ D \ P :=
  C.right_subset_nbhd_diff.trans C.nbhd_diff_subset_diff

/-- The reference point on the left of the arc. Exported as a function of the collar rather
than produced by an existential, so that a consumer holding a collar holds the point. -/
noncomputable def ptL (C : ArcCollar D P K) : Plane := C.isConnected_left.nonempty.some

/-- The reference point on the right of the arc. -/
noncomputable def ptR (C : ArcCollar D P K) : Plane := C.isConnected_right.nonempty.some

theorem ptL_mem (C : ArcCollar D P K) : C.ptL ∈ C.left := C.isConnected_left.nonempty.some_mem

theorem ptR_mem (C : ArcCollar D P K) : C.ptR ∈ C.right := C.isConnected_right.nonempty.some_mem

theorem ptL_mem_diff (C : ArcCollar D P K) : C.ptL ∈ D \ P := C.left_subset_diff C.ptL_mem

theorem ptR_mem_diff (C : ArcCollar D P K) : C.ptR ∈ D \ P := C.right_subset_diff C.ptR_mem

/-- A connected piece of `D ∖ P` that meets the neighbourhood of a collar lies in one of the
two components that collar's reference points name.

The piece meets `nbhd` in a point off `P`, which is therefore in one of the two tracks; the
piece and that track together are connected inside `D ∖ P` and contain the corresponding
reference point. -/
theorem meeting_subset_components (C₀ : ArcCollar D P K') {S : Set Plane}
    (hS : IsPreconnected S) (hSsub : S ⊆ D \ P) (hmeet : (C₀.nbhd ∩ S).Nonempty) :
    S ⊆ connectedComponentIn (D \ P) C₀.ptL ∪ connectedComponentIn (D \ P) C₀.ptR := by
  obtain ⟨y, hy₀, hyS⟩ := hmeet
  have hy : y ∈ C₀.left ∪ C₀.right := by
    rw [← C₀.nbhd_diff]; exact ⟨hy₀, (hSsub hyS).2⟩
  rcases hy with hy | hy
  · refine subset_union_of_subset_left ?_ _
    have hconn : IsPreconnected (S ∪ C₀.left) :=
      IsPreconnected.union y hyS hy hS C₀.isConnected_left.2
    have hsub : S ∪ C₀.left ⊆ D \ P := union_subset hSsub C₀.left_subset_diff
    exact fun _ hz =>
      hconn.subset_connectedComponentIn (Or.inr C₀.ptL_mem) hsub (Or.inl hz)
  · refine subset_union_of_subset_right ?_ _
    have hconn : IsPreconnected (S ∪ C₀.right) :=
      IsPreconnected.union y hyS hy hS C₀.isConnected_right.2
    have hsub : S ∪ C₀.right ⊆ D \ P := union_subset hSsub C₀.right_subset_diff
    exact fun _ hz =>
      hconn.subset_connectedComponentIn (Or.inr C₀.ptR_mem) hsub (Or.inl hz)

/-- **The whole of a second collar is covered by the two components named by the first**, as
soon as the two subarcs share a point.

Both tracks of `C` approach the shared point `z`, and `C₀.nbhd` is an open neighbourhood of it,
so each track of `C` meets `C₀.nbhd`; `meeting_subset_components` then places each of them in
one of the two components. This is the blueprint's "one track meets `B_L` and the other meets
`B_R`", with the two half-disks replaced by the fixed collar. -/
theorem nbhd_diff_subset_components (C₀ : ArcCollar D P K') (C : ArcCollar D P K)
    {z : Plane} (hz' : z ∈ K') (hz : z ∈ K) :
    C.nbhd \ P ⊆ connectedComponentIn (D \ P) C₀.ptL ∪ connectedComponentIn (D \ P) C₀.ptR := by
  have hmeetL : (C₀.nbhd ∩ C.left).Nonempty :=
    mem_closure_iff.1 (C.subset_closure_left hz) C₀.nbhd C₀.isOpen_nbhd (C₀.subset_nbhd hz')
  have hmeetR : (C₀.nbhd ∩ C.right).Nonempty :=
    mem_closure_iff.1 (C.subset_closure_right hz) C₀.nbhd C₀.isOpen_nbhd (C₀.subset_nbhd hz')
  rw [C.nbhd_diff]
  exact union_subset
    (C₀.meeting_subset_components C.isConnected_left.2 C.left_subset_diff hmeetL)
    (C₀.meeting_subset_components C.isConnected_right.2 C.right_subset_diff hmeetR)

end ArcCollar

/-! ### The clopen step -/

/-- The points of an open set that are in neither of two prescribed components form an open
set: each such point drags its whole component with it, and a component of an open subset of
the plane is open. -/
theorem isOpen_notMem_two_components {S : Set Plane} (hS : IsOpen S) (zL zR : Plane) :
    IsOpen {y | y ∈ S ∧ y ∉ connectedComponentIn S zL ∧ y ∉ connectedComponentIn S zR} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨hyS, hyL, hyR⟩
  refine ⟨connectedComponentIn S y, ?_, Plane.isOpen_connectedComponentIn hS,
    mem_connectedComponentIn hyS⟩
  intro w hw
  -- Two components are equal or disjoint: if `w` were in one of the two named components, that
  -- component would *be* the component of `y`, and `y` would be in it.
  have hcw : connectedComponentIn S y = connectedComponentIn S w := connectedComponentIn_eq hw
  refine ⟨connectedComponentIn_subset S y hw, fun hwL => hyL ?_, fun hwR => hyR ?_⟩
  · rw [show connectedComponentIn S zL = connectedComponentIn S y from
      (connectedComponentIn_eq hwL).trans hcw.symm]
    exact mem_connectedComponentIn hyS
  · rw [show connectedComponentIn S zR = connectedComponentIn S y from
      (connectedComponentIn_eq hwR).trans hcw.symm]
    exact mem_connectedComponentIn hyS

/-- **The clopen step, and the whole of "at most two sides" once a collar is available.** If
every point of `P` inside the region `D` has a neighbourhood inside `D` whose complement of `P`
is covered by the components of two fixed points `z_L, z_R`, then all of `D ∖ P` is covered by
those two components.

The set `T` of points of `D ∖ P` in neither component is open; the union `U` of the two
components with all the good neighbourhoods is open, contains `P ∩ D` and meets `D`; the two
are disjoint and cover `D`. Connectedness of `D` kills `T`. -/
theorem covered_by_two_of_local (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hPclosed : IsClosed P) {zL zR : Plane} (hzL : zL ∈ D \ P)
    (hloc : ∀ w ∈ D ∩ P, ∃ V : Set Plane, IsOpen V ∧ w ∈ V ∧ V ⊆ D ∧
      V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR)
    {x : Plane} (hx : x ∈ D \ P) :
    x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR := by
  by_contra hcon
  push Not at hcon
  have hSopen : IsOpen (D \ P) := hDopen.sdiff hPclosed
  -- `W` gathers every open piece of `D` that the hypothesis certifies.
  have hWopen : IsOpen (⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
      V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) :=
    isOpen_sUnion fun _ hV => hV.1
  have hUopen : IsOpen (connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) :=
    ((Plane.isOpen_connectedComponentIn hSopen).union
      (Plane.isOpen_connectedComponentIn hSopen)).union hWopen
  have hTopen := isOpen_notMem_two_components hSopen zL zR
  -- `U` and `T` are disjoint: a point of `T` is off `P`, so if it were in `W` it would be in
  -- one of the two components, and it is in neither by definition.
  have hdisj : ∀ y, y ∈ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR} →
      y ∈ {y | y ∈ D \ P ∧ y ∉ connectedComponentIn (D \ P) zL ∧
        y ∉ connectedComponentIn (D \ P) zR} → False := by
    rintro y (hy | hy) ⟨hyS, hyL, hyR⟩
    · exact hy.elim hyL hyR
    · obtain ⟨V, hV, hyV⟩ := hy
      exact (hV.2.2 ⟨hyV, hyS.2⟩).elim hyL hyR
  -- and they cover `D`: a point of `D` on `P` is inside one of the certified pieces.
  have hcover : D ⊆ (connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) ∪
      {y | y ∈ D \ P ∧ y ∉ connectedComponentIn (D \ P) zL ∧
        y ∉ connectedComponentIn (D \ P) zR} := by
    intro y hyD
    by_cases hyP : y ∈ P
    · obtain ⟨V, hVopen, hyV, hVD, hVsub⟩ := hloc y ⟨hyD, hyP⟩
      exact Or.inl (Or.inr ⟨V, ⟨hVopen, hVD, hVsub⟩, hyV⟩)
    · by_cases hyL : y ∈ connectedComponentIn (D \ P) zL
      · exact Or.inl (Or.inl (Or.inl hyL))
      by_cases hyR : y ∈ connectedComponentIn (D \ P) zR
      · exact Or.inl (Or.inl (Or.inr hyR))
      exact Or.inr ⟨⟨hyD, hyP⟩, hyL, hyR⟩
  obtain ⟨y, hyD, hyU, hyT⟩ := hDconn _ _ hUopen hTopen hcover
    ⟨zL, hzL.1, Or.inl (Or.inl (mem_connectedComponentIn hzL))⟩
    ⟨x, hx.1, hx, hcon.1, hcon.2⟩
  exact hdisj y hyU hyT

/-! ### Lemma "At most two sides" -/

/-- **Lemma "At most two sides".** Let `D` be a region and `P` a simple polygonal arc whose
endpoints `a, b` lie outside `D` and whose remaining points lie in `D`. Then there are two
points `z_L, z_R` of `D ∖ P` such that every point of `D ∖ P` lies in the component of one of
them — that is, `D ∖ P` has at most two components.

`IsPolygonal P` is carried because the blueprint statement carries it, and because it is what
makes `HasArcCollars` dischargeable; this proof does not use it, since all the geometry is
inside the collar.

The reference points are the two reference points of the collar of the middle third of the arc:
`K₀ = f '' [1/4, 3/4]` for a parametrisation `f` of `P`. Any other nondegenerate compact subarc
would do, and `ArcCollar.nbhd_diff_subset_components` is stated so that a consumer that has a
collar of its own can use *its* reference points instead. -/
theorem crosscut_at_most_two {a b : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (_hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hcollars : HasArcCollars D P) :
    ∃ zL ∈ D \ P, ∃ zR ∈ D \ P, ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR := by
  have hPclosed : IsClosed P := hP.isArc.isClosed
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := hP
  -- The part of the arc inside the region is exactly its interior, because its two endpoints
  -- are outside `D` and everything else is inside.
  have hDPeq : D ∩ P = f '' Ioo 0 1 := by
    have hdiff : P \ {a, b} = f '' Ioo 0 1 := by
      rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi]
      rfl
    rw [← hdiff]
    ext y
    simp only [mem_inter_iff, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨hyD, hyP⟩ => ⟨hyP, ?_⟩, fun ⟨hyP, hy⟩ => ⟨hPD ⟨hyP, by simpa using hy⟩, hyP⟩⟩
    rintro (rfl | rfl)
    exacts [ha hyD, hb hyD]
  -- Every nondegenerate closed parameter interval inside `(0, 1)` names an admissible subarc.
  have hsubarc : ∀ s t : ℝ, 0 < s → s < t → t < 1 → Nonempty (ArcCollar D P (f '' Icc s t)) := by
    intro s t hs hst ht
    have hsubI : Icc s t ⊆ I := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsubIoo : Icc s t ⊆ Ioo 0 1 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
    have htI : t ∈ Icc s t := right_mem_Icc.2 hst.le
    refine hcollars _ (by rw [hDPeq]; exact image_mono hsubIoo)
      (isCompact_image_of_subset_I hc hsubI isClosed_Icc)
      (isPreconnected_Icc.image f (hc.mono hsubI))
      ⟨f s, mem_image_of_mem f hsI, f t, mem_image_of_mem f htI, fun h => ?_⟩
    exact absurd (hi (hsubI hsI) (hsubI htI) h) (ne_of_lt hst)
  -- The fixed collar, around the middle half of the arc.
  obtain ⟨C₀⟩ := hsubarc (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
  have hz₀ : f (1 / 2) ∈ f '' Icc (1 / 4 : ℝ) (3 / 4) :=
    mem_image_of_mem f ⟨by norm_num, by norm_num⟩
  refine ⟨C₀.ptL, C₀.ptL_mem_diff, C₀.ptR, C₀.ptR_mem_diff, fun x hx => ?_⟩
  refine covered_by_two_of_local hDopen hDconn hPclosed C₀.ptL_mem_diff (fun w hw => ?_) hx
  -- For a point `w` of the arc inside `D`, take the subarc that joins it to the middle half:
  -- its collar is a neighbourhood of `w` and shares the point `f (1/2)` with the fixed one.
  rw [hDPeq] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨C⟩ := hsubarc (min u (1 / 4)) (max u (3 / 4))
    (lt_min hu.1 (by norm_num)) (by have := min_le_right u (1 / 4 : ℝ)
                                    have := le_max_right u (3 / 4 : ℝ)
                                    linarith)
    (max_lt hu.2 (by norm_num))
  refine ⟨C.nbhd, C.isOpen_nbhd,
    C.subset_nbhd (mem_image_of_mem f ⟨min_le_left _ _, le_max_left _ _⟩), C.nbhd_subset, ?_⟩
  exact C₀.nbhd_diff_subset_components C hz₀
    (mem_image_of_mem f ⟨le_trans (min_le_right _ _) (by norm_num),
      le_trans (by norm_num) (le_max_right _ _)⟩)

/-- **"At most two", read off two components already known to be distinct.** This is the form
Theorem "Crosscut theorem" cites: the crosscut-cells lemma hands it two *distinct* components of
`D ∖ P`, and this says there is nothing else.

Stated for an arbitrary set `S`, since it is pure component bookkeeping: if everything is
covered by the components of `z_L, z_R` and `v₁, v₂` have different components, then those two
components are the two, in one order or the other. -/
theorem covered_by_two_components_of_ne {S : Set Plane} {zL zR v₁ v₂ : Plane}
    (h : ∀ x ∈ S, x ∈ connectedComponentIn S zL ∨ x ∈ connectedComponentIn S zR)
    (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S)
    (hne : connectedComponentIn S v₁ ≠ connectedComponentIn S v₂) :
    ∀ x ∈ S, x ∈ connectedComponentIn S v₁ ∨ x ∈ connectedComponentIn S v₂ := by
  intro x hx
  rcases h v₁ h₁ with hv₁ | hv₁ <;> rcases h v₂ h₂ with hv₂ | hv₂
  · exact absurd ((connectedComponentIn_eq hv₁).symm.trans (connectedComponentIn_eq hv₂)) hne
  · rcases h x hx with hxx | hxx
    · exact Or.inl (by rw [connectedComponentIn_eq hv₁] at hxx; exact hxx)
    · exact Or.inr (by rw [connectedComponentIn_eq hv₂] at hxx; exact hxx)
  · rcases h x hx with hxx | hxx
    · exact Or.inr (by rw [connectedComponentIn_eq hv₂] at hxx; exact hxx)
    · exact Or.inl (by rw [connectedComponentIn_eq hv₁] at hxx; exact hxx)
  · exact absurd ((connectedComponentIn_eq hv₁).symm.trans (connectedComponentIn_eq hv₂)) hne

/-! ### The collar hypothesis is not vacuous: a straight crosscut

The collar of a *straight* crosscut is a rectangle, and the free-standing frame toolkit of
`Schoenflies/Strip.lean` — `coordAlong`, `coordAcross`, `strip`, `isOpen_strip`, `convex_strip`,
`dist_foot`, `frame_decomp` — builds it directly, with no cyclic vertex family in sight. So
`HasArcCollars` is discharged outright in the simplest crosscut configuration, and
`segment_crosscut_at_most_two` below is a hypothesis-free instance of the lemma.

This is the shape a general discharger has to reproduce along a chain of edges: it is exactly
the blueprint's edge block, and what is missing is the vertex disks between consecutive blocks
and the end cross-sections. -/

namespace Plane

/-- A nondegenerate segment has a unit direction and a length: `L • u = b - a` with `‖u‖ = 1`.

Stated as an existential so that the direction and the length are *opaque* to the consumer.
Writing them as `dir (b - a)` and `‖b - a‖` makes every subsequent rewrite of `b` reach inside
them, which is exactly the friction the strip apparatus avoids by carrying `tang` and `len` as
fields. -/
theorem exists_direction_length {a b : Plane} (hab : a ≠ b) :
    ∃ (u : Plane) (L : ℝ), 0 < L ∧ IsDirection u ∧ L • u = b - a := by
  have hne : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hL : (0 : ℝ) < ‖b - a‖ := norm_pos_iff.2 hne
  exact ⟨dir (b - a), ‖b - a‖, hL, isDirection_dir hne, by
    rw [dir, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]⟩

/-- **A nondegenerate segment, read in the frame of its own direction.** Its points are the ones
at signed distance zero whose progress along the direction lies between `0` and the length.

This is the segment analogue of `ClosedPolygon.mem_edge_iff`, which is stated for an edge of a
closed polygon and so is unavailable for a lone segment. -/
theorem mem_segment_iff_coord {a b u x : Plane} {L : ℝ} (hL : 0 < L) (hu : IsDirection u)
    (hLu : L • u = b - a) :
    x ∈ segment ℝ a b ↔ coordAcross a u x = 0 ∧ coordAlong a u x ∈ Icc 0 L := by
  constructor
  · intro hx
    rw [segment_eq_image'] at hx
    obtain ⟨θ, hθ, rfl⟩ := hx
    have hrw : a + θ • (b - a) = a + (θ * L) • u + (0 : ℝ) • perp u := by
      rw [mul_smul, hLu]; module
    dsimp only
    rw [hrw, coordAlong_param hu, coordAcross_param hu]
    exact ⟨rfl, mul_nonneg hθ.1 hL.le, by nlinarith [hθ.2, hL.le]⟩
  · rintro ⟨h0, hc⟩
    rw [segment_eq_image']
    refine ⟨coordAlong a u x / L, ⟨div_nonneg hc.1 hL.le, (div_le_one hL).2 hc.2⟩, ?_⟩
    dsimp only
    rw [← hLu, smul_smul, div_mul_cancel₀ _ hL.ne']
    nth_rewrite 2 [frame_decomp hu a x]
    rw [h0]
    module

/-- A point at signed distance zero is the point of the line with its own progress. -/
theorem eq_foot_of_coordAcross_eq_zero {a u x : Plane} (hu : IsDirection u)
    (h0 : coordAcross a u x = 0) : x = a + (coordAlong a u x) • u := by
  nth_rewrite 1 [frame_decomp hu a x]
  rw [h0]
  module

end Plane

open Plane in
/-- **A straight crosscut has two-sided collars.** For a nondegenerate segment whose endpoints
lie outside the region and whose remaining points lie inside, blueprint Lemma 1.8 (b) is a
rectangle: an open block around the subarc, of half-width small enough to stay inside the
region, split by the line of the segment into two convex halves.

This discharges `HasArcCollars` in the one case the existing strip apparatus reaches without an
arc collar being built, and so certifies that the hypothesis of `crosscut_at_most_two` is
satisfiable. -/
theorem hasArcCollars_segment {a b : Plane} (hab : a ≠ b) (hDopen : IsOpen D)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : segment ℝ a b \ {a, b} ⊆ D) :
    HasArcCollars D (segment ℝ a b) := by
  obtain ⟨u, L, hL, hu, hLu⟩ := exists_direction_length hab
  -- Reading the two coordinates off a frame position, and off the two endpoints.
  have hAlong : ∀ c s : ℝ, coordAlong a u (a + c • u + s • perp u) = c :=
    fun c s => coordAlong_param hu a c s
  have hAcross : ∀ c s : ℝ, coordAcross a u (a + c • u + s • perp u) = s :=
    fun c s => coordAcross_param hu a c s
  have hzero : ∀ c : ℝ, a + c • u = a + c • u + (0 : ℝ) • perp u := fun c => by module
  have hfoot : ∀ c : ℝ, coordAlong a u (a + c • u) = c := fun c => by
    rw [hzero c]; exact hAlong c 0
  have hfoot' : ∀ c : ℝ, coordAcross a u (a + c • u) = 0 := fun c => by
    rw [hzero c]; exact hAcross c 0
  have hAa : coordAlong a u a = 0 := by simp [coordAlong]
  have hAb : coordAlong a u b = L := by
    rw [coordAlong, ← hLu, real_inner_smul_right, real_inner_self_eq_norm_mul_norm, hu.norm]
    ring
  -- A point of the line strictly between the two endpoints is inside the region.
  have hline : ∀ c : ℝ, 0 < c → c < L → a + c • u ∈ D ∩ segment ℝ a b := by
    intro c hc0 hcL
    have hmem : a + c • u ∈ segment ℝ a b :=
      (mem_segment_iff_coord hL hu hLu).2 ⟨hfoot' c, by rw [hfoot c]; exact ⟨hc0.le, hcL.le⟩⟩
    refine ⟨hPD ⟨hmem, ?_⟩, hmem⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro (h | h)
    · have hcc := hfoot c
      rw [h, hAa] at hcc
      exact absurd hcc.symm (ne_of_gt hc0)
    · have hcc := hfoot c
      rw [h, hAb] at hcc
      exact absurd hcc.symm (ne_of_lt hcL)
  intro K hKsub hKcompact _ hKnontriv
  -- The progress of a point of `K` is strictly between `0` and `L`: at the two extremes the
  -- point would be an endpoint of the segment, and the endpoints are outside `D`.
  have hKcoord : ∀ x ∈ K, coordAcross a u x = 0 ∧ 0 < coordAlong a u x ∧ coordAlong a u x < L := by
    intro x hx
    obtain ⟨h0, hc⟩ := (mem_segment_iff_coord hL hu hLu).1 (hKsub hx).2
    refine ⟨h0, lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩
    · intro hz
      have hxa : x = a := by
        have h := eq_foot_of_coordAcross_eq_zero hu h0
        rwa [← hz, zero_smul, add_zero] at h
      exact ha (hxa ▸ (hKsub hx).1)
    · intro hz
      have hxb : x = b := by
        have h := eq_foot_of_coordAcross_eq_zero hu h0
        rw [hz, hLu, show a + (b - a) = b from by module] at h
        exact h
      exact hb (hxb ▸ (hKsub hx).1)
  obtain ⟨p, hpK, hpmin⟩ :=
    hKcompact.exists_isMinOn hKnontriv.nonempty (continuous_coordAlong a u).continuousOn
  obtain ⟨q, hqK, hqmax⟩ :=
    hKcompact.exists_isMaxOn hKnontriv.nonempty (continuous_coordAlong a u).continuousOn
  have hc₁pos : 0 < coordAlong a u p := (hKcoord p hpK).2.1
  have hc₂lt : coordAlong a u q < L := (hKcoord q hqK).2.2
  have hc₁c₂ : coordAlong a u p ≤ coordAlong a u q := isMinOn_iff.1 hpmin q hqK
  set t₁ := coordAlong a u p / 2 with ht₁
  set t₂ := (coordAlong a u q + L) / 2 with ht₂
  have ht₁pos : 0 < t₁ := by rw [ht₁]; linarith
  have ht₁c₁ : t₁ < coordAlong a u p := by rw [ht₁]; linarith
  have hc₂t₂ : coordAlong a u q < t₂ := by rw [ht₂]; linarith
  have ht₂L : t₂ < L := by rw [ht₂]; linarith
  have ht₁t₂ : t₁ < t₂ := by linarith
  -- The core of the block: the closed piece of the line over `[t₁, t₂]`, compact and inside `D`.
  have hScompact : IsCompact ((fun c : ℝ => a + c • u) '' Icc t₁ t₂) :=
    isCompact_Icc.image (by fun_prop)
  have hSsub : (fun c : ℝ => a + c • u) '' Icc t₁ t₂ ⊆ D := by
    rintro _ ⟨c, hc, rfl⟩
    exact (hline c (lt_of_lt_of_le ht₁pos hc.1) (lt_of_le_of_lt hc.2 ht₂L)).1
  obtain ⟨ρ, hρ, hρD⟩ := Plane.exists_thickening_subset hScompact hDopen hSsub
  -- Both halves reach every point of `K`, by offsetting it perpendicularly.
  have hclose : ∀ x ∈ K, ∀ d : ℝ,
      dist x (a + (coordAlong a u x) • u + d • perp u) = |d| := by
    intro x hx d
    nth_rewrite 1 [eq_foot_of_coordAcross_eq_zero hu (hKcoord x hx).1]
    rw [dist_eq_norm,
      show a + (coordAlong a u x) • u -
        (a + (coordAlong a u x) • u + d • perp u) = (-d) • perp u from by module,
      norm_smul, Real.norm_eq_abs, norm_perp, hu.norm, mul_one, abs_neg]
  have hKt : ∀ x ∈ K, t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ := fun x hx =>
    ⟨lt_of_lt_of_le ht₁c₁ (isMinOn_iff.1 hpmin x hx),
      lt_of_le_of_lt (isMaxOn_iff.1 hqmax x hx) hc₂t₂⟩
  refine ⟨{ nbhd := strip a u t₁ t₂ (-ρ) ρ
            left := strip a u t₁ t₂ 0 ρ
            right := strip a u t₁ t₂ (-ρ) 0
            isOpen_nbhd := isOpen_strip a u t₁ t₂ (-ρ) ρ
            subset_nbhd := ?_
            nbhd_subset := ?_
            nbhd_diff := ?_
            isConnected_left := ?_
            isConnected_right := ?_
            subset_closure_left := ?_
            subset_closure_right := ?_ }⟩
  · -- `K` is inside the block: its progress is between the two bounds and its offset is zero.
    intro x hx
    exact ⟨(hKt x hx).1, (hKt x hx).2, by rw [(hKcoord x hx).1]; linarith,
      by rw [(hKcoord x hx).1]; exact hρ⟩
  · -- The block is inside `D`: every point is within `ρ` of the foot of its perpendicular.
    intro x hx
    refine hρD (mem_thickening_iff.2 ⟨a + (coordAlong a u x) • u, ⟨_, ⟨hx.1.le, hx.2.1.le⟩, rfl⟩,
      ?_⟩)
    rw [dist_foot hu, abs_lt]
    exact ⟨hx.2.2.1, hx.2.2.2⟩
  · -- Off the segment, the block is the two open halves: a point of the block at signed distance
    -- zero is on the segment, because its progress lies inside `[0, L]`.
    ext x
    simp only [mem_sdiff, mem_union, mem_strip_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
      rcases lt_trichotomy (coordAcross a u x) 0 with h | h | h
      · exact Or.inr ⟨h1, h2, h3, h⟩
      · exact absurd ((mem_segment_iff_coord hL hu hLu).2
          ⟨h, by linarith [ht₁pos], by linarith [ht₂L]⟩) h5
      · exact Or.inl ⟨h1, h2, h, h4⟩
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · refine ⟨⟨h1, h2, by linarith, h4⟩, fun hmem => ?_⟩
        linarith [((mem_segment_iff_coord hL hu hLu).1 hmem).1]
      · refine ⟨⟨h1, h2, h3, by linarith⟩, fun hmem => ?_⟩
        linarith [((mem_segment_iff_coord hL hu hLu).1 hmem).1]
  · exact (convex_strip a u t₁ t₂ 0 ρ).isConnected
      ⟨a + ((t₁ + t₂) / 2) • u + (ρ / 2) • perp u,
        (mem_strip_param hu a).2 ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · exact (convex_strip a u t₁ t₂ (-ρ) 0).isConnected
      ⟨a + ((t₁ + t₂) / 2) • u + (-(ρ / 2)) • perp u,
        (mem_strip_param hu a).2 ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hσ : 0 < min (ρ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
    refine ⟨a + (coordAlong a u x) • u + (min (ρ / 2) (ε / 2)) • perp u,
      (mem_strip_param hu a).2 ⟨(hKt x hx).1, (hKt x hx).2, hσ,
        lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩, ?_⟩
    rw [hclose x hx _, abs_of_pos hσ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hσ : 0 < min (ρ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
    refine ⟨a + (coordAlong a u x) • u + (-(min (ρ / 2) (ε / 2))) • perp u,
      (mem_strip_param hu a).2 ⟨(hKt x hx).1, (hKt x hx).2,
        by have := min_le_left (ρ / 2) (ε / 2); linarith, neg_neg_iff_pos.2 hσ⟩, ?_⟩
    rw [hclose x hx _, abs_neg, abs_of_pos hσ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

/-- **A straight crosscut cuts a region into at most two pieces**, with no hypothesis left
standing: `hasArcCollars_segment` discharges the collar. -/
theorem segment_crosscut_at_most_two {a b : Plane} (hab : a ≠ b)
    (hDopen : IsOpen D) (hDconn : IsPreconnected D) (ha : a ∉ D) (hb : b ∉ D)
    (hPD : segment ℝ a b \ {a, b} ⊆ D) :
    ∃ zL ∈ D \ segment ℝ a b, ∃ zR ∈ D \ segment ℝ a b, ∀ x ∈ D \ segment ℝ a b,
      x ∈ connectedComponentIn (D \ segment ℝ a b) zL ∨
        x ∈ connectedComponentIn (D \ segment ℝ a b) zR :=
  crosscut_at_most_two hDopen hDconn (isArcBetween_segment hab) (isPolygonal_segment a b) ha hb
    hPD (hasArcCollars_segment hab hDopen ha hb hPD)

/-- **Lemma "At most two sides", in the form the crosscut theorem consumes.** Two distinct
components of `D ∖ P` exhaust it. -/
theorem crosscut_components_exhaust {a b v₁ v₂ : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hcollars : HasArcCollars D P)
    (h₁ : v₁ ∈ D \ P) (h₂ : v₂ ∈ D \ P)
    (hne : connectedComponentIn (D \ P) v₁ ≠ connectedComponentIn (D \ P) v₂) :
    ∀ x ∈ D \ P, x ∈ connectedComponentIn (D \ P) v₁ ∨ x ∈ connectedComponentIn (D \ P) v₂ := by
  obtain ⟨zL, -, zR, -, hcov⟩ :=
    crosscut_at_most_two hDopen hDconn hP hPpoly ha hb hPD hcollars
  exact covered_by_two_components_of_ne hcov h₁ h₂ hne

end Schoenflies
