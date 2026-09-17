/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.AccessibleJoin
import LeanPool.Schoenflies.CrosscutCells
import LeanPool.Schoenflies.JordanSeparates
import LeanPool.Schoenflies.TwoArcs
import LeanPool.Schoenflies.Graph.K33Land

/-!
# The Jordan curve theorem

The complement of a Jordan curve has exactly two regions, one bounded and one unbounded, and
both have the curve as their boundary. That is `Schoenflies.IsSeparating C` — the very
predicate `Schoenflies/CrosscutCells.lean` introduces and
`Schoenflies.ClosedPolygon.polygonal_jordan` establishes for a polygon — so every consumer of
the polygonal case applies verbatim to the general one, `inside C` and `outside C` included.

Everything here takes one hypothesis, carried explicitly through every statement
that needs it:

    harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ

which is `thm:arc-complement`, the complement of a simple arc is connected. Nothing else is
assumed; in particular no part of `thm:jordan` itself is.

## The two theorems

`lem:accessible-dense` (`Schoenflies.accessible_dense`) says the points of `C` reachable from a
fixed `x ∉ C` by a polygonal arc meeting `C` only at its endpoint are dense in `C`. Its proof
is the blueprint's: delete a small open subarc `J₀`, leaving a simple arc whose complement is
connected by `harc`; join `x` there to a point of another component of `Cᶜ`; the joining chain
must cross `C`, and it can only do so inside `J₀`.

`thm:jordan` (`Schoenflies.IsJordanCurve.isSeparating`) then needs "at most two components",
which is `Schoenflies.not_three_components`, and the boundary clause, which is
`lem:accessible-dense` again: an accessible point is a limit of the region it is accessible
from, so `C` lies in the closure of each region and, being disjoint from both, in each
frontier.

## Three places where this departs from the blueprint's route

**The first meeting is taken on a vertex list, not on a parametrisation.**
`Schoenflies.exists_first_meeting` recurses on the list: on the first segment the first hit is
the infimum of the hitting parameters, and if the first segment misses the obstacle it is
swallowed by the component of the start and the recursion moves on. It returns the *initial
chain*, so both consumers — the accessibility of the meeting point, and the third branch of a
tripod — read off the same lemma.

**The tripod is built without a graph.** The blueprint overlays the three access arcs
(`lem:polygonal-overlay`), takes a minimal connected spanning subgraph, and extracts its unique
degree-three vertex by `lem:three-leaf-tree`. `Schoenflies.exists_tripod` instead joins the
first two terminals by a crosscut (`lem:accessible-endpoints`), runs a chain from the third
terminal to that crosscut, and takes the first meeting: that meeting point *is* the branch
vertex, and cutting the crosscut there (`IsArcBetween.exists_split`) gives the other two
branches. Neither `Schoenflies.polygonal_overlay` nor `Graph.IsTree.three_leaves` is used.

**The nine terminals are chosen in nine prescribed parameter windows.** The blueprint chooses
them distinct — proving that a dense set meets a nonempty relatively open subarc infinitely
often — and then *orders* the three on each closed arc `Q_j` to find the middle one `y_j`.
`Schoenflies.exists_windows` supplies nine pairwise separated windows inside `(0,1)`, in three
blocks of three; distinctness is then disjointness of the windows, the middle terminal of a
block is always the one with row index `1`, and no order on the curve is ever constructed. The
blueprint's `Q_j` never appears: only the parameter blocks `[t 0 j, t 2 j]` do.

## Blueprint

* `Schoenflies.exists_first_meeting_segment`, `Schoenflies.exists_first_meeting`,
  `Schoenflies.exists_arc_to_first_meeting`, `Schoenflies.polyAccessible_first_meeting` — the
  first-meeting machinery `lem:accessible-dense` and `thm:jordan` both run on. General enough
  to be hoisted if a second module needs it.
* `Schoenflies.PolyAccessible.mem_closure` — an accessible point of `∂Ω` lies in `closure Ω`.
* `Schoenflies.IsLoop.compl_openArc` — `lem:jordan-circle` in the form used here: the curve
  minus an open subarc is the complementary closed arc.
* `Schoenflies.exists_polyAccessible_openArc`, `Schoenflies.accessible_dense` —
  `lem:accessible-dense`, in the parameter form the proof produces and in the closure form.
* `Schoenflies.exists_tripod` — the three internally disjoint branches of the blueprint's
  `T_i`, at the H5 step of `thm:jordan`.
* `Schoenflies.exists_windows`, `Schoenflies.uIcc_inter_uIcc_mid` — the choice of the nine
  terminals and the middle-point bookkeeping that replaces "order `p_{1j}, p_{2j}, p_{3j}`
  along `Q_j`".
* `Schoenflies.not_three_components` — the `K(3,3)` half of `thm:jordan`, through
  `Graph.IsArcK33.elim` (`cor:k33-subdivision`).
* `Schoenflies.subset_closure_of_accessible_dense`, `Schoenflies.IsJordanCurve.isSeparating` —
  `thm:jordan`.
-/

open Bornology Metric Set unitInterval

namespace Schoenflies

variable {C S U Ω : Set Plane} {u v : Plane}

/-! ### The first meeting of a polygonal chain with a closed set

A chain that starts off a closed obstacle `S` and eventually hits it has a *first* hit, and
the piece of the chain before it never leaves the component of `U` its start lies in. This is
the only reason `lem:accessible-dense` produces an *accessible* point rather than merely a
point of the curve, and it is proved by structural recursion on the vertex list: on the first
segment the first hit is the infimum of the hitting parameters, and if the first segment
misses `S` the segment itself is swallowed by the component and the recursion moves on. -/

/-- **The first meeting on a single segment.** The parameter interval of the hits is closed and
bounded below, so it has a least element; before it the segment stays in `U`, hence in the
component of `U` carrying the near endpoint. -/
theorem exists_first_meeting_segment (hS : IsClosed S) (hUS : Disjoint U S) (hu : u ∈ U)
    (hsub : segment ℝ u v ⊆ U ∪ S) (hmeet : (segment ℝ u v ∩ S).Nonempty) :
    ∃ p ∈ segment ℝ u v ∩ S, segment ℝ u p ⊆ segment ℝ u v ∧
      segment ℝ u p \ {p} ⊆ connectedComponentIn U u := by
  set φ : ℝ → Plane := fun t => u + t • (v - u) with hφ
  have hcont : Continuous φ := by fun_prop
  have hseg : segment ℝ u v = φ '' Icc 0 1 := segment_eq_image' ℝ u v
  -- The parameters at which the segment sits on the obstacle.
  set T : Set ℝ := Icc 0 1 ∩ φ ⁻¹' S with hT
  have hTclosed : IsClosed T := isClosed_Icc.inter (hS.preimage hcont)
  have hTne : T.Nonempty := by
    obtain ⟨z, hz, hzS⟩ := hmeet
    rw [hseg] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, ht, hzS⟩
  have hTbdd : BddBelow T := ⟨0, fun x hx => hx.1.1⟩
  set t₀ : ℝ := sInf T with ht₀
  have ht₀T : t₀ ∈ T := hTclosed.csInf_mem hTne hTbdd
  have ht₀I : t₀ ∈ Icc (0 : ℝ) 1 := ht₀T.1
  have ht₀S : φ t₀ ∈ S := ht₀T.2
  -- The infimum is positive: the near endpoint is off the obstacle.
  have ht₀pos : 0 < t₀ := by
    rcases ht₀I.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hmem : φ 0 ∈ S := by rw [h]; exact ht₀S
      have hu' : φ 0 = u := by simp [hφ]
      rw [hu'] at hmem
      exact hUS.ne_of_mem hu hmem rfl
  -- Before the infimum the segment misses the obstacle, so it lies in `U`.
  have hbefore : φ '' Ico 0 t₀ ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans ht₀I.2⟩
    have : φ t ∉ S := fun hcon => absurd (csInf_le hTbdd ⟨htI, hcon⟩) (not_le.2 ht.2)
    exact (hsub (hseg ▸ mem_image_of_mem φ htI)).resolve_right this
  have hcomp : φ '' Ico 0 t₀ ⊆ connectedComponentIn U u := by
    refine (isPreconnected_Ico.image φ hcont.continuousOn).subset_connectedComponentIn ?_ hbefore
    exact ⟨0, ⟨le_rfl, ht₀pos⟩, by simp [hφ]⟩
  refine ⟨φ t₀, ⟨hseg ▸ mem_image_of_mem φ ht₀I, ht₀S⟩, ?_, ?_⟩
  · -- The initial piece of the segment is a piece of the segment.
    rw [segment_eq_image' ℝ u (φ t₀), hseg]
    rintro z ⟨θ, hθ, rfl⟩
    refine ⟨θ * t₀, ⟨mul_nonneg hθ.1 ht₀I.1, ?_⟩, ?_⟩
    · nlinarith [hθ.1, hθ.2, ht₀I.1, ht₀I.2]
    · simp only [hφ, add_sub_cancel_left, smul_smul]
  · rintro z ⟨hz, hzne⟩
    rw [mem_singleton_iff] at hzne
    rw [segment_eq_image' ℝ u (φ t₀)] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    replace hzne : u + θ • (φ t₀ - u) ≠ φ t₀ := hzne
    change u + θ • (φ t₀ - u) ∈ connectedComponentIn U u
    have hzeq : u + θ • (φ t₀ - u) = φ (θ * t₀) := by
      simp only [hφ, add_sub_cancel_left, smul_smul]
    rw [hzeq] at hzne ⊢
    -- The excluded point is exactly the parameter `1`, so the rest is strictly below `t₀`.
    have hθ1 : θ < 1 := by
      rcases hθ.2.lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [h, one_mul]) hzne
    exact hcomp ⟨θ * t₀, ⟨mul_nonneg hθ.1 ht₀I.1, by nlinarith⟩, rfl⟩

/-- **The first meeting of a polygonal chain with a closed set.** A chain that starts in `U`,
runs inside `U ∪ S` and meets the closed set `S` has an initial piece — again a chain from the
same start — that reaches `S` exactly at its far end and otherwise stays inside the *component*
of `U` carrying the start.

The chain is returned as `u :: ws`, so that "same start" is definitional and no
`List.head` obligation is ever produced. -/
theorem exists_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) :
    ∀ (u : Plane) (vs : List Plane), u ∈ U → poly (u :: vs) ⊆ U ∪ S →
      (poly (u :: vs) ∩ S).Nonempty →
      ∃ (ws : List Plane) (p : Plane), p ∈ poly (u :: vs) ∩ S ∧
        poly (u :: ws) ⊆ poly (u :: vs) ∧
        (u :: ws).getLast (List.cons_ne_nil u ws) = p ∧
        poly (u :: ws) \ {p} ⊆ connectedComponentIn U u
  | u, [], hu, _, hmeet => by
      -- A one-vertex chain carries only its vertex, which is in `U` and so off `S`.
      obtain ⟨z, hz, hzS⟩ := hmeet
      rw [poly_singleton, mem_singleton_iff] at hz
      exact absurd (hz ▸ hzS) (fun h => hUS.ne_of_mem hu h rfl)
  | u, v :: rest, hu, hsub, hmeet => by
      rw [poly_cons_cons] at hsub hmeet ⊢
      by_cases hfirst : (segment ℝ u v ∩ S).Nonempty
      · -- The obstacle is met already on the first segment.
        obtain ⟨p, hp, hpsub, hpcomp⟩ :=
          exists_first_meeting_segment hS hUS hu (hsub.trans' subset_union_left) hfirst
        exact ⟨[p], p, ⟨Or.inl hp.1, hp.2⟩, by rw [poly_pair]; exact hpsub.trans subset_union_left,
          rfl, by rw [poly_pair]; exact hpcomp⟩
      · -- The first segment misses the obstacle, so it is swallowed by the component.
        rw [not_nonempty_iff_eq_empty] at hfirst
        have hempty : ∀ z, z ∈ segment ℝ u v → z ∉ S := fun z hz hzS =>
          Set.eq_empty_iff_forall_notMem.1 hfirst z ⟨hz, hzS⟩
        have hsegU : segment ℝ u v ⊆ U := fun z hz =>
          (hsub (Or.inl hz)).resolve_right (hempty z hz)
        have hsegcomp : segment ℝ u v ⊆ connectedComponentIn U u :=
          (convex_segment u v).isPreconnected.subset_connectedComponentIn
            (left_mem_segment ℝ u v) hsegU
        have hvU : v ∈ U := hsegU (right_mem_segment ℝ u v)
        have hvcomp : connectedComponentIn U v = connectedComponentIn U u :=
          (connectedComponentIn_eq (hsegcomp (right_mem_segment ℝ u v))).symm
        have hrestsub : poly (v :: rest) ⊆ U ∪ S := hsub.trans' subset_union_right
        have hrestmeet : (poly (v :: rest) ∩ S).Nonempty := by
          obtain ⟨z, hz, hzS⟩ := hmeet
          rcases hz with hz | hz
          · exact absurd hzS (hempty z hz)
          · exact ⟨z, hz, hzS⟩
        obtain ⟨ws, p, hp, hwsub, hwlast, hwcomp⟩ :=
          exists_first_meeting hS hUS v rest hvU hrestsub hrestmeet
        refine ⟨v :: ws, p, ⟨Or.inr hp.1, hp.2⟩, ?_, ?_, ?_⟩
        · rw [poly_cons_cons]
          exact union_subset_union_right _ hwsub
        · rw [List.getLast_cons (List.cons_ne_nil v ws)]; exact hwlast
        · rw [poly_cons_cons]
          rintro z ⟨hz | hz, hzne⟩
          · exact hsegcomp hz
          · exact hvcomp ▸ hwcomp ⟨hz, hzne⟩

/-- **The first meeting, as a simple arc.** The initial piece of the chain is re-extracted as a
*simple polygonal arc* from the first meeting point back to the start; it meets `S` only at
that point, and everything else on it stays in the component of `U` carrying the start.

This is the form both consumers want: `lem:accessible-dense` reads off the accessibility of `p`,
and the tripod construction of `thm:jordan` needs the arc itself. -/
theorem exists_arc_to_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) {u : Plane}
    {vs : List Plane} (hu : u ∈ U) (hsub : poly (u :: vs) ⊆ U ∪ S)
    (hmeet : (poly (u :: vs) ∩ S).Nonempty) :
    ∃ p ∈ poly (u :: vs) ∩ S, ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P p u ∧
      P ⊆ poly (u :: vs) ∧ P \ {p} ⊆ connectedComponentIn U u := by
  obtain ⟨ws, p, hp, hwsub, hwlast, hwcomp⟩ := exists_first_meeting hS hUS u vs hu hsub hmeet
  have hne : (u :: ws) ≠ [] := List.cons_ne_nil u ws
  have hpY : p ∈ poly (u :: ws) := hwlast ▸ getLast_mem_poly hne
  have huY : u ∈ poly (u :: ws) := head_mem_poly hne
  have hpu : p ≠ u := fun hcon => hUS.ne_of_mem hu (hcon ▸ hp.2) rfl
  obtain ⟨qs, hqs, hqhead, hqlast, hqsub, hqcomp, hqarc⟩ :=
    exists_simple_poly_of_isPolygonal_pinned ⟨u :: ws, rfl⟩ (isConnected_poly hne).2 hpu hpY huY
      hwcomp
  exact ⟨p, hp, poly qs, ⟨qs, rfl⟩, hqarc, hqsub.trans hwsub, hqcomp⟩

/-- The accessibility statement `lem:accessible-dense` produces: the first meeting point is
polygonally accessible from the component of `U` the chain started in. -/
theorem polyAccessible_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) {u : Plane}
    {vs : List Plane} (hu : u ∈ U) (hsub : poly (u :: vs) ⊆ U ∪ S)
    (hmeet : (poly (u :: vs) ∩ S).Nonempty) :
    ∃ p ∈ poly (u :: vs) ∩ S, PolyAccessible (connectedComponentIn U u) p := by
  obtain ⟨ws, p, hp, -, hwlast, hwcomp⟩ := exists_first_meeting hS hUS u vs hu hsub hmeet
  have hpu : p ≠ u := fun hcon => hUS.ne_of_mem hu (hcon ▸ hp.2) rfl
  exact ⟨p, hp, polyAccessible_of_poly' (List.cons_ne_nil u ws) hwlast
    (fun hcon => hpu hcon.symm) hwcomp⟩

/-! ### An accessible point is a limit of the region

The half of `thm:jordan`'s boundary clause that `lem:accessible-dense` supplies: an accessible
point of the curve is in the closure of the region it is accessible from. The access chain is
connected and carries a point of the region, so the accessible point is not isolated on it. -/

/-- **An accessible point off the region lies in its closure.** -/
theorem PolyAccessible.mem_closure {a : Plane} (h : PolyAccessible Ω a) (ha : a ∉ Ω) :
    a ∈ closure Ω := by
  obtain ⟨vs, hvs, hhead, hlast, hint⟩ := h
  refine closure_mono hint ?_
  have haY : a ∈ poly vs := hhead ▸ head_mem_poly hvs
  have hzY : vs.getLast hvs ∈ poly vs := getLast_mem_poly hvs
  have hzne : vs.getLast hvs ≠ a := fun hcon => ha (hcon ▸ hlast)
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_contra hcon
  push Not at hcon
  -- Were `a` isolated on the chain, the ball around it and the complement of `{a}` would
  -- split the chain into two nonempty relatively open pieces — but the chain is connected.
  obtain ⟨w, hwY, hwball, hwne⟩ :=
    (isConnected_poly hvs).2 (Metric.ball a ε) {a}ᶜ Metric.isOpen_ball isOpen_compl_singleton
      (fun z _ => by
        rcases eq_or_ne z a with rfl | hza
        · exact Or.inl (Metric.mem_ball_self hε)
        · exact Or.inr hza)
      ⟨a, haY, Metric.mem_ball_self hε⟩ ⟨vs.getLast hvs, hzY, hzne⟩
  have := hcon w ⟨hwY, hwne⟩
  rw [Metric.mem_ball, dist_comm] at hwball
  exact absurd hwball (not_lt.2 this)

/-! ### The curve with an open subarc deleted

`lem:jordan-circle`'s "two points cut the curve into two arcs" in the form
`lem:accessible-dense` consumes it: the complement *in the curve* of a relatively open subarc
is one closed arc. The proof is the parameter bookkeeping of `Schoenflies/TwoArcs.lean` — no
new topology. -/

/-- **The curve minus an open subarc is the complementary closed arc.** -/
theorem IsLoop.compl_openArc {f : ℝ → Plane} (hf : IsLoop f) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a < b) :
    f '' I \ f '' Ioo a b = f '' Icc 0 a ∪ f '' Icc b 1 := by
  have halt1 : a < 1 := lt_of_lt_of_le hab hb.2
  have hmI : ∀ m ∈ Ioo a b, m ∈ I ∧ m ≠ 1 := fun m hm =>
    ⟨⟨ha.1.trans hm.1.le, hm.2.le.trans hb.2⟩, ne_of_lt (lt_of_lt_of_le hm.2 hb.2)⟩
  -- No parameter outside `(a, b)` carries a point of the open subarc.
  have hfront : ∀ s ∈ Icc (0 : ℝ) a, f s ∉ f '' Ioo a b := by
    rintro s hs ⟨m, hm, hms⟩
    have hsI : s ∈ I := ⟨hs.1, hs.2.trans ha.2⟩
    have hs1 : s ≠ 1 := ne_of_lt (lt_of_le_of_lt hs.2 halt1)
    have := hf.injective_before_finish (hmI m hm).1 hsI (hmI m hm).2 hs1 hms
    exact absurd (this ▸ hm.1) (not_lt.2 hs.2)
  have hback : ∀ t ∈ Icc b (1 : ℝ), f t ∉ f '' Ioo a b := by
    rintro t ht ⟨m, hm, hms⟩
    have htI : t ∈ I := ⟨hb.1.trans ht.1, ht.2⟩
    rcases eq_or_ne t 1 with rfl | ht1
    · -- The finish carries the start, and the start is strictly before the open subarc.
      have := hf.injective_before_finish (hmI m hm).1 zero_mem_I (hmI m hm).2 one_ne_zero.symm
        (hms.trans hf.closes.symm)
      exact absurd (this ▸ hm.1) (not_lt.2 ha.1)
    · have := hf.injective_before_finish (hmI m hm).1 htI (hmI m hm).2 ht1 hms
      exact absurd (this ▸ hm.2) (not_lt.2 ht.1)
  apply Subset.antisymm
  · rintro z ⟨⟨t, htI, rfl⟩, hz⟩
    rcases le_or_gt t a with h | h
    · exact mem_union_left _ (mem_image_of_mem f ⟨htI.1, h⟩)
    · rcases le_or_gt b t with h' | h'
      · exact mem_union_right _ (mem_image_of_mem f ⟨h', htI.2⟩)
      · exact absurd (mem_image_of_mem f (⟨h, h'⟩ : t ∈ Ioo a b)) hz
  · rintro z (⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨mem_image_of_mem f ⟨hs.1, hs.2.trans ha.2⟩, hfront s hs⟩
    · exact ⟨mem_image_of_mem f ⟨hb.1.trans ht.1, ht.2⟩, hback t ht⟩

/-! ### Density of accessible points, `lem:accessible-dense`

The blueprint's proof verbatim: shrink the given relatively open arc to one whose closure is
inside it, delete it from the curve to leave a simple arc, join `x` to a point of another
component in the (connected) complement of that arc by a polygonal chain, and take the first
meeting of the chain with the curve.

The shrinking step is done on parameters. Instead of "an open arc `J₀` with closure inside
`J`" the statement below takes the open subarc `f '' Ioo a b` with `0 < a < b < 1`, which is
already strictly inside the parameter interval; every relatively open piece of the curve
contains such a subarc (`Schoenflies.basic_piece_inside_ball` supplies one inside any ball),
and that is all the blueprint's `J₀` is for. -/

/-- **`lem:accessible-dense`, in the parameter form the proof produces.** Every open subarc
strictly inside the parameter interval carries a point accessible from the component of `x`.

`harc` is `thm:arc-complement`: the complement of a simple arc is connected. -/
theorem exists_polyAccessible_openArc (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    {f : ℝ → Plane} (hf : IsLoop f) {x : Plane} (hx : x ∉ f '' I)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ p ∈ f '' Ioo a b, PolyAccessible (connectedComponentIn (f '' I)ᶜ x) p := by
  have hCurve : IsJordanCurve (f '' I) := ⟨f, hf, rfl⟩
  have haI : a ∈ I := ⟨ha.le, (hab.trans hb).le⟩
  have hbI : b ∈ I := ⟨(ha.trans hab).le, hb.le⟩
  -- The curve minus the open subarc is a simple arc, so its complement is connected.
  set D : Set Plane := f '' Icc 0 a ∪ f '' Icc b 1 with hD
  have hDeq : f '' I \ f '' Ioo a b = D := hf.compl_openArc haI hbI hab
  have hDarc : IsArc D :=
    (hf.outside_IsArcBetween haI hbI (ne_of_lt (hab.trans hb)) (ne_of_lt hb) hab).isArc
  have hDconn : IsConnected Dᶜ := harc D hDarc
  have hDopen : IsOpen Dᶜ := hDarc.isClosed.isOpen_compl
  have hDsub : D ⊆ f '' I := hDeq ▸ sdiff_subset
  have hxD : x ∈ Dᶜ := fun hcon => hx (hDsub hcon)
  -- A point in another component of the complement of the curve.
  obtain ⟨y, hyC, hyne⟩ : ∃ y ∈ (f '' I)ᶜ,
      connectedComponentIn (f '' I)ᶜ y ≠ connectedComponentIn (f '' I)ᶜ x := by
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := hCurve.exists_connectedComponentIn_ne
    by_cases h : connectedComponentIn (f '' I)ᶜ u₁ = connectedComponentIn (f '' I)ᶜ x
    · exact ⟨u₂, hu₂, fun hcon => hne (h.trans hcon.symm)⟩
    · exact ⟨u₁, hu₁, h⟩
  have hyD : y ∈ Dᶜ := fun hcon => hyC (hDsub hcon)
  obtain ⟨vs, hvs, hvsub, hvhead, hvlast⟩ :=
    exists_poly_of_isPreconnected hDopen hDconn.isPreconnected hxD hyD
  -- Present the chain as one headed by `x`, which is what the first-meeting lemma consumes.
  have hlist : x :: vs.tail = vs := by rw [← hvhead]; exact List.cons_head_tail hvs
  have hsubC : poly (x :: vs.tail) ⊆ (f '' I)ᶜ ∪ f '' I := fun z _ => em' (z ∈ f '' I)
  have hmeet : (poly (x :: vs.tail) ∩ f '' I).Nonempty := by
    rw [hlist]
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    -- Otherwise the chain avoids the curve, so it lies in one component — but its two ends
    -- were chosen in different ones.
    have hsubcompl : poly vs ⊆ (f '' I)ᶜ := fun z hz hzC =>
      Set.eq_empty_iff_forall_notMem.1 hcon z ⟨hz, hzC⟩
    have hone := (isConnected_poly hvs).2.subset_connectedComponentIn
      (hvhead ▸ head_mem_poly hvs) hsubcompl
    exact hyne (connectedComponentIn_eq (hone (hvlast ▸ getLast_mem_poly hvs))).symm
  obtain ⟨p, hp, hacc⟩ :=
    polyAccessible_first_meeting hCurve.isClosed disjoint_compl_left hx hsubC hmeet
  rw [hlist] at hp
  refine ⟨p, ?_, hacc⟩
  -- The first meeting is off the deleted arc, so it lies on the open subarc.
  by_contra hcon
  exact absurd (hDeq ▸ (⟨hp.2, hcon⟩ : p ∈ f '' I \ f '' Ioo a b)) (hvsub hp.1)

/-- **`lem:accessible-dense` (density of accessible points).** The points of `C` reachable from
`x` by a polygonal arc meeting `C` only at its endpoint are dense in `C`. -/
theorem accessible_dense (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) {x : Plane} (hx : x ∉ C) :
    C ⊆ closure {p | p ∈ C ∧ PolyAccessible (connectedComponentIn Cᶜ x) p} := by
  obtain ⟨f, hf, rfl⟩ := hC
  intro z hz
  rw [Metric.mem_closure_iff]
  intro r hr
  obtain ⟨c, d, hzcd, hball⟩ := basic_piece_inside_ball hf.continuousOn hz hr
  obtain ⟨w, hw, -⟩ := hzcd
  -- Trim the basic piece to an open subarc strictly inside the parameter interval.
  have h1 : c < w := hw.1.1
  have h2 : w < d := hw.1.2
  have h3 : (0 : ℝ) ≤ w := hw.2.1
  have h4 : w ≤ 1 := hw.2.2
  have hαβ : max c 0 < min d 1 := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by norm_num⟩⟩
  have hc0 : (0 : ℝ) ≤ max c 0 := le_max_right c 0
  have hd1 : min d 1 ≤ 1 := min_le_right d 1
  have hct : c ≤ max c 0 := le_max_left c 0
  have hdt : min d 1 ≤ d := min_le_left d 1
  set a : ℝ := max c 0 + (min d 1 - max c 0) / 3 with hadef
  set b : ℝ := max c 0 + 2 * (min d 1 - max c 0) / 3 with hbdef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hb1 : b < 1 := by rw [hbdef]; linarith
  have hsub : Ioo a b ⊆ Ioo c d ∩ I := by
    rintro t ⟨ht1, ht2⟩
    rw [hadef] at ht1
    rw [hbdef] at ht2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨p, hpIoo, hacc⟩ := exists_polyAccessible_openArc harc hf hx ha0 hab hb1
  refine ⟨p, ⟨image_mono (hsub.trans inter_subset_right) hpIoo, hacc⟩, ?_⟩
  rw [dist_comm]
  exact hball (image_mono hsub hpIoo)

/-! ### The tripod at a component

The blueprint builds the three internally disjoint branches from `x_i` to the three terminals
by overlaying the three access arcs, taking a minimal connected spanning subgraph, and reading
off its unique degree-three vertex (`lem:three-leaf-tree`). The construction below reaches the
same object without a graph: join the first two terminals by a *crosscut* — a simple polygonal
arc meeting the curve exactly at its two endpoints (`lem:accessible-endpoints` in crosscut
form) — then run a chain from the third terminal into the region and on to a point of that
crosscut, and take its **first meeting** with the crosscut. That meeting point is the branch
vertex; cutting the crosscut there (`IsArcBetween.exists_split`) supplies the other two
branches.

The output is the same three internally disjoint arcs, with the same two properties every
later step uses: each meets the curve only at its terminal, and two of them meet only at the
branch vertex. -/

/-- **Three internally disjoint arcs from one point of a region to three accessible points of
its complementary set.** The blueprint's `T_i` with its three branches, for `Ω` the `i`-th
component and the three points the terminals `p_{ij}`. -/
theorem exists_tripod (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (hdisj : Disjoint Ω C) {a b c : Plane} (haC : a ∈ C) (hbC : b ∈ C) (hcC : c ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) (hc : PolyAccessible Ω c) :
    ∃ x ∈ Ω, ∃ Ta Tb Tc : Set Plane,
      IsArcBetween Ta x a ∧ IsArcBetween Tb x b ∧ IsArcBetween Tc x c ∧
        Ta \ {a} ⊆ Ω ∧ Tb \ {b} ⊆ Ω ∧ Tc \ {c} ⊆ Ω ∧
        Ta ∩ Tb ⊆ {x} ∧ Ta ∩ Tc ⊆ {x} ∧ Tb ∩ Tc ⊆ {x} := by
  classical
  -- The crosscut from `a` to `b`.
  obtain ⟨ws, hws, hwhead, hwlast, hwΩ, hwarc, hwC⟩ :=
    exists_crosscut_of_polyAccessible hΩopen hΩconn hdisj hab haC hbC ha hb
  set A : Set Plane := poly ws with hA
  have hAclosed : IsClosed A := (isCompact_poly ws).isClosed
  have hcA : c ∉ A := fun hcon => by
    rcases (hwC ▸ (⟨hcon, hcC⟩ : c ∈ A ∩ C) : c ∈ ({a, b} : Set Plane)) with h | h
    exacts [hac h.symm, hbc h.symm]
  -- The access chain from `c`, continued inside `Ω` to an interior point of the crosscut.
  obtain ⟨cs, hcs, hchead, hclast, hcsub⟩ := hc
  obtain ⟨w, hwmem⟩ := hwarc.nonempty_diff
  have hwΩ' : w ∈ Ω := hwΩ hwmem
  obtain ⟨ls, hls, hlsub, hlhead, hllast⟩ :=
    exists_poly_of_isPreconnected hΩopen hΩconn hclast hwΩ'
  have hcatlist : cs ++ ls = cs ++ cs.getLast hcs :: ls.tail := by
    rw [← hlhead, List.cons_head_tail hls]
  have hcat : poly (cs ++ ls) = poly cs ∪ poly ls := by
    rw [hcatlist, poly_append hcs _ _ rfl, ← hlhead, List.cons_head_tail hls]
  -- The full chain starts at `c`, runs in `Ω ∪ {c}`, and reaches the crosscut.
  have hfullne : cs ++ ls ≠ [] := by simp [hcs]
  have hfullhead : (cs ++ ls).head hfullne = c := by
    rw [List.head_append_of_ne_nil hcs, hchead]
  have hfulllist : c :: (cs ++ ls).tail = cs ++ ls := by
    rw [← hfullhead]; exact List.cons_head_tail hfullne
  set U : Set Plane := (Ω ∪ {c}) \ A with hU
  have hUS : Disjoint U A := disjoint_sdiff_left
  have hcU : c ∈ U := ⟨Or.inr rfl, hcA⟩
  have hfullsub : poly (c :: (cs ++ ls).tail) ⊆ U ∪ A := by
    rw [hfulllist, hcat]
    rintro z hz
    have hzΩ : z ∈ Ω ∪ {c} := by
      rcases hz with hz | hz
      · rcases eq_or_ne z c with rfl | hzc
        · exact Or.inr rfl
        · exact Or.inl (hcsub ⟨hz, hzc⟩)
      · exact Or.inl (hlsub hz)
    rcases em (z ∈ A) with h | h
    · exact Or.inr h
    · exact Or.inl ⟨hzΩ, h⟩
  have hfullmeet : (poly (c :: (cs ++ ls).tail) ∩ A).Nonempty := by
    rw [hfulllist, hcat]
    exact ⟨w, Or.inr (hllast ▸ getLast_mem_poly hls), hwmem.1⟩
  obtain ⟨x, hx, P, -, hParc, -, hPcomp⟩ :=
    exists_arc_to_first_meeting hAclosed hUS hcU hfullsub hfullmeet
  rw [hfulllist, hcat] at hx
  -- The branch vertex is interior to the crosscut.
  have hxU : ∀ z ∈ P, z ≠ x → z ∈ U := fun z hz hzx =>
    connectedComponentIn_subset _ _ (hPcomp ⟨hz, hzx⟩)
  have hxΩ : x ∈ Ω := by
    rcases hx.1 with hz | hz
    · rcases eq_or_ne x c with rfl | hxc
      · exact absurd hx.2 hcA
      · exact hcsub ⟨hz, hxc⟩
    · exact hlsub hz
  have hPC : P ∩ C = {c} := by
    apply Subset.antisymm
    · rintro z ⟨hzP, hzC⟩
      rcases eq_or_ne z x with rfl | hzx
      · exact absurd rfl (hdisj.ne_of_mem hxΩ hzC)
      · rcases (hxU z hzP hzx).1 with h | h
        · exact absurd rfl (hdisj.ne_of_mem h hzC)
        · exact h
    · rintro z rfl; exact ⟨hParc.right_mem, hcC⟩
  have hPΩ : P \ {c} ⊆ Ω := by
    rintro z ⟨hzP, hzc⟩
    rcases eq_or_ne z x with rfl | hzx
    · exact hxΩ
    · exact ((hxU z hzP hzx).1).resolve_right hzc
  have hPA : P ∩ A ⊆ {x} := by
    rintro z ⟨hzP, hzA⟩
    by_contra hzx
    exact (hxU z hzP (fun h => hzx (by rw [h]; rfl))).2 hzA
  -- Cut the crosscut at the branch vertex.
  have hxa : x ≠ a := fun hcon => hdisj.ne_of_mem hxΩ (hcon ▸ haC) rfl
  have hxb : x ≠ b := fun hcon => hdisj.ne_of_mem hxΩ (hcon ▸ hbC) rfl
  obtain ⟨A₁, A₂, hA₁, hA₂, hAcov, hAmeet⟩ := hwarc.exists_split hx.2 hxa hxb
  have hbA₁ : b ∉ A₁ := fun hcon => hxb (by
    have : b ∈ A₁ ∩ A₂ := ⟨hcon, hA₂.right_mem⟩
    rw [hAmeet] at this; exact this.symm)
  have haA₂ : a ∉ A₂ := fun hcon => hxa (by
    have : a ∈ A₁ ∩ A₂ := ⟨hA₁.left_mem, hcon⟩
    rw [hAmeet] at this; exact this.symm)
  have hAΩ : A \ {a, b} ⊆ Ω := hwΩ
  refine ⟨x, hxΩ, A₁, A₂, P, hA₁.reverse, hA₂, hParc, ?_, ?_, hPΩ, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hza⟩
    refine hAΩ ⟨hAcov ▸ mem_union_left _ hz, ?_⟩
    rintro (rfl | rfl)
    exacts [hza rfl, hbA₁ hz]
  · rintro z ⟨hz, hzb⟩
    refine hAΩ ⟨hAcov ▸ mem_union_right _ hz, ?_⟩
    rintro (rfl | rfl)
    exacts [haA₂ hz, hzb rfl]
  · exact hAmeet.subset
  · exact fun z hz => hPA ⟨hz.2, hAcov ▸ mem_union_left _ hz.1⟩
  · exact fun z hz => hPA ⟨hz.2, hAcov ▸ mem_union_right _ hz.1⟩

/-! ### Nine parameter windows

The blueprint chooses the nine terminals `p_{ij}` distinct and then *orders* the three on each
arc `Q_j` to find the middle one `y_j`. Choosing them in nine prescribed, pairwise separated
parameter windows does both jobs at once: distinctness is disjointness of the windows, and the
middle one is always the terminal of the middle index. No order on the curve is ever
constructed.

The windows are `((6j + 2i + 2)/24, (6j + 2i + 3)/24)`, which for `i, j < 3` are nine disjoint
intervals inside `(0, 1)`, ordered lexicographically by `(j, i)`. -/

/-- Nine parameter windows strictly inside `(0, 1)`, in blocks of three: increasing the row
index `i` within a block, or the block index `j`, moves past the end of the current window. -/
theorem exists_windows : ∃ w : Fin 3 → Fin 3 → ℝ,
    (∀ i j, 0 < w i j) ∧ (∀ i j, w i j + 1 / 24 < 1) ∧
      (∀ i j k l : Fin 3, (j = l ∧ i.val < k.val) ∨ j.val < l.val →
        w i j + 1 / 24 ≤ w k l) := by
  refine ⟨fun i j => (6 * (j.val : ℝ) + 2 * (i.val : ℝ) + 2) / 24, ?_, ?_, ?_⟩
  · intro i j
    have h1 : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    linarith
  · intro i j
    have h1 : ((j.val : ℝ)) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
    have h2 : ((i.val : ℝ)) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 i.isLt
    linarith
  · rintro i j k l (⟨rfl, hik⟩ | hjl)
    · have h : ((i.val : ℝ)) + 1 ≤ (k.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hik
      linarith
    · have h : ((j.val : ℝ)) + 1 ≤ (l.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hjl
      have h1 : ((i.val : ℝ)) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 i.isLt
      have h2 : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
      linarith

/-- Two closed intervals sharing the endpoint `m`, one on each side of it, meet only there. -/
theorem uIcc_inter_uIcc_mid {r s m : ℝ} (hr : r ≤ m) (hs : m ≤ s) :
    uIcc r m ∩ uIcc s m ⊆ {m} := by
  rw [uIcc_of_le hr, uIcc_of_ge hs]
  rintro z ⟨⟨-, h2⟩, ⟨h3, -⟩⟩
  exact le_antisymm h2 h3

/-! ### At most two components

The heart of `thm:jordan`. Three components would give three tripods, whose nine branches,
extended along the curve to the three middle terminals, are a plane `K(3,3)` subdivision —
excluded by `cor:k33-subdivision` (`Graph.IsArcK33.elim`). -/

/-- **Three points of the complement of a Jordan curve cannot lie in three distinct
components.** -/
theorem not_three_components (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) {q : Fin 3 → Plane} (hqC : ∀ i, q i ∉ C)
    (hqne : ∀ i k, i ≠ k → connectedComponentIn Cᶜ (q i) ≠ connectedComponentIn Cᶜ (q k)) :
    False := by
  classical
  obtain ⟨f, hf, rfl⟩ := hC
  have hCclosed : IsClosed (f '' I) := IsJordanCurve.isClosed ⟨f, hf, rfl⟩
  set Ω : Fin 3 → Set Plane := fun i => connectedComponentIn (f '' I)ᶜ (q i) with hΩdef
  have hΩopen : ∀ i, IsOpen (Ω i) := fun _ =>
    Plane.isOpen_connectedComponentIn hCclosed.isOpen_compl
  have hΩconn : ∀ i, IsPreconnected (Ω i) := fun _ => isPreconnected_connectedComponentIn
  have hΩdisj : ∀ i, Disjoint (Ω i) (f '' I) := fun i =>
    Set.disjoint_left.2 fun z hz => connectedComponentIn_subset _ _ hz
  have hΩij : ∀ i k, i ≠ k → Disjoint (Ω i) (Ω k) := by
    intro i k hik
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hqne i k hik ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm)
  -- Nine terminals, one per window, each accessible from its own component.
  obtain ⟨w, hw0, hw1, hwstep⟩ := exists_windows
  have key : ∀ i j : Fin 3, ∃ s : ℝ, s ∈ Ioo (w i j) (w i j + 1 / 24) ∧
      PolyAccessible (Ω i) (f s) := by
    intro i j
    obtain ⟨-, ⟨s, hs, rfl⟩, hacc⟩ :=
      exists_polyAccessible_openArc harc hf (hqC i) (hw0 i j)
        (by linarith : w i j < w i j + 1 / 24) (hw1 i j)
    exact ⟨s, hs, hacc⟩
  choose t ht hacc using key
  /- ### Parameter bookkeeping -/
  have hmono : ∀ i j k l : Fin 3, (j = l ∧ i.val < k.val) ∨ j.val < l.val → t i j < t k l :=
    fun i j k l h => lt_of_lt_of_le (ht i j).2 (le_trans (hwstep i j k l h) (ht k l).1.le)
  have htI : ∀ i j, t i j ∈ Ico (0 : ℝ) 1 :=
    fun i j => ⟨((hw0 i j).trans (ht i j).1).le, (ht i j).2.trans (hw1 i j)⟩
  have htI' : ∀ i j, t i j ∈ I := fun i j => ⟨(htI i j).1, (htI i j).2.le⟩
  have hle : ∀ i k j : Fin 3, i.val ≤ k.val → t i j ≤ t k j := by
    intro i k j h
    rcases h.lt_or_eq with h | h
    · exact (hmono i j k j (Or.inl ⟨rfl, h⟩)).le
    · rw [Fin.val_injective h]
  have htinj : ∀ i j k l : Fin 3, t i j = t k l → i = k ∧ j = l := by
    intro i j k l h
    rcases lt_trichotomy j.val l.val with hjl | hjl | hjl
    · exact absurd h (ne_of_lt (hmono i j k l (Or.inr hjl)))
    · have hjl' : j = l := Fin.val_injective hjl
      subst hjl'
      rcases lt_trichotomy i.val k.val with hik | hik | hik
      · exact absurd h (ne_of_lt (hmono i j k j (Or.inl ⟨rfl, hik⟩)))
      · exact ⟨Fin.val_injective hik, rfl⟩
      · exact absurd h.symm (ne_of_lt (hmono k j i j (Or.inl ⟨rfl, hik⟩)))
    · exact absurd h.symm (ne_of_lt (hmono k l i j (Or.inr hjl)))
  have hpC : ∀ i j, f (t i j) ∈ f '' I := fun i j => mem_image_of_mem f (htI' i j)
  have hpinj : ∀ i j k l : Fin 3, f (t i j) = f (t k l) → i = k ∧ j = l :=
    fun i j k l h => htinj i j k l (hf.injOn (htI i j) (htI k l) h)
  -- The block of parameters carrying the three terminals of one arc `Q_j`.
  have htM : ∀ i j : Fin 3, t i j ∈ Icc (t 0 j) (t 2 j) := fun i j =>
    ⟨hle 0 i j (Nat.zero_le _), hle i 2 j (Nat.lt_succ_iff.1 i.isLt)⟩
  have hMIco : ∀ (j : Fin 3), Icc (t 0 j) (t 2 j) ⊆ Ico (0 : ℝ) 1 := fun j s hs =>
    ⟨(htI 0 j).1.trans hs.1, lt_of_le_of_lt hs.2 (htI 2 j).2⟩
  have hMdisj : ∀ j l : Fin 3, j.val < l.val →
      ∀ s ∈ Icc (t 0 j) (t 2 j), ∀ s' ∈ Icc (t 0 l) (t 2 l), s < s' := fun j l h s hs s' hs' =>
    lt_of_le_of_lt hs.2 (lt_of_lt_of_le (hmono 2 j 0 l (Or.inr h)) hs'.1)
  /- ### The three arcs along the curve -/
  have hRparam : ∀ i j : Fin 3, uIcc (t i j) (t 1 j) ⊆ Icc (t 0 j) (t 2 j) := fun i j =>
    uIcc_subset_Icc (htM i j) (htM 1 j)
  have hRC : ∀ i j : Fin 3, f '' uIcc (t i j) (t 1 j) ⊆ f '' I := fun i j =>
    image_mono ((hRparam i j).trans ((hMIco j).trans Ico_subset_Icc_self))
  have hpR : ∀ i j : Fin 3, f (t i j) ∈ f '' uIcc (t i j) (t 1 j) := fun i j =>
    mem_image_of_mem f left_mem_uIcc
  have hRRdisj : ∀ i j k l : Fin 3, j ≠ l →
      f '' uIcc (t i j) (t 1 j) ∩ f '' uIcc (t k l) (t 1 l) = ∅ := by
    intro i j k l hjl
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨s, hs, rfl⟩, s', hs', hz'⟩
    have h1 : s ∈ Icc (t 0 j) (t 2 j) := hRparam i j hs
    have h2 : s' ∈ Icc (t 0 l) (t 2 l) := hRparam k l hs'
    have hss : s' = s := hf.injOn (hMIco l h2) (hMIco j h1) hz'
    rw [hss] at h2
    rcases lt_trichotomy j.val l.val with h | h | h
    · exact absurd (hMdisj j l h s h1 s h2) (lt_irrefl s)
    · exact hjl (Fin.val_injective h)
    · exact absurd (hMdisj l j h s h2 s h1) (lt_irrefl s)
  have hRRmeet : ∀ i j k : Fin 3, i ≠ k →
      f '' uIcc (t i j) (t 1 j) ∩ f '' uIcc (t k j) (t 1 j) ⊆ {f (t 1 j)} := by
    intro i j k hik
    have hord : ∀ c e : Fin 3, c.val < e.val → t c j ≤ t 1 j ∧ t 1 j ≤ t e j := by
      intro c e h
      have he := e.isLt
      exact ⟨hle c 1 j (by omega), hle 1 e j (by omega)⟩
    rintro z ⟨⟨s, hs, rfl⟩, s', hs', hz'⟩
    have hss : s' = s := hf.injOn (hMIco j (hRparam k j hs')) (hMIco j (hRparam i j hs)) hz'
    subst hss
    rcases lt_trichotomy i.val k.val with h | h | h
    · exact mem_singleton_iff.2 (by
        rw [uIcc_inter_uIcc_mid (hord i k h).1 (hord i k h).2 ⟨hs, hs'⟩])
    · exact absurd (Fin.val_injective h) hik
    · exact mem_singleton_iff.2 (by
        rw [uIcc_inter_uIcc_mid (hord k i h).1 (hord k i h).2 ⟨hs', hs⟩])
  /- ### The three tripods -/
  have htri : ∀ i : Fin 3, ∃ xc : Plane, xc ∈ Ω i ∧ ∃ T : Fin 3 → Set Plane,
      (∀ j, IsArcBetween (T j) xc (f (t i j))) ∧ (∀ j, T j \ {f (t i j)} ⊆ Ω i) ∧
        (∀ j l, j ≠ l → T j ∩ T l ⊆ {xc}) := by
    intro i
    have hne : ∀ j l : Fin 3, j ≠ l → f (t i j) ≠ f (t i l) := fun j l hjl hcon =>
      hjl (hpinj i j i l hcon).2
    obtain ⟨xc, hxc, Ta, Tb, Tc, hTa, hTb, hTc, hTa', hTb', hTc', h01, h02, h12⟩ :=
      exists_tripod (hΩopen i) (hΩconn i) (hΩdisj i) (hpC i 0) (hpC i 1) (hpC i 2)
        (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
        (hacc i 0) (hacc i 1) (hacc i 2)
    refine ⟨xc, hxc, ![Ta, Tb, Tc], ?_, ?_, ?_⟩
    · intro j; fin_cases j <;> assumption
    · intro j; fin_cases j <;> assumption
    · intro j l hjl
      fin_cases j <;> fin_cases l <;>
        first
          | exact absurd rfl hjl
          | assumption
          | (rw [inter_comm]; assumption)
  choose xx hxxΩ TT hTTarc hTTsub hTTmeet using htri
  /- ### Assembling the `K(3,3)` -/
  have hTC : ∀ i j, TT i j ∩ f '' I = {f (t i j)} := by
    intro i j
    apply Subset.antisymm
    · rintro z ⟨hz1, hz2⟩
      by_contra hzne
      exact (hΩdisj i).ne_of_mem (hTTsub i j ⟨hz1, hzne⟩) hz2 rfl
    · rintro z rfl
      exact ⟨(hTTarc i j).right_mem, hpC i j⟩
  have hTR : ∀ i j k l : Fin 3, ∀ z ∈ TT i j, z ∈ f '' uIcc (t k l) (t 1 l) →
      z = f (t i j) ∧ f (t i j) ∈ f '' uIcc (t k l) (t 1 l) := by
    intro i j k l z hz hz'
    have hzp : z = f (t i j) := by
      have hmem : z ∈ TT i j ∩ f '' I := ⟨hz, hRC k l hz'⟩
      rw [hTC i j] at hmem
      exact hmem
    exact ⟨hzp, hzp ▸ hz'⟩
  have hTTdisj : ∀ i j k l : Fin 3, i ≠ k → TT i j ∩ TT k l = ∅ := by
    intro i j k l hik
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    rcases eq_or_ne z (f (t i j)) with rfl | h1
    · have hmem : f (t i j) ∈ TT k l ∩ f '' I := ⟨hz2, hpC i j⟩
      rw [hTC k l] at hmem
      exact hik (hpinj i j k l hmem).1
    · rcases eq_or_ne z (f (t k l)) with rfl | h2
      · have hmem : f (t k l) ∈ TT i j ∩ f '' I := ⟨hz1, hpC k l⟩
        rw [hTC i j] at hmem
        exact hik (hpinj k l i j hmem).1.symm
      · exact (hΩij i k hik).ne_of_mem (hTTsub i j ⟨hz1, h1⟩) (hTTsub k l ⟨hz2, h2⟩) rfl
  -- The nine branch paths: a tripod branch, continued along the curve to the middle terminal.
  have harcP : ∀ i j : Fin 3,
      IsArcBetween (TT i j ∪ f '' uIcc (t i j) (t 1 j)) (xx i) (f (t 1 j)) := by
    intro i j
    rcases eq_or_ne i 1 with rfl | hi1
    · -- The middle terminal *is* the terminal: the arc along the curve degenerates.
      have hdeg : f '' uIcc (t 1 j) (t 1 j) = {f (t 1 j)} := by
        rw [uIcc_self, image_singleton]
      rw [hdeg, union_eq_self_of_subset_right
        (singleton_subset_iff.2 (hTTarc 1 j).right_mem)]
      exact hTTarc 1 j
    · have hne : t i j ≠ t 1 j := fun hcon => hi1 (htinj i j 1 j hcon).1
      have harcR : IsArcBetween (f '' uIcc (t i j) (t 1 j)) (f (t i j)) (f (t 1 j)) :=
        isArcBetween_subarc hf.continuousOn
          (hf.injOn.mono ((hRparam i j).trans (hMIco j)))
          (htI' i j) (htI' 1 j) hne
      refine (hTTarc i j).concatenate harcR (fun z hz hz' => ?_)
      exact (hTR i j i j z hz hz').1
  refine (Graph.IsArcK33.elim (x := xx) (y := fun j => f (t 1 j))
    (P := fun i j => TT i j ∪ f '' uIcc (t i j) (t 1 j)) ?_)
  have hmeetHalf : ∀ i j k l : Fin 3, (i, j) ≠ (k, l) →
      (TT i j ∪ f '' uIcc (t i j) (t 1 j)) ∩ (TT k l ∪ f '' uIcc (t k l) (t 1 l)) ⊆
        ({xx i, f (t 1 j)} : Set Plane) := by
    rintro i j k l hne z ⟨hz1, hz2⟩
    have hRRne : ∀ c e d g : Fin 3, d ≠ g → f (t c d) ∈ f '' uIcc (t e g) (t 1 g) → False :=
      fun c e d g hdg hmem =>
        absurd (hRRdisj c d e g hdg) (Set.nonempty_iff_ne_empty.1 ⟨f (t c d), hpR c d, hmem⟩)
    rcases eq_or_ne i k with rfl | hik
    · have hjl : j ≠ l := fun h => hne (by rw [h])
      rcases hz1 with hz1 | hz1 <;> rcases hz2 with hz2 | hz2
      · exact Or.inl (hTTmeet i j l hjl ⟨hz1, hz2⟩)
      · exact absurd ((hTR i j i l z hz1 hz2).2) (fun h => hRRne i i j l hjl h)
      · exact absurd ((hTR i l i j z hz2 hz1).2) (fun h => hRRne i i l j (Ne.symm hjl) h)
      · exact absurd (hRRdisj i j i l hjl) (Set.nonempty_iff_ne_empty.1 ⟨z, hz1, hz2⟩)
    · rcases hz1 with hz1 | hz1 <;> rcases hz2 with hz2 | hz2
      · exact absurd (hTTdisj i j k l hik) (Set.nonempty_iff_ne_empty.1 ⟨z, hz1, hz2⟩)
      · obtain ⟨hzp, hmem⟩ := hTR i j k l z hz1 hz2
        rcases eq_or_ne j l with rfl | hjl
        · exact Or.inr (by rw [hzp]; exact hRRmeet i j k hik ⟨hpR i j, hmem⟩)
        · exact absurd hmem (fun h => hRRne i k j l hjl h)
      · obtain ⟨hzp, hmem⟩ := hTR k l i j z hz2 hz1
        rcases eq_or_ne j l with rfl | hjl
        · exact Or.inr (by rw [hzp]; exact hRRmeet k j i (Ne.symm hik) ⟨hpR k j, hmem⟩)
        · exact absurd hmem (fun h => hRRne k i l j (Ne.symm hjl) h)
      · rcases eq_or_ne j l with rfl | hjl
        · exact Or.inr (hRRmeet i j k hik ⟨hz1, hz2⟩)
        · exact absurd (hRRdisj i j k l hjl) (Set.nonempty_iff_ne_empty.1 ⟨z, hz1, hz2⟩)
  exact
    { arc := harcP
      x_injective := by
        intro i k hik
        by_contra hne
        exact (hΩij i k hne).ne_of_mem (hxxΩ i) (hik ▸ hxxΩ k) rfl
      y_injective := fun j l h => (hpinj 1 j 1 l h).2
      ne := fun i j hcon =>
        (hΩdisj i).ne_of_mem (hxxΩ i) (hcon ▸ hpC 1 j) rfl
      meet := fun i j k l hne =>
        subset_inter (hmeetHalf i j k l hne)
          (by rw [inter_comm]; exact hmeetHalf k l i j (Ne.symm hne)) }

/-! ### The Jordan curve theorem

Stated as `IsSeparating C`, the predicate `Schoenflies/CrosscutCells.lean` introduces and
`Schoenflies.ClosedPolygon.polygonal_jordan` establishes in the polygonal case. Unfolding it,
that is exactly the blueprint's statement: `inside C` and `outside C` are each a single region,
one bounded and one unbounded (`IsSeparating.isBounded_inside`,
`IsSeparating.not_isBounded_outside`), and both have `C` as boundary. Every consumer written
against the polygonal case therefore applies verbatim. -/

/-- A point of the curve is in the closure of any region it is accessible from — the reverse
inclusion of the boundary clause, packaged for both regions at once. -/
theorem subset_closure_of_accessible_dense
    (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ) (hC : IsJordanCurve C) {x : Plane}
    (hx : x ∉ C) : C ⊆ closure (connectedComponentIn Cᶜ x) := by
  refine (accessible_dense harc hC hx).trans (closure_mono ?_) |>.trans closure_closure.subset
  rintro p ⟨hpC, hacc⟩
  exact hacc.mem_closure fun hcon => absurd hpC (connectedComponentIn_subset _ _ hcon)

/-- **`thm:jordan` (the Jordan curve theorem).** The complement of a Jordan curve has exactly
two regions, one bounded and one unbounded, and both have the curve as their boundary.

`harc` is `thm:arc-complement`. -/
theorem IsJordanCurve.isSeparating (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) : IsSeparating C := by
  have hCclosed : IsClosed C := hC.isClosed
  -- The unbounded region is the component of the outside of a large square.
  obtain ⟨base, hbase, hbaseub, hbaseuniq⟩ :=
    exists_unique_unbounded_connectedComponentIn_compl hC.isCompact
  have houtside : Schoenflies.outside C = connectedComponentIn Cᶜ base := by
    apply Subset.antisymm
    · intro z hz
      rw [← hbaseuniq z hz.1 hz.2]
      exact mem_connectedComponentIn hz.1
    · intro z hz
      refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
      rw [← connectedComponentIn_eq hz]
      exact hbaseub
  -- The complement has a bounded component too: at most one component is unbounded.
  obtain ⟨z₀, hz₀⟩ : (Schoenflies.inside C).Nonempty := by
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := hC.exists_connectedComponentIn_ne
    by_cases h₁ : IsBounded (connectedComponentIn Cᶜ u₁)
    · exact ⟨u₁, hu₁, h₁⟩
    · by_cases h₂ : IsBounded (connectedComponentIn Cᶜ u₂)
      · exact ⟨u₂, hu₂, h₂⟩
      · exact absurd ((hbaseuniq u₁ hu₁ h₁).trans (hbaseuniq u₂ hu₂ h₂).symm) hne
  -- Any two points of the bounded part share a component: a third would give three.
  have hsame : ∀ z ∈ Schoenflies.inside C,
      connectedComponentIn Cᶜ z = connectedComponentIn Cᶜ z₀ := by
    intro z hz
    by_contra hne
    -- `z`, `z₀` and the unbounded base would be three distinct components.
    refine not_three_components harc hC (q := ![z, z₀, base]) ?_ ?_
    · intro i; fin_cases i
      exacts [hz.1, hz₀.1, hbase]
    · have hzb : connectedComponentIn Cᶜ z ≠ connectedComponentIn Cᶜ base := fun hcon =>
        hbaseub (hcon ▸ hz.2)
      have hz₀b : connectedComponentIn Cᶜ z₀ ≠ connectedComponentIn Cᶜ base := fun hcon =>
        hbaseub (hcon ▸ hz₀.2)
      intro i k hik
      fin_cases i <;> fin_cases k <;>
        first
          | exact absurd rfl hik
          | exact hne
          | exact hzb
          | exact hz₀b
          | exact Ne.symm hne
          | exact Ne.symm hzb
          | exact Ne.symm hz₀b
  have hinside : Schoenflies.inside C = connectedComponentIn Cᶜ z₀ := by
    refine Subset.antisymm (fun z hz => ?_) (connectedComponentIn_subset_inside hz₀)
    rw [← hsame z hz]
    exact mem_connectedComponentIn hz.1
  refine ⟨hC, ?_, ?_, ?_, ?_⟩
  · rw [hinside]
    exact ⟨⟨z₀, mem_connectedComponentIn hz₀.1⟩, isPreconnected_connectedComponentIn⟩
  · rw [houtside]
    exact ⟨⟨base, mem_connectedComponentIn hbase⟩, isPreconnected_connectedComponentIn⟩
  · apply Subset.antisymm
    · rw [hinside]; exact Plane.frontier_connectedComponentIn_compl_subset hCclosed z₀
    · rw [(Schoenflies.isOpen_inside hCclosed).frontier_eq]
      exact subset_sdiff.2 ⟨hinside ▸ subset_closure_of_accessible_dense harc hC hz₀.1,
        Set.disjoint_left.2 fun z hzC hzin => hzin.1 hzC⟩
  · apply Subset.antisymm
    · rw [houtside]; exact Plane.frontier_connectedComponentIn_compl_subset hCclosed base
    · rw [(Schoenflies.isOpen_outside hCclosed).frontier_eq]
      exact subset_sdiff.2 ⟨houtside ▸ subset_closure_of_accessible_dense harc hC hbase,
        Set.disjoint_left.2 fun z hzC hzout => hzout.1 hzC⟩

end Schoenflies
