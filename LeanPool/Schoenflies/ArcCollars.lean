/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Concatenate
public import LeanPool.Schoenflies.CrosscutAtMostTwo
public import LeanPool.Schoenflies.StripLocal

/-!
# Two-sided collars along a simple polygonal arc

`Schoenflies/CrosscutAtMostTwo.lean` proves Lemma "At most two sides" assuming
`Schoenflies.HasArcCollars`: every compact piece of `D ∩ P` has a two-sided collar inside `D`.
This module discharges that hypothesis for a polygonal arc presented by its vertex list.

## The route: a linear chain, not a cyclic one

`Schoenflies/Strip.lean` builds the collar of blueprint Lemma 1.8 for a `ClosedPolygon`, whose
vertex family is indexed by `ZMod (m + 3)`. The apparatus is redone here on a *linear* index —
route (A) of the three the blueprint's arc case admits. Closing the arc into a polygon (route
(B)) was rejected: it needs a return path from one end of the arc back to the other meeting the
arc only at its ends, and producing one is the two-sided collar of the arc all over again.

Two things change from the cyclic case, and both make the arc case *easier*.

* **There are no sectors at the two extreme vertices.** An edge block already stops short of
  both of its endpoints by the trim `lam`, so the collar of the whole chain of blocks is an open
  neighbourhood of the arc minus two small end caps — which is all that is wanted, because the
  compact piece `K` sits at positive distance from the two endpoints of a crosscut (they are
  outside `D` and `K` is inside).
* **The neighbourhood is open by construction.** The collar of a closed polygon has to contain
  the curve, so `StripData.nbhd` is a union of open sets *plus the carrier*, and
  `StripData.nbhd_eq` is needed to see that it is open. Here `nbhd` is defined outright as the
  union of the vertex balls and the edge tubes; it contains the arc only away from its two ends,
  and there is nothing to prove.

What does **not** change is the germ argument at a corner: `Plane.germs_split'` is applied
exactly as in the cyclic case, with the incoming ray at vertex `i + 1` written `A.back i` and
the outgoing one `A.tang (i + 1)`.

## The one thing left open

`PolyArc` is a *presentation*: a simple polygonal arc given by its vertex list, exactly as
`ClosedPolygon` presents a simple closed polygonal curve. Everything is proved for a `PolyArc`,
and `Schoenflies.polyArc_crosscut_at_most_two` is Lemma "At most two sides" for one with no
hypothesis left standing at all. What is *not* proved is the converse presentation statement:
that a set which happens to be a simple polygonal arc is the carrier of some `PolyArc`. That is
the arc analogue of `Schoenflies.exists_closedPolygon`, which `Schoenflies/Realization.lean`
proves for a Jordan curve; it is normalisation, not geometry.
`Schoenflies.hasArcCollars` therefore carries it as the hypothesis
`Schoenflies.IsPolyArcCarrier`. See the note at the end of the file for the route.

The presentation is checked in both other directions, so neither the structure nor the
hypothesis is vacuous or accidentally false: `Schoenflies.PolyArc.isArcBetween_carrier` and
`Schoenflies.PolyArc.isPolygonal_carrier` say the carrier of a `PolyArc` *is* a simple polygonal
arc, and `Schoenflies.isPolyArcCarrier_segment` exhibits one.

## Blueprint

* `Schoenflies.PolyArc` — a simple polygonal arc presented by its vertex list; the arc analogue
  of `Schoenflies.ClosedPolygon`.
* `Schoenflies.ArcStrip` — the constants of blueprint Lemma 1.8 (b), as a structure: the cone
  radius `R`, the trim `lam`, the half-width `rho`, and the separations they satisfy. The arc
  analogue of `Schoenflies.StripData`, with the two clauses that make the collar fit inside the
  prescribed region and clear of the two endpoints.
* `Schoenflies.ArcStrip.nbhd`, `.sideL`, `.sideR` — the collar `N` and its two tracks `N_L`,
  `N_R` of Lemma 1.8 (b).
* `Schoenflies.ArcStrip.nbhd_diff_carrier`, `.isConnected_sideL`, `.isConnected_sideR`,
  `.sideL_disjoint_sideR`, `.subset_closure_sideL`, `.subset_closure_sideR` — the clauses of
  Lemma 1.8 (b).
* `Schoenflies.exists_arcStrip` — the constants exist. The arc analogue of
  `Schoenflies.exists_stripData_subset`.
* `Schoenflies.ArcStrip.collar`, `Schoenflies.PolyArc.exists_arcCollar`,
  `Schoenflies.PolyArc.hasArcCollars` — Lemma 1.8 (b) itself, as the interface
  `Schoenflies.ArcCollar` that `Schoenflies/CrosscutAtMostTwo.lean` consumes.
* `Schoenflies.PolyArc.isArcBetween_carrier`, `Schoenflies.PolyArc.isPolygonal_carrier` — the
  carrier of a `PolyArc` is a simple polygonal arc between its two extreme vertices.
* `Schoenflies.polyArc_crosscut_at_most_two`,
  `Schoenflies.polyArc_crosscut_components_exhaust` — Lemma "At most two sides" for a polygonal
  arc presented by a vertex list, with no further assumptions.
* `Schoenflies.hasArcCollars`, `Schoenflies.crosscut_at_most_two_of_polyArc`,
  `Schoenflies.crosscut_components_exhaust_of_polyArc` — the same for a *set* `P` presented by
  `Schoenflies.IsPolyArcCarrier`.
* `Schoenflies.segmentPolyArc`, `Schoenflies.isPolyArcCarrier_segment` — a straight crosscut as
  a `PolyArc`, which recovers `Schoenflies.hasArcCollars_segment` as a special case.
-/

public section

open Metric Set

namespace Schoenflies

open Plane

/-! ## Simple polygonal arcs

A polygonal arc is presented by its vertex list `v 0, …, v (n + 1)`; its edges are the `n + 1`
segments `edge i = [v i, v (i + 1)]` for `i ≤ n`, and its *interior* vertices — the ones that
carry a corner, and hence a sector of the collar — are `v 1, …, v n`.

The vertex function is indexed by all of `ℕ` and asked to be injective outright, rather than
injective on `{0, …, n + 1}`. Nothing past `v (n + 1)` is ever looked at except through
`A.tang i` and `A.len i`, which are only well behaved when `v i ≠ v (i + 1)`; asking for global
injectivity buys that for free and removes an `i ≤ n` side condition from every lemma about the
edge frame. It costs a discharger nothing: a finite vertex list is padded to an injective
sequence by any tail of fresh points. -/

/-- A **simple polygonal arc**, presented by its vertex list. The arc runs from `vertex 0` to
`vertex (n + 1)` along the `n + 1` edges `[vertex i, vertex (i + 1)]`, `i ≤ n`. -/
structure PolyArc (n : ℕ) where
  /-- The vertices, in order along the arc. Only `vertex 0, …, vertex (n + 1)` are on it. -/
  vertex : ℕ → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}
  /-- No redundant vertex: the two edges at an *interior* vertex are not collinear. The two
  extreme vertices carry no condition, because the collar puts no sector there. -/
  corner : ∀ i < n, det (vertex i - vertex (i + 1)) (vertex (i + 2) - vertex (i + 1)) ≠ 0

/-! ### The turned vector of a reversed direction -/

namespace Plane

/-- Turning the reverse of a vector is the reverse of turning it. -/
theorem perp_neg (u : Plane) : perp (-u) = -perp u := by
  ext k; fin_cases k <;> simp [perp]

end Plane

namespace PolyArc

variable {n : ℕ} (A : PolyArc n) (i j : ℕ) (c t s : ℝ)

/-- The length of edge `i`. -/
noncomputable def len : ℝ := ‖A.vertex (i + 1) - A.vertex i‖

/-- The unit tangent of edge `i`, which is also the outgoing ray at `vertex i`. -/
noncomputable def tang : Plane := dir (A.vertex (i + 1) - A.vertex i)

/-- The incoming ray at `vertex (i + 1)`: the direction back along edge `i`. -/
noncomputable def back : Plane := dir (A.vertex i - A.vertex (i + 1))

/-- The point at progress `t` and signed offset `s` in the frame of edge `i`. -/
noncomputable def off : Plane := A.vertex i + t • A.tang i + s • perp (A.tang i)

/-- The point of edge `i` at distance `c` from its initial vertex. -/
noncomputable def pt : Plane := A.off i c 0

/-- Edge `i` of the arc. -/
def edge : Set Plane := segment ℝ (A.vertex i) (A.vertex (i + 1))

/-- The carrier of the arc: the union of its `n + 1` edges. -/
def carrier : Set Plane := ⋃ i, ⋃ (_ : i ≤ n), A.edge i

variable {A i j c t s}

theorem mem_carrier_iff {x : Plane} : x ∈ A.carrier ↔ ∃ i ≤ n, x ∈ A.edge i := by
  simp only [carrier, Set.mem_iUnion, exists_prop]

theorem edge_subset_carrier (hi : i ≤ n) : A.edge i ⊆ A.carrier :=
  fun _ hx => mem_carrier_iff.2 ⟨i, hi, hx⟩

theorem vertex_ne : A.vertex i ≠ A.vertex (i + 1) := fun h => by
  have := A.vertex_inj h; omega

theorem sub_ne_zero_of_edge : A.vertex (i + 1) - A.vertex i ≠ 0 :=
  sub_ne_zero.2 (vertex_ne (A := A) (i := i)).symm

theorem len_pos : 0 < A.len i := norm_pos_iff.2 sub_ne_zero_of_edge

theorem isDirection_tang : IsDirection (A.tang i) := isDirection_dir sub_ne_zero_of_edge

theorem len_smul_tang : (A.len i) • A.tang i = A.vertex (i + 1) - A.vertex i := by
  rw [tang, dir, smul_smul, len, mul_inv_cancel₀ (norm_ne_zero_iff.2 sub_ne_zero_of_edge),
    one_smul]

theorem vertex_succ_eq : A.vertex (i + 1) = A.vertex i + (A.len i) • A.tang i := by
  rw [len_smul_tang]; module

/-- The incoming ray at `vertex (i + 1)` is the reverse of the tangent of edge `i`. -/
theorem back_eq : A.back i = -A.tang i := by
  rw [back, tang, dir, dir, norm_sub_rev (A.vertex i) (A.vertex (i + 1))]
  module

theorem isDirection_back : IsDirection (A.back i) := by
  rw [back_eq, IsDirection, norm_neg]; exact isDirection_tang.norm

theorem perp_back : perp (A.back i) = -perp (A.tang i) := by
  rw [back_eq, perp_neg]

/-- The corner condition, read on the two unit rays at an interior vertex. -/
theorem det_rays_ne_zero (hi : i < n) : det (A.back i) (A.tang (i + 1)) ≠ 0 := by
  obtain ⟨c₁, hc₁, h₁⟩ := dir_eq_smul (sub_ne_zero.2 (vertex_ne (A := A) (i := i)))
  obtain ⟨c₂, hc₂, h₂⟩ := dir_eq_smul (sub_ne_zero_of_edge (A := A) (i := i + 1))
  rw [back, tang, h₁, h₂, det_smul_left, det_smul_right]
  exact mul_ne_zero hc₁.ne' (mul_ne_zero hc₂.ne' (A.corner i hi))

/-! ### The edge frame -/

theorem off_zero_zero : A.off i 0 0 = A.vertex i := by rw [off]; module

theorem pt_zero : A.pt i 0 = A.vertex i := off_zero_zero

theorem pt_eq : A.pt i c = A.vertex i + c • A.tang i := by rw [pt, off, zero_smul, add_zero]

theorem pt_len : A.pt i (A.len i) = A.vertex (i + 1) := by
  rw [pt_eq, ← vertex_succ_eq]

theorem off_sub_vertex : A.off i t s - A.vertex i = t • A.tang i + s • perp (A.tang i) := by
  rw [off]; module

theorem pt_sub_vertex : A.pt i c - A.vertex i = c • A.tang i := by
  rw [pt, off_sub_vertex, zero_smul, add_zero]

theorem dist_pt_vertex : dist (A.pt i c) (A.vertex i) = |c| := by
  rw [dist_eq_norm, pt_sub_vertex, norm_smul, Real.norm_eq_abs, isDirection_tang.norm, mul_one]

theorem off_sub_vertex_succ :
    A.off i t s - A.vertex (i + 1) = (t - A.len i) • A.tang i + s • perp (A.tang i) := by
  rw [off, vertex_succ_eq]; module

/-- The same difference written in the frame of the incoming ray, which is the form the germ
argument at `vertex (i + 1)` consumes. -/
theorem off_sub_vertex_succ_ray :
    A.off i t s - A.vertex (i + 1) =
      (A.len i - t) • A.back i - s • perp (A.back i) := by
  rw [off_sub_vertex_succ, perp_back, back_eq]
  module

theorem dist_off_vertex_le : dist (A.off i t s) (A.vertex i) ≤ |t| + |s| := by
  rw [dist_eq_norm, off_sub_vertex]
  calc ‖t • A.tang i + s • perp (A.tang i)‖ ≤ ‖t • A.tang i‖ + ‖s • perp (A.tang i)‖ :=
        norm_add_le _ _
    _ = |t| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

theorem dist_off_vertex_succ_le :
    dist (A.off i t s) (A.vertex (i + 1)) ≤ |t - A.len i| + |s| := by
  rw [dist_eq_norm, off_sub_vertex_succ]
  calc ‖(t - A.len i) • A.tang i + s • perp (A.tang i)‖
      ≤ ‖(t - A.len i) • A.tang i‖ + ‖s • perp (A.tang i)‖ := norm_add_le _ _
    _ = |t - A.len i| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

theorem dist_pt_vertex_succ : dist (A.pt i c) (A.vertex (i + 1)) = |c - A.len i| := by
  rw [pt, dist_eq_norm, off_sub_vertex_succ, zero_smul, add_zero, norm_smul, Real.norm_eq_abs,
    isDirection_tang.norm, mul_one]

theorem dist_off_pt : dist (A.off i t s) (A.pt i t) = |s| := by
  rw [pt, dist_eq_norm, show A.off i t s - A.off i t 0 = s • perp (A.tang i) by
    rw [off, off]; module, norm_smul, Real.norm_eq_abs, norm_perp, isDirection_tang.norm,
    mul_one]

@[simp] theorem coordAlong_off : coordAlong (A.vertex i) (A.tang i) (A.off i t s) = t :=
  coordAlong_param isDirection_tang _ _ _

@[simp] theorem coordAcross_off : coordAcross (A.vertex i) (A.tang i) (A.off i t s) = s :=
  coordAcross_param isDirection_tang _ _ _

/-- Every point is the point of some frame position, so the two coordinates identify it. -/
theorem off_coord (A : PolyArc n) (i : ℕ) (x : Plane) :
    x = A.off i (coordAlong (A.vertex i) (A.tang i) x) (coordAcross (A.vertex i) (A.tang i) x) :=
  frame_decomp isDirection_tang _ _

/-! ### Edges as sets -/

theorem mem_edge_iff {x : Plane} :
    x ∈ A.edge i ↔ ∃ c ∈ Set.Icc (0 : ℝ) (A.len i), x = A.pt i c := by
  rw [edge, segment_eq_image' ℝ]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    refine ⟨θ * A.len i, ⟨mul_nonneg hθ0 len_pos.le, ?_⟩, ?_⟩
    · nlinarith [len_pos (A := A) (i := i)]
    · rw [pt_eq, ← len_smul_tang]
      simp [smul_smul]
  · rintro ⟨c, ⟨hc0, hc1⟩, rfl⟩
    refine ⟨c / A.len i, ⟨div_nonneg hc0 len_pos.le, ?_⟩, ?_⟩
    · rw [div_le_one len_pos]; exact hc1
    · rw [pt_eq, ← len_smul_tang]
      simp [smul_smul, div_mul_cancel₀ _ (len_pos (A := A) (i := i)).ne']

theorem pt_mem_edge (hc : c ∈ Set.Icc (0 : ℝ) (A.len i)) : A.pt i c ∈ A.edge i :=
  mem_edge_iff.2 ⟨c, hc, rfl⟩

theorem vertex_mem_edge : A.vertex i ∈ A.edge i := by
  rw [← pt_zero]; exact pt_mem_edge ⟨le_refl _, len_pos.le⟩

theorem vertex_succ_mem_edge : A.vertex (i + 1) ∈ A.edge i := by
  rw [← pt_len]; exact pt_mem_edge ⟨len_pos.le, le_refl _⟩

theorem vertex_mem_carrier (hi : i ≤ n) : A.vertex i ∈ A.carrier :=
  edge_subset_carrier hi vertex_mem_edge

/-- A point of edge `i`, seen from the vertex it leaves, is a nonnegative multiple of the
outgoing ray. -/
theorem mem_edge_sub {x : Plane} (hx : x ∈ A.edge i) :
    ∃ c : ℝ, 0 ≤ c ∧ x - A.vertex i = c • A.tang i := by
  obtain ⟨c, ⟨hc0, _⟩, rfl⟩ := mem_edge_iff.1 hx
  exact ⟨c, hc0, pt_sub_vertex⟩

/-- A point of edge `i`, seen from the vertex it arrives at, is a nonnegative multiple of the
incoming ray there. -/
theorem mem_edge_sub_succ {x : Plane} (hx : x ∈ A.edge i) :
    ∃ c : ℝ, 0 ≤ c ∧ x - A.vertex (i + 1) = c • A.back i := by
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := mem_edge_iff.1 hx
  refine ⟨A.len i - c, by linarith, ?_⟩
  rw [pt, off_sub_vertex_succ, back_eq, zero_smul, add_zero]
  module

/-- Walking back along the incoming ray from `vertex (i + 1)` traverses edge `i`. -/
theorem vertex_add_smul_back : A.vertex (i + 1) + c • A.back i = A.pt i (A.len i - c) := by
  rw [pt_eq, back_eq, vertex_succ_eq]
  module

theorem mem_edge_of_smul_back (hc0 : 0 ≤ c) (hc1 : c ≤ A.len i) :
    A.vertex (i + 1) + c • A.back i ∈ A.edge i := by
  rw [vertex_add_smul_back]
  exact pt_mem_edge ⟨by linarith, by linarith⟩

theorem mem_edge_of_smul_tang (hc0 : 0 ≤ c) (hc1 : c ≤ A.len i) :
    A.vertex i + c • A.tang i ∈ A.edge i := by
  rw [← pt_eq]; exact pt_mem_edge ⟨hc0, hc1⟩

theorem isCompact_edge : IsCompact (A.edge i) := isCompact_segment _ _

theorem continuous_pt (A : PolyArc n) (i : ℕ) : Continuous (A.pt i) := by
  have h : A.pt i = fun c : ℝ => A.vertex i + c • A.tang i := funext fun _ => pt_eq
  rw [h]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-! ### What simplicity gives -/

/-- **Simplicity, first form.** A vertex lies on no edge but the (at most two) edges incident
to it. -/
theorem vertex_notMem_edge (hi : i ≤ n + 1) (hj : j ≤ n) (h1 : i ≠ j) (h2 : i ≠ j + 1) :
    A.vertex i ∉ A.edge j := by
  intro hx
  rcases Nat.lt_or_ge i (n + 1) with hlt | hge
  · -- `vertex i` is also the initial vertex of edge `i`, which exists.
    have hi' : i ≤ n := by omega
    have hmem : A.vertex i ∈ A.edge j ∩ A.edge i := ⟨hx, vertex_mem_edge⟩
    have hsub := A.edges_meet j hj i hi' (Ne.symm h1) hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
    rcases hsub with h | h
    · exact h1 (A.vertex_inj h)
    · exact h2 (A.vertex_inj h)
  · -- `vertex (n + 1)` is the terminal vertex of edge `n`.
    have hin : i = n + 1 := by omega
    subst hin
    have hjn : j ≠ n := fun h => h2 (by omega)
    have hmem : A.vertex (n + 1) ∈ A.edge j ∩ A.edge n := ⟨hx, vertex_succ_mem_edge⟩
    have hsub := A.edges_meet j hj n (le_refl n) hjn hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
    rcases hsub with h | h
    · exact h1 (A.vertex_inj h)
    · exact h2 (A.vertex_inj h)

/-- The trimmed core of edge `i`: the points at distance at least `lam` from both endpoints. -/
def trimmed (A : PolyArc n) (i : ℕ) (lam : ℝ) : Set Plane :=
  A.pt i '' Set.Icc lam (A.len i - lam)

theorem pt_mem_trimmed {lam : ℝ} (hc : c ∈ Set.Icc lam (A.len i - lam)) :
    A.pt i c ∈ A.trimmed i lam := ⟨c, hc, rfl⟩

theorem isCompact_trimmed {lam : ℝ} : IsCompact (A.trimmed i lam) :=
  isCompact_Icc.image (A.continuous_pt i)

theorem trimmed_subset_edge {lam : ℝ} (hlam : 0 < lam) : A.trimmed i lam ⊆ A.edge i := by
  rintro _ ⟨c, hc, rfl⟩
  exact pt_mem_edge ⟨le_trans hlam.le hc.1, le_trans hc.2 (by linarith)⟩

/-- **Simplicity, second form.** The trimmed core of an edge misses every other edge: the two
common points `edges_meet` allows are the endpoints, and the trim removes them. -/
theorem trimmed_disjoint_edge {lam : ℝ} (hlam : 0 < lam) (hi : i ≤ n) (hj : j ≤ n) (hij : j ≠ i) :
    Disjoint (A.trimmed i lam) (A.edge j) := by
  rw [Set.disjoint_left]
  rintro x ⟨c, hc, rfl⟩ hx
  have hc0 : (0 : ℝ) ≤ c := le_trans hlam.le hc.1
  have hcl : c ≤ A.len i := le_trans hc.2 (by linarith)
  have hmem : A.pt i c ∈ A.edge i ∩ A.edge j := ⟨pt_mem_edge ⟨hc0, hcl⟩, hx⟩
  have hsub := A.edges_meet i hi j hj (Ne.symm hij) hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · have h0 : |c| = 0 := by rw [← dist_pt_vertex (A := A) (i := i) (c := c), h, dist_self]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.1]
  · have h0 : |c - A.len i| = 0 := by
      rw [← dist_pt_vertex_succ (A := A) (i := i) (c := c), h, dist_self]
    rw [abs_of_nonpos (by linarith)] at h0
    linarith [hc.2]

/-! ### The four germs at an interior vertex

`Plane.germs_split'` applied at the interior vertex `v (i + 1)`, whose incoming ray is
`A.back i` and whose outgoing ray is `A.tang (i + 1)`. The smallness of the offset is left as a
hypothesis; the block versions supply it from the `germ` field of an `ArcStrip`. -/

theorem off_sub_mem_arcL_start (hi : i < n) (hs : 0 < s)
    (hsm : s * |inner ℝ (A.back i) (A.tang (i + 1))| <
      t * |det (A.back i) (A.tang (i + 1))|) :
    A.off (i + 1) t s - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := by
  rw [off_sub_vertex]
  exact (germs_split' (det_rays_ne_zero hi) hs hsm).1.2

theorem off_sub_mem_arcR_start (hi : i < n) (hs : s < 0)
    (hsm : (-s) * |inner ℝ (A.back i) (A.tang (i + 1))| <
      t * |det (A.back i) (A.tang (i + 1))|) :
    A.off (i + 1) t s - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := by
  have h : A.off (i + 1) t s - A.vertex (i + 1) =
      t • A.tang (i + 1) - (-s) • perp (A.tang (i + 1)) := by
    rw [off_sub_vertex]; module
  rw [h]
  exact (germs_split' (det_rays_ne_zero hi) (by linarith) hsm).2.2

theorem off_sub_mem_arcL_finish (hi : i < n) (hs : 0 < s)
    (hsm : s * |inner ℝ (A.back i) (A.tang (i + 1))| <
      (A.len i - t) * |det (A.back i) (A.tang (i + 1))|) :
    A.off i t s - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := by
  rw [off_sub_vertex_succ_ray]
  exact (germs_split' (det_rays_ne_zero hi) hs hsm).1.1

theorem off_sub_mem_arcR_finish (hi : i < n) (hs : s < 0)
    (hsm : (-s) * |inner ℝ (A.back i) (A.tang (i + 1))| <
      (A.len i - t) * |det (A.back i) (A.tang (i + 1))|) :
    A.off i t s - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := by
  have h : A.off i t s - A.vertex (i + 1) =
      (A.len i - t) • A.back i + (-s) • perp (A.back i) := by
    rw [off_sub_vertex_succ_ray]; module
  rw [h]
  exact (germs_split' (det_rays_ne_zero hi) (by linarith) hsm).2.1

end PolyArc

/-! ## The constants

`ArcStrip` is the arc analogue of `Schoenflies.StripData`: the blueprint's "choose the blocks so
that consecutive ones overlap and nonadjacent closures are disjoint", with every constant named.
Three fields have no counterpart in the closed case, and they are what makes the collar a collar
*of `K` inside `D`*: `ball_subset` and `tube_subset` put every piece inside the prescribed open
set, and `sep_ends` keeps `K` clear of the two ends of the arc, where the collar has no pieces.

`sep_ends` is not a restriction in the intended application: the two endpoints of a crosscut lie
outside `D` and `K` lies inside, so the distance from `K` to either endpoint is positive and `R`
is chosen below it. -/

/-- The constants of the collar of a compact piece `K` of the simple polygonal arc `A`, inside a
prescribed open set `D`. -/
structure ArcStrip {n : ℕ} (A : PolyArc n) (D K : Set Plane) where
  /-- The radius of the vertex sectors. -/
  R : ℝ
  /-- The distance by which an edge block stops short of each endpoint of its edge. -/
  lam : ℝ
  /-- The half-width of an edge block. -/
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_lam : rho < lam
  /-- The sectors reach past the ends of the blocks they have to overlap. -/
  two_lam_lt_R : 2 * lam < R
  /-- The blocks are nonempty, with room to spare at both ends. -/
  four_lam_lt_len : ∀ i ≤ n, 4 * lam < A.len i
  /-- A sector does not run past the far end of an incident edge. -/
  R_le_len : ∀ i ≤ n, R ≤ A.len i
  /-- Distinct vertices are `2R` apart, so distinct sectors are disjoint. -/
  sep_vertex : ∀ i ≤ n + 1, ∀ j ≤ n + 1, i ≠ j → 2 * R ≤ dist (A.vertex i) (A.vertex j)
  /-- A vertex is `2R` away from every nonincident edge. -/
  sep_vertex_edge : ∀ i ≤ n + 1, ∀ j ≤ n, i ≠ j → i ≠ j + 1 →
    ∀ y ∈ A.edge j, 2 * R ≤ dist (A.vertex i) y
  /-- The trimmed edge `i` is `2 * rho` away from every other edge. -/
  sep_trim_edge : ∀ i ≤ n, ∀ j ≤ n, j ≠ i → ∀ c ∈ Set.Icc lam (A.len i - lam),
    ∀ y ∈ A.edge j, 2 * rho ≤ dist (A.pt i c) y
  /-- **The vertex-matching threshold**, at the interior vertices only. -/
  germ : ∀ i < n, rho * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) ≤
    lam * |det (A.back i) (A.tang (i + 1))|
  /-- The sector at an interior vertex is inside the prescribed open set. -/
  ball_subset : ∀ i < n, ball (A.vertex (i + 1)) R ⊆ D
  /-- The block of an edge is inside the prescribed open set: a `rho`-ball about a point of the
  trimmed core is. -/
  tube_subset : ∀ i ≤ n, ∀ c ∈ Set.Icc lam (A.len i - lam), ball (A.pt i c) rho ⊆ D
  /-- The compact piece is inside the arc… -/
  subset_carrier : K ⊆ A.carrier
  /-- …and clear of its two endpoints, where the collar has no pieces. -/
  sep_ends : ∀ x ∈ K, R ≤ dist x (A.vertex 0) ∧ R ≤ dist x (A.vertex (n + 1))

namespace ArcStrip

variable {n : ℕ} {A : PolyArc n} {D K : Set Plane} (S : ArcStrip A D K) {i j k : ℕ} {x : Plane}

theorem lam_pos : 0 < S.lam := lt_trans S.rho_pos S.rho_lt_lam

theorem R_pos : 0 < S.R := by have := S.lam_pos; linarith [S.two_lam_lt_R]

theorem rho_lt_R : S.rho < S.R := by
  have := S.lam_pos; have := S.rho_lt_lam; linarith [S.two_lam_lt_R]

theorem lam_lt_R : S.lam < S.R := by have := S.lam_pos; linarith [S.two_lam_lt_R]

/-! ### The four families of blocks -/

/-- The left block of edge `i`. -/
def blockL (i : ℕ) : Set Plane :=
  strip (A.vertex i) (A.tang i) S.lam (A.len i - S.lam) 0 S.rho

/-- The right block of edge `i`. -/
def blockR (i : ℕ) : Set Plane :=
  strip (A.vertex i) (A.tang i) S.lam (A.len i - S.lam) (-S.rho) 0

/-- The full tube of edge `i`: the trimmed edge thickened by `rho` on both sides. -/
def tube (i : ℕ) : Set Plane :=
  strip (A.vertex i) (A.tang i) S.lam (A.len i - S.lam) (-S.rho) S.rho

/-- The left sector at the interior vertex `vertex (i + 1)`. -/
def sectorL (i : ℕ) : Set Plane :=
  cone (A.vertex (i + 1)) (arcCCW (A.tang (i + 1)) (A.back i)) S.R

/-- The right sector at the interior vertex `vertex (i + 1)`. -/
def sectorR (i : ℕ) : Set Plane :=
  cone (A.vertex (i + 1)) (arcCCW (A.back i) (A.tang (i + 1))) S.R

/-- The `k`-th link of the left chain: the block of edge `0` to start with, and thereafter the
sector at `vertex k` glued to the block of edge `k`. Consecutive links overlap in the block of
the earlier edge, which is what makes the union connected. -/
def chainL (T : ArcStrip A D K) : ℕ → Set Plane
  | 0 => T.blockL 0
  | (k + 1) => T.sectorL k ∪ T.blockL (k + 1)

/-- The `k`-th link of the right chain. -/
def chainR (T : ArcStrip A D K) : ℕ → Set Plane
  | 0 => T.blockR 0
  | (k + 1) => T.sectorR k ∪ T.blockR (k + 1)

/-- The left track of the collar. -/
def sideL : Set Plane := ⋃ k, ⋃ (_ : k ≤ n), S.chainL k

/-- The right track of the collar. -/
def sideR : Set Plane := ⋃ k, ⋃ (_ : k ≤ n), S.chainR k

/-- The collar: the union of the edge tubes and the balls about the interior vertices. Unlike
the closed case it is *not* a neighbourhood of the whole arc — it stops short of the two
endpoints — and it is manifestly open. -/
def nbhd : Set Plane :=
  (⋃ i, ⋃ (_ : i ≤ n), S.tube i) ∪ (⋃ i, ⋃ (_ : i < n), ball (A.vertex (i + 1)) S.R)

theorem mem_blockL_iff : x ∈ S.blockL i ↔
    S.lam < coordAlong (A.vertex i) (A.tang i) x ∧
      coordAlong (A.vertex i) (A.tang i) x < A.len i - S.lam ∧
      0 < coordAcross (A.vertex i) (A.tang i) x ∧
      coordAcross (A.vertex i) (A.tang i) x < S.rho := Iff.rfl

theorem mem_blockR_iff : x ∈ S.blockR i ↔
    S.lam < coordAlong (A.vertex i) (A.tang i) x ∧
      coordAlong (A.vertex i) (A.tang i) x < A.len i - S.lam ∧
      -S.rho < coordAcross (A.vertex i) (A.tang i) x ∧
      coordAcross (A.vertex i) (A.tang i) x < 0 := Iff.rfl

theorem mem_tube_iff : x ∈ S.tube i ↔
    S.lam < coordAlong (A.vertex i) (A.tang i) x ∧
      coordAlong (A.vertex i) (A.tang i) x < A.len i - S.lam ∧
      -S.rho < coordAcross (A.vertex i) (A.tang i) x ∧
      coordAcross (A.vertex i) (A.tang i) x < S.rho := Iff.rfl

theorem mem_blockL_off {t s : ℝ} : A.off i t s ∈ S.blockL i ↔
    S.lam < t ∧ t < A.len i - S.lam ∧ 0 < s ∧ s < S.rho := by
  rw [mem_blockL_iff, PolyArc.coordAlong_off, PolyArc.coordAcross_off]

theorem mem_blockR_off {t s : ℝ} : A.off i t s ∈ S.blockR i ↔
    S.lam < t ∧ t < A.len i - S.lam ∧ -S.rho < s ∧ s < 0 := by
  rw [mem_blockR_iff, PolyArc.coordAlong_off, PolyArc.coordAcross_off]

theorem mem_tube_off {t s : ℝ} : A.off i t s ∈ S.tube i ↔
    S.lam < t ∧ t < A.len i - S.lam ∧ -S.rho < s ∧ s < S.rho := by
  rw [mem_tube_iff, PolyArc.coordAlong_off, PolyArc.coordAcross_off]

theorem isOpen_blockL : IsOpen (S.blockL i) := isOpen_strip _ _ _ _ _ _
theorem isOpen_blockR : IsOpen (S.blockR i) := isOpen_strip _ _ _ _ _ _
theorem isOpen_tube : IsOpen (S.tube i) := isOpen_strip _ _ _ _ _ _
theorem isOpen_sectorL : IsOpen (S.sectorL i) := isOpen_cone (isOpen_arcCCW _ _)
theorem isOpen_sectorR : IsOpen (S.sectorR i) := isOpen_cone (isOpen_arcCCW _ _)

theorem convex_blockL : Convex ℝ (S.blockL i) := convex_strip _ _ _ _ _ _
theorem convex_blockR : Convex ℝ (S.blockR i) := convex_strip _ _ _ _ _ _

theorem isConnected_sectorL (hi : i < n) : IsConnected (S.sectorL i) :=
  isConnected_cone_arcCCW _
    (by rw [det_comm]; exact neg_ne_zero.2 (PolyArc.det_rays_ne_zero hi)) S.R_pos

theorem isConnected_sectorR (hi : i < n) : IsConnected (S.sectorR i) :=
  isConnected_cone_arcCCW _ (PolyArc.det_rays_ne_zero hi) S.R_pos

theorem blockL_subset_tube : S.blockL i ⊆ S.tube i := fun _ hy =>
  ⟨hy.1, hy.2.1, by linarith [S.rho_pos, hy.2.2.1], hy.2.2.2⟩

theorem blockR_subset_tube : S.blockR i ⊆ S.tube i := fun _ hy =>
  ⟨hy.1, hy.2.1, hy.2.2.1, by linarith [S.rho_pos, hy.2.2.2]⟩

theorem sectorL_subset_ball : S.sectorL i ⊆ ball (A.vertex (i + 1)) S.R := cone_subset_ball
theorem sectorR_subset_ball : S.sectorR i ⊆ ball (A.vertex (i + 1)) S.R := cone_subset_ball

/-- The foot of the perpendicular from a point of a tube lies on the trimmed edge, within `rho`
of the point. -/
theorem exists_foot (h : x ∈ S.tube i) :
    ∃ c ∈ Set.Icc S.lam (A.len i - S.lam), dist x (A.pt i c) < S.rho := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_tube_iff.1 h
  refine ⟨coordAlong (A.vertex i) (A.tang i) x, ⟨h1.le, h2.le⟩, ?_⟩
  rw [PolyArc.pt_eq, dist_foot PolyArc.isDirection_tang, abs_lt]
  exact ⟨h3, h4⟩

theorem pt_mem_edge_of_trim {c : ℝ} (hc : c ∈ Set.Icc S.lam (A.len i - S.lam)) :
    A.pt i c ∈ A.edge i :=
  PolyArc.pt_mem_edge ⟨le_trans S.lam_pos.le hc.1, le_trans hc.2 (by linarith [S.lam_pos])⟩

/-! ### The germ argument at an interior vertex -/

/-- The threshold hypothesis, specialised to a point of a block. -/
theorem germ_ineq (hi : i < n) {t s : ℝ} (ht : S.lam < t) (hs0 : 0 < s) (hs : s < S.rho) :
    s * |inner ℝ (A.back i) (A.tang (i + 1))| < t * |det (A.back i) (A.tang (i + 1))| := by
  have hd : 0 < |det (A.back i) (A.tang (i + 1))| := abs_pos.2 (PolyArc.det_rays_ne_zero hi)
  have habs : (0 : ℝ) ≤ |inner ℝ (A.back i) (A.tang (i + 1))| := abs_nonneg _
  have h1 : s * |inner ℝ (A.back i) (A.tang (i + 1))| ≤
      s * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) := by nlinarith
  have h2 : s * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) <
      S.rho * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) := by nlinarith
  have h3 := S.germ i hi
  nlinarith

/-- A point of the left block of edge `i + 1`, seen from the interior vertex it leaves, is in the
left arc there. -/
theorem blockL_sub_mem_arcL_start (hi : i < n) (h : x ∈ S.blockL (i + 1)) :
    x - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_blockL_iff.1 h
  rw [PolyArc.off_coord A (i + 1) x]
  exact PolyArc.off_sub_mem_arcL_start hi h3 (S.germ_ineq hi h1 h3 h4)

/-- A point of the left block of edge `i`, seen from the interior vertex it arrives at. -/
theorem blockL_sub_mem_arcL_finish (hi : i < n) (h : x ∈ S.blockL i) :
    x - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_blockL_iff.1 h
  rw [PolyArc.off_coord A i x]
  exact PolyArc.off_sub_mem_arcL_finish hi h3
    (S.germ_ineq hi (by linarith) h3 h4)

theorem blockR_sub_mem_arcR_start (hi : i < n) (h : x ∈ S.blockR (i + 1)) :
    x - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_blockR_iff.1 h
  rw [PolyArc.off_coord A (i + 1) x]
  exact PolyArc.off_sub_mem_arcR_start hi h4
    (S.germ_ineq hi h1 (by linarith) (by linarith))

theorem blockR_sub_mem_arcR_finish (hi : i < n) (h : x ∈ S.blockR i) :
    x - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := S.mem_blockR_iff.1 h
  rw [PolyArc.off_coord A i x]
  exact PolyArc.off_sub_mem_arcR_finish hi h4
    (S.germ_ineq hi (by linarith) (by linarith) (by linarith))

end ArcStrip

/-! ### Two shapes of bounded union

Both tracks and the collar are unions over an initial segment of `ℕ`. These two rewrites are the
only interface to that indexing. -/

theorem mem_iUnion_le_nat {α : Type*} {F : ℕ → Set α} {m : ℕ} {x : α} :
    x ∈ (⋃ i, ⋃ (_ : i ≤ m), F i) ↔ ∃ i ≤ m, x ∈ F i := by
  simp only [Set.mem_iUnion, exists_prop]

theorem mem_iUnion_lt_nat {α : Type*} {F : ℕ → Set α} {m : ℕ} {x : α} :
    x ∈ (⋃ i, ⋃ (_ : i < m), F i) ↔ ∃ i < m, x ∈ F i := by
  simp only [Set.mem_iUnion, exists_prop]

namespace ArcStrip

variable {n : ℕ} {A : PolyArc n} {D K : Set Plane} (S : ArcStrip A D K) {i j k : ℕ} {x : Plane}

/-! ### Nonadjacent blocks are disjoint

Every step is one of the separation hypotheses of `ArcStrip` against one of the two containments
`exists_foot` and `sectorL_subset_ball`. -/

/-- A tube misses every edge but its own. -/
theorem tube_notMem_edge (hi : i ≤ n) (hj : j ≤ n) (hji : j ≠ i) (h : x ∈ S.tube i) :
    x ∉ A.edge j := by
  intro hx
  obtain ⟨c, hc, hd⟩ := S.exists_foot h
  have := S.sep_trim_edge i hi j hj hji c hc x hx
  rw [dist_comm] at hd
  linarith [S.rho_pos]

/-- A block misses its own edge, because its points have nonzero offset. -/
theorem block_notMem_own_edge (h : x ∈ S.blockL i ∪ S.blockR i) : x ∉ A.edge i := by
  intro hx
  obtain ⟨c, -, rfl⟩ := PolyArc.mem_edge_iff.1 hx
  have hzero : coordAcross (A.vertex i) (A.tang i) (A.pt i c) = 0 := by
    rw [PolyArc.pt]; exact PolyArc.coordAcross_off
  rcases h with h | h
  · have hpos := (S.mem_blockL_iff.1 h).2.2.1
    rw [hzero] at hpos; exact lt_irrefl 0 hpos
  · have hneg := (S.mem_blockR_iff.1 h).2.2.2
    rw [hzero] at hneg; exact lt_irrefl 0 hneg

theorem block_notMem_carrier (hi : i ≤ n) (h : x ∈ S.blockL i ∪ S.blockR i) : x ∉ A.carrier := by
  intro hx
  obtain ⟨j, hj, hxj⟩ := PolyArc.mem_carrier_iff.1 hx
  by_cases hij : j = i
  · exact S.block_notMem_own_edge h (hij ▸ hxj)
  · have htube : x ∈ S.tube i :=
      h.elim (fun h => S.blockL_subset_tube h) (fun h => S.blockR_subset_tube h)
    exact S.tube_notMem_edge hi hj hij htube hxj

/-- A tube stays out of the sectors at every vertex other than its edge's own two. -/
theorem tube_notMem_ball_vertex (hi : i ≤ n) (hj : j ≤ n + 1) (hj1 : j ≠ i) (hj2 : j ≠ i + 1)
    (h : x ∈ S.tube i) : x ∉ ball (A.vertex j) S.R := by
  intro hx
  obtain ⟨c, hc, hd⟩ := S.exists_foot h
  have hsep := S.sep_vertex_edge j hj i hi hj1 hj2 _ (S.pt_mem_edge_of_trim hc)
  have h1 : dist (A.vertex j) (A.pt i c) ≤ dist (A.vertex j) x + dist x (A.pt i c) :=
    dist_triangle _ _ _
  rw [mem_ball, dist_comm] at hx
  linarith [S.rho_lt_R]

/-- A sector misses every edge that is not incident to its vertex. -/
theorem sector_notMem_far_edge (hi : i ≤ n + 1) (hj : j ≤ n) (h1 : i ≠ j) (h2 : i ≠ j + 1)
    (h : x ∈ ball (A.vertex i) S.R) : x ∉ A.edge j := by
  intro hx
  have := S.sep_vertex_edge i hi j hj h1 h2 x hx
  rw [mem_ball, dist_comm] at h
  linarith [S.R_pos]

/-- A sector misses the two edges incident to its vertex: their points lie on the two bounding
rays, and the arcs are open. -/
theorem sectorL_notMem_carrier (hi : i < n) (h : x ∈ S.sectorL i) : x ∉ A.carrier := by
  intro hx
  obtain ⟨j, hj, hxj⟩ := PolyArc.mem_carrier_iff.1 hx
  by_cases hji : j = i
  · rw [hji] at hxj
    obtain ⟨c, hc, he⟩ := PolyArc.mem_edge_sub_succ hxj
    exact ((notMem_arcCCW_smul (A.back i) (A.tang (i + 1)) hc).2) (he ▸ h.1)
  by_cases hjs : j = i + 1
  · rw [hjs] at hxj
    obtain ⟨c, hc, he⟩ := PolyArc.mem_edge_sub hxj
    exact ((notMem_arcCCW_smul (A.tang (i + 1)) (A.back i) hc).1) (he ▸ h.1)
  · exact S.sector_notMem_far_edge (by omega) hj (fun he => hjs he.symm)
      (fun he => hji (by omega)) h.2 hxj

theorem sectorR_notMem_carrier (hi : i < n) (h : x ∈ S.sectorR i) : x ∉ A.carrier := by
  intro hx
  obtain ⟨j, hj, hxj⟩ := PolyArc.mem_carrier_iff.1 hx
  by_cases hji : j = i
  · rw [hji] at hxj
    obtain ⟨c, hc, he⟩ := PolyArc.mem_edge_sub_succ hxj
    exact ((notMem_arcCCW_smul (A.back i) (A.tang (i + 1)) hc).1) (he ▸ h.1)
  by_cases hjs : j = i + 1
  · rw [hjs] at hxj
    obtain ⟨c, hc, he⟩ := PolyArc.mem_edge_sub hxj
    exact ((notMem_arcCCW_smul (A.tang (i + 1)) (A.back i) hc).2) (he ▸ h.1)
  · exact S.sector_notMem_far_edge (by omega) hj (fun he => hjs he.symm)
      (fun he => hji (by omega)) h.2 hxj

/-! ### The two tracks, as sets -/

theorem blockL_subset_chainL (k : ℕ) : S.blockL k ⊆ S.chainL k := by
  cases k with
  | zero => exact subset_rfl
  | succ k => exact subset_union_right

theorem blockR_subset_chainR (k : ℕ) : S.blockR k ⊆ S.chainR k := by
  cases k with
  | zero => exact subset_rfl
  | succ k => exact subset_union_right

theorem mem_sideL_iff :
    x ∈ S.sideL ↔ (∃ i ≤ n, x ∈ S.blockL i) ∨ (∃ i < n, x ∈ S.sectorL i) := by
  rw [sideL, mem_iUnion_le_nat]
  constructor
  · rintro ⟨k, hk, hxk⟩
    cases k with
    | zero => exact Or.inl ⟨0, Nat.zero_le n, hxk⟩
    | succ k =>
        rcases hxk with h | h
        · exact Or.inr ⟨k, by omega, h⟩
        · exact Or.inl ⟨k + 1, hk, h⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, hi, S.blockL_subset_chainL i h⟩
    · exact ⟨i + 1, by omega, Or.inl h⟩

theorem mem_sideR_iff :
    x ∈ S.sideR ↔ (∃ i ≤ n, x ∈ S.blockR i) ∨ (∃ i < n, x ∈ S.sectorR i) := by
  rw [sideR, mem_iUnion_le_nat]
  constructor
  · rintro ⟨k, hk, hxk⟩
    cases k with
    | zero => exact Or.inl ⟨0, Nat.zero_le n, hxk⟩
    | succ k =>
        rcases hxk with h | h
        · exact Or.inr ⟨k, by omega, h⟩
        · exact Or.inl ⟨k + 1, hk, h⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, hi, S.blockR_subset_chainR i h⟩
    · exact ⟨i + 1, by omega, Or.inl h⟩

theorem blockL_subset_sideL (hi : i ≤ n) : S.blockL i ⊆ S.sideL :=
  fun _ h => S.mem_sideL_iff.2 (Or.inl ⟨i, hi, h⟩)

theorem blockR_subset_sideR (hi : i ≤ n) : S.blockR i ⊆ S.sideR :=
  fun _ h => S.mem_sideR_iff.2 (Or.inl ⟨i, hi, h⟩)

theorem sectorL_subset_sideL (hi : i < n) : S.sectorL i ⊆ S.sideL :=
  fun _ h => S.mem_sideL_iff.2 (Or.inr ⟨i, hi, h⟩)

theorem sectorR_subset_sideR (hi : i < n) : S.sectorR i ⊆ S.sideR :=
  fun _ h => S.mem_sideR_iff.2 (Or.inr ⟨i, hi, h⟩)

theorem sideL_disjoint_carrier : Disjoint S.sideL A.carrier := by
  rw [Set.disjoint_left]
  intro y hy hc
  rcases S.mem_sideL_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact S.block_notMem_carrier hi (Or.inl h) hc
  · exact S.sectorL_notMem_carrier hi h hc

theorem sideR_disjoint_carrier : Disjoint S.sideR A.carrier := by
  rw [Set.disjoint_left]
  intro y hy hc
  rcases S.mem_sideR_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact S.block_notMem_carrier hi (Or.inr h) hc
  · exact S.sectorR_notMem_carrier hi h hc

theorem sideL_subset_nbhd : S.sideL ⊆ S.nbhd := by
  intro y hy
  rcases S.mem_sideL_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact Or.inl (mem_iUnion_le_nat.2 ⟨i, hi, S.blockL_subset_tube h⟩)
  · exact Or.inr (mem_iUnion_lt_nat.2 ⟨i, hi, S.sectorL_subset_ball h⟩)

theorem sideR_subset_nbhd : S.sideR ⊆ S.nbhd := by
  intro y hy
  rcases S.mem_sideR_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact Or.inl (mem_iUnion_le_nat.2 ⟨i, hi, S.blockR_subset_tube h⟩)
  · exact Or.inr (mem_iUnion_lt_nat.2 ⟨i, hi, S.sectorR_subset_ball h⟩)

/-! ### The collar minus the arc is exactly the two tracks -/

/-- **A vertex ball minus the arc is covered by the two sectors at that vertex.** A point of the
ball off the arc points in some direction from the vertex; that direction is either one of the
two incident rays — and then the point is *on* the incident edge, because `R_le_len` says the
sector does not run past the far end — or on one of the two arcs, and then the point is in the
corresponding sector. -/
theorem ball_diff_carrier_subset (hi : i < n) :
    ball (A.vertex (i + 1)) S.R \ A.carrier ⊆ S.sectorL i ∪ S.sectorR i := by
  rintro y ⟨hy, hyc⟩
  have hne : y - A.vertex (i + 1) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hyc (h ▸ PolyArc.vertex_mem_carrier (i := i + 1) (by omega))
  rcases mem_ray_or_mem_arcCCW' (PolyArc.det_rays_ne_zero hi) hne with
    ⟨c, hc, hcy⟩ | ⟨c, hc, hcy⟩ | harc | harc
  · -- Back along the incoming edge: the point lies on edge `i`.
    refine absurd ?_ hyc
    have hd : dist y (A.vertex (i + 1)) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        (PolyArc.isDirection_back (A := A) (i := i)).norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = A.vertex (i + 1) + c • A.back i := by rw [← hcy]; module
    rw [hy']
    exact PolyArc.edge_subset_carrier (by omega)
      (PolyArc.mem_edge_of_smul_back hc.le (le_trans hy.le (S.R_le_len i (by omega))))
  · -- Out along the outgoing edge: the point lies on edge `i + 1`.
    refine absurd ?_ hyc
    have hd : dist y (A.vertex (i + 1)) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        (PolyArc.isDirection_tang (A := A) (i := i + 1)).norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = A.vertex (i + 1) + c • A.tang (i + 1) := by rw [← hcy]; module
    rw [hy']
    exact PolyArc.edge_subset_carrier (by omega)
      (PolyArc.mem_edge_of_smul_tang hc.le (le_trans hy.le (S.R_le_len (i + 1) (by omega))))
  · exact Or.inr ⟨harc, hy⟩
  · exact Or.inl ⟨harc, hy⟩

/-- **A tube minus the arc is its two blocks.** -/
theorem tube_diff_carrier_subset (hi : i ≤ n) :
    S.tube i \ A.carrier ⊆ S.blockL i ∪ S.blockR i := by
  rintro y ⟨⟨h1, h2, h3, h4⟩, hyc⟩
  rcases lt_trichotomy (coordAcross (A.vertex i) (A.tang i) y) 0 with h | h | h
  · exact Or.inr (S.mem_blockR_iff.2 ⟨h1, h2, h3, h⟩)
  · refine absurd ?_ hyc
    have hy0 : y = A.pt i (coordAlong (A.vertex i) (A.tang i) y) := by
      rw [PolyArc.pt, ← h]; exact PolyArc.off_coord A i y
    rw [hy0]
    exact PolyArc.edge_subset_carrier hi (PolyArc.pt_mem_edge
      ⟨by linarith [S.lam_pos], by linarith [S.lam_pos]⟩)
  · exact Or.inl (S.mem_blockL_iff.2 ⟨h1, h2, h, h4⟩)

/-- **Lemma 1.8 (b), the set equality.** Removing the arc from the collar leaves exactly the two
labelled tracks. -/
theorem nbhd_diff_carrier : S.nbhd \ A.carrier = S.sideL ∪ S.sideR := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨hy, hyc⟩
    rcases hy with hy | hy
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion_le_nat.1 hy
      rcases S.tube_diff_carrier_subset hi ⟨hyi, hyc⟩ with h | h
      · exact Or.inl (S.blockL_subset_sideL hi h)
      · exact Or.inr (S.blockR_subset_sideR hi h)
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion_lt_nat.1 hy
      rcases S.ball_diff_carrier_subset hi ⟨hyi, hyc⟩ with h | h
      · exact Or.inl (S.sectorL_subset_sideL hi h)
      · exact Or.inr (S.sectorR_subset_sideR hi h)
  · rintro y (hy | hy)
    · exact ⟨S.sideL_subset_nbhd hy, fun hc => Set.disjoint_left.1 S.sideL_disjoint_carrier hy hc⟩
    · exact ⟨S.sideR_subset_nbhd hy, fun hc => Set.disjoint_left.1 S.sideR_disjoint_carrier hy hc⟩

theorem isOpen_nbhd : IsOpen S.nbhd :=
  (isOpen_iUnion fun _ => isOpen_iUnion fun _ => S.isOpen_tube).union
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball)

/-- **The collar is inside the prescribed open set.** -/
theorem nbhd_subset : S.nbhd ⊆ D := by
  rintro y (hy | hy)
  · obtain ⟨i, hi, hyi⟩ := mem_iUnion_le_nat.1 hy
    obtain ⟨c, hc, hd⟩ := S.exists_foot hyi
    exact S.tube_subset i hi c hc (mem_ball.2 hd)
  · obtain ⟨i, hi, hyi⟩ := mem_iUnion_lt_nat.1 hy
    exact S.ball_subset i hi hyi

end ArcStrip

/-! ## Chaining a linear family

The union of the left pieces is connected because consecutive pieces overlap. Unlike the cyclic
case there is no closing overlap to discard: the chain `0, 1, …, N` is exactly the spanning tree
of the overlap graph. -/

/-- A family of connected sets indexed by an initial segment of `ℕ`, in which every member meets
its successor, has connected union. -/
theorem isConnected_iUnion_chain {α : Type*} [TopologicalSpace α] {F : ℕ → Set α} :
    ∀ N : ℕ, (∀ k ≤ N, IsConnected (F k)) → (∀ k < N, (F k ∩ F (k + 1)).Nonempty) →
      IsConnected (⋃ k, ⋃ (_ : k ≤ N), F k) := by
  intro N
  induction N with
  | zero =>
      intro hconn _
      have h : (⋃ k, ⋃ (_ : k ≤ 0), F k) = F 0 := by
        ext y
        rw [mem_iUnion_le_nat]
        exact ⟨fun ⟨k, hk, hy⟩ => by rwa [Nat.le_zero.1 hk] at hy, fun hy => ⟨0, le_refl 0, hy⟩⟩
      rw [h]
      exact hconn 0 (le_refl 0)
  | succ N ih =>
      intro hconn hmeet
      have h : (⋃ k, ⋃ (_ : k ≤ N + 1), F k) = (⋃ k, ⋃ (_ : k ≤ N), F k) ∪ F (N + 1) := by
        ext y
        simp only [mem_iUnion_le_nat, Set.mem_union]
        constructor
        · rintro ⟨k, hk, hy⟩
          rcases Nat.lt_or_ge k (N + 1) with hlt | hge
          · exact Or.inl ⟨k, by omega, hy⟩
          · exact Or.inr (by rwa [show k = N + 1 by omega] at hy)
        · rintro (⟨k, hk, hy⟩ | hy)
          · exact ⟨k, by omega, hy⟩
          · exact ⟨N + 1, le_refl _, hy⟩
      rw [h]
      obtain ⟨z, hz1, hz2⟩ := hmeet N (by omega)
      exact IsConnected.union ⟨z, mem_iUnion_le_nat.2 ⟨N, le_refl N, hz1⟩, hz2⟩
        (ih (fun k hk => hconn k (by omega)) fun k hk => hmeet k (by omega))
        (hconn (N + 1) (le_refl _))

/-- One positive offset below an accuracy, below a geometric bound, and small enough against a
germ threshold. This is the arc's replacement for the `exists_common_bound` of
`Schoenflies/StripLocal.lean`, which is private there. -/
theorem exists_offset_bound {ε b X k : ℝ} (hε : 0 < ε) (hb : 0 < b) (hX : 0 < X) (hk : 0 < k) :
    ∃ σ : ℝ, 0 < σ ∧ σ < ε ∧ σ < b ∧ σ * k < X := by
  refine ⟨min (min (ε / 2) (b / 2)) (X / (2 * k)),
    lt_min (lt_min (by linarith) (by linarith)) (by positivity), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  · have h : min (min (ε / 2) (b / 2)) (X / (2 * k)) ≤ X / (2 * k) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h hk.le
    have h3 : X / (2 * k) * k = X / 2 := by field_simp
    rw [h3] at h2
    linarith

namespace ArcStrip

variable {n : ℕ} {A : PolyArc n} {D K : Set Plane} (S : ArcStrip A D K) {i j k : ℕ} {x : Plane}

/-! ### The overlaps

The blueprint's "consecutive edge and vertex blocks overlap in a nonempty labelled half-strip".
Both witnesses sit at across-coordinate `rho / 2`, at along-coordinate `3 lam / 2` from the
interior vertex in question. -/

theorem lam_lt_three_halves_lam : S.lam < 3 * S.lam / 2 := by have := S.lam_pos; linarith

theorem three_halves_lam_lt (hi : i ≤ n) : 3 * S.lam / 2 < A.len i - S.lam := by
  have := S.lam_pos
  have := S.four_lam_lt_len i hi
  linarith

theorem overlap_dist_lt : 3 * S.lam / 2 + S.rho / 2 < S.R := by
  have := S.rho_lt_lam
  have := S.two_lam_lt_R
  linarith

theorem mem_blockL_overlap_start (hi : i < n) :
    A.off (i + 1) (3 * S.lam / 2) (S.rho / 2) ∈ S.blockL (i + 1) :=
  S.mem_blockL_off.2 ⟨S.lam_lt_three_halves_lam, S.three_halves_lam_lt (by omega),
    by linarith [S.rho_pos], by linarith [S.rho_pos]⟩

theorem mem_blockR_overlap_start (hi : i < n) :
    A.off (i + 1) (3 * S.lam / 2) (-(S.rho / 2)) ∈ S.blockR (i + 1) :=
  S.mem_blockR_off.2 ⟨S.lam_lt_three_halves_lam, S.three_halves_lam_lt (by omega),
    by linarith [S.rho_pos], by linarith [S.rho_pos]⟩

theorem mem_blockL_overlap_finish (hi : i < n) :
    A.off i (A.len i - 3 * S.lam / 2) (S.rho / 2) ∈ S.blockL i := by
  have h1 : S.lam < A.len i - 3 * S.lam / 2 := by
    have := S.lam_pos; have := S.four_lam_lt_len i (by omega); linarith
  exact S.mem_blockL_off.2 ⟨h1, by have := S.lam_pos; linarith, by linarith [S.rho_pos],
    by linarith [S.rho_pos]⟩

theorem mem_blockR_overlap_finish (hi : i < n) :
    A.off i (A.len i - 3 * S.lam / 2) (-(S.rho / 2)) ∈ S.blockR i := by
  have h1 : S.lam < A.len i - 3 * S.lam / 2 := by
    have := S.lam_pos; have := S.four_lam_lt_len i (by omega); linarith
  exact S.mem_blockR_off.2 ⟨h1, by have := S.lam_pos; linarith, by linarith [S.rho_pos],
    by linarith [S.rho_pos]⟩

/-- **The overlap at the departure vertex.** -/
theorem mem_overlapL_start (hi : i < n) :
    A.off (i + 1) (3 * S.lam / 2) (S.rho / 2) ∈ S.blockL (i + 1) ∩ S.sectorL i := by
  refine ⟨S.mem_blockL_overlap_start hi,
    S.blockL_sub_mem_arcL_start hi (S.mem_blockL_overlap_start hi), ?_⟩
  refine lt_of_le_of_lt PolyArc.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [S.lam_pos] : (0:ℝ) < 3 * S.lam / 2),
    abs_of_pos (by linarith [S.rho_pos] : (0:ℝ) < S.rho / 2)]
  exact S.overlap_dist_lt

/-- **The overlap at the arrival vertex.** -/
theorem mem_overlapL_finish (hi : i < n) :
    A.off i (A.len i - 3 * S.lam / 2) (S.rho / 2) ∈ S.blockL i ∩ S.sectorL i := by
  refine ⟨S.mem_blockL_overlap_finish hi,
    S.blockL_sub_mem_arcL_finish hi (S.mem_blockL_overlap_finish hi), ?_⟩
  refine lt_of_le_of_lt PolyArc.dist_off_vertex_succ_le ?_
  rw [show A.len i - 3 * S.lam / 2 - A.len i = -(3 * S.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [S.lam_pos] : (0:ℝ) < 3 * S.lam / 2),
    abs_of_pos (by linarith [S.rho_pos] : (0:ℝ) < S.rho / 2)]
  exact S.overlap_dist_lt

theorem mem_overlapR_start (hi : i < n) :
    A.off (i + 1) (3 * S.lam / 2) (-(S.rho / 2)) ∈ S.blockR (i + 1) ∩ S.sectorR i := by
  refine ⟨S.mem_blockR_overlap_start hi,
    S.blockR_sub_mem_arcR_start hi (S.mem_blockR_overlap_start hi), ?_⟩
  refine lt_of_le_of_lt PolyArc.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [S.lam_pos] : (0:ℝ) < 3 * S.lam / 2),
    abs_neg, abs_of_pos (by linarith [S.rho_pos] : (0:ℝ) < S.rho / 2)]
  exact S.overlap_dist_lt

theorem mem_overlapR_finish (hi : i < n) :
    A.off i (A.len i - 3 * S.lam / 2) (-(S.rho / 2)) ∈ S.blockR i ∩ S.sectorR i := by
  refine ⟨S.mem_blockR_overlap_finish hi,
    S.blockR_sub_mem_arcR_finish hi (S.mem_blockR_overlap_finish hi), ?_⟩
  refine lt_of_le_of_lt PolyArc.dist_off_vertex_succ_le ?_
  rw [show A.len i - 3 * S.lam / 2 - A.len i = -(3 * S.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [S.lam_pos] : (0:ℝ) < 3 * S.lam / 2),
    abs_neg, abs_of_pos (by linarith [S.rho_pos] : (0:ℝ) < S.rho / 2)]
  exact S.overlap_dist_lt

theorem blockL_nonempty (hi : i ≤ n) : (S.blockL i).Nonempty :=
  ⟨A.off i (3 * S.lam / 2) (S.rho / 2), S.mem_blockL_off.2
    ⟨S.lam_lt_three_halves_lam, S.three_halves_lam_lt hi, by linarith [S.rho_pos],
      by linarith [S.rho_pos]⟩⟩

theorem blockR_nonempty (hi : i ≤ n) : (S.blockR i).Nonempty :=
  ⟨A.off i (3 * S.lam / 2) (-(S.rho / 2)), S.mem_blockR_off.2
    ⟨S.lam_lt_three_halves_lam, S.three_halves_lam_lt hi, by linarith [S.rho_pos],
      by linarith [S.rho_pos]⟩⟩

theorem isConnected_blockL (hi : i ≤ n) : IsConnected (S.blockL i) :=
  S.convex_blockL.isConnected (S.blockL_nonempty hi)

theorem isConnected_blockR (hi : i ≤ n) : IsConnected (S.blockR i) :=
  S.convex_blockR.isConnected (S.blockR_nonempty hi)

/-! ### The two tracks are connected -/

theorem isConnected_chainL (hk : k ≤ n) : IsConnected (S.chainL k) := by
  cases k with
  | zero => exact S.isConnected_blockL (Nat.zero_le n)
  | succ k =>
      exact IsConnected.union ⟨_, (S.mem_overlapL_start (by omega)).2,
        (S.mem_overlapL_start (by omega)).1⟩ (S.isConnected_sectorL (by omega))
        (S.isConnected_blockL hk)

theorem isConnected_chainR (hk : k ≤ n) : IsConnected (S.chainR k) := by
  cases k with
  | zero => exact S.isConnected_blockR (Nat.zero_le n)
  | succ k =>
      exact IsConnected.union ⟨_, (S.mem_overlapR_start (by omega)).2,
        (S.mem_overlapR_start (by omega)).1⟩ (S.isConnected_sectorR (by omega))
        (S.isConnected_blockR hk)

theorem chainL_meet (hk : k < n) : (S.chainL k ∩ S.chainL (k + 1)).Nonempty :=
  ⟨_, S.blockL_subset_chainL k (S.mem_overlapL_finish hk).1,
    Or.inl (S.mem_overlapL_finish hk).2⟩

theorem chainR_meet (hk : k < n) : (S.chainR k ∩ S.chainR (k + 1)).Nonempty :=
  ⟨_, S.blockR_subset_chainR k (S.mem_overlapR_finish hk).1,
    Or.inl (S.mem_overlapR_finish hk).2⟩

/-- **The left track of the collar is connected.** -/
theorem isConnected_sideL : IsConnected S.sideL :=
  isConnected_iUnion_chain n (fun _ hk => S.isConnected_chainL hk) fun _ hk => S.chainL_meet hk

/-- **The right track of the collar is connected.** -/
theorem isConnected_sideR : IsConnected S.sideR :=
  isConnected_iUnion_chain n (fun _ hk => S.isConnected_chainR hk) fun _ hk => S.chainR_meet hk

theorem isOpen_sideL : IsOpen S.sideL := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  rcases S.mem_sideL_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact ⟨S.blockL i, S.blockL_subset_sideL hi, S.isOpen_blockL, h⟩
  · exact ⟨S.sectorL i, S.sectorL_subset_sideL hi, S.isOpen_sectorL, h⟩

theorem isOpen_sideR : IsOpen S.sideR := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  rcases S.mem_sideR_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
  · exact ⟨S.blockR i, S.blockR_subset_sideR hi, S.isOpen_blockR, h⟩
  · exact ⟨S.sectorR i, S.sectorR_subset_sideR hi, S.isOpen_sectorR, h⟩

end ArcStrip

namespace ArcStrip

variable {n : ℕ} {A : PolyArc n} {D K : Set Plane} (S : ArcStrip A D K) {i j k : ℕ} {x : Plane}

/-! ### The two tracks are disjoint

Not a clause of `Schoenflies.ArcCollar` — the consumer does not need it — but it comes out of
the same four families times four families as in the cyclic case, and a later consumer will
want it. -/

theorem blockL_disjoint_blockR (hi : i ≤ n) (hj : j ≤ n) (hL : x ∈ S.blockL i)
    (hR : x ∈ S.blockR j) : False := by
  by_cases hij : j = i
  · rw [hij] at hR
    exact absurd (S.mem_blockL_iff.1 hL).2.2.1 (asymm (S.mem_blockR_iff.1 hR).2.2.2)
  · obtain ⟨c, hc, hd⟩ := S.exists_foot (S.blockL_subset_tube hL)
    obtain ⟨c', hc', hd'⟩ := S.exists_foot (S.blockR_subset_tube hR)
    have hsep := S.sep_trim_edge i hi j hj hij c hc _ (S.pt_mem_edge_of_trim hc')
    have h1 : dist (A.pt i c) (A.pt j c') ≤ dist (A.pt i c) x + dist x (A.pt j c') :=
      dist_triangle _ _ _
    rw [dist_comm] at hd
    linarith

theorem blockL_disjoint_sectorR (hi : i ≤ n) (hj : j < n) (hL : x ∈ S.blockL i)
    (hR : x ∈ S.sectorR j) : False := by
  by_cases hij : i = j
  · rw [hij] at hL
    exact (arcCCW_disjoint' (PolyArc.det_rays_ne_zero hj)).ne_of_mem
      hR.1 (S.blockL_sub_mem_arcL_finish hj hL) rfl
  by_cases hij2 : i = j + 1
  · rw [hij2] at hL
    exact (arcCCW_disjoint' (PolyArc.det_rays_ne_zero hj)).ne_of_mem
      hR.1 (S.blockL_sub_mem_arcL_start hj hL) rfl
  · exact S.tube_notMem_ball_vertex hi (by omega) (fun h => hij2 h.symm)
      (fun h => hij (by omega)) (S.blockL_subset_tube hL) hR.2

theorem sectorL_disjoint_blockR (hi : i < n) (hj : j ≤ n) (hL : x ∈ S.sectorL i)
    (hR : x ∈ S.blockR j) : False := by
  by_cases hij : j = i
  · rw [hij] at hR
    exact (arcCCW_disjoint' (PolyArc.det_rays_ne_zero hi)).ne_of_mem
      (S.blockR_sub_mem_arcR_finish hi hR) hL.1 rfl
  by_cases hij2 : j = i + 1
  · rw [hij2] at hR
    exact (arcCCW_disjoint' (PolyArc.det_rays_ne_zero hi)).ne_of_mem
      (S.blockR_sub_mem_arcR_start hi hR) hL.1 rfl
  · exact S.tube_notMem_ball_vertex hj (by omega) (fun h => hij2 h.symm)
      (fun h => hij (by omega)) (S.blockR_subset_tube hR) hL.2

theorem sectorL_disjoint_sectorR (hi : i < n) (hj : j < n) (hL : x ∈ S.sectorL i)
    (hR : x ∈ S.sectorR j) : False := by
  by_cases hij : i = j
  · rw [hij] at hL
    exact (arcCCW_disjoint' (PolyArc.det_rays_ne_zero hj)).ne_of_mem hR.1 hL.1 rfl
  · have hsep := S.sep_vertex (i + 1) (by omega) (j + 1) (by omega) (by omega)
    have hdL : dist x (A.vertex (i + 1)) < S.R := hL.2
    have hdR : dist x (A.vertex (j + 1)) < S.R := hR.2
    have h1 : dist (A.vertex (i + 1)) (A.vertex (j + 1)) ≤
        dist (A.vertex (i + 1)) x + dist x (A.vertex (j + 1)) := dist_triangle _ _ _
    rw [dist_comm (A.vertex (i + 1)) x] at h1
    linarith

/-- **The two tracks of the collar are disjoint.** -/
theorem sideL_disjoint_sideR : Disjoint S.sideL S.sideR := by
  rw [Set.disjoint_left]
  intro y hy hz
  rcases S.mem_sideL_iff.1 hy with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;>
    rcases S.mem_sideR_iff.1 hz with ⟨j, hj, h'⟩ | ⟨j, hj, h'⟩
  · exact S.blockL_disjoint_blockR hi hj h h'
  · exact S.blockL_disjoint_sectorR hi hj h h'
  · exact S.sectorL_disjoint_blockR hi hj h h'
  · exact S.sectorL_disjoint_sectorR hi hj h h'

/-! ### The compact piece is inside the collar

`sep_ends` is what makes this work: a point of `K` on the first edge is at least `R` from the
first vertex, so it is never in the gap the collar leaves at that end, and symmetrically at the
other end. -/

/-- **`K` is inside the collar.** -/
theorem subset_nbhd : K ⊆ S.nbhd := by
  intro y hy
  obtain ⟨i, hi, hyi⟩ := PolyArc.mem_carrier_iff.1 (S.subset_carrier hy)
  obtain ⟨hend0, hend1⟩ := S.sep_ends y hy
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := PolyArc.mem_edge_iff.1 hyi
  have hlow : i = 0 → S.R ≤ c := by
    intro h
    have heq : A.vertex 0 = A.vertex i := by rw [h]
    rwa [heq, PolyArc.dist_pt_vertex, abs_of_nonneg hc0] at hend0
  have hhigh : i = n → S.R ≤ A.len i - c := by
    intro h
    have heq : A.vertex (n + 1) = A.vertex (i + 1) := by rw [h]
    rw [heq, PolyArc.dist_pt_vertex_succ, abs_of_nonpos (by linarith)] at hend1
    linarith
  rcases lt_or_ge c S.R with h1 | h1
  · have hi0 : i ≠ 0 := fun h => by have h2 := hlow h; linarith
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    refine Or.inr (mem_iUnion_lt_nat.2 ⟨j, by omega, ?_⟩)
    rw [mem_ball, PolyArc.dist_pt_vertex, abs_of_nonneg hc0]
    exact h1
  rcases lt_or_ge (A.len i - S.R) c with h2 | h2
  · have hin : i ≠ n := fun h => by have h2' := hhigh h; linarith
    refine Or.inr (mem_iUnion_lt_nat.2 ⟨i, by omega, ?_⟩)
    rw [mem_ball, PolyArc.dist_pt_vertex_succ, abs_of_nonpos (by linarith)]
    linarith
  · refine Or.inl (mem_iUnion_le_nat.2 ⟨i, hi, ?_⟩)
    rw [PolyArc.pt]
    exact S.mem_tube_off.2 ⟨by linarith [S.lam_lt_R], by linarith [S.lam_lt_R],
      by linarith [S.rho_pos], S.rho_pos⟩

/-! ### Both tracks approach every point of `K` -/

/-- A sector comes arbitrarily close to its vertex: shrink a point of it towards the vertex,
which stays in the arc because an arc of directions is a cone. -/
theorem exists_near_sectorL (hi : i < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ S.sectorL i, dist y (A.vertex (i + 1)) < ε := by
  obtain ⟨z, hz⟩ := (S.isConnected_sectorL hi).nonempty
  have harc : z - A.vertex (i + 1) ∈ arcCCW (A.tang (i + 1)) (A.back i) := hz.1
  have hwne : z - A.vertex (i + 1) ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - A.vertex (i + 1)‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - A.vertex (i + 1)‖ < S.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨A.vertex (i + 1) + (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)),
    ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) := lt_min one_pos (by positivity)
     have hsub : A.vertex (i + 1) +
         (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)) -
         A.vertex (i + 1) =
         (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)) := by module)
  · rw [Set.mem_ofPred_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) ≤ ε / (2 * ‖z - A.vertex (i + 1)‖) :=
      min_le_right _ _
    have hkey : ε / (2 * ‖z - A.vertex (i + 1)‖) * ‖z - A.vertex (i + 1)‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

theorem exists_near_sectorR (hi : i < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ S.sectorR i, dist y (A.vertex (i + 1)) < ε := by
  obtain ⟨z, hz⟩ := (S.isConnected_sectorR hi).nonempty
  have harc : z - A.vertex (i + 1) ∈ arcCCW (A.back i) (A.tang (i + 1)) := hz.1
  have hwne : z - A.vertex (i + 1) ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - A.vertex (i + 1)‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - A.vertex (i + 1)‖ < S.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨A.vertex (i + 1) + (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)),
    ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) := lt_min one_pos (by positivity)
     have hsub : A.vertex (i + 1) +
         (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)) -
         A.vertex (i + 1) =
         (min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖))) • (z - A.vertex (i + 1)) := by module)
  · rw [Set.mem_ofPred_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - A.vertex (i + 1)‖)) ≤ ε / (2 * ‖z - A.vertex (i + 1)‖) :=
      min_le_right _ _
    have hkey : ε / (2 * ‖z - A.vertex (i + 1)‖) * ‖z - A.vertex (i + 1)‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

/-- **Both tracks come arbitrarily close to every point of `K`.** In the middle of an edge this
is the block; at an interior vertex it is `exists_near_sectorL`; in between it is the germ with
the progress held fixed and the offset shrunk below the corner's threshold. The two cases the
cyclic argument does not have — a point near an *extreme* vertex, where there is no sector —
are excluded by `sep_ends`. -/
theorem exists_near_sides (hx : x ∈ K) {ε : ℝ} (hε : 0 < ε) :
    (∃ y ∈ S.sideL, dist x y < ε) ∧ (∃ y ∈ S.sideR, dist x y < ε) := by
  obtain ⟨i, hi, hxi⟩ := PolyArc.mem_carrier_iff.1 (S.subset_carrier hx)
  obtain ⟨hend0, hend1⟩ := S.sep_ends x hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := PolyArc.mem_edge_iff.1 hxi
  have hlow : i = 0 → S.R ≤ c := by
    intro h
    have heq : A.vertex 0 = A.vertex i := by rw [h]
    rwa [heq, PolyArc.dist_pt_vertex, abs_of_nonneg hc0] at hend0
  have hhigh : i = n → S.R ≤ A.len i - c := by
    intro h
    have heq : A.vertex (n + 1) = A.vertex (i + 1) := by rw [h]
    rw [heq, PolyArc.dist_pt_vertex_succ, abs_of_nonpos (by linarith)] at hend1
    linarith
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · -- the initial vertex of the edge, which `sep_ends` forces to be an interior vertex
    have hi0 : i ≠ 0 := fun h => by
      have h2 := hlow h; rw [← hc0'] at h2; linarith [S.R_pos]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j < n := by omega
    rw [← hc0', PolyArc.pt_zero]
    obtain ⟨y, hy, hd⟩ := S.exists_near_sectorL hj hε
    obtain ⟨y', hy', hd'⟩ := S.exists_near_sectorR hj hε
    exact ⟨⟨y, S.sectorL_subset_sideL hj hy, by rw [dist_comm]; exact hd⟩,
      ⟨y', S.sectorR_subset_sideR hj hy', by rw [dist_comm]; exact hd'⟩⟩
  rcases eq_or_lt_of_le hc1 with hc1' | hc1'
  · -- the terminal vertex of the edge
    have hin : i ≠ n := fun h => by
      have h2 := hhigh h; rw [hc1'] at h2; linarith [S.R_pos]
    have hin' : i < n := by omega
    rw [hc1', PolyArc.pt_len]
    obtain ⟨y, hy, hd⟩ := S.exists_near_sectorL hin' hε
    obtain ⟨y', hy', hd'⟩ := S.exists_near_sectorR hin' hε
    exact ⟨⟨y, S.sectorL_subset_sideL hin' hy, by rw [dist_comm]; exact hd⟩,
      ⟨y', S.sectorR_subset_sideR hin' hy', by rw [dist_comm]; exact hd'⟩⟩
  by_cases hmid : S.lam < c ∧ c < A.len i - S.lam
  · -- an interior point of the middle stretch: the block does it
    have hσpos : 0 < min (S.rho / 2) (ε / 2) := lt_min (by linarith [S.rho_pos]) (by linarith)
    have hσrho : min (S.rho / 2) (ε / 2) < S.rho :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith [S.rho_pos])
    have hσε : min (S.rho / 2) (ε / 2) < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨⟨A.off i c (min (S.rho / 2) (ε / 2)), S.blockL_subset_sideL hi
        (S.mem_blockL_off.2 ⟨hmid.1, hmid.2, hσpos, hσrho⟩), ?_⟩,
      ⟨A.off i c (-min (S.rho / 2) (ε / 2)), S.blockR_subset_sideR hi
        (S.mem_blockR_off.2 ⟨hmid.1, hmid.2, by linarith, by linarith⟩), ?_⟩⟩
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_pos hσpos]; exact hσε
    · rw [dist_comm, PolyArc.dist_off_pt,
        abs_of_neg (by linarith : -min (S.rho / 2) (ε / 2) < 0)]
      linarith
  push Not at hmid
  by_cases hnear : c ≤ S.lam
  · -- near the initial vertex, which `sep_ends` again forces to be interior
    have hi0 : i ≠ 0 := fun h => by have h2 := hlow h; linarith [S.lam_lt_R]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j < n := by omega
    have hdet : 0 < |det (A.back j) (A.tang (j + 1))| := abs_pos.2 (PolyArc.det_rays_ne_zero hj)
    have hker : (0 : ℝ) < 1 + |inner ℝ (A.back j) (A.tang (j + 1))| := by positivity
    obtain ⟨σ, hσpos, hσε, hσR, hσm⟩ := exists_offset_bound hε
      (show (0 : ℝ) < S.R - S.lam by linarith [S.lam_lt_R]) (mul_pos hc0' hdet) hker
    have hgerm : σ * |inner ℝ (A.back j) (A.tang (j + 1))| <
        c * |det (A.back j) (A.tang (j + 1))| := by
      have h1 := mul_le_mul_of_nonneg_left
        (show |inner ℝ (A.back j) (A.tang (j + 1))| ≤
          1 + |inner ℝ (A.back j) (A.tang (j + 1))| by linarith) hσpos.le
      linarith
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (A.off (j + 1) c τ) (A.vertex (j + 1)) < S.R := by
      intro τ hτ
      have h := PolyArc.dist_off_vertex_le (A := A) (i := j + 1) (t := c) (s := τ)
      rw [abs_of_pos hc0'] at h
      linarith
    refine ⟨⟨A.off (j + 1) c σ, S.sectorL_subset_sideL hj
        ⟨PolyArc.off_sub_mem_arcL_start hj hσpos hgerm, hdv σ (by rw [abs_of_pos hσpos])⟩, ?_⟩,
      ⟨A.off (j + 1) c (-σ), S.sectorR_subset_sideR hj
        ⟨PolyArc.off_sub_mem_arcR_start hj (by linarith) (by rw [neg_neg]; exact hgerm),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩, ?_⟩⟩
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_pos hσpos]; exact hσε
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_neg (by linarith : -σ < 0)]; linarith
  · -- near the terminal vertex
    push Not at hnear
    have hfar : A.len i - c ≤ S.lam := by have h := hmid hnear; linarith
    have hin : i ≠ n := fun h => by have h2 := hhigh h; linarith [S.lam_lt_R]
    have hin' : i < n := by omega
    have hdet : 0 < |det (A.back i) (A.tang (i + 1))| :=
      abs_pos.2 (PolyArc.det_rays_ne_zero hin')
    have hker : (0 : ℝ) < 1 + |inner ℝ (A.back i) (A.tang (i + 1))| := by positivity
    obtain ⟨σ, hσpos, hσε, hσR, hσm⟩ := exists_offset_bound hε
      (show (0 : ℝ) < S.R - S.lam by linarith [S.lam_lt_R])
      (mul_pos (show (0 : ℝ) < A.len i - c by linarith) hdet) hker
    have hgerm : σ * |inner ℝ (A.back i) (A.tang (i + 1))| <
        (A.len i - c) * |det (A.back i) (A.tang (i + 1))| := by
      have h1 := mul_le_mul_of_nonneg_left
        (show |inner ℝ (A.back i) (A.tang (i + 1))| ≤
          1 + |inner ℝ (A.back i) (A.tang (i + 1))| by linarith) hσpos.le
      linarith
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (A.off i c τ) (A.vertex (i + 1)) < S.R := by
      intro τ hτ
      have h := PolyArc.dist_off_vertex_succ_le (A := A) (i := i) (t := c) (s := τ)
      rw [abs_sub_comm, abs_of_pos (show (0 : ℝ) < A.len i - c by linarith)] at h
      linarith
    refine ⟨⟨A.off i c σ, S.sectorL_subset_sideL hin'
        ⟨PolyArc.off_sub_mem_arcL_finish hin' hσpos hgerm, hdv σ (by rw [abs_of_pos hσpos])⟩, ?_⟩,
      ⟨A.off i c (-σ), S.sectorR_subset_sideR hin'
        ⟨PolyArc.off_sub_mem_arcR_finish hin' (by linarith) (by rw [neg_neg]; exact hgerm),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩, ?_⟩⟩
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_pos hσpos]; exact hσε
    · rw [dist_comm, PolyArc.dist_off_pt, abs_of_neg (by linarith : -σ < 0)]; linarith

/-- Every point of `K` is in the closure of the left track. -/
theorem subset_closure_sideL : K ⊆ closure S.sideL := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨⟨z, hz, hd⟩, -⟩ := S.exists_near_sides hy hε
  exact ⟨z, hz, hd⟩

/-- Every point of `K` is in the closure of the right track. -/
theorem subset_closure_sideR : K ⊆ closure S.sideR := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨-, ⟨z, hz, hd⟩⟩ := S.exists_near_sides hy hε
  exact ⟨z, hz, hd⟩

/-! ### Lemma 1.8 (b) -/

/-- **The two-sided collar of the compact piece `K` along the arc**, as the record
`Schoenflies.ArcCollar` that `Schoenflies/CrosscutAtMostTwo.lean` consumes. The construction is
exported, not existentially packaged: `nbhd`, `sideL` and `sideR` are definitions with an API
of their own, and `Schoenflies.ArcStrip.sideL_disjoint_sideR` and
`Schoenflies.ArcStrip.isOpen_sideL` are two clauses of Lemma 1.8 (b) that the record drops. -/
def collar : ArcCollar D A.carrier K where
  nbhd := S.nbhd
  left := S.sideL
  right := S.sideR
  isOpen_nbhd := S.isOpen_nbhd
  subset_nbhd := S.subset_nbhd
  nbhd_subset := S.nbhd_subset
  nbhd_diff := S.nbhd_diff_carrier
  isConnected_left := S.isConnected_sideL
  isConnected_right := S.isConnected_sideR
  subset_closure_left := S.subset_closure_sideL
  subset_closure_right := S.subset_closure_sideR

@[simp] theorem collar_nbhd : S.collar.nbhd = S.nbhd := rfl
@[simp] theorem collar_left : S.collar.left = S.sideL := rfl
@[simp] theorem collar_right : S.collar.right = S.sideR := rfl

end ArcStrip

/-! ## Choosing the constants

The blueprint's own recipe, in the blueprint's order, with the two clauses about the prescribed
open set folded in at the step where they can be met.

1. `R` from the edge lengths, the pairwise vertex separations, the distance from each vertex to
   each nonincident edge, the openness of `D` at each interior vertex, and the distance from `K`
   to the two endpoints of the arc.
2. `lam := R / 5`, which gives `2 lam < R` and, through `R ≤ len i`, also `4 lam < len i`.
3. `rho` from the distance of each *trimmed* edge to every other edge, from the germ threshold
   at every interior vertex, and from the compact separation of each trimmed edge from the
   complement of `D`. Step 3 is where "the collar is inside `D`" is really paid for: a trimmed
   core is a compact subset of `D`, because the only points of the arc outside `D` are its two
   endpoints and the trim removes them. -/

namespace PolyArc

variable {n : ℕ} {A : PolyArc n} {i : ℕ} {c : ℝ}

/-- A point of a trimmed core is not the first vertex of the arc: on the first edge the trim
keeps it away, and on any other edge simplicity does. -/
theorem pt_ne_vertex_zero {lam : ℝ} (hlam : 0 < lam) (hi : i ≤ n)
    (hc : c ∈ Set.Icc lam (A.len i - lam)) : A.pt i c ≠ A.vertex 0 := by
  have hmem : A.pt i c ∈ A.edge i :=
    pt_mem_edge ⟨le_trans hlam.le hc.1, le_trans hc.2 (by linarith)⟩
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · intro h
    have hd : dist (A.pt 0 c) (A.vertex 0) = |c| := dist_pt_vertex
    rw [h, dist_self, abs_of_nonneg (le_trans hlam.le hc.1)] at hd
    linarith [hc.1]
  · intro h
    exact vertex_notMem_edge (A := A) (i := 0) (j := i) (by omega) hi (by omega) (by omega)
      (h ▸ hmem)

/-- …nor the last vertex of the arc. -/
theorem pt_ne_vertex_last {lam : ℝ} (hlam : 0 < lam) (hi : i ≤ n)
    (hc : c ∈ Set.Icc lam (A.len i - lam)) : A.pt i c ≠ A.vertex (n + 1) := by
  have hmem : A.pt i c ∈ A.edge i :=
    pt_mem_edge ⟨le_trans hlam.le hc.1, le_trans hc.2 (by linarith)⟩
  rcases Nat.lt_or_ge i n with hilt | hige
  · intro h
    exact vertex_notMem_edge (A := A) (i := n + 1) (j := i) (le_refl _) hi (by omega) (by omega)
      (h ▸ hmem)
  · have hin : i = n := by omega
    intro h
    have hd : dist (A.pt i c) (A.vertex (i + 1)) = |c - A.len i| := dist_pt_vertex_succ
    have heq : A.vertex (i + 1) = A.vertex (n + 1) := by rw [hin]
    rw [heq, h, dist_self, abs_of_nonpos (by linarith [hc.2, hlam] : c - A.len i ≤ 0)] at hd
    linarith [hc.2]

/-- **Step 1: the cone radius.** -/
theorem exists_cone_radius (A : PolyArc n) {D K : Set Plane} (hD : IsOpen D)
    (hKcompact : IsCompact K) (hKD : K ⊆ D) (hint : ∀ j, 1 ≤ j → j ≤ n → A.vertex j ∈ D)
    (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D) :
    ∃ R > 0, (∀ i ≤ n, R ≤ A.len i) ∧
      (∀ i ≤ n + 1, ∀ j ≤ n + 1, i ≠ j → 2 * R ≤ dist (A.vertex i) (A.vertex j)) ∧
      (∀ i ≤ n + 1, ∀ j ≤ n, i ≠ j → i ≠ j + 1 → ∀ y ∈ A.edge j, 2 * R ≤ dist (A.vertex i) y) ∧
      (∀ i < n, ball (A.vertex (i + 1)) R ⊆ D) ∧
      (∀ x ∈ K, R ≤ dist x (A.vertex 0) ∧ R ≤ dist x (A.vertex (n + 1))) := by
  -- (1) below every edge length
  obtain ⟨e₁, he₁, hlen⟩ :=
    exists_pos_le_of_finite (Set.finite_le_nat n) (f := fun i => A.len i) fun _ _ => len_pos
  -- (2) the pairwise vertex separations
  have h₂ : ∃ ε > 0, ∀ p : ℕ × ℕ, p ∈ ({i | i ≤ n + 1} ×ˢ {i | i ≤ n + 1}) →
      (p.1 ≠ p.2 → ε ≤ dist (A.vertex p.1) (A.vertex p.2)) := by
    refine exists_pos_forall_of_finite
      ((Set.finite_le_nat (n + 1)).prod (Set.finite_le_nat (n + 1))) ?_ ?_
    · intro _ δ ε _ hδε h hne
      exact le_trans hδε (h hne)
    · rintro ⟨i, j⟩ -
      by_cases hij : i = j
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · exact ⟨dist (A.vertex i) (A.vertex j), dist_pos.2 fun h => hij (A.vertex_inj h),
          fun _ => le_refl _⟩
  -- (3) a vertex against the edges it is not incident to
  have h₃ : ∃ ε > 0, ∀ p : ℕ × ℕ, p ∈ ({i | i ≤ n + 1} ×ˢ {i | i ≤ n}) →
      (p.1 ≠ p.2 → p.1 ≠ p.2 + 1 → ∀ y ∈ A.edge p.2, ε ≤ dist (A.vertex p.1) y) := by
    refine exists_pos_forall_of_finite
      ((Set.finite_le_nat (n + 1)).prod (Set.finite_le_nat n)) ?_ ?_
    · intro _ δ ε _ hδε h h1 h2 y hy
      exact le_trans hδε (h h1 h2 y hy)
    · rintro ⟨i, j⟩ hp
      by_cases h1 : i = j
      · exact ⟨1, one_pos, fun h => absurd h1 h⟩
      by_cases h2 : i = j + 1
      · exact ⟨1, one_pos, fun _ h => absurd h2 h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_singleton isCompact_edge
          (Set.disjoint_singleton_left.2 (vertex_notMem_edge hp.1 hp.2 h1 h2))
        exact ⟨ρ, hρ, fun _ _ y hy => hsep _ rfl y hy⟩
  -- (4) the prescribed open set, at the interior vertices
  have h₄ : ∃ ε > 0, ∀ i : ℕ, i ∈ {i | i < n} → ball (A.vertex (i + 1)) ε ⊆ D := by
    refine exists_pos_forall_of_finite (Set.finite_lt_nat n) ?_ ?_
    · intro _ δ ε _ hδε h
      exact subset_trans (ball_subset_ball hδε) h
    · intro i hi
      have hi' : i < n := hi
      exact Metric.isOpen_iff.1 hD _ (hint (i + 1) (by omega) (by omega))
  -- (5) the two endpoints of the arc, which are off `K`
  obtain ⟨e₅, he₅, hK0⟩ := Plane.exists_dist_pos hKcompact isCompact_singleton
    (Set.disjoint_singleton_right.2 fun h => ha (hKD h))
  obtain ⟨e₆, he₆, hK1⟩ := Plane.exists_dist_pos hKcompact isCompact_singleton
    (Set.disjoint_singleton_right.2 fun h => hb (hKD h))
  obtain ⟨e₂, he₂, hvv⟩ := h₂
  obtain ⟨e₃, he₃, hve⟩ := h₃
  obtain ⟨e₄, he₄, hball⟩ := h₄
  refine ⟨min (min e₁ (e₂ / 2)) (min (e₃ / 2) (min e₄ (min e₅ e₆))),
    lt_min (lt_min he₁ (by linarith)) (lt_min (by linarith) (lt_min he₄ (lt_min he₅ he₆))),
    fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi j hj h1 h2 y hy => ?_,
    fun i hi => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (hlen i hi)
  · have h := hvv (i, j) (Set.mk_mem_prod hi hj) hij
    have hm : min (min e₁ (e₂ / 2)) (min (e₃ / 2) (min e₄ (min e₅ e₆))) ≤ e₂ / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  · have h := hve (i, j) (Set.mk_mem_prod hi hj) h1 h2 y hy
    have hm : min (min e₁ (e₂ / 2)) (min (e₃ / 2) (min e₄ (min e₅ e₆))) ≤ e₃ / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · exact subset_trans (ball_subset_ball
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))) (hball i hi)
  · exact le_trans (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
      (hK0 x hx _ rfl)
  · exact le_trans (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
      (hK1 x hx _ rfl)

/-- **Step 3: the half-width.** -/
theorem exists_half_width (A : PolyArc n) {D : Set Plane} {lam : ℝ} (hD : IsOpen D)
    (hlam : 0 < lam) (hcore : ∀ i ≤ n, A.trimmed i lam ⊆ D) :
    ∃ rho > 0, rho < lam ∧
      (∀ i ≤ n, ∀ j ≤ n, j ≠ i → ∀ c ∈ Set.Icc lam (A.len i - lam), ∀ y ∈ A.edge j,
        2 * rho ≤ dist (A.pt i c) y) ∧
      (∀ i < n, rho * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) ≤
        lam * |det (A.back i) (A.tang (i + 1))|) ∧
      (∀ i ≤ n, ∀ c ∈ Set.Icc lam (A.len i - lam), ball (A.pt i c) rho ⊆ D) := by
  -- (1) each trimmed edge against every other edge
  have h₁ : ∃ ε > 0, ∀ p : ℕ × ℕ, p ∈ ({i | i ≤ n} ×ˢ {i | i ≤ n}) →
      (p.2 ≠ p.1 → ∀ x ∈ A.trimmed p.1 lam, ∀ y ∈ A.edge p.2, ε ≤ dist x y) := by
    refine exists_pos_forall_of_finite ((Set.finite_le_nat n).prod (Set.finite_le_nat n)) ?_ ?_
    · intro _ δ ε _ hδε h hne x hx y hy
      exact le_trans hδε (h hne x hx y hy)
    · rintro ⟨i, j⟩ hp
      by_cases hij : j = i
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_trimmed isCompact_edge
          (trimmed_disjoint_edge hlam hp.1 hp.2 hij)
        exact ⟨ρ, hρ, fun _ => hsep⟩
  -- (2) the germ threshold at every interior vertex
  have h₂ : ∃ ε > 0, ∀ i : ℕ, i ∈ {i | i < n} →
      ε * (1 + |inner ℝ (A.back i) (A.tang (i + 1))|) ≤
        lam * |det (A.back i) (A.tang (i + 1))| := by
    refine exists_pos_forall_of_finite (Set.finite_lt_nat n) ?_ ?_
    · intro i δ ε _ hδε h
      have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (A.back i) (A.tang (i + 1))| := by positivity
      nlinarith
    · intro i hi
      have hi' : i < n := hi
      have hbd : 0 < |det (A.back i) (A.tang (i + 1))| := abs_pos.2 (det_rays_ne_zero hi')
      have hac : (0 : ℝ) < 1 + |inner ℝ (A.back i) (A.tang (i + 1))| := by positivity
      exact ⟨lam * |det (A.back i) (A.tang (i + 1))| /
          (1 + |inner ℝ (A.back i) (A.tang (i + 1))|),
        div_pos (mul_pos hlam hbd) hac, le_of_eq (by field_simp)⟩
  -- (3) the prescribed open set, along every trimmed core
  have h₃ : ∃ ε > 0, ∀ i : ℕ, i ∈ {i | i ≤ n} →
      ∀ c ∈ Set.Icc lam (A.len i - lam), ball (A.pt i c) ε ⊆ D := by
    refine exists_pos_forall_of_finite (Set.finite_le_nat n) ?_ ?_
    · intro _ δ ε _ hδε h c hc
      exact subset_trans (ball_subset_ball hδε) (h c hc)
    · intro i hi
      have hi' : i ≤ n := hi
      obtain ⟨ρ, hρ, hsub⟩ :=
        Plane.exists_thickening_subset isCompact_trimmed hD (hcore i hi')
      exact ⟨ρ, hρ, fun c hc y hy => hsub (mem_thickening_iff.2 ⟨A.pt i c, pt_mem_trimmed hc, hy⟩)⟩
  obtain ⟨ε₁, hε₁, htrim⟩ := h₁
  obtain ⟨ε₂, hε₂, hgerm⟩ := h₂
  obtain ⟨ε₃, hε₃, hballs⟩ := h₃
  refine ⟨min (min (ε₁ / 2) ε₂) (min ε₃ (lam / 2)),
    lt_min (lt_min (by linarith) hε₂) (lt_min hε₃ (by linarith)), ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  · intro i hi j hj hij c hc y hy
    have h := htrim (i, j) (Set.mk_mem_prod hi hj) hij _ (pt_mem_trimmed hc) y hy
    have hm : min (min (ε₁ / 2) ε₂) (min ε₃ (lam / 2)) ≤ ε₁ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · intro i hi
    have h := hgerm i hi
    have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (A.back i) (A.tang (i + 1))| := by positivity
    have hm : min (min (ε₁ / 2) ε₂) (min ε₃ (lam / 2)) ≤ ε₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith
  · intro i hi c hc
    exact subset_trans (ball_subset_ball
      (le_trans (min_le_right _ _) (min_le_left _ _))) (hballs i hi c hc)

end PolyArc

/-- **Lemma 1.8 (b), the constants.** A simple polygonal arc whose two endpoints lie outside the
region `D` and whose remaining points lie inside it carries an `ArcStrip` for every compact
piece `K` of `D ∩ P`. -/
theorem exists_arcStrip {n : ℕ} (A : PolyArc n) {D K : Set Plane} (hD : IsOpen D)
    (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D)
    (hPD : A.carrier \ {A.vertex 0, A.vertex (n + 1)} ⊆ D)
    (hKcompact : IsCompact K) (hKsub : K ⊆ D ∩ A.carrier) :
    Nonempty (ArcStrip A D K) := by
  -- Every interior vertex is inside the region, being on the arc and distinct from its ends.
  have hint : ∀ j, 1 ≤ j → j ≤ n → A.vertex j ∈ D := by
    intro j h1 h2
    refine hPD ⟨PolyArc.vertex_mem_carrier h2, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact absurd (A.vertex_inj h) (by omega)
    · exact absurd (A.vertex_inj h) (by omega)
  obtain ⟨R, hR, hRlen, hRvv, hRve, hRball, hRends⟩ :=
    A.exists_cone_radius hD hKcompact (fun _ hz => (hKsub hz).1) hint ha hb
  have hlam : (0 : ℝ) < R / 5 := by linarith
  -- Every trimmed core is a compact subset of the region: the trim removes the two endpoints.
  have hcore : ∀ i ≤ n, A.trimmed i (R / 5) ⊆ D := by
    rintro i hi _ ⟨c, hc, rfl⟩
    refine hPD ⟨PolyArc.edge_subset_carrier hi (PolyArc.pt_mem_edge
      ⟨le_trans hlam.le hc.1, le_trans hc.2 (by linarith)⟩), ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact PolyArc.pt_ne_vertex_zero hlam hi hc h
    · exact PolyArc.pt_ne_vertex_last hlam hi hc h
  obtain ⟨rho, hrho, hrl, htrim, hgerm, hballs⟩ := A.exists_half_width hD hlam hcore
  exact ⟨⟨R, R / 5, rho, hrho, hrl, by linarith, fun i hi => by have := hRlen i hi; linarith,
    hRlen, hRvv, hRve, htrim, hgerm, hRball, hballs, fun _ hz => (hKsub hz).2, hRends⟩⟩

/-! ## Lemma 1.8 (b), and `HasArcCollars` -/

namespace PolyArc

/-- **Two-sided polygonal strips, the arc case.** Every compact piece of the arc lying inside
the region has a two-sided collar there. The collar is `ArcStrip.collar`, a construction, not an
existential: `Schoenflies.exists_arcStrip` produces the constants and every part of the collar is
a definition with an API. -/
theorem exists_arcCollar {n : ℕ} (A : PolyArc n) {D K : Set Plane} (hD : IsOpen D)
    (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D)
    (hPD : A.carrier \ {A.vertex 0, A.vertex (n + 1)} ⊆ D)
    (hKcompact : IsCompact K) (hKsub : K ⊆ D ∩ A.carrier) :
    Nonempty (ArcCollar D A.carrier K) := by
  obtain ⟨S⟩ := exists_arcStrip A hD ha hb hPD hKcompact hKsub
  exact ⟨S.collar⟩

/-- **`HasArcCollars` for a polygonal arc.** This is the hypothesis of
`Schoenflies.crosscut_at_most_two`, discharged.

Note that neither connectedness nor nontriviality of `K` is used: the collar exists for *every*
compact subset of `D ∩ P`. -/
theorem hasArcCollars {n : ℕ} (A : PolyArc n) {D : Set Plane} (hD : IsOpen D)
    (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D)
    (hPD : A.carrier \ {A.vertex 0, A.vertex (n + 1)} ⊆ D) :
    HasArcCollars D A.carrier :=
  fun _ hKsub hKcompact _ _ => A.exists_arcCollar hD ha hb hPD hKcompact hKsub

end PolyArc

/-- **`P` is a simple polygonal arc from `a` to `b`, presented by a vertex list.** This is the
arc analogue of what `Schoenflies.exists_closedPolygon` proves for a Jordan curve, and it is the
one thing this module does not prove; see the note at the end of the file. -/
def IsPolyArcCarrier (P : Set Plane) (a b : Plane) : Prop :=
  ∃ (n : ℕ) (A : PolyArc n), A.carrier = P ∧ A.vertex 0 = a ∧ A.vertex (n + 1) = b

/-- **`HasArcCollars` for a set presented as the carrier of a `PolyArc`.** The conclusion is
literally the `Schoenflies.HasArcCollars` that `Schoenflies/CrosscutAtMostTwo.lean` carries as a
hypothesis, and the hypotheses are those of `Schoenflies.crosscut_at_most_two` together with the
presentation of `P` by a vertex list. -/
theorem hasArcCollars {D P : Set Plane} {a b : Plane} (hD : IsOpen D)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D) (hchain : IsPolyArcCarrier P a b) :
    HasArcCollars D P := by
  obtain ⟨n, A, rfl, rfl, rfl⟩ := hchain
  exact A.hasArcCollars hD ha hb hPD

/-- **Lemma "At most two sides" for a polygonal arc presented by a vertex list.** -/
theorem crosscut_at_most_two_of_polyArc {D P : Set Plane} {a b : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D) (hchain : IsPolyArcCarrier P a b) :
    ∃ zL ∈ D \ P, ∃ zR ∈ D \ P, ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR :=
  crosscut_at_most_two hDopen hDconn hP hPpoly ha hb hPD
    (hasArcCollars hDopen ha hb hPD hchain)

/-- **Lemma "At most two sides", in the form the crosscut theorem consumes**, for a polygonal
arc presented by a vertex list. -/
theorem crosscut_components_exhaust_of_polyArc {D P : Set Plane} {a b v₁ v₂ : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D) (hchain : IsPolyArcCarrier P a b)
    (h₁ : v₁ ∈ D \ P) (h₂ : v₂ ∈ D \ P)
    (hne : connectedComponentIn (D \ P) v₁ ≠ connectedComponentIn (D \ P) v₂) :
    ∀ x ∈ D \ P, x ∈ connectedComponentIn (D \ P) v₁ ∨ x ∈ connectedComponentIn (D \ P) v₂ :=
  crosscut_components_exhaust hDopen hDconn hP hPpoly ha hb hPD
    (hasArcCollars hDopen ha hb hPD hchain) h₁ h₂ hne

/-! ## The presentation is faithful: the carrier is a simple polygonal arc

`PolyArc` is a *presentation*, so the interface owes a check in the other direction: that the
carrier of a `PolyArc` really is a simple polygonal arc between its two extreme vertices. Both
halves are an induction along the chain of edges, and the only input is simplicity: consecutive
edges meet exactly at the vertex they share, and nonconsecutive ones not at all.

With them, Lemma "At most two sides" for an arc presented by a vertex list has **no hypothesis
left standing** — `Schoenflies.polyArc_crosscut_at_most_two`. -/

namespace PolyArc

variable {n k : ℕ} {A : PolyArc n}

/-- The union of the first `k + 1` edges. -/
def prefixCarrier (A : PolyArc n) (k : ℕ) : Set Plane := ⋃ i, ⋃ (_ : i ≤ k), A.edge i

theorem mem_prefixCarrier_iff {x : Plane} :
    x ∈ A.prefixCarrier k ↔ ∃ i ≤ k, x ∈ A.edge i := mem_iUnion_le_nat

theorem prefixCarrier_zero : A.prefixCarrier 0 = A.edge 0 := by
  ext y
  rw [mem_prefixCarrier_iff]
  exact ⟨fun ⟨i, hi, hy⟩ => by rwa [Nat.le_zero.1 hi] at hy, fun hy => ⟨0, le_refl 0, hy⟩⟩

theorem prefixCarrier_succ :
    A.prefixCarrier (k + 1) = A.prefixCarrier k ∪ A.edge (k + 1) := by
  ext y
  simp only [mem_prefixCarrier_iff, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hy⟩
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · exact Or.inl ⟨i, by omega, hy⟩
    · exact Or.inr (by rwa [show i = k + 1 by omega] at hy)
  · rintro (⟨i, hi, hy⟩ | hy)
    · exact ⟨i, by omega, hy⟩
    · exact ⟨k + 1, le_refl _, hy⟩

theorem prefixCarrier_last (A : PolyArc n) : A.prefixCarrier n = A.carrier := rfl

/-- **Consecutive edges meet exactly at the vertex they share**, and nonconsecutive ones not at
all: the union of the first `k + 1` edges meets edge `k + 1` only at `vertex (k + 1)`. -/
theorem prefixCarrier_meet (hk : k + 1 ≤ n) :
    ∀ z ∈ A.prefixCarrier k, z ∈ A.edge (k + 1) → z = A.vertex (k + 1) := by
  intro z hz hz'
  obtain ⟨i, hi, hzi⟩ := mem_prefixCarrier_iff.1 hz
  have h1 := A.edges_meet i (by omega) (k + 1) hk (by omega) ⟨hzi, hz'⟩
  have h2 := A.edges_meet (k + 1) hk i (by omega) (by omega) ⟨hz', hzi⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (A.vertex_inj (h1.symm.trans h2)) (by omega)
  · exact absurd (A.vertex_inj (h1.symm.trans h2)) (by omega)
  · exact h2
  · exact absurd (A.vertex_inj (h1.symm.trans h2)) (by omega)

/-- **The union of the first `k + 1` edges is an arc from the first vertex to `vertex (k + 1)`.**
-/
theorem isArcBetween_prefixCarrier (A : PolyArc n) :
    ∀ k ≤ n, IsArcBetween (A.prefixCarrier k) (A.vertex 0) (A.vertex (k + 1)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [prefixCarrier_zero]
      exact isArcBetween_segment (vertex_ne (A := A) (i := 0))
  | succ k ih =>
      intro hk
      rw [prefixCarrier_succ]
      exact IsArcBetween.concatenate (ih (by omega))
        (isArcBetween_segment (vertex_ne (A := A) (i := k + 1))) (prefixCarrier_meet hk)

/-- **The carrier of a `PolyArc` is an arc between its two extreme vertices.** -/
theorem isArcBetween_carrier (A : PolyArc n) :
    IsArcBetween A.carrier (A.vertex 0) (A.vertex (n + 1)) :=
  A.isArcBetween_prefixCarrier n (le_refl n)

theorem isPolygonal_prefixCarrier (A : PolyArc n) : ∀ k, IsPolygonal (A.prefixCarrier k) := by
  intro k
  induction k with
  | zero => rw [prefixCarrier_zero]; exact isPolygonal_segment _ _
  | succ k ih =>
      rw [prefixCarrier_succ]
      exact ih.union (isPolygonal_segment _ _)
        ⟨A.vertex (k + 1), mem_prefixCarrier_iff.2 ⟨k, le_refl k, vertex_succ_mem_edge⟩,
          vertex_mem_edge⟩

/-- **The carrier of a `PolyArc` is polygonal.** -/
theorem isPolygonal_carrier (A : PolyArc n) : IsPolygonal A.carrier :=
  A.isPolygonal_prefixCarrier n

end PolyArc

/-- **Lemma "At most two sides" for a polygonal arc presented by a vertex list, with nothing
left standing.** The arc hypothesis and the polygonality hypothesis of
`Schoenflies.crosscut_at_most_two` are supplied by the presentation itself, and the collar
hypothesis by `Schoenflies.PolyArc.hasArcCollars`. -/
theorem polyArc_crosscut_at_most_two {n : ℕ} (A : PolyArc n) {D : Set Plane} (hDopen : IsOpen D)
    (hDconn : IsPreconnected D) (ha : A.vertex 0 ∉ D) (hb : A.vertex (n + 1) ∉ D)
    (hPD : A.carrier \ {A.vertex 0, A.vertex (n + 1)} ⊆ D) :
    ∃ zL ∈ D \ A.carrier, ∃ zR ∈ D \ A.carrier, ∀ x ∈ D \ A.carrier,
      x ∈ connectedComponentIn (D \ A.carrier) zL ∨
        x ∈ connectedComponentIn (D \ A.carrier) zR :=
  crosscut_at_most_two hDopen hDconn A.isArcBetween_carrier A.isPolygonal_carrier ha hb hPD
    (A.hasArcCollars hDopen ha hb hPD)

/-- **Lemma "At most two sides", in the form the crosscut theorem consumes**, for a polygonal
arc presented by a vertex list, with nothing left standing. -/
theorem polyArc_crosscut_components_exhaust {n : ℕ} (A : PolyArc n) {D : Set Plane}
    {v₁ v₂ : Plane} (hDopen : IsOpen D) (hDconn : IsPreconnected D) (ha : A.vertex 0 ∉ D)
    (hb : A.vertex (n + 1) ∉ D) (hPD : A.carrier \ {A.vertex 0, A.vertex (n + 1)} ⊆ D)
    (h₁ : v₁ ∈ D \ A.carrier) (h₂ : v₂ ∈ D \ A.carrier)
    (hne : connectedComponentIn (D \ A.carrier) v₁ ≠ connectedComponentIn (D \ A.carrier) v₂) :
    ∀ x ∈ D \ A.carrier, x ∈ connectedComponentIn (D \ A.carrier) v₁ ∨
      x ∈ connectedComponentIn (D \ A.carrier) v₂ :=
  crosscut_components_exhaust hDopen hDconn A.isArcBetween_carrier A.isPolygonal_carrier ha hb
    hPD (A.hasArcCollars hDopen ha hb hPD) h₁ h₂ hne

/-! ## The presentation is not vacuous: a straight crosscut

A nondegenerate segment is a `PolyArc 0`: one edge, no interior vertex, so both `edges_meet` and
`corner` are vacuous. The vertex function is padded past the segment by walking on in the same
direction, which keeps it injective — this is the padding convention the structure's docstring
describes, in its simplest instance. With it, `Schoenflies.hasArcCollars_segment` of
`Schoenflies/CrosscutAtMostTwo.lean` is a special case of `Schoenflies.hasArcCollars`, which
certifies that `Schoenflies.IsPolyArcCarrier` is satisfiable and that the whole apparatus above
is not vacuous. -/

/-- The one-edge arc from `a` to `b`, with its vertex list padded injectively past `b`. -/
noncomputable def segmentPolyArc {a b : Plane} (hab : a ≠ b) : PolyArc 0 where
  vertex := fun k => a + (k : ℝ) • (b - a)
  vertex_inj := by
    intro k l h
    have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have key : ((k : ℝ) - (l : ℝ)) • (b - a) = 0 := by
      linear_combination (norm := module) h
    rcases smul_eq_zero.1 key with hk | hk
    · have hkl : (k : ℝ) = (l : ℝ) := by linarith
      exact_mod_cast hkl
    · exact absurd hk hba
  edges_meet := by
    intro i hi j hj hij
    exact absurd (show i = j by omega) hij
  corner := by
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)

@[simp] theorem segmentPolyArc_vertex_zero {a b : Plane} (hab : a ≠ b) :
    (segmentPolyArc hab).vertex 0 = a := by
  change a + ((0 : ℕ) : ℝ) • (b - a) = a
  push_cast
  module

@[simp] theorem segmentPolyArc_vertex_one {a b : Plane} (hab : a ≠ b) :
    (segmentPolyArc hab).vertex 1 = b := by
  change a + ((1 : ℕ) : ℝ) • (b - a) = b
  push_cast
  module

theorem segmentPolyArc_carrier {a b : Plane} (hab : a ≠ b) :
    (segmentPolyArc hab).carrier = segment ℝ a b := by
  ext y
  rw [PolyArc.mem_carrier_iff]
  constructor
  · rintro ⟨i, hi, hy⟩
    have hi0 : i = 0 := by omega
    rw [hi0] at hy
    simpa only [PolyArc.edge, Nat.zero_add, segmentPolyArc_vertex_zero,
      segmentPolyArc_vertex_one] using hy
  · intro hy
    exact ⟨0, le_refl 0, by
      simpa only [PolyArc.edge, Nat.zero_add, segmentPolyArc_vertex_zero,
      segmentPolyArc_vertex_one] using hy⟩

/-- A nondegenerate segment is presented by a vertex list. -/
theorem isPolyArcCarrier_segment {a b : Plane} (hab : a ≠ b) :
    IsPolyArcCarrier (segment ℝ a b) a b :=
  ⟨0, segmentPolyArc hab, segmentPolyArc_carrier hab, segmentPolyArc_vertex_zero hab,
    segmentPolyArc_vertex_one hab⟩

/-!
## What is still missing

Exactly one thing: `Schoenflies.IsPolyArcCarrier`. Everything above is proved for an arc
*presented by its vertex list*, and `Schoenflies.hasArcCollars` therefore carries that
presentation as a hypothesis in place of the blueprint's set-level "`P` is a simple polygonal
arc" (`IsArcBetween P a b` together with `IsPolygonal P`).

The missing theorem is

```
theorem isPolyArcCarrier_of_isPolygonal {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) (hab : a ≠ b) : IsPolyArcCarrier P a b
```

the arc analogue of `Schoenflies.exists_closedPolygon`, which `Schoenflies/Realization.lean`
proves for a Jordan curve. It is a *normalisation* statement, not geometry: it says a set that
happens to be both an arc and a finite union of segments can be cut into a chain. The route is
the one `Schoenflies/Realization.lean` takes in the closed case, and its three steps are:

1. `Schoenflies.IsArcBetween.exists_poly_eq` already gives a vertex list `vs` with
   `poly vs = P`, `vs.head = a`, `vs.getLast = b`. That list may backtrack: nothing yet says its
   vertices occur in order along `P`.
2. Order them. Each segment `[vs i, vs (i+1)]` is contained in `P` and is an arc between its
   ends, so by `Schoenflies.IsArcBetween.eq_of_subset` it *is* the subarc of `P` between the two
   parameters. The parameters of the `vs i`, sorted and deduplicated, therefore cut `[0, 1]` into
   intervals each of which is covered by one of those segments, and the subarc over each is a
   segment. That is the chain, with `vertex_inj` and `edges_meet` immediate from injectivity of
   the parametrisation.
3. Delete redundant vertices, i.e. merge two consecutive collinear edges into one. This is the
   blueprint's own first sentence ("Delete redundant vertices at which two consecutive edges are
   collinear") and is what `corner` needs; the closed-curve analogue is
   `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`.

None of the three is formalised for an arc. The remaining results require no such interface.
-/

end Schoenflies
