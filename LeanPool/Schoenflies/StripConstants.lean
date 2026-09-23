/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Strip
public import LeanPool.Schoenflies.PolyPath

/-!
# The constants of a polygonal collar exist

`Schoenflies.StripData` names the three numbers the two-sided strip lemma runs on — a cone
radius `R`, a trim `lam` and a half-width `rho` — together with the separation hypotheses they
have to satisfy. Everything in `Schoenflies/Strip.lean` is stated *for a given* `StripData`;
this module produces one, removing that parameter from the resulting theorem.

The recipe is the blueprint's own, in the blueprint's order:

1. `R` from three sources — the pairwise vertex separations, the distance from each vertex to
   each nonincident edge, and the prescribed open set — each an instance of Lemma 1.4, plus
   `R ≤ len i` so that a sector cannot run past the far end of an incident edge. The vertex
   separations are asked for with a factor `2` of slack, which is what the block-versus-sector
   estimates of `Strip.lean` spend.
2. `lam := R / 5`, which gives `2 * lam < R` and, through `R ≤ len i`, also `4 * lam < len i`.
3. `rho` from the distance of each *trimmed* edge to every other edge, and from the germ
   threshold `rho * (1 + |⟪r₁, r₂⟫|) ≤ lam * |det r₁ r₂|` at every vertex. The determinant is
   nonzero at a corner, so the threshold is a positive upper bound on `rho` and is met by
   shrinking; `rho < lam` is one more shrinking.

Steps 1 and 3 are finite families of positive bounds, combined by
`Schoenflies.exists_pos_forall_of_finite`.

## What simplicity is used for

Two of the separations are *false* for a self-touching closed polygonal curve, and each is the
exact point where `ClosedPolygon.edges_meet` is consumed:

* `ClosedPolygon.vertex_notMem_edge` — a vertex lies on no edge but the two incident to it.
  This is what makes `{vertex i}` and `edge j` disjoint compact sets.
* `ClosedPolygon.trimmed_disjoint_edge` — the trimmed core of an edge misses every other edge.
  Here the two endpoints allowed by `edges_meet` are excluded by the trim itself, since a point
  of the core is at distance at least `lam` from both.

`edges_meet` as stated is one-sided (`edge i ∩ edge j ⊆ {vertex i, vertex (i + 1)}`), but it is
quantified over all ordered pairs, so the symmetric instance is available and both proofs below
use whichever side is convenient. It carries enough simplicity for both statements.

## Blueprint

* `Schoenflies.exists_stripData_subset` — the constants of Lemma 1.8 (Two-sided polygonal
  strips), chosen inside a prescribed open set containing the curve; this is the "Lemma 1.4 (a)
  lets all disks and strips be chosen inside the prescribed open set" of the last paragraph of
  the proof.
* `Schoenflies.exists_stripData` — the same without a prescribed open set.
* `Schoenflies.ClosedPolygon.exists_cone_radius`,
  `Schoenflies.ClosedPolygon.exists_half_width` — steps 1 and 3 of the recipe, which are the
  instances of Lemma 1.4 that Lemma 1.8 consumes.
* `Schoenflies.StripData.nbhd_subset_thickening` — the collar of Lemma 1.8 lies in the
  `R`-neighbourhood of the curve, which is how the prescribed open set is honoured.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i j : ZMod (m + 3)} {c lam : ℝ}

/-! ### Compactness of the pieces -/

theorem isCompact_edge : IsCompact (P.edge i) := isCompact_segment _ _

theorem isCompact_carrier (P : ClosedPolygon m) : IsCompact P.carrier :=
  isCompact_iUnion fun _ => isCompact_edge

theorem continuous_pt (P : ClosedPolygon m) (i : ZMod (m + 3)) : Continuous (P.pt i) := by
  have h : P.pt i = fun c : ℝ => P.vertex i + c • P.tang i := funext fun _ => pt_eq
  rw [h]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-! ### What simplicity gives

The two statements below are the only consumers of `ClosedPolygon.edges_meet` in the whole
choice of constants, and neither is true without it. -/

/-- **Simplicity, first form.** A vertex lies on no edge but the two edges incident to it.
Without this the "a vertex is `2R` away from every nonincident edge" hypothesis of `StripData`
would be unsatisfiable, since the vertex would sit *on* one of those edges. -/
theorem vertex_notMem_edge (hj1 : j ≠ i - 1) (hj2 : j ≠ i) : P.vertex i ∉ P.edge j := by
  intro hx
  -- Use `edges_meet` in the order that puts the *other* edge's endpoints on the right.
  have hmem : P.vertex i ∈ P.edge j ∩ P.edge i := ⟨hx, vertex_mem_edge⟩
  have hsub := P.edges_meet j i hj2 hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · exact hj2 (P.vertex_inj h).symm
  · exact hj1 (by rw [P.vertex_inj h]; ring)

/-- The trimmed core of edge `i`: the points of the edge at distance at least `lam` from both
of its endpoints. An edge block of `StripData` hugs this core. -/
def trimmed (P : ClosedPolygon m) (i : ZMod (m + 3)) (lam : ℝ) : Set Plane :=
  P.pt i '' Set.Icc lam (P.len i - lam)

theorem pt_mem_trimmed (hc : c ∈ Set.Icc lam (P.len i - lam)) : P.pt i c ∈ P.trimmed i lam :=
  ⟨c, hc, rfl⟩

theorem isCompact_trimmed : IsCompact (P.trimmed i lam) :=
  isCompact_Icc.image (P.continuous_pt i)

/-- **Simplicity, second form.** The trimmed core of an edge misses every other edge. The two
common points `edges_meet` allows are the endpoints of the edge, and the trim removes them: a
core point is at distance at least `lam` from either endpoint. No lower bound on the edge
length is needed: if the trim eats the whole edge the core is empty. -/
theorem trimmed_disjoint_edge (hlam : 0 < lam) (hij : j ≠ i) :
    Disjoint (P.trimmed i lam) (P.edge j) := by
  rw [Set.disjoint_left]
  rintro x ⟨c, hc, rfl⟩ hx
  have hc0 : (0 : ℝ) ≤ c := le_trans hlam.le hc.1
  have hcl : c ≤ P.len i := le_trans hc.2 (by linarith)
  have hmem : P.pt i c ∈ P.edge i ∩ P.edge j := ⟨pt_mem_edge ⟨hc0, hcl⟩, hx⟩
  have hsub := P.edges_meet i j (Ne.symm hij) hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · -- The core point is the initial vertex, so its progress is `0`, below the trim.
    have h0 : |c| = 0 := by rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, dist_self]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.1]
  · -- The core point is the terminal vertex, so its progress is `len i`, above the trim.
    have h0 : |c| = P.len i := by
      rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, len, dist_eq_norm]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.2]

end ClosedPolygon

/-! ## Where the collar lives

The collar sits inside the `R`-neighbourhood of the curve: a sector is inside a ball of radius
`R` about a point of the curve, and a block is within `rho < R` of the foot of its
perpendicular, which is on the curve. This is the whole content of "the neighbourhoods may be
chosen inside any prescribed open set containing the curve". -/

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P)

/-- The collar of `Strip.lean` lies in the `R`-neighbourhood of the polygon. -/
theorem nbhd_subset_thickening : D.nbhd ⊆ thickening D.R P.carrier := by
  intro x hx
  have hx' : x ∈ D.sideL ∪ D.sideR ∪ P.carrier := hx
  rcases hx' with (hL | hR) | hc
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hL
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inl hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hR
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inr hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · exact self_subset_thickening D.R_pos _ hc

end StripData

/-! ## Choosing the constants -/

namespace ClosedPolygon

/-- **Step 1: the cone radius.** One positive `R` that is below every edge length, that
separates the vertices pairwise with a factor `2` to spare, that keeps every vertex `2R` away
from every nonincident edge, and whose neighbourhood of the curve stays inside the prescribed
open set. -/
theorem exists_cone_radius (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) :
    ∃ R > 0, (∀ i, R ≤ P.len i) ∧
      (∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)) ∧
      (∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y) ∧
      thickening R P.carrier ⊆ U := by
  -- (1) below every edge length
  obtain ⟨e₁, he₁, hlen⟩ :=
    exists_pos_le_of_finite (Set.finite_univ (α := ZMod (m + 3))) (f := fun i => P.len i)
      (fun _ _ => len_pos)
  -- (2) the pairwise vertex separations: distinct vertices are distinct points
  have h₂ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.1 ≠ p.2 → ε ≤ dist (P.vertex p.1) (P.vertex p.2)) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne
      exact le_trans hδε (h hne)
    · rintro ⟨i, j⟩ -
      by_cases hij : i = j
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · exact ⟨dist (P.vertex i) (P.vertex j),
          dist_pos.2 fun h => hij (P.vertex_inj h), fun _ => le_refl _⟩
  -- (3) a vertex against the edges it is not incident to: simplicity makes them disjoint
  have h₃ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 - 1 → p.2 ≠ p.1 → ∀ y ∈ P.edge p.2, ε ≤ dist (P.vertex p.1) y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h h1 h2 y hy
      exact le_trans hδε (h h1 h2 y hy)
    · rintro ⟨i, j⟩ -
      by_cases hj1 : j = i - 1
      · exact ⟨1, one_pos, fun h => absurd hj1 h⟩
      by_cases hj2 : j = i
      · exact ⟨1, one_pos, fun _ h => absurd hj2 h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_singleton isCompact_edge
          (Set.disjoint_singleton_left.2 (vertex_notMem_edge hj1 hj2))
        exact ⟨ρ, hρ, fun _ _ y hy => hsep _ rfl y hy⟩
  -- (4) the prescribed open set
  obtain ⟨e₄, he₄, hthick⟩ := Plane.exists_thickening_subset (isCompact_carrier P) hU hPU
  obtain ⟨e₂, he₂, hvv⟩ := h₂
  obtain ⟨e₃, he₃, hve⟩ := h₃
  refine ⟨min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄),
    lt_min (lt_min he₁ (by linarith)) (lt_min (by linarith) he₄), fun i => ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (hlen i (Set.mem_univ i))
  · intro i j hij
    have h := hvv (i, j) (Set.mem_univ _) hij
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₂ / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  · intro i j hj1 hj2 y hy
    have h := hve (i, j) (Set.mem_univ _) hj1 hj2 y hy
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₃ / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · exact subset_trans
      (thickening_mono (le_trans (min_le_right _ _) (min_le_right _ _)) _) hthick

/-- The germ threshold at a single vertex. The corner condition makes `det ≠ 0`, so the right
side is positive and the inequality is a genuine upper bound on the half-width. -/
theorem exists_germ_bound (P : ClosedPolygon m) (i : ZMod (m + 3)) {lam : ℝ} (hlam : 0 < lam) :
    ∃ ε > 0, ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
      lam * |det (P.rayIn i) (P.tang i)| := by
  have hb : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 det_rays_ne_zero
  have ha : 0 < 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
    have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
  refine ⟨lam * |det (P.rayIn i) (P.tang i)| / (1 + |inner ℝ (P.rayIn i) (P.tang i)|),
    div_pos (mul_pos hlam hb) ha, le_of_eq ?_⟩
  field_simp

/-- **Step 3: the half-width.** One positive `rho` below `lam`, separating each trimmed edge
from every other edge with a factor `2` to spare, and meeting the germ threshold at every
vertex. Only `0 < lam` is needed: if `lam` were so large that a trimmed edge came out empty,
its separation clause would be vacuous. -/
theorem exists_half_width (P : ClosedPolygon m) {lam : ℝ} (hlam : 0 < lam) :
    ∃ rho > 0, rho < lam ∧
      (∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
        2 * rho ≤ dist (P.pt i c) y) ∧
      (∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
        lam * |det (P.rayIn i) (P.tang i)|) := by
  -- (1) each trimmed edge against every other edge: two disjoint compact sets
  have h₁ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 → ∀ x ∈ P.trimmed p.1 lam, ∀ y ∈ P.edge p.2, ε ≤ dist x y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne x hx y hy
      exact le_trans hδε (h hne x hx y hy)
    · rintro ⟨i, j⟩ -
      by_cases hij : j = i
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_trimmed isCompact_edge
          (trimmed_disjoint_edge hlam hij)
        exact ⟨ρ, hρ, fun _ => hsep⟩
  -- (2) the germ threshold at every vertex
  have h₂ : ∃ ε > 0, ∀ i : ZMod (m + 3), i ∈ (Set.univ : Set _) →
      ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)| := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro i δ ε _ hδε h
      have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
        have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
      nlinarith
    · intro i _
      exact P.exists_germ_bound i hlam
  obtain ⟨ε₁, hε₁, htrim⟩ := h₁
  obtain ⟨ε₂, hε₂, hgerm⟩ := h₂
  refine ⟨min (min (ε₁ / 2) ε₂) (lam / 2),
    lt_min (lt_min (by linarith) hε₂) (by linarith), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro i j hij c hc y hy
    have h := htrim (i, j) (Set.mem_univ _) hij _ (pt_mem_trimmed hc) y hy
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₁ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · intro i
    have h := hgerm i (Set.mem_univ _)
    have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
      have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith

end ClosedPolygon

open ClosedPolygon

/-- **Lemma 1.8, the constants.** Every simple closed polygon carries a `StripData`, and its
collar can be put inside any prescribed open set containing the curve. This is what makes
`Schoenflies/Strip.lean` with the required constants supplied. -/
theorem exists_stripData_subset (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) : ∃ D : StripData P, D.nbhd ⊆ U := by
  obtain ⟨R, hR, hRlen, hRvv, hRve, hRU⟩ := P.exists_cone_radius hU hPU
  have hlam : (0 : ℝ) < R / 5 := by linarith
  have hlen4 : ∀ i, 4 * (R / 5) < P.len i := fun i => by have := hRlen i; linarith
  obtain ⟨rho, hrho, hrl, htrim, hgerm⟩ := P.exists_half_width hlam
  refine ⟨⟨R, R / 5, rho, hrho, hrl, by linarith, hlen4, hRlen, hRvv, hRve, htrim, hgerm⟩, ?_⟩
  exact subset_trans (StripData.nbhd_subset_thickening _) hRU

/-- Every simple closed polygon carries a `StripData`. -/
theorem exists_stripData (P : ClosedPolygon m) : Nonempty (StripData P) :=
  ⟨(exists_stripData_subset P isOpen_univ (subset_univ _)).choose⟩

end Schoenflies
