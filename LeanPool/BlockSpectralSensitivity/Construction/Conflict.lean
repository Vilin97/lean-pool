/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Construction.Basic

/-!
# Unique pairwise conflicts

Fix distinct `i, j` with an arc `i → j`.  The certificate `C_i` fixes the gate
coordinate `q_{ij} = (j, γ(i,j))` to `false`, while `C_j` fixes the whole block
`B_j` — in particular `q_{ij}` — to `true`.  So `q_{ij}` is a conflicting literal,
and Section 4 shows it is the *only* one.

Consequences proved here:

* `conflict_gateCoord` / `exists_conflict_of_ne` / `eq_gateCoord_of_conflict` /
  `filter_conflict_eq_singleton` — existence and uniqueness of the conflict;
* `disjoint_cube_cert` / `sat_cert_unique` — the subcubes `C_i` are pairwise disjoint,
  so every positive input has a unique *owner*;
* `gateCoord_mem_violSet`, `eq_gateCoord_of_mem_violSet_of_fixed`, `one_le_dist_cert` — the
  quantitative facts used in Section 11.2.

Note that the statement `dist(C_i, C_j) = 1` of Section 4 refers to the distance
*between the two subcubes*, i.e. to the projection of a point of `C_i` that is
extremal for `C_j`; it is **not** true that every `x ∈ C_i` is at distance `1` from
`C_j` (a point of `C_i` may violate many gate literals of `C_j` in third blocks,
where `C_i` leaves the coordinate free).  Accordingly we prove the two correct
statements `one_le_dist_cert` and `eq_gateCoord_of_mem_violSet_of_fixed`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda

namespace Construction

variable {ι : Type*} {r : ℕ}

section Cert

variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}

/-- If `i → j` then `q_{ij} = (j, γ(i,j))` is a conflicting literal between `C_i`
and `C_j` (Section 4). -/
theorem conflict_gateCoord (hji : j ≠ i) (hij : Arc i j) :
    (cert Arc γ i).Conflict (cert Arc γ j) (gateCoord γ i j) :=
  ⟨false, cert_apply_gateCoord hji hij, cert_apply_of_fst_eq (gateCoord_fst γ i j)⟩

/-- Distinct certificates always conflict: at the gate coordinate of whichever of the two
arcs joins `i` and `j` (Section 4). -/
theorem exists_conflict_of_ne (hT : IsTournament Arc) (hij : i ≠ j) :
    ∃ v : Coord ι r, (cert Arc γ i).Conflict (cert Arc γ j) v :=
  (hT.arc_or_arc hij).elim (fun h ↦ ⟨_, conflict_gateCoord hij.symm h⟩)
    fun h ↦ ⟨_, (conflict_gateCoord hij h).symm⟩

/-- `q_{ij}` is the *unique* conflicting literal between `C_i` and `C_j` (Section 4). -/
theorem eq_gateCoord_of_conflict (hT : IsTournament Arc)
    (hji : j ≠ i) (hij : Arc i j) {v : Coord ι r}
    (h : (cert Arc γ i).Conflict (cert Arc γ j) v) : v = gateCoord γ i j := by
  obtain ⟨b, hP, hQ⟩ := h
  rcases cert_eq_some_iff.1 hP with ⟨h1, rfl⟩ | ⟨h1, -, hg, rfl⟩
  · -- `C_i` fixes `v` to `true`, so `C_j` would have to fix it to `false`, i.e. `j → i`.
    obtain ⟨ha, -⟩ := arc_and_snd_eq_of_cert_eq_some (fun hh ↦ hji (hh.symm.trans h1)) hQ
    simp [h1, hT.arc_eq_false_of_arc hij] at ha
  · -- `C_j` fixes `v` to `true`, so `v` lies in `B_j` and `C_i` fixes it as a gate.
    have h2 : v.1 = j := not_not.1 fun h2 ↦ cert_ne_some_true_of_fst_ne h2 hQ
    rw [← h2, gateCoord_fst_eq_self hg]

/-- Every positive input lies in exactly one certificate subcube: the *owner*
(Section 4). -/
theorem sat_cert_unique (hT : IsTournament Arc)
    {x : Input (Coord ι r)} (hi : (cert Arc γ i).Sat x) (hj : (cert Arc γ j).Sat x) :
    i = j :=
  PartialAssign.sat_unique_of_conflict (fun _ _ hne ↦ exists_conflict_of_ne hT hne) hi hj

end Cert

section Fintype

variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}

/-- The set of coordinates on which `C_i` and `C_j` conflict is the singleton `{q_{ij}}`
(Section 4). -/
theorem filter_conflict_eq_singleton (hT : IsTournament Arc)
    (hji : j ≠ i) (hij : Arc i j) :
    (Finset.univ.filter fun v : Coord ι r ↦ (cert Arc γ i).Conflict (cert Arc γ j) v)
      = {gateCoord γ i j} := by
  ext v
  simp only [Finset.mem_filter_univ, Finset.mem_singleton]
  refine ⟨eq_gateCoord_of_conflict hT hji hij, ?_⟩
  rintro rfl
  exact conflict_gateCoord hji hij

/-- Distinct certificate subcubes are disjoint (Section 4). -/
theorem disjoint_cube_cert (hT : IsTournament Arc) (hij : i ≠ j) :
    Disjoint (cert Arc γ i).cube (cert Arc γ j).cube :=
  (exists_conflict_of_ne hT hij).elim fun _ hv ↦ hv.disjoint_cube

/-- The unique conflict is always violated: `q_{ij} ∈ violSet (C_j) x` for `x ∈ C_i`
(Section 4). -/
theorem gateCoord_mem_violSet (hji : j ≠ i) (hij : Arc i j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) :
    gateCoord γ i j ∈ (cert Arc γ j).violSet x :=
  (conflict_gateCoord hji hij).mem_violSet hx

/-- Any violated literal of `C_j` at a point of `C_i` that is also fixed by `C_i` must be
the unique conflict `q_{ij}` (Section 4, used in Section 11.2). -/
theorem eq_gateCoord_of_mem_violSet_of_fixed (hT : IsTournament Arc)
    (hji : j ≠ i) (hij : Arc i j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) {v : Coord ι r}
    (hv : v ∈ (cert Arc γ j).violSet x) (hfix : v ∈ (cert Arc γ i).fixedSet) :
    v = gateCoord γ i j := by
  obtain ⟨b, hb, hne⟩ := PartialAssign.mem_violSet_iff_exists_ne.1 hv
  obtain ⟨b', hb'⟩ := PartialAssign.mem_fixedSet_iff_exists.1 hfix
  rw [hx.eq_of_fixed hb'] at hne
  refine eq_gateCoord_of_conflict hT hji hij ⟨b', hb', ?_⟩
  rw [hb, Bool.eq_not_of_ne hne.symm]

/-- A point of `C_i` is at distance at least `1` from `C_j` when `i ≠ j`; in particular
`C_i ∩ C_j = ∅` (Section 4). -/
theorem one_le_dist_cert (hT : IsTournament Arc) (hij : i ≠ j)
    {x : Input (Coord ι r)} (hx : (cert Arc γ i).Sat x) : 1 ≤ (cert Arc γ j).dist x :=
  (exists_conflict_of_ne hT hij).elim fun v hv ↦ Finset.card_pos.2 ⟨v, hv.mem_violSet hx⟩

end Fintype

end Construction

end BSLambda
