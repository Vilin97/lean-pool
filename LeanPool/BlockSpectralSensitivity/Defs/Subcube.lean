/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Defs.Cube

/-!
# Partial assignments and subcubes

A *consistent partial assignment* is modelled as a function `V → Option Bool`:
`none` means the coordinate is free, `some b` means it is fixed to `b`.  (Consistency
is automatic in this encoding.)

Main definitions, following Section 1.3 of `bs_lambda.txt`:

* `PartialAssign.Sat P x` / `PartialAssign.cube P` — the subcube `C(P)`;
* `PartialAssign.proj P x` — the nearest-point projection `π_C(x)`;
* `PartialAssign.Conflict P Q v` — `P` and `Q` fix `v` to opposite values;
* `PartialAssign.fixedSet P` — the coordinates fixed by `P`;
* `PartialAssign.codim P` — its cardinality;
* `PartialAssign.violSet P x` — the fixed literals of `P` violated by `x`;
* `PartialAssign.dist P x` — `dist(x, C(P))`, the number of violated literals;
* `PartialAssign.indUnion P` — the indicator of the union of a family of subcubes.

The two directions relating a point to its projection are `PartialAssign.isLeast_dist`
(the projection realises the distance) and `PartialAssign.eq_flipSet_proj_violSet`
(the point is recovered from the projection by flipping the violated literals).

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda

/-- A consistent partial assignment on the coordinate set `V`: `none` = free,
`some b` = fixed to `b`. -/
abbrev PartialAssign (V : Type*) : Type _ := V → Option Bool

namespace PartialAssign

variable {V : Type*}

/-! ### Satisfaction, projection and conflicts -/

/-- `x` satisfies every literal of `P`. -/
def Sat (P : PartialAssign V) (x : Input V) : Prop := ∀ v b, P v = some b → x v = b

lemma Sat.eq_of_fixed {P : PartialAssign V} {x : Input V} (hx : P.Sat x) {v : V} {b : Bool}
    (hv : P v = some b) : x v = b := hx v b hv

/-- The nearest-point projection of `x` onto `C(P)`: reset every violated fixed
coordinate, leave the free coordinates alone. -/
def proj (P : PartialAssign V) (x : Input V) : Input V := fun v => (P v).getD (x v)

/-- The projection keeps the value `P` fixes, falling back on the value of `x`. -/
@[simp] lemma proj_apply (P : PartialAssign V) (x : Input V) (v : V) :
    P.proj x v = (P v).getD (x v) := rfl

@[simp] lemma proj_sat (P : PartialAssign V) (x : Input V) : P.Sat (P.proj x) := by
  intro v b hv
  simp [hv]

lemma proj_eq_self_of_sat {P : PartialAssign V} {x : Input V} (hx : P.Sat x) : P.proj x = x := by
  funext v
  cases hv : P v with
  | none => simp [hv]
  | some b => simp [hv, hx.eq_of_fixed hv]

/-- Two partial assignments *conflict* at `v` if they fix `v` to opposite values. -/
def Conflict (P Q : PartialAssign V) (v : V) : Prop := ∃ b, P v = some b ∧ Q v = some (!b)

/-- `Conflict` is an existential over `Bool`, hence decidable; providing the instance
keeps the `Finset` statements of Section 4 free of `Classical.dec`. -/
instance (P Q : PartialAssign V) (v : V) : Decidable (P.Conflict Q v) :=
  inferInstanceAs (Decidable (∃ b, P v = some b ∧ Q v = some (!b)))

lemma Conflict.symm {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v) : Q.Conflict P v := by
  obtain ⟨b, hP, hQ⟩ := h
  refine ⟨!b, hQ, ?_⟩
  simp [hP]

/-- Points of two conflicting subcubes disagree at the conflict coordinate. -/
lemma Conflict.ne {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v)
    {x y : Input V} (hx : P.Sat x) (hy : Q.Sat y) : x v ≠ y v := by
  obtain ⟨b, hP, hQ⟩ := h
  rw [hx.eq_of_fixed hP, hy.eq_of_fixed hQ]
  simp

/-- A point of the cube lies in at most one member of a pairwise conflicting family. -/
lemma sat_unique_of_conflict {ι : Type*} {P : ι → PartialAssign V}
    (h : Pairwise fun i j ↦ ∃ v, (P i).Conflict (P j) v) {i j : ι} {x : Input V}
    (hi : (P i).Sat x) (hj : (P j).Sat x) : i = j := by
  by_contra hij
  obtain ⟨v, hv⟩ := h hij
  exact hv.ne hi hj rfl

/-- Two partial assignments that conflict nowhere have a common point: merge them, taking
the value of `P` where `P` fixes a coordinate and the value of `Q` elsewhere. -/
lemma exists_sat_and_sat_of_forall_not_conflict {P Q : PartialAssign V}
    (h : ∀ v, ¬ P.Conflict Q v) : ∃ x : Input V, P.Sat x ∧ Q.Sat x := by
  refine ⟨P.proj fun v ↦ (Q v).getD false, P.proj_sat _, fun v b hb ↦ ?_⟩
  cases hP : P v with
  | none => simp [hP, hb]
  | some c =>
    simp only [proj_apply, hP, Option.getD_some]
    by_contra hne
    refine h v ⟨c, hP, ?_⟩
    cases b <;> simp_all

/-- Converse of `Conflict.disjoint_cube`: disjoint subcubes come from a conflicting pair of
literals. -/
lemma exists_conflict_of_forall_not_sat {P Q : PartialAssign V}
    (h : ∀ x : Input V, P.Sat x → ¬ Q.Sat x) : ∃ v, P.Conflict Q v := by
  by_contra hc
  obtain ⟨x, hx, hx'⟩ := exists_sat_and_sat_of_forall_not_conflict (not_exists.1 hc)
  exact h x hx hx'

section Fintype

variable [Fintype V]

instance (P : PartialAssign V) (x : Input V) : Decidable (P.Sat x) :=
  inferInstanceAs (Decidable (∀ v b, P v = some b → x v = b))

/-! ### The fixed coordinates and the codimension -/

/-- The set of coordinates fixed by `P`. -/
def fixedSet (P : PartialAssign V) : Finset V := Finset.univ.filter fun v => (P v).isSome

@[simp] lemma mem_fixedSet {P : PartialAssign V} {v : V} :
    v ∈ P.fixedSet ↔ (P v).isSome := by simp [fixedSet]

lemma mem_fixedSet_iff_ne_none {P : PartialAssign V} {v : V} : v ∈ P.fixedSet ↔ P v ≠ none := by
  simp [fixedSet, Option.isSome_iff_ne_none]

/-- A fixed coordinate carries an actual value. -/
lemma mem_fixedSet_iff_exists {P : PartialAssign V} {v : V} :
    v ∈ P.fixedSet ↔ ∃ b, P v = some b := by
  rw [mem_fixedSet_iff_ne_none, Option.ne_none_iff_exists']

/-- The codimension of the subcube `C(P)`: the number of coordinates that `P` fixes. -/
def codim (P : PartialAssign V) : ℕ := P.fixedSet.card

/-- The defining equation for `codim`, so that call sites need not unfold the `def`. -/
lemma codim_eq_card_fixedSet (P : PartialAssign V) : P.codim = P.fixedSet.card := rfl

/-- Two points of the same subcube can only differ at a coordinate the subcube leaves free. -/
theorem notMem_fixedSet_of_apply_ne {P : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (hy : P.Sat y) {v : V} (hne : x v ≠ y v) : v ∉ P.fixedSet := fun hv ↦ by
  obtain ⟨b, hb⟩ := mem_fixedSet_iff_exists.1 hv
  exact hne ((hx.eq_of_fixed hb).trans (hy.eq_of_fixed hb).symm)

/-- A point that agrees with a point of `C(P)` off the coordinates fixed by `P` projects
onto it. -/
lemma proj_eq_of_sat_of_eq_off_fixedSet {P : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (h : ∀ v ∉ P.fixedSet, y v = x v) : P.proj y = x := by
  funext v
  cases hv : P v with
  | none => simpa [hv] using h v (by simp [hv])
  | some b => simp [hv, hx.eq_of_fixed hv]

/-! ### The violated literals and the distance to the subcube -/

/-- The fixed literals of `P` that `x` violates. -/
def violSet (P : PartialAssign V) (x : Input V) : Finset V :=
  Finset.univ.filter fun v => P v ≠ none ∧ P v ≠ some (x v)

@[simp] lemma mem_violSet {P : PartialAssign V} {x : Input V} {v : V} :
    v ∈ P.violSet x ↔ P v ≠ none ∧ P v ≠ some (x v) := by simp [violSet]

/-- `v` is violated by `x` exactly when `P` fixes `v` to a value other than `x v`. -/
lemma mem_violSet_iff_exists_ne {P : PartialAssign V} {x : Input V} {v : V} :
    v ∈ P.violSet x ↔ ∃ b, P v = some b ∧ x v ≠ b := by
  cases hv : P v <;> simp [hv, eq_comm]

lemma violSet_subset_fixedSet (P : PartialAssign V) (x : Input V) :
    P.violSet x ⊆ P.fixedSet := fun _ hv ↦ mem_fixedSet_iff_ne_none.2 (mem_violSet.1 hv).1

/-- A point that agrees outside `A` with some point of `C(P)` violates no literal of `P`
outside `A`. -/
lemma violSet_subset_of_sat_of_eq_off {P : PartialAssign V} {x y : Input V} {A : Finset V}
    (hx : P.Sat x) (h : ∀ v ∉ A, y v = x v) : P.violSet y ⊆ A := by
  intro v hv
  by_contra hvA
  obtain ⟨b, hb, hne⟩ := mem_violSet_iff_exists_ne.1 hv
  exact hne ((h v hvA).trans (hx.eq_of_fixed hb))

/-- `dist(x, C(P))`: the number of fixed literals of `P` violated by `x`. -/
def dist (P : PartialAssign V) (x : Input V) : ℕ := (P.violSet x).card

/-- The defining equation for `dist`, so that call sites need not unfold the `def`. -/
lemma dist_eq_card_violSet (P : PartialAssign V) (x : Input V) :
    P.dist x = (P.violSet x).card := rfl

lemma dist_le_codim (P : PartialAssign V) (x : Input V) : P.dist x ≤ P.codim :=
  Finset.card_le_card (P.violSet_subset_fixedSet x)

@[simp] lemma dist_eq_zero_iff {P : PartialAssign V} {x : Input V} : P.dist x = 0 ↔ P.Sat x := by
  simp only [dist_eq_card_violSet, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem,
    mem_violSet_iff_exists_ne, not_exists, not_and, not_not]
  exact Iff.rfl

/-- The distance to `C(P)` is realised by the projection. -/
lemma hammingDist_proj (P : PartialAssign V) (x : Input V) :
    hammingDist x (P.proj x) = P.dist x := by
  rw [hammingDist, dist_eq_card_violSet]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases hv : P v <;> simp [hv, eq_comm]

/-- No point of `C(P)` is closer to `x` than `dist(x, C(P))`. -/
lemma dist_le_hammingDist {P : PartialAssign V} {x y : Input V} (hy : P.Sat y) :
    P.dist x ≤ hammingDist x y :=
  Finset.card_le_card <| violSet_subset_of_sat_of_eq_off hy fun _ hv ↦ by simpa using hv

/-- A coordinate at which `P` and `Q` conflict is a literal of `Q` violated by every
point of the subcube of `P`. -/
lemma Conflict.mem_violSet {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v)
    {x : Input V} (hx : P.Sat x) : v ∈ Q.violSet x := by
  obtain ⟨b, hP, hQ⟩ := h
  refine mem_violSet_iff_exists_ne.2 ⟨!b, hQ, ?_⟩
  simp [hx.eq_of_fixed hP]

/-- Converse of `Conflict.ne`: a coordinate fixed by both `P` and `Q` at which two
satisfying points differ is a conflict coordinate. -/
lemma conflict_of_mem_fixedSet {P Q : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (hy : Q.Sat y) {v : V} (hP : v ∈ P.fixedSet) (hQ : v ∈ Q.fixedSet) (hne : x v ≠ y v) :
    P.Conflict Q v := by
  obtain ⟨b, hb⟩ := mem_fixedSet_iff_exists.1 hP
  obtain ⟨b', hb'⟩ := mem_fixedSet_iff_exists.1 hQ
  rw [hx.eq_of_fixed hb, hy.eq_of_fixed hb'] at hne
  refine ⟨b, hb, ?_⟩
  rw [hb', Bool.eq_not_of_ne hne.symm]

/-! ### The indicator of a union of subcubes -/

section IndUnion

variable {ι : Type*} [Fintype ι]

/-- The indicator of the union `⋃ i, C(P i)` of a family of subcubes. -/
def indUnion (P : ι → PartialAssign V) : Input V → Bool := fun x => decide (∃ i, (P i).Sat x)

variable {P : ι → PartialAssign V} {x : Input V}

@[simp] lemma indUnion_eq_true_iff : indUnion P x = true ↔ ∃ i, (P i).Sat x := by simp [indUnion]

@[simp] lemma indUnion_eq_false_iff : indUnion P x = false ↔ ∀ i, ¬ (P i).Sat x := by
  simp [indUnion]

/-- Every point of a member subcube is positive. -/
lemma indUnion_eq_true_of_sat {i : ι} (h : (P i).Sat x) : indUnion P x = true :=
  indUnion_eq_true_iff.2 ⟨i, h⟩

end IndUnion

end Fintype

/-! ### The subcube as a `Finset` -/

section Cube

variable [Fintype V] [DecidableEq V]

/-- The subcube `C(P)` cut out by the partial assignment `P`. -/
def cube (P : PartialAssign V) : Finset (Input V) := Finset.univ.filter fun x => P.Sat x

@[simp] lemma mem_cube {P : PartialAssign V} {x : Input V} : x ∈ P.cube ↔ P.Sat x := by
  simp [cube]

lemma proj_mem_cube (P : PartialAssign V) (x : Input V) : P.proj x ∈ P.cube := by
  simp

/-- `dist(x, C(P))` really is the minimum Hamming distance to the subcube. -/
lemma isLeast_dist (P : PartialAssign V) (x : Input V) :
    IsLeast (hammingDist x '' P.cube) (P.dist x) :=
  ⟨⟨P.proj x, by simp, P.hammingDist_proj x⟩, by
    rintro _ ⟨y, hy, rfl⟩
    exact dist_le_hammingDist (mem_cube.1 hy)⟩

/-- If `P` and `Q` conflict somewhere then their subcubes are disjoint. -/
lemma Conflict.disjoint_cube {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v) :
    Disjoint P.cube Q.cube :=
  Finset.disjoint_left.2 fun _ hx hx' ↦ h.ne (mem_cube.1 hx) (mem_cube.1 hx') rfl

/-! ### Points, projections and flips -/

/-- Flipping a coordinate that `P` leaves free keeps the point inside `C(P)`. -/
theorem Sat.flipSet_singleton {P : PartialAssign V} {x : Input V} (hx : P.Sat x) {v : V}
    (hv : v ∉ P.fixedSet) : P.Sat (flipSet x {v}) := fun w b hw ↦ by
  have hwv : w ≠ v := fun h ↦ hv (h ▸ mem_fixedSet_iff_exists.2 ⟨b, hw⟩)
  rw [flipSet_apply_of_notMem (Finset.notMem_singleton.2 hwv)]
  exact hx.eq_of_fixed hw

/-- Every point is recovered from its projection onto `C(P)` by flipping exactly the
literals of `P` that it violates. -/
theorem eq_flipSet_proj_violSet (P : PartialAssign V) (x : Input V) :
    x = flipSet (P.proj x) (P.violSet x) := by
  funext v
  by_cases hv : v ∈ P.violSet x
  · obtain ⟨b, hb, hne⟩ := mem_violSet_iff_exists_ne.1 hv
    rw [flipSet_apply_of_mem hv, proj_apply, hb, Option.getD_some]
    exact Bool.eq_not_of_ne hne
  · rw [flipSet_apply_of_notMem hv, proj_apply]
    simp only [mem_violSet, ne_eq, not_and_or, not_not] at hv
    rcases hv with hv | hv <;> simp [hv]

/-- A point at distance one from `C(P)` is a single flip of its projection, at the unique
violated coordinate. -/
theorem eq_flipSet_proj_of_dist_eq_one {P : PartialAssign V} {x : Input V} (hd : P.dist x = 1) :
    ∃ v, P.violSet x = {v} ∧ x = flipSet (P.proj x) {v} := by
  rw [dist_eq_card_violSet] at hd
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hd
  exact ⟨v, hv, hv ▸ eq_flipSet_proj_violSet P x⟩

/-! ### Two conflicting subcubes joined by a two-coordinate flip -/

/-- If `x ∈ C(P)`, its `{p, q}`-flip lies in `C(Q)`, `P` and `Q` conflict at `q` and `Q`
leaves `p` free, then `q` is the only literal of `Q` that `x` violates. -/
lemma violSet_eq_singleton_of_conflict {P Q : PartialAssign V} {x : Input V} {p q : V}
    (hx : P.Sat x) (hy : Q.Sat (flipSet x {p, q})) (hc : P.Conflict Q q)
    (hp : p ∉ Q.fixedSet) : Q.violSet x = {q} := by
  have hsub : Q.violSet x ⊆ {p, q} :=
    violSet_subset_of_sat_of_eq_off hy fun _ hv ↦ (flipSet_apply_of_notMem hv).symm
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hc.mem_violSet hx, fun v hv ↦ ?_⟩
  rcases Finset.mem_insert.1 (hsub hv) with rfl | h
  · exact absurd (violSet_subset_fixedSet _ _ hv) hp
  · exact Finset.mem_singleton.1 h

/-- In the situation of `violSet_eq_singleton_of_conflict`, if instead `P` does fix `p`,
then the flipped point violates exactly the two literals `p` and `q` of `P`. -/
lemma violSet_eq_pair_of_conflict {P Q : PartialAssign V} {x : Input V} {p q : V}
    (hx : P.Sat x) (hy : Q.Sat (flipSet x {p, q})) (hc : P.Conflict Q q)
    (hp : p ∈ P.fixedSet) : P.violSet (flipSet x {p, q}) = {p, q} := by
  obtain ⟨b, hb⟩ := mem_fixedSet_iff_exists.1 hp
  refine Finset.Subset.antisymm
    (violSet_subset_of_sat_of_eq_off hx fun _ ↦ flipSet_apply_of_notMem) ?_
  rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  refine ⟨mem_violSet_iff_exists_ne.2 ⟨b, hb, ?_⟩, hc.symm.mem_violSet hy⟩
  rw [flipSet_apply_of_mem (Finset.mem_insert_self _ _), hx.eq_of_fixed hb]
  simp

end Cube

end PartialAssign

end BSLambda
