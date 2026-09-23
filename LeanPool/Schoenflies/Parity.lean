/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Subdivide
public import LeanPool.Schoenflies.Direction
public import LeanPool.Schoenflies.Square
public import LeanPool.Schoenflies.PolyPath

/-!
# The crossing count of a polygon, and its parity

This is the arithmetic half of the polygonal Jordan curve theorem. A closed polygon is a
list of edges; a point off it gets a number, the count of edges the ray leaving the point
meets; and the whole separation statement follows from the fact that this number changes by
one exactly when the ray's foot sweeps across an edge.

## The frame

The blueprint rotates the coordinate system so that no edge is horizontal. Rotating a curve
is a change of the curve, which would have to be transported back at the end, so instead the
*ray direction* is carried as a parameter. A direction `u` (a unit vector,
`Plane.IsDirection`) fixes an orthonormal frame through

* `fwd u z` — how far along `u` the point `z` lies,
* `hgt u z` — how far across `u` it lies, positive on the counterclockwise side.

"Horizontal" becomes "level for `u`", i.e. `hgt u a = hgt u b`, and
`exists_direction_hgt_ne` — a one-line consequence of `Plane.exists_isDirection_det_ne_zero`
— supplies a `u` for which no edge of a finite list is level. Nothing below needs the
direction to be produced that way: `hgt u P.1 ≠ hgt u P.2` for every piece is carried as a
hypothesis, so no curve is ever moved and nothing has to be transported back.

## The count

An edge is a `Piece`, i.e. its pair of ends, and a polygon is a `List Piece` — the same
representation the overlay uses, so a subdivision produced by `Schoenflies.subdivide` can be
fed straight in. `Crosses u P q` says that the level line through `q` meets `P` strictly
beyond `q`, with the blueprint's half-open convention at the lower end, which is what makes
the count well defined with no genericity assumption. `crossings` counts and `parity`
reduces mod `2`.

Closedness of the polygon enters through `IsClosedChain`: the boundary of the edge list
vanishes mod `2`, stated by duality as "every `ZMod 2`-valued function of the ends sums to
zero over the list". `edgesOf` builds a closed chain from a cyclic vertex list, and
`IsClosedChain` survives `subdivide`.

## Blueprint

* `crossings`, `parity` — the count `π_C` of the section "The polygonal Jordan and crosscut
  theorems".
* `exists_direction_hgt_ne` — the setup of that section: a ray direction level for no edge.
* `crossings_subdivide`, `parity_subdivide` — Lemma 2.1 (subdivision invariance). Proved for
  the *count*, not only its parity, and for the whole `subdivide` operation of
  `Schoenflies.Subdivide`, not only for a single cut.
* `parity_eq_of_mem_ball`, `parity_eq_of_isPreconnected`,
  `parity_eq_of_mem_connectedComponentIn` — the first half of Lemma 2.2 (crossing parity):
  `π_C` is locally constant off the polygon, hence constant on each component of the
  complement.
* `parity_flip` — the second half of Lemma 4.4: the two local sides of an edge have opposite
  parity.
* `parity_eq_zero_of_lt` — `π_C = 0` beyond the polygon in the ray direction; the value on
  the unbounded region.
* `IsClosedChain`, `edgesOf`, `isClosedChain_subdivide` — the closedness hypothesis, its
  supply from a cyclic vertex list, and its survival of subdivision.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

variable {u a b c p q z w : Plane} {s t : ℝ} {L : List Piece}

/-! ### The frame attached to a direction -/

/-- How far across the direction `u` the point `z` lies. Edges on which this is constant are
the blueprint's horizontal edges. -/
def hgt (u z : Plane) : ℝ := Plane.det u z

/-- How far along the direction `u` the point `z` lies. The ray from `q` is the set of points
of the same `hgt` and larger `fwd`. -/
noncomputable def fwd (u z : Plane) : ℝ := inner ℝ z u

theorem hgt_eq (u z : Plane) : hgt u z = u 0 * z 1 - u 1 * z 0 := rfl

theorem fwd_eq (u z : Plane) : fwd u z = z 0 * u 0 + z 1 * u 1 := Plane.inner_eq z u

namespace Plane

theorem add_apply (x y : Plane) (i : Fin 2) : (x + y) i = x i + y i := rfl

theorem smul_apply (r : ℝ) (x : Plane) (i : Fin 2) : (r • x) i = r * x i := rfl

end Plane

/-- The coordinate rewriting used throughout: every claim about `hgt` and `fwd` of an affine
combination is a polynomial identity in the four coordinates. -/
theorem hgt_lin (u a b : Plane) (t : ℝ) :
    hgt u (a + t • (b - a)) = hgt u a + t * (hgt u b - hgt u a) := by
  simp only [hgt_eq, Plane.add_apply, Plane.smul_apply, Plane.sub_apply]; ring

theorem fwd_lin (u a b : Plane) (t : ℝ) :
    fwd u (a + t • (b - a)) = fwd u a + t * (fwd u b - fwd u a) := by
  simp only [fwd_eq, Plane.add_apply, Plane.smul_apply, Plane.sub_apply]; ring

theorem hgt_sub (u x y : Plane) : hgt u (x - y) = hgt u x - hgt u y := by
  simp only [hgt_eq, Plane.sub_apply]; ring

theorem fwd_sub (u x y : Plane) : fwd u (x - y) = fwd u x - fwd u y := by
  simp only [fwd_eq, Plane.sub_apply]; ring

theorem hgt_add_smul (u v x : Plane) (t : ℝ) :
    hgt u (x + t • v) = hgt u x + t * hgt u v := by
  simp only [hgt_eq, Plane.add_apply, Plane.smul_apply]; ring

theorem fwd_add_smul (u v x : Plane) (t : ℝ) :
    fwd u (x + t • v) = fwd u x + t * fwd u v := by
  simp only [fwd_eq, Plane.add_apply, Plane.smul_apply]; ring

/-- `hgt` against `u` is `fwd` against the turned direction. This is how the two coordinates
of the frame are bounded by the norm. -/
theorem hgt_eq_fwd_perp (u z : Plane) : hgt u z = fwd (Plane.perp u) z := by
  simp only [hgt_eq, fwd_eq, Plane.perp_zero, Plane.perp_one]; ring

section Direction

variable (hu : Plane.IsDirection u)
include hu

theorem norm_sq_one : u 0 ^ 2 + u 1 ^ 2 = 1 := by
  rw [← Plane.norm_sq_eq, hu, one_pow]

omit hu in
@[simp] theorem hgt_self : hgt u u = 0 := by simp only [hgt_eq]; ring

theorem fwd_self : fwd u u = 1 := by rw [fwd_eq, ← norm_sq_one hu]; ring

theorem hgt_perp : hgt u (Plane.perp u) = 1 := by
  rw [hgt_eq, ← norm_sq_one hu]; simp only [Plane.perp_zero, Plane.perp_one]; ring

omit hu in
theorem fwd_perp : fwd u (Plane.perp u) = 0 := by
  simp only [fwd_eq, Plane.perp_zero, Plane.perp_one]; ring

/-- The frame is a basis: every vector is its two coordinates. -/
theorem decomp (v : Plane) : v = fwd u v • u + hgt u v • Plane.perp u := by
  have h1 := norm_sq_one hu
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Plane.add_apply, Plane.smul_apply, Plane.perp_zero,
      Plane.perp_one, hgt_eq, fwd_eq]
  · linear_combination (-(v 0)) * h1
  · linear_combination (-(v 1)) * h1

/-- Two points with the same frame coordinates are equal. -/
theorem eq_of_coords (h1 : fwd u z = fwd u w) (h2 : hgt u z = hgt u w) : z = w := by
  have hz := decomp hu z
  have hw := decomp hu w
  rw [h1, h2] at hz
  exact hz.trans hw.symm

theorem abs_fwd_le_norm (v : Plane) : |fwd u v| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm v u
  rw [hu, mul_one] at h
  exact h

theorem abs_hgt_le_norm (v : Plane) : |hgt u v| ≤ ‖v‖ := by
  have hp : Plane.IsDirection (Plane.perp u) := by
    rw [Plane.IsDirection, Plane.norm_perp]; exact hu
  rw [hgt_eq_fwd_perp]
  exact abs_fwd_le_norm hp v

end Direction

/-! ### Where an edge meets a level line -/

/-- The point of the line through `a` and `b` at height `t`. Only used when the line is not
level, i.e. `hgt u a ≠ hgt u b`. -/
noncomputable def meet (u a b : Plane) (t : ℝ) : Plane :=
  a + ((t - hgt u a) / (hgt u b - hgt u a)) • (b - a)

theorem hgt_meet (h : hgt u a ≠ hgt u b) (t : ℝ) : hgt u (meet u a b t) = t := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [meet, hgt_lin]
  field_simp
  ring

theorem fwd_meet (u a b : Plane) (t : ℝ) :
    fwd u (meet u a b t) =
      fwd u a + ((t - hgt u a) / (hgt u b - hgt u a)) * (fwd u b - fwd u a) :=
  fwd_lin u a b _

/-- Below the top and above the bottom, the meeting point is on the edge. -/
theorem meet_mem_segment (h : hgt u a < hgt u b) (h1 : hgt u a ≤ t) (h2 : t ≤ hgt u b) :
    meet u a b t ∈ segment ℝ a b := by
  have hne : (0:ℝ) < hgt u b - hgt u a := by linarith
  rw [segment_eq_image' ℝ a b]
  exact ⟨_, ⟨div_nonneg (by linarith) hne.le, (div_le_one hne).2 (by linarith)⟩, rfl⟩

/-- The meeting point is the only point of the edge at its height. -/
theorem eq_meet (h : hgt u a ≠ hgt u b) (hz : z ∈ segment ℝ a b) :
    z = meet u a b (hgt u z) := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [segment_eq_image' ℝ a b] at hz
  obtain ⟨r, -, rfl⟩ := hz
  have : (hgt u (a + r • (b - a)) - hgt u a) / (hgt u b - hgt u a) = r := by
    rw [hgt_lin]; field_simp; ring
  rw [meet, this]

/-- Reversing an edge does not move its meeting point. -/
theorem meet_swap (h : hgt u a ≠ hgt u b) (t : ℝ) : meet u b a t = meet u a b t := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have h2 : (t - hgt u b) / (hgt u a - hgt u b)
      = 1 - (t - hgt u a) / (hgt u b - hgt u a) := by field_simp; ring
  rw [meet, meet, h2, sub_smul, one_smul, smul_sub, smul_sub]
  abel

/-! ### The crossing count -/

/-- The edge `P` meets the level line through `q` strictly beyond `q`.

The height test is half-open at the bottom: an edge whose lower end is exactly at the height
of `q` counts, one whose upper end is counts not. That convention is what makes the count
well defined at every `q` off the polygon, with no genericity assumption. -/
def Crosses (u : Plane) (P : Piece) (q : Plane) : Prop :=
  min (hgt u P.1) (hgt u P.2) ≤ hgt u q ∧ hgt u q < max (hgt u P.1) (hgt u P.2) ∧
    fwd u q < fwd u (meet u P.1 P.2 (hgt u q))

/-- Crossing is decided classically; the count is a `noncomputable` definition. -/
noncomputable instance decidableCrosses (u : Plane) (P : Piece) (q : Plane) :
    Decidable (Crosses u P q) := Classical.dec _

theorem crosses_swap (h : hgt u a ≠ hgt u b) (q : Plane) :
    Crosses u (b, a) q ↔ Crosses u (a, b) q := by
  simp only [Crosses, meet_swap h, min_comm (hgt u b) (hgt u a), max_comm (hgt u b) (hgt u a)]

/-- How many edges of `L` the ray from `q` crosses. -/
noncomputable def crossings (u : Plane) (L : List Piece) (q : Plane) : ℕ :=
  (L.map (fun P => if Crosses u P q then 1 else 0)).sum

/-- The contribution of one edge to the parity. -/
noncomputable def mark (u : Plane) (P : Piece) (q : Plane) : ZMod 2 :=
  if Crosses u P q then 1 else 0

/-- The crossing parity `π_C(q)`. -/
noncomputable def parity (u : Plane) (L : List Piece) (q : Plane) : ZMod 2 :=
  (L.map (fun P => mark u P q)).sum

@[simp] theorem crossings_nil (u q : Plane) : crossings u [] q = 0 := rfl

@[simp] theorem crossings_cons (u : Plane) (P : Piece) (L : List Piece) (q : Plane) :
    crossings u (P :: L) q = (if Crosses u P q then 1 else 0) + crossings u L q := by
  classical
  simp [crossings]

theorem crossings_append (u : Plane) (L₁ L₂ : List Piece) (q : Plane) :
    crossings u (L₁ ++ L₂) q = crossings u L₁ q + crossings u L₂ q := by
  classical
  simp [crossings, List.sum_append]

@[simp] theorem parity_nil (u q : Plane) : parity u [] q = 0 := rfl

@[simp] theorem parity_cons (u : Plane) (P : Piece) (L : List Piece) (q : Plane) :
    parity u (P :: L) q = mark u P q + parity u L q := by
  simp [parity]

theorem parity_append (u : Plane) (L₁ L₂ : List Piece) (q : Plane) :
    parity u (L₁ ++ L₂) q = parity u L₁ q + parity u L₂ q := by
  simp [parity, List.sum_append]

theorem parity_eq_crossings (u : Plane) (L : List Piece) (q : Plane) :
    parity u L q = (crossings u L q : ZMod 2) := by
  classical
  induction L with
  | nil => simp
  | cons P L ih =>
    rw [parity_cons, ih, crossings_cons, Nat.cast_add, mark]
    split_ifs <;> simp

/-! ### Subdivision invariance -/

/-- A piece with distinct end heights is nondegenerate: this is the hypothesis the
subdivision machinery of `Schoenflies.Subdivide` asks for. -/
theorem nondeg_of_hgt_ne {P : Piece} (h : hgt u P.1 ≠ hgt u P.2) : P.Nondeg := by
  intro hEq
  exact h (by rw [hEq])

/-- An interior point of a non-level edge is strictly between its ends in height. -/
theorem hgt_lt_of_mem_openSegment (hab : hgt u a < hgt u b) (hc : c ∈ openSegment ℝ a b) :
    hgt u a < hgt u c ∧ hgt u c < hgt u b := by
  rw [openSegment_eq_image' ℝ a b] at hc
  obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hc
  rw [hgt_lin]
  constructor
  · nlinarith
  · nlinarith

theorem hgt_ne_of_mem_openSegment (hab : hgt u a ≠ hgt u b) (hc : c ∈ openSegment ℝ a b) :
    hgt u a ≠ hgt u c ∧ hgt u c ≠ hgt u b := by
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨h1, h2⟩ := hgt_lt_of_mem_openSegment h hc
    exact ⟨ne_of_lt h1, ne_of_lt h2⟩
  · obtain ⟨h1, h2⟩ := hgt_lt_of_mem_openSegment h (by rwa [openSegment_symm] at hc)
    exact ⟨ne_of_gt h2, ne_of_gt h1⟩

/-- Cutting an edge keeps both halves non-level. -/
theorem splitAt_hgt_ne {P : Piece} (hP : hgt u P.1 ≠ hgt u P.2) (c : Plane) :
    ∀ Q ∈ splitAt c P, hgt u Q.1 ≠ hgt u Q.2 := by
  classical
  obtain ⟨a, b⟩ := P
  unfold splitAt
  split_ifs with hcc
  · simp only [Piece.interior] at hcc
    obtain ⟨h1, h2⟩ := hgt_ne_of_mem_openSegment hP hcc
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h1
    · rcases List.mem_singleton.1 hQ with rfl
      exact h2
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact hP

theorem splitAllAt_hgt_ne (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (c : Plane) :
    ∀ Q ∈ splitAllAt c L, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_hgt_ne (hL P hP) c Q hQP

theorem subdivide_hgt_ne (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (points : List Plane) :
    ∀ Q ∈ subdivide L points, hgt u Q.1 ≠ hgt u Q.2 := by
  induction points generalizing L with
  | nil => exact hL
  | cons c cs ih => exact ih (splitAllAt_hgt_ne hL c)

/-- The meeting point does not move when the edge is cut: both halves lie on the same line,
and a non-level line meets a level line only once. -/
theorem eq_meet_of_smul (hab : hgt u a ≠ hgt u b) (r : ℝ) (hz : z = a + r • (b - a)) :
    z = meet u a b (hgt u z) := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hr : (hgt u z - hgt u a) / (hgt u b - hgt u a) = r := by
    rw [hz, hgt_lin]; field_simp; ring
  rw [meet, hr, hz]

theorem meet_left_eq (hab : hgt u a ≠ hgt u b) (hac : hgt u a ≠ hgt u c)
    {r : ℝ} (hc : c = a + r • (b - a)) (t : ℝ) : meet u a c t = meet u a b t := by
  have hca : c - a = r • (b - a) := by rw [hc]; abel
  have hz : meet u a c t = a + (((t - hgt u a) / (hgt u c - hgt u a)) * r) • (b - a) := by
    rw [meet, hca, smul_smul]
  rw [eq_meet_of_smul hab _ hz, hgt_meet hac]

theorem meet_right_eq (hab : hgt u a ≠ hgt u b) (hcb : hgt u c ≠ hgt u b)
    {r : ℝ} (hc : c = a + r • (b - a)) (t : ℝ) : meet u c b t = meet u a b t := by
  have hbc : b - c = (1 - r) • (b - a) := by rw [hc, sub_smul, one_smul]; abel
  have key : ∀ k : ℝ, c + k • (b - c) = a + (r + k * (1 - r)) • (b - a) := by
    intro k
    rw [hbc, smul_smul, hc, add_smul]
    abel
  have hz : meet u c b t = a + (r + ((t - hgt u c) / (hgt u b - hgt u c)) * (1 - r)) • (b - a) := by
    rw [meet]; exact key _
  rw [eq_meet_of_smul hab _ hz, hgt_meet hcb]

private theorem crossings_split_aux (hab : hgt u a < hgt u b) (hc : c ∈ openSegment ℝ a b)
    (q : Plane) :
    (if Crosses u (a, c) q then 1 else 0) + (if Crosses u (c, b) q then 1 else 0)
      = (if Crosses u (a, b) q then (1 : ℕ) else 0) := by
  obtain ⟨hac, hcb⟩ := hgt_lt_of_mem_openSegment hab hc
  obtain ⟨r, -, hr⟩ := (openSegment_eq_image' ℝ a b).subset hc
  -- the three edges meet the level line through `q` in one and the same point
  have hm1 : meet u a c (hgt u q) = meet u a b (hgt u q) :=
    meet_left_eq (ne_of_lt hab) (ne_of_lt hac) hr.symm _
  have hm2 : meet u c b (hgt u q) = meet u a b (hgt u q) :=
    meet_right_eq (ne_of_lt hab) (ne_of_lt hcb) hr.symm _
  simp only [Crosses, hm1, hm2, min_eq_left hab.le, max_eq_right hab.le,
    min_eq_left hac.le, max_eq_right hac.le, min_eq_left hcb.le, max_eq_right hcb.le]
  by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
  · by_cases h1 : hgt u a ≤ hgt u q
    · by_cases h2 : hgt u q < hgt u c
      · rw [ite_eq_left ⟨h1, h2, hD⟩,
      ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
          ite_eq_left ⟨h1, by linarith, hD⟩]
      · push Not at h2
        by_cases h3 : hgt u q < hgt u b
        · rw [ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
          ite_eq_left ⟨h2, h3, hD⟩,
            ite_eq_left ⟨h1, h3, hD⟩]
        · rw [ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
            ite_eq_right (by rintro ⟨-, g, -⟩; linarith)]
    · push Not at h1
      rw [ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
      ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
        ite_eq_right (by rintro ⟨g, -, -⟩; linarith)]
  · rw [ite_eq_right (by rintro ⟨-, -, g⟩; exact hD g),
      ite_eq_right (by rintro ⟨-, -, g⟩; exact hD g),
      ite_eq_right (by rintro ⟨-, -, g⟩; exact hD g)]

private theorem crossings_split (hab : hgt u a ≠ hgt u b) (hc : c ∈ openSegment ℝ a b)
    (q : Plane) :
    (if Crosses u (a, c) q then 1 else 0) + (if Crosses u (c, b) q then 1 else 0)
      = (if Crosses u (a, b) q then (1 : ℕ) else 0) := by
  obtain ⟨hac, hcb⟩ := hgt_ne_of_mem_openSegment hab hc
  rcases lt_or_gt_of_ne hab with h | h
  · exact crossings_split_aux h hc q
  · have hc' : c ∈ openSegment ℝ b a := by rwa [openSegment_symm]
    have key := crossings_split_aux h hc' q
    simp only [crosses_swap hcb, crosses_swap hac, crosses_swap hab] at key
    rw [add_comm]
    exact key

/-- Cutting one edge does not change the crossing count. -/
theorem crossings_splitAt {P : Piece} (hP : hgt u P.1 ≠ hgt u P.2) (c q : Plane) :
    crossings u (splitAt c P) q = crossings u [P] q := by
  classical
  obtain ⟨a, b⟩ := P
  unfold splitAt
  split_ifs with hcc
  · simp only [Piece.interior] at hcc
    simp only [crossings_cons, crossings_nil, add_zero]
    exact crossings_split hP hcc q
  · rfl

/-- Cutting the whole list at one point does not change the crossing count. -/
theorem crossings_splitAllAt (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (c q : Plane) :
    crossings u (splitAllAt c L) q = crossings u L q := by
  induction L with
  | nil => rfl
  | cons P L ih =>
    have hP : hgt u P.1 ≠ hgt u P.2 := hL P (by simp)
    have hL' : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2 := fun Q hQ => hL Q (by simp [hQ])
    rw [splitAllAt, List.flatMap_cons, crossings_append, ← splitAllAt, ih hL',
      crossings_splitAt hP c q, crossings_cons, crossings_cons, crossings_nil, add_zero]

/-- **Subdivision invariance** (Lemma 2.1). Subdividing changes no crossing count — not even
its parity is needed here; the count itself is unchanged. -/
theorem crossings_subdivide (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (points : List Plane)
    (q : Plane) : crossings u (subdivide L points) q = crossings u L q := by
  induction points generalizing L with
  | nil => rfl
  | cons c cs ih =>
    rw [subdivide_cons, ih (splitAllAt_hgt_ne hL c), crossings_splitAllAt hL c q]

/-- **Subdivision invariance**, in the form the crosscut theorem uses. -/
theorem parity_subdivide (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (points : List Plane)
    (q : Plane) : parity u (subdivide L points) q = parity u L q := by
  rw [parity_eq_crossings, parity_eq_crossings, crossings_subdivide hL]

/-! ### Closed chains -/

theorem sum_map_add {α : Type*} (l : List α) (F G : α → ZMod 2) :
    (l.map (fun x => F x + G x)).sum = (l.map F).sum + (l.map G).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_flatMap {α β : Type*} (l : List α) (g : α → List β) (F : β → ZMod 2) :
    ((l.flatMap g).map F).sum = (l.map (fun x => ((g x).map F).sum)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]

theorem add_self_zmod_two (x : ZMod 2) : x + x = 0 := by
  revert x; decide

/-- The edge list is a **closed chain**: its boundary vanishes mod `2`. Stated by duality —
every `ZMod 2`-valued function of the ends sums to zero over the list — which is exactly what
the parity argument consumes, and which `isClosedChain_edgesOf` supplies for a cyclic vertex
list. -/
def IsClosedChain (L : List Piece) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map (fun P => f P.1 + f P.2)).sum = 0

theorem isClosedChain_nil : IsClosedChain [] := fun _ => by simp

/-- The closed edge list of a cyclic vertex list: `[v₀v₁, v₁v₂, …, v_{n-1}v₀]`. -/
def edgesOf (vs : List Plane) : List Piece := vs.zip (vs.rotate 1)

theorem isClosedChain_edgesOf (vs : List Plane) : IsClosedChain (edgesOf vs) := by
  intro f
  have h1 : (edgesOf vs).map Prod.fst = vs :=
    List.map_fst_zip (by simp)
  have h2 : (edgesOf vs).map Prod.snd = vs.rotate 1 :=
    List.map_snd_zip (by simp)
  have e1 : ((edgesOf vs).map (fun P => f P.1)).sum = (vs.map f).sum := by
    calc ((edgesOf vs).map (fun P => f P.1)).sum
        = (((edgesOf vs).map Prod.fst).map f).sum := by rw [List.map_map]; rfl
      _ = (vs.map f).sum := by rw [h1]
  have e2 : ((edgesOf vs).map (fun P => f P.2)).sum = ((vs.rotate 1).map f).sum := by
    calc ((edgesOf vs).map (fun P => f P.2)).sum
        = (((edgesOf vs).map Prod.snd).map f).sum := by rw [List.map_map]; rfl
      _ = ((vs.rotate 1).map f).sum := by rw [h2]
  have e3 : ((vs.rotate 1).map f).sum = (vs.map f).sum :=
    List.Perm.sum_eq (List.Perm.map f (vs.rotate_perm 1))
  rw [sum_map_add, e1, e2, e3]
  exact add_self_zmod_two _

/-- Cutting an edge in two does not disturb the boundary: the cut point is added twice. -/
theorem isClosedChain_splitAllAt (h : IsClosedChain L) (c : Plane) :
    IsClosedChain (splitAllAt c L) := by
  classical
  intro f
  have step : ∀ P : Piece, (((splitAt c P).map (fun Q => f Q.1 + f Q.2)).sum) = f P.1 + f P.2 := by
    intro P
    obtain ⟨a, b⟩ := P
    unfold splitAt
    split_ifs
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      linear_combination add_self_zmod_two (f c)
    · simp
  rw [splitAllAt, sum_map_flatMap, List.map_congr_left (fun P _ => step P)]
  exact h f

theorem isClosedChain_subdivide (h : IsClosedChain L) (points : List Plane) :
    IsClosedChain (subdivide L points) := by
  induction points generalizing L with
  | nil => exact h
  | cons c cs ih => exact ih (isClosedChain_splitAllAt h c)

/-! ### What a list of edges occupies -/

theorem mem_cover {P : Piece} (hP : P ∈ L) (hz : z ∈ P.seg) : z ∈ cover L :=
  Set.mem_biUnion hP hz

theorem isCompact_cover (L : List Piece) : IsCompact (cover L) := by
  induction L with
  | nil => rw [cover_nil]; exact isCompact_empty
  | cons P L ih => rw [cover_cons]; exact (isCompact_segment P.1 P.2).union ih

theorem isClosed_cover (L : List Piece) : IsClosed (cover L) := (isCompact_cover L).isClosed

/-- Where an edge meets the level line, when it does. -/
theorem meet_mem_seg {P : Piece} (h : hgt u P.1 ≠ hgt u P.2)
    (h1 : min (hgt u P.1) (hgt u P.2) ≤ t) (h2 : t ≤ max (hgt u P.1) (hgt u P.2)) :
    meet u P.1 P.2 t ∈ P.seg := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [min_eq_left hlt.le] at h1
    rw [max_eq_right hlt.le] at h2
    exact meet_mem_segment hlt h1 h2
  · rw [min_eq_right hlt.le] at h1
    rw [max_eq_left hlt.le] at h2
    have hmem := meet_mem_segment hlt h1 h2
    rwa [meet_swap h, segment_symm] at hmem

/-! ### Moving the base point -/

section Moves

variable (hu : Plane.IsDirection u)
include hu

omit hu in
theorem hgt_along (q : Plane) (s : ℝ) : hgt u (q + s • u) = hgt u q := by
  rw [hgt_add_smul, hgt_self]; ring

theorem fwd_along (q : Plane) (s : ℝ) : fwd u (q + s • u) = fwd u q + s := by
  rw [fwd_add_smul, fwd_self hu]; ring

theorem hgt_across (q : Plane) (s : ℝ) : hgt u (q + s • Plane.perp u) = hgt u q + s := by
  rw [hgt_add_smul, hgt_perp hu]; ring

omit hu in
theorem fwd_across (q : Plane) (s : ℝ) : fwd u (q + s • Plane.perp u) = fwd u q := by
  rw [fwd_add_smul, fwd_perp]; ring

/-- The segment from `q` in the ray direction is exactly the points at the same height with
`fwd` in between. -/
theorem mem_segment_along {q y : Plane} {s : ℝ} (hs : 0 ≤ s) (h1 : hgt u y = hgt u q)
    (h2 : fwd u q ≤ fwd u y) (h3 : fwd u y ≤ fwd u q + s) :
    y ∈ segment ℝ q (q + s • u) := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hy : y = q := eq_of_coords hu (by linarith) h1
    rw [hy, zero_smul, add_zero]
    exact left_mem_segment ℝ q q
  · rw [segment_eq_image' ℝ q (q + s • u)]
    refine ⟨(fwd u y - fwd u q) / s,
      ⟨div_nonneg (by linarith) hs, (div_le_one hspos).2 (by linarith)⟩, ?_⟩
    simp only []
    have hsub : q + s • u - q = s • u := by abel
    rw [hsub, smul_smul, div_mul_cancel₀ _ (ne_of_gt hspos)]
    exact eq_of_coords hu (by rw [fwd_add_smul, fwd_self hu]; ring)
      (by rw [hgt_add_smul, hgt_self, h1]; ring)

/-- The segment from `q` across the ray direction is exactly the points with the same `fwd`
and height in between. -/
theorem mem_segment_across {q y : Plane} {s : ℝ} (hs : 0 ≤ s) (h1 : fwd u y = fwd u q)
    (h2 : hgt u q ≤ hgt u y) (h3 : hgt u y ≤ hgt u q + s) :
    y ∈ segment ℝ q (q + s • Plane.perp u) := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hy : y = q := eq_of_coords hu h1 (by linarith)
    rw [hy, zero_smul, add_zero]
    exact left_mem_segment ℝ q q
  · rw [segment_eq_image' ℝ q (q + s • Plane.perp u)]
    refine ⟨(hgt u y - hgt u q) / s,
      ⟨div_nonneg (by linarith) hs, (div_le_one hspos).2 (by linarith)⟩, ?_⟩
    simp only []
    have hsub : q + s • Plane.perp u - q = s • Plane.perp u := by abel
    rw [hsub, smul_smul, div_mul_cancel₀ _ (ne_of_gt hspos)]
    exact eq_of_coords hu (by rw [fwd_add_smul, fwd_perp, h1]; ring)
      (by rw [hgt_add_smul, hgt_perp hu]; ring)

omit hu in
/-- A connected piece of an edge that stays between two heights and never meets the level
line `fwd = ξ` stays on one side of it. -/
theorem side_const {lo hi ξ : ℝ}
    (hmiss : ∀ y ∈ segment ℝ a b, fwd u y = ξ → lo ≤ hgt u y → hgt u y ≤ hi → False)
    (hz : z ∈ segment ℝ a b) (hw : w ∈ segment ℝ a b)
    (hzl : lo ≤ hgt u z) (hzh : hgt u z ≤ hi) (hwl : lo ≤ hgt u w) (hwh : hgt u w ≤ hi) :
    (ξ < fwd u z ↔ ξ < fwd u w) := by
  have key : ∀ z w : Plane, z ∈ segment ℝ a b → w ∈ segment ℝ a b →
      lo ≤ hgt u z → hgt u z ≤ hi → lo ≤ hgt u w → hgt u w ≤ hi →
      ξ < fwd u z → ξ < fwd u w := by
    intro z w hz hw hzl hzh hwl hwh hlt
    by_contra hcon
    push Not at hcon
    have hpos : 0 < fwd u z - fwd u w := by linarith
    set r := (fwd u z - ξ) / (fwd u z - fwd u w) with hr
    have hr0 : 0 ≤ r := div_nonneg (by linarith) hpos.le
    have hr1 : r ≤ 1 := (div_le_one hpos).2 (by linarith)
    have hy : z + r • (w - z) ∈ segment ℝ a b :=
      (convex_segment a b).segment_subset hz hw
        (by rw [segment_eq_image' ℝ z w]; exact ⟨r, ⟨hr0, hr1⟩, rfl⟩)
    refine hmiss _ hy ?_ ?_ ?_
    · rw [fwd_lin, hr]; field_simp; ring
    · rw [hgt_lin]
      linarith [mul_nonneg hr0 (sub_nonneg.2 hwl), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hzl)]
    · rw [hgt_lin]
      linarith [mul_nonneg hr0 (sub_nonneg.2 hwh), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hzh)]
  exact ⟨fun h => key z w hz hw hzl hzh hwl hwh h, fun h => key w z hw hz hwl hwh hzl hzh h⟩

/-- Moving the base point along the ray direction, without meeting the polygon, changes no
crossing. -/
theorem parity_move_along (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q : Plane} {s : ℝ}
    (hs : 0 ≤ s) (hmiss : ∀ y ∈ segment ℝ q (q + s • u), y ∉ cover L) :
    parity u L (q + s • u) = parity u L q := by
  refine congrArg List.sum (List.map_congr_left ?_)
  intro P hP
  have hPne := hL P hP
  have hiff : Crosses u P (q + s • u) ↔ Crosses u P q := by
    simp only [Crosses, hgt_along, fwd_along hu]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hmiss _ (mem_segment_along hu hs (hgt_meet hPne _) h3.le hcon)
        (mem_cover hP (meet_mem_seg hPne h1 h2.le))
  simp only [mark, hiff]

end Moves

/-! ### Sweeping across the ray direction -/

/-- The marker attached to a vertex when the base point is swept across by `s`: the vertex
counts when its height lies in the half-open band swept out and it lies beyond the base
point. Summed over both ends of every edge this vanishes, because the polygon is closed;
that is the whole content of crossing parity. -/
noncomputable def fmark (u q : Plane) (s : ℝ) (v : Plane) : ZMod 2 :=
  if hgt u q < hgt u v ∧ hgt u v ≤ hgt u q + s ∧ fwd u q < fwd u v then 1 else 0

theorem mark_swap (h : hgt u a ≠ hgt u b) (q : Plane) : mark u (b, a) q = mark u (a, b) q := by
  simp only [mark, crosses_swap h]

section Across

variable (hu : Plane.IsDirection u)
include hu

/-- One edge, swept across. The crossings gained or lost are exactly the ends whose heights
the sweep passes, on the far side of the base point. -/
private theorem mark_step {q : Plane} {s : ℝ} (hs : 0 ≤ s) (hab : hgt u a < hgt u b)
    (hmiss : ∀ y ∈ segment ℝ a b, fwd u y = fwd u q → hgt u q ≤ hgt u y →
      hgt u y ≤ hgt u q + s → False) :
    mark u (a, b) q + mark u (a, b) (q + s • Plane.perp u)
      = fmark u q s a + fmark u q s b := by
  have hne : hgt u a ≠ hgt u b := ne_of_lt hab
  have hha : ∀ t : ℝ, hgt u (meet u a b t) = t := fun t => hgt_meet hne t
  have hma : ∀ t : ℝ, hgt u a ≤ t → t ≤ hgt u b → meet u a b t ∈ segment ℝ a b :=
    fun t h1 h2 => meet_mem_segment hab h1 h2
  have haseg : a ∈ segment ℝ a b := left_mem_segment ℝ a b
  have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
  have hside : ∀ z, z ∈ segment ℝ a b → ∀ w, w ∈ segment ℝ a b →
      hgt u q ≤ hgt u z → hgt u z ≤ hgt u q + s →
      hgt u q ≤ hgt u w → hgt u w ≤ hgt u q + s →
      (fwd u q < fwd u z ↔ fwd u q < fwd u w) :=
    fun z hz w hw h1 h2 h3 h4 => side_const hmiss hz hw h1 h2 h3 h4
  simp only [mark, fmark, Crosses, min_eq_left hab.le, max_eq_right hab.le,
    hgt_across hu, fwd_across]
  rcases le_or_gt (hgt u a) (hgt u q) with hA | hA
  · rcases lt_or_ge (hgt u q + s) (hgt u b) with hB | hB
    · -- the sweep stays strictly below the upper end: no end is passed
      have e := hside (meet u a b (hgt u q)) (hma _ hA (by linarith))
        (meet u a b (hgt u q + s)) (hma _ (by linarith) hB.le)
        (hha _).ge (by rw [hha]; linarith) (by rw [hha]; linarith) (hha _).le
      by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
      · rw [ite_eq_left ⟨hA, by linarith, hD⟩,
          ite_eq_left ⟨by linarith, hB, e.1 hD⟩,
          ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith)]
        decide
      · rw [ite_eq_right (by rintro ⟨-, -, g⟩; exact hD g),
          ite_eq_right (by rintro ⟨-, -, g⟩; exact hD (e.2 g)),
          ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith)]
    · rcases lt_or_ge (hgt u q) (hgt u b) with hB2 | hB2
      · -- the sweep passes the upper end
        have e := hside (meet u a b (hgt u q)) (hma _ hA hB2.le) b hbseg
          (hha _).ge (by rw [hha]; linarith) (by linarith) hB
        by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
        · rw [ite_eq_left ⟨hA, hB2, hD⟩,
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
            ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
          ite_eq_left ⟨hB2, hB, e.1 hD⟩]
          decide
        · rw [ite_eq_right (by rintro ⟨-, -, g⟩; exact hD g),
            ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
            ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
            ite_eq_right (by rintro ⟨-, -, g⟩; exact hD (e.2 g))]
      · -- the edge is entirely below the sweep
        rw [ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
          ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
      ite_eq_right (by rintro ⟨g, -, -⟩; linarith)]
  · rcases le_or_gt (hgt u a) (hgt u q + s) with hA2 | hA2
    · rcases lt_or_ge (hgt u q + s) (hgt u b) with hB | hB
      · -- the sweep passes the lower end only
        have e := hside (meet u a b (hgt u q + s)) (hma _ hA2 hB.le) a haseg
          (by rw [hha]; linarith) (hha _).le (by linarith) hA2
        by_cases hD : fwd u q < fwd u a
        · rw [ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
          ite_eq_left ⟨hA2, hB, e.2 hD⟩,
            ite_eq_left ⟨hA, hA2, hD⟩,
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith)]
          decide
        · rw [ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
            ite_eq_right (by rintro ⟨-, -, g⟩; exact hD (e.1 g)),
            ite_eq_right (by rintro ⟨-, -, g⟩; exact hD g),
            ite_eq_right (by rintro ⟨-, g, -⟩; linarith)]
      · -- the sweep passes both ends
        have e := hside a haseg b hbseg (by linarith) hA2 (by linarith) hB
        by_cases hD : fwd u q < fwd u a
        · rw [ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
            ite_eq_left ⟨hA, hA2, hD⟩,
          ite_eq_left ⟨by linarith, hB, e.1 hD⟩]
          decide
        · rw [ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
            ite_eq_right (by rintro ⟨-, -, g⟩; exact hD g),
            ite_eq_right (by rintro ⟨-, -, g⟩; exact hD (e.2 g))]
    · -- the edge is entirely above the sweep
      rw [ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
      ite_eq_right (by rintro ⟨g, -, -⟩; linarith),
        ite_eq_right (by rintro ⟨-, g, -⟩; linarith),
      ite_eq_right (by rintro ⟨-, g, -⟩; linarith)]

/-- Sweeping the base point across the ray direction, without meeting the polygon, does not
change the parity. This is where the polygon has to be closed. -/
theorem parity_move_across (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q : Plane} {s : ℝ} (hs : 0 ≤ s)
    (hmiss : ∀ y ∈ segment ℝ q (q + s • Plane.perp u), y ∉ cover L) :
    parity u L (q + s • Plane.perp u) = parity u L q := by
  have key : ∀ P ∈ L, mark u P q + mark u P (q + s • Plane.perp u)
      = fmark u q s P.1 + fmark u q s P.2 := by
    intro P hP
    obtain ⟨a, b⟩ := P
    have hne := hL (a, b) hP
    have hmiss' : ∀ y ∈ segment ℝ a b, fwd u y = fwd u q → hgt u q ≤ hgt u y →
        hgt u y ≤ hgt u q + s → False := fun y hy h1 h2 h3 =>
      hmiss y (mem_segment_across hu hs h1 h2 h3) (mem_cover hP hy)
    rcases lt_or_gt_of_ne hne with h | h
    · exact mark_step hu hs h hmiss'
    · have hmiss'' : ∀ y ∈ segment ℝ b a, fwd u y = fwd u q → hgt u q ≤ hgt u y →
          hgt u y ≤ hgt u q + s → False := by
        intro y hy
        exact hmiss' y (by rwa [segment_symm] at hy)
      have hstep := mark_step hu hs h hmiss''
      rw [mark_swap hne, mark_swap hne] at hstep
      rw [hstep]
      exact add_comm _ _
  have hzero : parity u L q + parity u L (q + s • Plane.perp u) = 0 := by
    rw [parity, parity, ← sum_map_add, List.map_congr_left key]
    exact hC (fun v => fmark u q s v)
  have harith : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  exact harith _ _ hzero

/-- The two moves, for a shift of either sign. -/
theorem parity_move_along' (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q q' : Plane} (s : ℝ)
    (hq' : q' = q + s • u) (hmiss : ∀ y ∈ segment ℝ q q', y ∉ cover L) :
    parity u L q' = parity u L q := by
  rcases le_or_gt 0 s with hs | hs
  · subst hq'; exact parity_move_along hu hL hs hmiss
  · have hq : q = q' + (-s) • u := by rw [hq', neg_smul, add_neg_cancel_right]
    have hmiss' : ∀ y ∈ segment ℝ q' (q' + (-s) • u), y ∉ cover L := by
      intro y hy
      rw [← hq] at hy
      exact hmiss y (by rwa [segment_symm] at hy)
    have hmove := parity_move_along hu hL (by linarith : (0:ℝ) ≤ -s) hmiss'
    rw [← hq] at hmove
    exact hmove.symm

theorem parity_move_across' (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q q' : Plane} (s : ℝ) (hq' : q' = q + s • Plane.perp u)
    (hmiss : ∀ y ∈ segment ℝ q q', y ∉ cover L) :
    parity u L q' = parity u L q := by
  rcases le_or_gt 0 s with hs | hs
  · subst hq'; exact parity_move_across hu hL hC hs hmiss
  · have hq : q = q' + (-s) • Plane.perp u := by rw [hq', neg_smul, add_neg_cancel_right]
    have hmiss' : ∀ y ∈ segment ℝ q' (q' + (-s) • Plane.perp u), y ∉ cover L := by
      intro y hy
      rw [← hq] at hy
      exact hmiss y (by rwa [segment_symm] at hy)
    have hmove := parity_move_across hu hL hC (by linarith : (0:ℝ) ≤ -s) hmiss'
    rw [← hq] at hmove
    exact hmove.symm

end Across

/-! ### Crossing parity -/

theorem exists_ball_avoiding {z : Plane} (h : z ∉ cover L) :
    ∃ ε > 0, ∀ y ∈ ball z ε, y ∉ cover L := by
  have hopen := (isClosed_cover L).isOpen_compl
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hsub⟩ := hopen z h
  exact ⟨ε, hε, fun y hy => hsub hy⟩

section Constancy

variable (hu : Plane.IsDirection u)
include hu

/-- The parity is constant on a ball that misses the polygon: reach any nearby point by a
move along the ray direction followed by a move across it. -/
theorem parity_eq_of_mem_ball (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q q' : Plane} {ε : ℝ} (hq' : q' ∈ ball q ε) (hmiss : ∀ y ∈ ball q ε, y ∉ cover L) :
    parity u L q' = parity u L q := by
  have hεpos : 0 < ε := lt_of_le_of_lt dist_nonneg (mem_ball.1 hq')
  have hqb : q ∈ ball q ε := mem_ball_self hεpos
  obtain ⟨w, hw⟩ : ∃ w : Plane, w = q + (fwd u (q' - q)) • u := ⟨_, rfl⟩
  have hwball : w ∈ ball q ε := by
    have hsub : q + (fwd u (q' - q)) • u - q = (fwd u (q' - q)) • u := by abel
    rw [mem_ball, dist_eq_norm, hw, hsub, norm_smul, Real.norm_eq_abs, hu, mul_one]
    calc |fwd u (q' - q)| ≤ ‖q' - q‖ := abs_fwd_le_norm hu _
      _ = dist q' q := (dist_eq_norm q' q).symm
      _ < ε := mem_ball.1 hq'
  have hq'w : q' = w + (hgt u (q' - q)) • Plane.perp u := by
    have hd := decomp hu (q' - q)
    rw [hw, add_assoc, ← hd]
    abel
  have h1 : parity u L w = parity u L q :=
    parity_move_along' hu hL _ hw
      (fun y hy => hmiss y ((convex_ball q ε).segment_subset hqb hwball hy))
  have h2 : parity u L q' = parity u L w :=
    parity_move_across' hu hL hC _ hq'w
      (fun y hy => hmiss y ((convex_ball q ε).segment_subset hwball hq' hy))
  rw [h2, h1]

/-- **Crossing parity** (Lemma 2.2). `π_C` is constant on every preconnected subset of the
complement of the polygon — in particular on every component. -/
theorem parity_eq_of_isPreconnected (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {S : Set Plane} (hS : IsPreconnected S)
    (hSC : ∀ z ∈ S, z ∉ cover L) {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    parity u L x = parity u L y := by
  by_contra hne
  have hopen : ∀ c : ZMod 2, IsOpen {z : Plane | z ∉ cover L ∧ parity u L z = c} := by
    intro c
    rw [Metric.isOpen_iff]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hz1
    exact ⟨ε, hε, fun t ht => ⟨hball t ht,
      by rw [parity_eq_of_mem_ball hu hL hC ht hball, hz2]⟩⟩
  have htwo : ∀ e : ZMod 2, e = parity u L x ∨ e = parity u L y := by
    revert hne
    generalize parity u L x = c
    generalize parity u L y = d
    revert c d
    decide
  obtain ⟨z, -, hzA, hzB⟩ :=
    hS _ _ (hopen (parity u L x)) (hopen (parity u L y))
      (fun t ht => (htwo (parity u L t)).imp (fun h => ⟨hSC t ht, h⟩) (fun h => ⟨hSC t ht, h⟩))
      ⟨x, hx, hSC x hx, rfl⟩ ⟨y, hy, hSC y hy, rfl⟩
  exact hne (hzA.2 ▸ hzB.2)

/-- The parity is constant on the component of the complement containing a point. -/
theorem parity_eq_of_mem_connectedComponentIn (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {x y : Plane} (hx : x ∉ cover L)
    (hy : y ∈ connectedComponentIn (cover L)ᶜ x) : parity u L y = parity u L x :=
  parity_eq_of_isPreconnected hu hL hC isPreconnected_connectedComponentIn
    (fun _ ht => connectedComponentIn_subset _ _ ht) hy (mem_connectedComponentIn hx)

end Constancy

/-! ### The value far along the ray, and the jump across an edge -/

/-- Beyond the polygon in the ray direction the count is zero. -/
theorem parity_eq_zero_of_lt (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q : Plane}
    (h : ∀ z ∈ cover L, fwd u z < fwd u q) : parity u L q = 0 := by
  refine List.sum_eq_zero ?_
  intro x hx
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
  refine ite_eq_right ?_
  rintro ⟨h1, h2, h3⟩
  exact absurd (h _ (mem_cover hP (meet_mem_seg (hL P hP) h1 h2.le))) (not_lt.2 h3.le)

section Flip

variable (hu : Plane.IsDirection u)
include hu

/-- **Opposite sides of an edge** (Lemma 2.2, second half). At an interior point `p` of one
edge of the list which no other edge of the list passes through, the two points just before
and just after `p` in the ray direction lie off the polygon and have opposite parity: the
count changes by one as the base point sweeps across the edge. -/
theorem parity_flip {L₁ L₂ : List Piece} {a b p : Plane}
    (hL : ∀ P ∈ L₁ ++ (a, b) :: L₂, hgt u P.1 ≠ hgt u P.2)
    (hp : p ∈ openSegment ℝ a b) (h1 : p ∉ cover L₁) (h2 : p ∉ cover L₂) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      p + t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      parity u (L₁ ++ (a, b) :: L₂) (p - t • u)
        = parity u (L₁ ++ (a, b) :: L₂) (p + t • u) + 1 := by
  have hab : hgt u a ≠ hgt u b := hL (a, b) (by simp)
  have hpK : p ∉ cover (L₁ ++ L₂) := by
    rw [cover_append]
    rintro (h | h)
    · exact h1 h
    · exact h2 h
  obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hpK
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  -- the two test points and their frame coordinates
  have hneg : p - t • u = p + (-t) • u := by rw [neg_smul]; abel
  have hgm : hgt u (p - t • u) = hgt u p := by rw [hneg, hgt_along]
  have hgp : hgt u (p + t • u) = hgt u p := hgt_along p t
  have hfm : fwd u (p - t • u) = fwd u p - t := by rw [hneg, fwd_along hu]; ring
  have hfp : fwd u (p + t • u) = fwd u p + t := fwd_along hu p t
  have hdist : ∀ r : ℝ, |r| < ε → p + r • u ∈ ball p ε := by
    intro r hr
    have hsub : p + r • u - p = r • u := by abel
    rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, hu, mul_one]
    exact hr
  have habsm : |(-t)| < ε := by rw [abs_neg, abs_of_pos ht]; exact htε
  have habsp : |t| < ε := by rw [abs_of_pos ht]; exact htε
  -- the only point of the edge at the height of `p` is `p` itself
  have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
  have hmeetp : meet u a b (hgt u p) = p := (eq_meet hab hpseg).symm
  have hnotseg : ∀ r : ℝ, r ≠ 0 → p + r • u ∉ segment ℝ a b := by
    intro r hr hmem
    have heq : p + r • u = p := by
      rw [eq_meet hab hmem, hgt_along, hmeetp]
    have hf : fwd u (p + r • u) = fwd u p + r := fwd_along hu p r
    rw [heq] at hf
    exact hr (by linarith)
  have hcov : ∀ r : ℝ, r ≠ 0 → |r| < ε → p + r • u ∉ cover (L₁ ++ (a, b) :: L₂) := by
    intro r hr hrε hmem
    rw [cover_append, cover_cons] at hmem
    rcases hmem with h | h | h
    · exact hball _ (hdist r hrε) (by rw [cover_append]; exact Or.inl h)
    · exact hnotseg r hr h
    · exact hball _ (hdist r hrε) (by rw [cover_append]; exact Or.inr h)
  -- an edge other than `(a, b)` meets the level line far from `p`, so it is not affected
  have hfar : ∀ P ∈ L₁ ++ L₂, hgt u P.1 ≠ hgt u P.2 →
      min (hgt u P.1) (hgt u P.2) ≤ hgt u p → hgt u p ≤ max (hgt u P.1) (hgt u P.2) →
      ε ≤ |fwd u (meet u P.1 P.2 (hgt u p)) - fwd u p| := by
    intro P hP hPne g1 g2
    have hmcov : meet u P.1 P.2 (hgt u p) ∈ cover (L₁ ++ L₂) :=
      mem_cover hP (meet_mem_seg hPne g1 g2)
    have hmnb : ¬ (dist (meet u P.1 P.2 (hgt u p)) p < ε) := fun h =>
      hball _ (mem_ball.2 h) hmcov
    push Not at hmnb
    rw [dist_eq_norm] at hmnb
    have hh : hgt u (meet u P.1 P.2 (hgt u p) - p) = 0 := by
      rw [hgt_sub, hgt_meet hPne]; ring
    have hd := decomp hu (meet u P.1 P.2 (hgt u p) - p)
    rw [hh, zero_smul, add_zero] at hd
    have hnorm : ‖meet u P.1 P.2 (hgt u p) - p‖
        = |fwd u (meet u P.1 P.2 (hgt u p) - p)| := by
      conv_lhs => rw [hd]
      rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
    rw [hnorm, fwd_sub] at hmnb
    exact hmnb
  have hother : ∀ P ∈ L₁ ++ L₂, mark u P (p - t • u) + mark u P (p + t • u) = 0 := by
    intro P hP
    have hPne : hgt u P.1 ≠ hgt u P.2 := by
      rcases List.mem_append.1 hP with h | h
      · exact hL P (by simp [h])
      · exact hL P (by simp [h])
    have hiff : Crosses u P (p - t • u) ↔ Crosses u P (p + t • u) := by
      simp only [Crosses, hgm, hgp, hfm, hfp]
      constructor
      · rintro ⟨g1, g2, g3⟩
        refine ⟨g1, g2, ?_⟩
        rcases le_abs.1 (hfar P hP hPne g1 g2.le) with hcase | hcase
        · linarith
        · linarith
      · rintro ⟨g1, g2, g3⟩
        exact ⟨g1, g2, by linarith⟩
    simp only [mark, hiff]
    exact add_self_zmod_two _
  -- the edge `(a, b)` itself is crossed from exactly one of the two points
  have hbtw : min (hgt u a) (hgt u b) < hgt u p ∧ hgt u p < max (hgt u a) (hgt u b) := by
    rcases lt_or_gt_of_ne hab with h | h
    · obtain ⟨g1, g2⟩ := hgt_lt_of_mem_openSegment h hp
      rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨g1, g2⟩
    · obtain ⟨g1, g2⟩ := hgt_lt_of_mem_openSegment h (by rwa [openSegment_symm] at hp)
      rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨g1, g2⟩
  have hedge : mark u (a, b) (p - t • u) + mark u (a, b) (p + t • u) = 1 := by
    have hm1 : Crosses u (a, b) (p - t • u) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hgm]; exact hbtw.1.le
      · rw [hgm]; exact hbtw.2
      · rw [hgm, hfm, hmeetp]; linarith
    have hm2 : ¬ Crosses u (a, b) (p + t • u) := by
      rintro ⟨-, -, g⟩
      rw [hgp, hfp, hmeetp] at g
      linarith
    rw [mark, mark,
          ite_eq_left hm1,
      ite_eq_right hm2, add_zero]
  refine ⟨by rw [hneg]; exact hcov (-t) (by linarith) habsm, hcov t (ne_of_gt ht) habsp, ?_⟩
  have hz1 : (L₁.map (fun P => mark u P (p - t • u) + mark u P (p + t • u))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact hother P (List.mem_append_left _ hP)
  have hz2 : (L₂.map (fun P => mark u P (p - t • u) + mark u P (p + t • u))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact hother P (List.mem_append_right _ hP)
  have hsum : parity u (L₁ ++ (a, b) :: L₂) (p - t • u)
      + parity u (L₁ ++ (a, b) :: L₂) (p + t • u) = 1 := by
    rw [parity, parity, ← sum_map_add, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, hz1, hz2, hedge]
    ring
  have harith : ∀ x y : ZMod 2, x + y = 1 → x = y + 1 := by decide
  exact harith _ _ hsum

end Flip

/-! ### Choosing the ray direction -/

/-- The blueprint's opening move — "rotate so that no edge is horizontal" — without rotating
anything: finitely many edge directions rule out only finitely many rays, so some direction
is level for none of them. -/
theorem exists_direction_hgt_ne (L : List Piece) (hnd : ∀ P ∈ L, P.Nondeg) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2 := by
  obtain ⟨u, hu, hdet⟩ :=
    Plane.exists_isDirection_det_ne_zero (L.finite_toSet.image (fun P : Piece => P.2 - P.1))
  refine ⟨u, hu, fun P hP heq => ?_⟩
  have hne : P.2 - P.1 ≠ 0 := sub_ne_zero.2 fun h => hnd P hP h.symm
  have hzero : hgt u (P.2 - P.1) = 0 := by rw [hgt_sub, heq]; ring
  exact hdet _ ⟨P, hP, rfl⟩ hne hzero

end Schoenflies
