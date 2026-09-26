/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Plane

/-!
# Directions, and the two arcs cut out by a pair of rays

This module supplies the *direction facts* that the two-sided strip lemma runs on. Everything
here is stated through the sign of the orientation form `Plane.det`: no angle is named, no
inverse trigonometric function appears, and no case distinction on the sense of a turn is
ever made.

A *direction* is a unit vector (`Plane.IsDirection`). What actually matters about a direction
is its ray — the set of its positive multiples — because every predicate below is invariant
under positive scaling (`Plane.smul_mem_arcCCW`). So the arcs are defined on all nonzero
vectors and the unit-vector normalisation `Plane.dir` is only a convenience.

## The two arcs

Two directions `u` and `w` that are neither equal nor opposite are exactly two directions with
`det u w ≠ 0` (`Plane.det_ne_zero_iff`). They cut the circle of directions into two open arcs.
The arc traversed counterclockwise from `u` to `w` is `Plane.arcCCW u w`, defined by Sedgewick's
`ccw` predicate on the triple `(u, d, w)`: at least two of the three consecutive orientation
forms are positive. This definition is manifestly invariant under rotating the triple, and — this
is the point — it is correct for *both* arcs at once, the short one and the long one, with no
sign hypothesis in the definition itself.

`Plane.mem_ray_or_mem_arcCCW` and `Plane.arcCCW_disjoint` say that the two arcs and the two
bounding rays partition the nonzero vectors.

## The transfer fact

`Plane.same_arc_of_det_neg_of_det_pos` is Appendix C's transfer fact: *a direction with negative
`det` against the first ray lies on the same arc as a direction with positive `det` against the
second*. Note that no nearness hypothesis is needed for it — see the module note below.

## Blueprint

* `Plane.IsDirection`, `Plane.dir`, `Plane.arcCCW`, `Plane.det_ne_zero_iff`,
  `Plane.mem_ray_or_mem_arcCCW`, `Plane.arcCCW_disjoint` — Appendix C, item 1, "two distinct,
  non-opposite unit vectors bound two open arcs of directions".
* `Plane.same_arc_of_det_neg_of_det_pos` — Appendix C, item 1, the transfer fact.
* `Plane.exists_isDirection_det_ne_zero`, `Plane.exists_isDirection_det_and_inner_ne_zero` —
  Appendix C, item 1, "the existence of a unit vector avoiding any prescribed finite set of
  directions".
* `Plane.germs_split`, `Plane.exists_germ_threshold` — the vertex matching inside Lemma 1.8
  (Two-sided polygonal strips): the two left half-strip germs land on one arc and the two right
  ones on the other.

## A note on "near"

Appendix C states the transfer fact for directions *near* the two bounding rays. The nearness is
not needed: `Plane.mem_arcCCW_rev_iff` shows that the arc counterclockwise from `w` to `u` is cut
out by a *disjunction* of two sign conditions, so a single sign suffices to land on it. The
mirror statement — a direction with positive `det` against `u` and one with negative `det`
against `w` both lie on `arcCCW u w` — is *not* available from one sign each, because that arc is
cut out by the *conjunction* (`Plane.mem_arcCCW_iff`). Lemma 1.8 needs the mirror statement too,
for the two right germs, and there the missing second sign is exactly what "`s/t` small" buys:
`Plane.exists_germ_threshold` supplies it, with an explicit threshold.
-/

public section

open Set

namespace Schoenflies

namespace Plane

variable {u w d d₁ d₂ r₁ r₂ v : Plane} {r t s : ℝ}

/-! ### Directions -/

/-- A *direction* is a unit vector. Only the ray a direction spans ever matters below, but
normalising to unit length gives a canonical representative of that ray. -/
def IsDirection (u : Plane) : Prop := ‖u‖ = 1

theorem IsDirection.ne_zero (hu : IsDirection u) : u ≠ 0 := by
  intro h
  rw [IsDirection, h, norm_zero] at hu
  exact zero_ne_one hu

theorem IsDirection.norm (hu : IsDirection u) : ‖u‖ = 1 := hu

/-- The unit vector along a nonzero vector. -/
noncomputable def dir (u : Plane) : Plane := ‖u‖⁻¹ • u

theorem isDirection_dir (hu : u ≠ 0) : IsDirection (dir u) := by
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [IsDirection, dir, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

theorem dir_ne_zero (hu : u ≠ 0) : dir u ≠ 0 := (isDirection_dir hu).ne_zero

/-- `dir u` is a positive multiple of `u`, which is why every sign-of-`det` predicate is blind
to the difference. -/
theorem dir_eq_smul (hu : u ≠ 0) : ∃ c : ℝ, 0 < c ∧ dir u = c • u :=
  ⟨‖u‖⁻¹, inv_pos.2 (norm_pos_iff.2 hu), rfl⟩

/-! ### Nonvanishing of `det` -/

theorem ne_zero_left_of_det_ne_zero (h : det u w ≠ 0) : u ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

theorem ne_zero_right_of_det_ne_zero (h : det u w ≠ 0) : w ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

/-- Two directions are neither equal nor opposite exactly when the orientation form does not
kill them. This is the angle-free reading of "two distinct, non-opposite unit vectors". -/
theorem det_ne_zero_iff (hu : IsDirection u) (hw : IsDirection w) :
    det u w ≠ 0 ↔ w ≠ u ∧ w ≠ -u := by
  constructor
  · intro h
    refine ⟨fun he => h (by rw [he]; simp), fun he => h ?_⟩
    rw [he, show (-u : Plane) = (-1 : ℝ) • u by module, det_smul_right, det_self, mul_zero]
  · rintro ⟨hne, hopp⟩ h
    -- `det u w = 0` makes `w` a multiple of `u`; unit length pins the factor to `±1`.
    obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u w hu.ne_zero).1 h
    have hc : |c| = 1 := by
      have := hw.norm
      rwa [norm_smul, Real.norm_eq_abs, hu.norm, mul_one] at this
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hc with rfl | rfl
    · exact hne (one_smul ℝ u)
    · exact hopp (by module)

/-! ### The two arcs -/

/-- The open arc of directions traversed counterclockwise from `u` to `w`.

A nonzero `d` lies on it when at least two of the three consecutive orientation forms of the
triple `(u, d, w)` are positive. The definition is a cyclic condition, so it is correct for the
short arc and for the long arc alike, with no hypothesis on the sign of `det u w`. -/
@[expose] def arcCCW (u w : Plane) : Set Plane :=
  {d | (0 < det u d ∧ 0 < det d w) ∨ (0 < det d w ∧ 0 < det w u) ∨ (0 < det w u ∧ 0 < det u d)}

/-- Fix the orientation by `0 < det u w`, so that `w` is counterclockwise of `u` by less than a
half turn. Then the arc counterclockwise from `u` to `w` is the *short* one, and membership is
the conjunction of two sign conditions. -/
theorem mem_arcCCW_iff (h : 0 < det u w) : d ∈ arcCCW u w ↔ 0 < det u d ∧ 0 < det d w := by
  have hwu : det w u < 0 := by rw [det_comm w u]; linarith
  refine ⟨?_, Or.inl⟩
  rintro (h1 | ⟨_, h2⟩ | ⟨h2, _⟩)
  · exact h1
  · linarith
  · linarith

/-- With the same orientation `0 < det u w`, the arc counterclockwise from `w` back to `u` is the
*long* one — more than a half turn — and membership is a **disjunction**. This asymmetry is the
whole content of the transfer fact: one sign suffices here, two are needed on the short arc. -/
theorem mem_arcCCW_rev_iff (h : 0 < det u w) :
    d ∈ arcCCW w u ↔ det u d < 0 ∨ det d w < 0 := by
  have e1 : det w d = -det d w := det_comm w d
  have e2 : det d u = -det u d := det_comm d u
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h2, _⟩ | ⟨_, h1⟩)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inr (by rw [e1] at h1; linarith)
  · rintro (h1 | h2)
    · exact Or.inr (Or.inl ⟨by rw [e2]; linarith, h⟩)
    · exact Or.inr (Or.inr ⟨h, by rw [e1]; linarith⟩)

/-- The two arcs are disjoint. -/
theorem arcCCW_disjoint (h : 0 < det u w) : Disjoint (arcCCW u w) (arcCCW w u) := by
  rw [Set.disjoint_left]
  intro d hd hd'
  rw [mem_arcCCW_iff h] at hd
  rw [mem_arcCCW_rev_iff h] at hd'
  rcases hd' with h' | h' <;> linarith [hd.1, hd.2]

/-- Every sign-of-`det` condition is blind to positive rescaling, so the arcs really are sets of
*rays*, not of vectors. -/
theorem smul_mem_arcCCW (hr : 0 < r) : r • d ∈ arcCCW u w ↔ d ∈ arcCCW u w := by
  have key : ∀ x : ℝ, 0 < r * x ↔ 0 < x := by
    intro x
    constructor <;> intro hx <;> nlinarith
  simp only [arcCCW, Set.mem_ofPred_eq, det_smul_left, det_smul_right, key]

theorem dir_mem_arcCCW_iff (hd : d ≠ 0) : dir d ∈ arcCCW u w ↔ d ∈ arcCCW u w := by
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul hd
  rw [hcd, smul_mem_arcCCW hc]

/-- The two rays and the two arcs exhaust the nonzero vectors. Together with
`Plane.arcCCW_disjoint` this is the statement that two distinct, non-opposite directions bound
two arcs. -/
theorem mem_ray_or_mem_arcCCW (h : 0 < det u w) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • u) ∨ (∃ c : ℝ, 0 < c ∧ d = c • w) ∨
      d ∈ arcCCW u w ∨ d ∈ arcCCW w u := by
  have hu : u ≠ 0 := ne_zero_left_of_det_ne_zero h.ne'
  have hw : w ≠ 0 := ne_zero_right_of_det_ne_zero h.ne'
  by_cases hneg : det u d < 0 ∨ det d w < 0
  · exact Or.inr (Or.inr (Or.inr ((mem_arcCCW_rev_iff h).2 hneg)))
  push Not at hneg
  obtain ⟨h1, h2⟩ := hneg
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · exact Or.inr (Or.inr (Or.inl ((mem_arcCCW_iff h).2 ⟨h1', h2'⟩)))
    · -- `det d w = 0`: `d` lies along the line of `w`, and `det u d ≥ 0` fixes the sign.
      obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul w d hw).1 (by rw [det_comm w d, ← h2']; ring)
      refine Or.inr (Or.inl ⟨c, ?_, rfl⟩)
      rw [det_smul_right] at h1'
      nlinarith
  · -- `det u d = 0`: `d` lies along the line of `u`, and `det d w ≥ 0` fixes the sign.
    obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u d hu).1 h1'.symm
    refine Or.inl ⟨c, ?_, rfl⟩
    rw [det_smul_left] at h2
    rcases lt_or_eq_of_le h2 with h2' | h2'
    · nlinarith
    · exfalso
      have : c = 0 := by
        rcases mul_eq_zero.1 h2'.symm with hc | hd'
        · exact hc
        · exact absurd hd' h.ne'
      exact hd (by rw [this, zero_smul])

/-! ### The transfer fact -/

/-- A direction with **negative** `det` against `u` lies on the arc counterclockwise from `w`
to `u`. No nearness hypothesis is needed. -/
theorem mem_arcCCW_rev_of_det_neg (h : 0 < det u w) (hd : det u d < 0) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inl hd)

/-- A direction with **positive** `det` against `w` lies on the arc counterclockwise from `w`
to `u`. No nearness hypothesis is needed. -/
theorem mem_arcCCW_rev_of_det_pos (h : 0 < det u w) (hd : 0 < det w d) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inr (by rw [det_comm d w]; linarith))

/-- **Appendix C, transfer.** A direction with negative `det` against the first ray lies on the
same arc as a direction with positive `det` against the second: both lie on the arc traversed
counterclockwise from the second ray to the first. -/
theorem same_arc_of_det_neg_of_det_pos (h : 0 < det u w) (h₁ : det u d₁ < 0) (h₂ : 0 < det w d₂) :
    d₁ ∈ arcCCW w u ∧ d₂ ∈ arcCCW w u :=
  ⟨mem_arcCCW_rev_of_det_neg h h₁, mem_arcCCW_rev_of_det_pos h h₂⟩

/-- The mirror form, for the other pair of germs: a direction with positive `det` against `u`
**and** negative `det` against `w` lies on the arc counterclockwise from `u` to `w`. Here both
signs are genuinely needed; see the module note. -/
theorem mem_arcCCW_of_det_pos_of_det_neg (h : 0 < det u w) (h₁ : 0 < det u d) (h₂ : det w d < 0) :
    d ∈ arcCCW u w :=
  (mem_arcCCW_iff h).2 ⟨h₁, by rw [det_comm d w]; linarith⟩

/-! ### Half-strip germs

Fix a vertex with incoming unit tangent `u` and outgoing unit tangent `w`, and let `r₁ = -u`,
`r₂ = w` be the two rays leaving the vertex, so that `perp r₁ = -u^⊥` and `perp r₂ = w^⊥`.
Then the four half-strip germs of Lemma 1.8 are, in the blueprint's own notation,

* incoming left, `-t u + s u^⊥ = t • r₁ - s • perp r₁`;
* outgoing left, `t w + s w^⊥ = t • r₂ + s • perp r₂`;
* incoming right, `-t u - s u^⊥ = t • r₁ + s • perp r₁`;
* outgoing right, `t w - s w^⊥ = t • r₂ - s • perp r₂`,

each with `t, s > 0`. The four computations below place them on the two arcs. -/

/-- The orientation form of a germ against its own tangent sees only the transverse
coefficient: this is the blueprint's `det(r₁, d) = -s` and `det(r₂, d) = s`. -/
theorem det_germ_self (r : Plane) (t s : ℝ) :
    det r (t • r + s • perp r) = s * ‖r‖ ^ 2 := by
  rw [det_add_right, det_smul_right, det_smul_right, det_self, det_perp_self]
  ring

theorem det_germ_self' (r : Plane) (t s : ℝ) :
    det (t • r + s • perp r) r = -(s * ‖r‖ ^ 2) := by
  rw [det_comm, det_germ_self]

/-- The orientation form of a germ at `r₁` against the *other* ray. The inner-product term is
what makes the transverse coefficient have to be small relative to the longitudinal one. -/
theorem det_germ (r₁ r₂ : Plane) (t s : ℝ) :
    det (t • r₁ + s • perp r₁) r₂ = t * det r₁ r₂ - s * inner ℝ r₁ r₂ := by
  rw [det_add_left, det_smul_left, det_smul_left, det_perp_left]
  ring

/-- The orientation form of a germ at `r₂` against the other ray. -/
theorem det_germ' (r₁ r₂ : Plane) (t s : ℝ) :
    det r₁ (t • r₂ + s • perp r₂) = t * det r₁ r₂ + s * inner ℝ r₁ r₂ := by
  rw [det_add_right, det_smul_right, det_smul_right, det_perp_right]

private theorem sq_norm_pos_left (h : 0 < det r₁ r₂) : 0 < ‖r₁‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_left_of_det_ne_zero h.ne')) 2

private theorem sq_norm_pos_right (h : 0 < det r₁ r₂) : 0 < ‖r₂‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_right_of_det_ne_zero h.ne')) 2

/-- The **incoming left** germ lands on the arc counterclockwise from `r₂` to `r₁`, for *every*
longitudinal coefficient `t`: this is the half of the vertex matching that costs nothing,
because that arc is cut out by a disjunction. -/
theorem germ_mem_arcCCW_rev_of_left (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_neg h ?_
  have e : t • r₁ - s • perp r₁ = t • r₁ + (-s) • perp r₁ := by module
  rw [e, det_germ_self]
  nlinarith [sq_norm_pos_left h]

/-- The **outgoing left** germ lands on the same arc, again for every `t`. -/
theorem germ_mem_arcCCW_rev_of_right (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_pos h ?_
  rw [det_germ_self]
  exact mul_pos hs (sq_norm_pos_right h)

/-- The **incoming right** germ lands on the arc counterclockwise from `r₁` to `r₂` provided the
transverse coefficient is small enough against the longitudinal one. The inequality
`s ⟪r₁, r₂⟫ < t det(r₁, r₂)` is exactly "`s/t` small", written without a division. -/
theorem germ_mem_arcCCW_of_left (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ := by
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [det_germ_self]
    exact mul_pos hs (sq_norm_pos_left h)
  · rw [det_germ]
    linarith

/-- The **outgoing right** germ lands on the same arc, under the same smallness condition. -/
theorem germ_mem_arcCCW_of_right (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂ := by
  have e : t • r₂ - s • perp r₂ = t • r₂ + (-s) • perp r₂ := by module
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [e, det_germ']
    linarith
  · rw [e, det_germ_self']
    nlinarith [sq_norm_pos_right h]

/-- **The vertex matching of Lemma 1.8.** With the strips narrow enough — `s ⟪r₁, r₂⟫` under
`t det(r₁, r₂)` — the two left germs lie on one arc and the two right germs on the other. No
angle is named and no case distinction on the sense of the turn arises: the two cases of the
turn are the two orders in which `r₁` and `r₂` may be presented, and `det_comm` exchanges
them. -/
theorem germs_split (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) :=
  ⟨⟨germ_mem_arcCCW_rev_of_left h hs t, germ_mem_arcCCW_rev_of_right h hs t⟩,
    ⟨germ_mem_arcCCW_of_left h hs hsmall, germ_mem_arcCCW_of_right h hs hsmall⟩⟩

/-- The quantitative form: there is a slope threshold below which the vertex matching holds.
This is what "make the strips narrow enough that this side matching holds in every vertex disk"
means in Lemma 1.8, and it is the one place where a size condition, rather than a bare sign of
`det`, is unavoidable. -/
theorem exists_germ_threshold (h : 0 < det r₁ r₂) :
    ∃ ε > 0, ∀ t s : ℝ, 0 < t → 0 < s → s < ε * t →
      (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
        (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) := by
  set A : ℝ := |inner ℝ r₁ r₂| with hA
  have hA0 : (0 : ℝ) < 1 + A := by positivity
  refine ⟨det r₁ r₂ / (1 + A), by positivity, fun t s _ hs hlt => germs_split h hs ?_⟩
  -- Clear the denominator in `s < (det r₁ r₂ / (1 + A)) * t`.
  have hmul := mul_lt_mul_of_pos_right hlt hA0
  have hclear : det r₁ r₂ / (1 + A) * t * (1 + A) = det r₁ r₂ * t := by
    field_simp
  rw [hclear] at hmul
  have hle : inner ℝ r₁ r₂ ≤ A := le_abs_self _
  nlinarith

/-! ### A direction avoiding finitely many others

The argument is a counting one, with no measure and no trigonometry: the one-parameter family
`a ↦ (1, a)` meets the line of any fixed nonzero vector at most once, so finitely many vectors
rule out only finitely many parameters, and `ℝ` has more than finitely many. -/

/-- The family used to dodge finitely many directions. -/
private theorem mk_one_ne_zero (a : ℝ) : mk 1 a ≠ 0 := by
  intro h
  have h0 : mk 1 a 0 = (0 : Plane) 0 := by rw [h]
  simp at h0

private theorem det_mk_one (a : ℝ) (v : Plane) : det (mk 1 a) v = v 1 - a * v 0 := by
  simp [det]

/-- **Appendix C.** There is a unit vector not parallel to any of a prescribed finite set of
nonzero vectors. This is what lets one rotate coordinates so that no edge of a finite polygonal
figure is horizontal. -/
theorem exists_isDirection_det_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 := by
  -- The parameters ruled out by `S` are the slopes of its members, hence at most as many as `S`.
  have hbad : {a : ℝ | ∃ v ∈ S, v ≠ 0 ∧ det (mk 1 a) v = 0}.Finite := by
    refine Set.Finite.subset (hS.image fun v => v 1 / v 0) ?_
    rintro a ⟨v, hv, hv0, hdet⟩
    rw [det_mk_one] at hdet
    have h0 : v 0 ≠ 0 := by
      intro h
      refine hv0 ?_
      have h1 : v 1 = 0 := by rw [h] at hdet; linarith
      ext i
      fin_cases i <;> simp [h, h1]
    exact ⟨v, hv, by field_simp; linarith⟩
  obtain ⟨a, ha⟩ := hbad.infinite_compl.nonempty
  refine ⟨dir (mk 1 a), isDirection_dir (mk_one_ne_zero a),
    fun v hv hv0 hdet => ha ⟨v, hv, hv0, ?_⟩⟩
  -- `dir` only rescales, so it cannot create a vanishing orientation form.
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul (mk_one_ne_zero a)
  rw [hcd, det_smul_left] at hdet
  rcases mul_eq_zero.1 hdet with h | h
  · exact absurd h hc.ne'
  · exact h

/-- The same, dodging the perpendicular directions too: a unit vector `u` for which no member of
a prescribed finite set of nonzero vectors is either parallel or perpendicular to `u`. In the
rotated coordinates this says that no edge is horizontal and none is vertical. -/
theorem exists_isDirection_det_and_inner_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 ∧ inner ℝ u v ≠ 0 := by
  obtain ⟨u, hu, hdet⟩ := exists_isDirection_det_ne_zero (hS.union (hS.image perp))
  refine ⟨u, hu, fun v hv hv0 => ⟨hdet v (Or.inl hv) hv0, ?_⟩⟩
  -- `det u (perp v) = ⟪u, v⟫`, so dodging `perp v` is dodging the perpendicular.
  have hpv : perp v ≠ 0 := by
    intro h
    exact hv0 (by have := norm_perp v; rw [h, norm_zero] at this; exact norm_eq_zero.1 this.symm)
  have := hdet (perp v) (Or.inr ⟨v, hv, rfl⟩) hpv
  rwa [det_perp_right] at this

/-! ### The arcs are open

Not needed by Lemma 1.8, which uses only the partition, but it justifies the word "open" in
"two open arcs of directions". -/

theorem continuous_det_right (u : Plane) : Continuous fun d : Plane => det u d := by
  refine Continuous.sub (Continuous.mul continuous_const ?_) (Continuous.mul continuous_const ?_)
  · exact PiLp.continuous_apply _ _ 1
  · exact PiLp.continuous_apply _ _ 0

theorem continuous_det_left (w : Plane) : Continuous fun d : Plane => det d w := by
  refine Continuous.sub (Continuous.mul ?_ continuous_const) (Continuous.mul ?_ continuous_const)
  · exact PiLp.continuous_apply _ _ 0
  · exact PiLp.continuous_apply _ _ 1

theorem isOpen_arcCCW (u w : Plane) : IsOpen (arcCCW u w) := by
  have h1 : IsOpen {d : Plane | 0 < det u d} := isOpen_lt continuous_const (continuous_det_right u)
  have h2 : IsOpen {d : Plane | 0 < det d w} := isOpen_lt continuous_const (continuous_det_left w)
  by_cases h : 0 < det w u
  · have : arcCCW u w = {d : Plane | 0 < det u d} ∪ {d : Plane | 0 < det d w} := by
      ext d
      simp only [arcCCW, Set.mem_ofPred_eq, mem_union]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h2, _⟩ | ⟨_, h1⟩) <;> tauto
      · rintro (hx | hx)
        · exact Or.inr (Or.inr ⟨h, hx⟩)
        · exact Or.inr (Or.inl ⟨hx, h⟩)
    rw [this]
    exact h1.union h2
  · have : arcCCW u w = {d : Plane | 0 < det u d} ∩ {d : Plane | 0 < det d w} := by
      ext d
      simp only [arcCCW, Set.mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro (hx | ⟨_, hx⟩ | ⟨hx, _⟩) <;> [exact hx; exact absurd hx h; exact absurd hx h]
      · exact Or.inl
    rw [this]
    exact h1.inter h2

end Plane

end Schoenflies
