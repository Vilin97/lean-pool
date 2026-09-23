/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Plane

/-!
# Strongly accessible boundary points

A point `p` of the boundary of a region `D` is *strongly accessible* when an open disk
contained in `D` is tangent to the boundary at `p`. Ordinary accessibility (some arc in `D`
ending at `p`) is too weak for the iterative construction: what is wanted at `p` is a definite
wedge of straight segments running into `D`, which can then be shrunk to avoid any compact set
already built.

This module supplies that wedge. The tangent disk `B(q, r)` at `p` is turned into the open
cone `accessCone p v s` of points seen from `p` in a direction within 60 degrees of
`v = (q - p)/r` and at distance less than `s`; the content of Lemma 8.4 is that this cone lies
in the disk as soon as `s ≤ r`, and hence in `D`.

## Blueprint

* `Schoenflies.StronglyAccessible` — Definition 8.1 (strong accessibility).
* `Schoenflies.stronglyAccessible_of_isMinOn` — Lemma 8.2 (nearest points are strongly
  accessible).
* `Schoenflies.tangent_cone` — Lemma 8.4 (tangent-disk cone), in the literal form of the
  blueprint; `Schoenflies.accessCone_subset_ball` is the same estimate packaged as the
  inclusion of a truncated cone, which is the form the consumers use.
* `Schoenflies.exists_countable_dense_stronglyAccessible` — Proposition 8.5 (countable dense
  strong-access set).

Lemma 8.3 (density of strongly accessible points) is not formalized here: its proof runs
through `C = ∂D`, i.e. through the Jordan curve theorem, which is not yet available. Its role
is played by Proposition 8.5, which is stated with `C ⊆ closure D` as a hypothesis.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

variable {C D E : Set Plane} {p q v w : Plane} {r s s' t : ℝ}

/-! ### Strong accessibility -/

/-- Definition 8.1 (strong accessibility). A point `p` is *strongly accessible* from `D` when
some open disk of positive radius contained in `D` is tangent to `p`, that is, has `p` on its
boundary circle. -/
def StronglyAccessible (D : Set Plane) (p : Plane) : Prop :=
  ∃ (q : Plane) (r : ℝ), 0 < r ∧ dist q p = r ∧ ball q r ⊆ D

theorem StronglyAccessible.mono (h : StronglyAccessible D p) (hDE : D ⊆ E) :
    StronglyAccessible E p := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  exact ⟨q, r, hr, hd, hball.trans hDE⟩

/-- The centre of a tangent disk is not the point of tangency. -/
theorem StronglyAccessible.exists_ne (h : StronglyAccessible D p) :
    ∃ q ∈ D, p ≠ q := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  refine ⟨q, hball (mem_ball_self hr), fun hpq => ?_⟩
  rw [← hpq, dist_self] at hd
  exact absurd hd.symm hr.ne'

/-- Lemma 8.2 (nearest points are strongly accessible). If `a ∈ C` is nearest to a point `q`
off `C`, then the ball of radius `dist q a` around `q` misses `C`; being connected it stays
inside the connected component of `q` in the complement of `C`, so any set `D` containing that
component contains a disk tangent to `C` at `a`.

The hypothesis is phrased as `connectedComponentIn Cᶜ q ⊆ D` rather than as `D` being that
component, so that it can be discharged by an inclusion when `D` is known only up to
containment. No closedness of `C` is needed. -/
theorem stronglyAccessible_of_isMinOn {a : Plane} (hq : q ∉ C) (ha : a ∈ C)
    (hmin : ∀ b ∈ C, dist q a ≤ dist q b) (hD : connectedComponentIn Cᶜ q ⊆ D) :
    StronglyAccessible D a := by
  have hpos : 0 < dist q a := dist_pos.2 fun h => hq (h ▸ ha)
  refine ⟨q, dist q a, hpos, rfl, ?_⟩
  -- Every point strictly nearer to `q` than `a` is off `C`, by minimality.
  have hball : ball q (dist q a) ⊆ Cᶜ := by
    intro z hz hzC
    rw [mem_ball, dist_comm] at hz
    exact absurd (hmin z hzC) (not_le.2 hz)
  -- A ball is connected, so it lies in the component of its centre.
  exact ((convex_ball q (dist q a)).isPreconnected.subset_connectedComponentIn
    (mem_ball_self hpos) hball).trans hD

/-! ### The cone of access directions -/

/-- The open cone of straight access segments at `p` around the unit direction `v`, truncated
at radius `s`: the points seen from `p` in a direction `w` with `⟪v, w⟫ > 1/2` and at distance
less than `s`. Writing the condition as `‖x - p‖ / 2 < ⟪v, x - p⟫` avoids normalizing `x - p`,
and makes the openness of the cone immediate. -/
def accessCone (p v : Plane) (s : ℝ) : Set Plane :=
  {x | ‖x - p‖ < s ∧ ‖x - p‖ / 2 < inner ℝ v (x - p)}

theorem mem_accessCone_iff {x : Plane} :
    x ∈ accessCone p v s ↔ ‖x - p‖ < s ∧ ‖x - p‖ / 2 < inner ℝ v (x - p) := Iff.rfl

theorem accessCone_subset_ball_self : accessCone p v s ⊆ ball p s := fun x hx => by
  rw [mem_ball, dist_eq_norm]; exact hx.1

/-- The apex is not in the cone: the cone is a set of *access* points, all distinct from `p`. -/
theorem notMem_accessCone : p ∉ accessCone p v s := by
  intro h
  have := h.2
  simp at this

theorem accessCone_mono (hs : s ≤ s') : accessCone p v s ⊆ accessCone p v s' :=
  fun _ hx => ⟨hx.1.trans_le hs, hx.2⟩

/-- The cone is open. -/
theorem isOpen_accessCone : IsOpen (accessCone p v s) := by
  have h1 : Continuous fun x : Plane => ‖x - p‖ := (continuous_id.sub continuous_const).norm
  have h2 : Continuous fun x : Plane => inner ℝ v (x - p) :=
    continuous_const.inner (continuous_id.sub continuous_const)
  rw [accessCone, ofPred_and]
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt (h1.div_const 2) h2)

/-- Membership in the cone in the form used by the blueprint: a unit direction `w` making an
angle of less than 60 degrees with `v`, and a distance `t` below the truncation radius. -/
theorem mem_accessCone (hw : ‖w‖ = 1) (hcone : 1 / 2 < inner ℝ v w) (ht : 0 < t) (hts : t < s) :
    p + t • w ∈ accessCone p v s := by
  have hsub : p + t • w - p = t • w := by module
  have hnorm : ‖p + t • w - p‖ = t := by
    rw [hsub, norm_smul, hw, Real.norm_eq_abs, abs_of_pos ht, mul_one]
  refine ⟨by rw [hnorm]; exact hts, ?_⟩
  rw [hnorm, hsub, real_inner_smul_right]
  nlinarith

/-- The cone at `p` around the direction `v` is nonempty for every positive truncation radius:
the direction `v` itself is admissible. -/
theorem accessCone_nonempty (hv : ‖v‖ = 1) (hs : 0 < s) : (accessCone p v s).Nonempty := by
  refine ⟨p + (s / 2) • v, mem_accessCone hv ?_ (by linarith) (by linarith)⟩
  rw [real_inner_self_eq_norm_sq, hv]
  norm_num

/-- An open segment leaving `p` in an admissible direction lies in the cone. -/
theorem openSegment_subset_accessCone (hw : ‖w‖ = 1) (hcone : 1 / 2 < inner ℝ v w) (hs : 0 < s) :
    openSegment ℝ p (p + s • w) ⊆ accessCone p v s := by
  rintro x ⟨α, β, hα, hβ, hαβ, rfl⟩
  have hα' : α = 1 - β := by linarith
  subst hα'
  have hx : (1 - β) • p + β • (p + s • w) = p + (β * s) • w := by module
  rw [hx]
  exact mem_accessCone hw hcone (by positivity) (by nlinarith)

/-! ### The tangent-disk cone -/

/-- Lemma 8.4 (tangent-disk cone), in the form the construction uses. If the disk `B(q, r)` is
tangent at `p`, then the whole truncated cone around `v = (q - p)/r` of any radius `s ≤ r` lies
inside that disk.

The estimate behind it is the blueprint's: for `x` in the cone, with `d = ‖x - p‖`,
`‖x - q‖² = d² - 2⟪x - p, q - p⟫ + r² < d² - rd + r² = r² + d(d - r) < r²`. -/
theorem accessCone_subset_ball (hr : 0 < r) (hpq : ‖q - p‖ = r) (hs : s ≤ r) :
    accessCone p (r⁻¹ • (q - p)) s ⊆ ball q r := by
  rintro x ⟨hlt, hcone⟩
  set d := ‖x - p‖ with hd
  set I := inner ℝ (q - p) (x - p) with hI
  -- Clear the normalization: the cone condition is `r * d / 2 < ⟪q - p, x - p⟫`.
  rw [real_inner_smul_left] at hcone
  have hmul : r * (d / 2) < r * (r⁻¹ * I) := by
    exact mul_lt_mul_of_pos_left hcone hr
  have hcancel : r * (r⁻¹ * I) = I := by
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hcancel] at hmul
  -- The cone condition forces `x ≠ p`, since `I ≤ r * d` by Cauchy–Schwarz.
  have hcs : I ≤ r * d := by
    have := real_inner_le_norm (q - p) (x - p)
    rwa [hpq] at this
  have hd0 : 0 < d := by nlinarith [norm_nonneg (x - p)]
  have hdr : d < r := hlt.trans_le hs
  -- The estimate.
  have hxq : x - q = (x - p) - (q - p) := by module
  have key : ‖x - q‖ ^ 2 < r ^ 2 := by
    rw [hxq, norm_sub_sq_real, hpq, real_inner_comm]
    nlinarith
  rw [mem_ball, dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hr.le key

/-- Lemma 8.4 (tangent-disk cone), in the literal form of the blueprint: if `B(q, r)` is
tangent at `p`, `v = (q - p)/r`, and `w` is a unit vector with `⟪v, w⟫ > 1/2`, then the
straight ray from `p` in the direction `w` stays in the disk up to distance `r`. -/
theorem tangent_cone (hr : 0 < r) (hpq : ‖q - p‖ = r) (hw : ‖w‖ = 1)
    (hcone : 1 / 2 < inner ℝ (r⁻¹ • (q - p)) w) (ht : 0 < t) (htr : t < r) :
    p + t • w ∈ ball q r :=
  accessCone_subset_ball hr hpq le_rfl (mem_accessCone hw hcone ht htr)

/-- A strongly accessible point has a nonempty open cone of straight access segments into `D`,
and the cone may be truncated at any radius below the radius of the tangent disk — which is how
the construction makes it avoid a compact set already built. -/
theorem StronglyAccessible.exists_cone (h : StronglyAccessible D p) :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone p v s ⊆ D := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  have hpq : ‖q - p‖ = r := by rw [← dist_eq_norm]; exact hd
  refine ⟨r⁻¹ • (q - p), ?_, r, hr, fun s hs => (accessCone_subset_ball hr hpq hs).trans hball⟩
  rw [norm_smul, hpq, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_cancel₀ hr.ne']

/-- A strongly accessible point is the endpoint of a straight access segment: the open segment
from `p` to the centre of the tangent disk lies in `D`. -/
theorem StronglyAccessible.openSegment_subset (h : StronglyAccessible D p) :
    ∃ z ∈ D, p ≠ z ∧ openSegment ℝ p z ⊆ D := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  refine ⟨q, hball (mem_ball_self hr), ?_, ?_⟩
  · intro hpq
    rw [← hpq, dist_self] at hd
    exact absurd hd.symm hr.ne'
  · rintro x ⟨α, β, hα, hβ, hαβ, rfl⟩
    have hα' : α = 1 - β := by linarith
    subst hα'
    refine hball ?_
    have hx : (1 - β) • p + β • q - q = (1 - β) • (p - q) := by module
    rw [mem_ball, dist_eq_norm, hx, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
      ← dist_eq_norm, dist_comm, hd]
    nlinarith

/-! ### A countable dense set of strongly accessible points -/

/-- Proposition 8.5 (countable dense strong-access set). For every rational point of `D` pick a
nearest point of `C`; the chosen points are countably many, all strongly accessible, and dense
in `C`, since a point of `C` is approximated by points of `D` and the nearest point of `C` to
such a `q` is at most `dist q p` from `q`, hence at most `2 * dist q p` from `p`.

The hypothesis `C ⊆ closure D` replaces the blueprint's appeal to `C = ∂D` (Theorem 6.1);
`hDmax` says `D` swallows the connected component in `Cᶜ` of each of its points, which holds
when `D` is such a component. -/
theorem exists_countable_dense_stronglyAccessible (hC : IsCompact C) (hCne : C.Nonempty)
    (hDopen : IsOpen D) (hDC : D ⊆ Cᶜ) (hDmax : ∀ q ∈ D, connectedComponentIn Cᶜ q ⊆ D)
    (hCD : C ⊆ closure D) :
    ∃ A ⊆ C, A.Countable ∧ (∀ a ∈ A, StronglyAccessible D a) ∧ C ⊆ closure A := by
  -- A countable dense subset of the plane, cut down to `D`.
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense Plane
  -- A nearest point of `C` to each point of the plane.
  have hnear : ∀ x : Plane, ∃ a, a ∈ C ∧ ∀ b ∈ C, dist x a ≤ dist x b := by
    intro x
    obtain ⟨a, haC, hmin⟩ :=
      hC.exists_isMinOn hCne (Continuous.continuousOn (continuous_const.dist continuous_id))
    exact ⟨a, haC, fun b hb => isMinOn_iff.1 hmin b hb⟩
  choose f hfC hfmin using hnear
  refine ⟨f '' (S ∩ D), ?_, (hScount.mono inter_subset_left).image f, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hfC x
  · rintro _ ⟨x, hx, rfl⟩
    exact stronglyAccessible_of_isMinOn (hDC hx.2) (hfC x) (hfmin x) (hDmax x hx.2)
  · -- Density.
    intro p hp
    rw [Metric.mem_closure_iff]
    intro ε hε
    -- A point of `D` within `ε/2` of `p` …
    obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.1 (hCD hp) (ε / 2) (by linarith)
    -- … and, `D` being open, a point of `S ∩ D` still within `ε/2` of `p`.
    obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.1 hDopen y hyD
    obtain ⟨z, hzS, hz⟩ := hSdense.exists_dist_lt y (lt_min hδ (by linarith : 0 < ε / 2 - dist p y))
    have hzD : z ∈ D := hδD (by rw [mem_ball, dist_comm]; exact hz.trans_le (min_le_left _ _))
    have hpz : dist p z < ε / 2 := by
      have := (dist_triangle p y z).trans_lt
        (by linarith [hz.trans_le (min_le_right δ (ε / 2 - dist p y))] :
          dist p y + dist y z < ε / 2)
      exact this
    -- The chosen nearest point to `z` is at most `dist z p` from `z`.
    refine ⟨f z, ⟨z, ⟨hzS, hzD⟩, rfl⟩, ?_⟩
    have h1 : dist z (f z) ≤ dist z p := hfmin z p hp
    have h2 : dist p (f z) ≤ dist p z + dist z (f z) := dist_triangle _ _ _
    rw [dist_comm z p] at h1
    linarith

end Schoenflies
