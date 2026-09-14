/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The plane, and the compactness toolkit

The plane is `EuclideanSpace ℝ (Fin 2)`. This module fixes that choice, supplies the
orientation form `det` and the right-angle rotation `perp` used to keep track of the two
sides of a polygonal curve, and collects the elementary consequences of compactness and
connectedness that the rest of the development uses without comment.

## Blueprint

* `det`, `perp` — Appendix C, item 1.
* `Plane.notMem_of_mem_segment_of_isMinOn` — Lemma 1.3 (nearest-point segment).
* `Plane.exists_thickening_subset`, `Plane.exists_dist_pos`, `Plane.exists_ball_subset_diff`
  — Lemma 1.4 (a), (b), (c) (compact separation).
* `Plane.eq_singleton_iInter_of_diam_tendsto_zero` — Lemma 1.6 (nested compact singleton).
* `Plane.connectedComponentIn_eq_of_frontier_disjoint` — Lemma 1.7 (recognizing a component).

Lemma 1.5 (closure and diameter) is `Metric.diam_closure` in Mathlib.
-/

open Metric Set

namespace Schoenflies

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Plane

/-- Build a point of the plane from its two coordinates. -/
abbrev mk (x y : ℝ) : Plane := !₂[x, y]

@[simp] theorem mk_zero (x y : ℝ) : mk x y 0 = x := rfl
@[simp] theorem mk_one (x y : ℝ) : mk x y 1 = y := rfl

/-! ### The orientation form and the right-angle rotation -/

/-- The orientation form `det (a, b) = a₁b₂ - a₂b₁`. It is positive exactly when `b` lies
counterclockwise of `a`. -/
def det (a b : Plane) : ℝ := a 0 * b 1 - a 1 * b 0

/-- `u` turned counterclockwise through a right angle. -/
def perp (u : Plane) : Plane := mk (-u 1) (u 0)

@[simp] theorem perp_zero (u : Plane) : perp u 0 = -u 1 := rfl
@[simp] theorem perp_one (u : Plane) : perp u 1 = u 0 := rfl

@[simp] theorem det_self (a : Plane) : det a a = 0 := by simp [det]; ring

theorem det_comm (a b : Plane) : det a b = -det b a := by simp [det]; ring

@[simp] theorem det_smul_left (r : ℝ) (a b : Plane) : det (r • a) b = r * det a b := by
  simp [det]; ring

@[simp] theorem det_smul_right (r : ℝ) (a b : Plane) : det a (r • b) = r * det a b := by
  simp [det]; ring

theorem det_add_left (a b c : Plane) : det (a + b) c = det a c + det b c := by
  simp [det]; ring

theorem det_add_right (a b c : Plane) : det a (b + c) = det a b + det a c := by
  simp [det]; ring

/-- The defining property of `perp`: it is the counterclockwise right-angle rotation, so it
pairs positively with its argument. -/
@[simp] theorem det_perp_self (u : Plane) : det u (perp u) = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [det, Fin.sum_univ_two]
  ring

theorem inner_eq (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- Turning twice reverses. -/
@[simp] theorem perp_perp (u : Plane) : perp (perp u) = -u := by
  ext i; fin_cases i <;> simp

@[simp] theorem inner_perp_self (u : Plane) : inner ℝ u (perp u) = 0 := by
  rw [inner_eq]; simp; ring

/-- Against `perp` on the right, `det` becomes the inner product. Together with
`det_perp_left` this is what lets the strip lemma trade one for the other. -/
@[simp] theorem det_perp_right (u v : Plane) : det u (perp v) = inner ℝ u v := by
  rw [inner_eq]; simp [det]

@[simp] theorem det_perp_left (u v : Plane) : det (perp u) v = -inner ℝ u v := by
  rw [inner_eq]; simp [det]; ring

@[simp] theorem det_perp_perp (u v : Plane) : det (perp u) (perp v) = det u v := by
  simp [det]; ring

@[simp] theorem norm_perp (u : Plane) : ‖perp u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, sq_abs]
  ring

/-- Two vectors are parallel exactly when the orientation form kills them. This is the
angle-free reading of "`u` and `v` point along one line". -/
theorem det_eq_zero_iff_smul (u v : Plane) (hu : u ≠ 0) :
    det u v = 0 ↔ ∃ r : ℝ, v = r • u := by
  constructor
  · intro h
    -- `u ≠ 0` means some coordinate is nonzero; solve for the ratio there.
    have hcoord : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu (by ext i; fin_cases i <;> simp [hc.1, hc.2])
    simp only [det, sub_eq_zero] at h
    rcases hcoord with h0 | h1
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp; linarith
    · refine ⟨v 1 / u 1, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp; linarith
  · rintro ⟨r, rfl⟩
    simp

/-! ### Compactness -/

variable {K L U V : Set Plane} {x a y : Plane}

/-- Lemma 1.3 (nearest-point segment). If `a` is a point of `K` nearest to `x ∉ K`, then the
half-open segment `[x, a)` misses `K`. -/
theorem notMem_of_mem_segment_of_isMinOn (haK : a ∈ K) (hxK : x ∉ K)
    (hmin : ∀ b ∈ K, dist x a ≤ dist x b) (hy : y ∈ segment ℝ x a) (hya : y ≠ a) :
    y ∉ K := by
  intro hyK
  -- `a ≠ x`, since `a ∈ K` and `x ∉ K`, so the segment is nondegenerate.
  have hax : a ≠ x := fun h => hxK (h ▸ haK)
  have hpos : 0 < dist x a := dist_pos.2 (Ne.symm hax)
  -- Write `y = x + t • (a - x)` with `0 ≤ t ≤ 1`; `t = 1` is excluded by `y ≠ a`.
  rw [segment_eq_image' ℝ x a] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have ht1 : t < 1 := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · exact absurd (by rw [h]; module) hya
  -- Then `dist x y = t * dist x a < dist x a`, contradicting minimality.
  have hdist : dist x (x + t • (a - x)) = t * dist x a := by
    rw [dist_eq_norm, dist_eq_norm]
    have : x - (x + t • (a - x)) = t • (x - a) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have := hmin _ hyK
  rw [hdist] at this
  nlinarith

/-- Lemma 1.4 (a) (compact separation). A compact set inside an open set has a uniform
neighbourhood inside it. Empty `K` is allowed: `thickening ρ ∅ = ∅`. -/
theorem exists_thickening_subset (hK : IsCompact K) (hU : IsOpen U) (h : K ⊆ U) :
    ∃ ρ > 0, thickening ρ K ⊆ U :=
  hK.exists_thickening_subset_open hU h

/-- Lemma 1.4 (b) (compact separation). Two disjoint nonempty compact sets have positive
distance. -/
theorem exists_dist_pos (hK : IsCompact K) (hL : IsCompact L) (hd : Disjoint K L) :
    ∃ ρ > 0, ∀ p ∈ K, ∀ q ∈ L, ρ ≤ dist p q := by
  obtain ⟨ρ, hρ, hsub⟩ :=
    hK.exists_thickening_subset_open hL.isClosed.isOpen_compl (disjoint_left.1 hd)
  refine ⟨ρ, hρ, fun p hp q hq => ?_⟩
  by_contra hlt
  exact hsub (mem_thickening_iff.2 ⟨p, hp, by rw [dist_comm]; exact not_le.1 hlt⟩) hq

/-- Lemma 1.4 (c) (compact separation). A point of an open set off a compact set has a ball
inside the difference. -/
theorem exists_ball_subset_diff (hU : IsOpen U) (hK : IsCompact K) (hx : x ∈ U \ K) :
    ∃ ρ > 0, ball x ρ ⊆ U \ K := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx.1
  obtain ⟨s, hs, hsK⟩ :=
    (isCompact_singleton (x := x)).exists_thickening_subset_open hK.isClosed.isOpen_compl
      (by simpa using hx.2)
  refine ⟨min r s, lt_min hr hs, fun z hz => ⟨hrU (ball_subset_ball (min_le_left _ _) hz), ?_⟩⟩
  exact hsK (mem_thickening_iff.2 ⟨x, rfl, lt_of_lt_of_le (mem_ball.1 hz) (min_le_right _ _)⟩)

/-- Lemma 1.6 (nested compact singleton). A decreasing sequence of nonempty compact sets whose
diameters tend to `0` has a single point in its intersection. -/
theorem eq_singleton_iInter_of_diam_tendsto_zero {K : ℕ → Set Plane}
    (hne : ∀ n, (K n).Nonempty) (hK : ∀ n, IsCompact (K n)) (hmono : Antitone K)
    (hdiam : Filter.Tendsto (fun n => diam (K n)) Filter.atTop (nhds 0)) :
    ∃ p, ⋂ n, K n = {p} := by
  have hnonempty : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => hmono (Nat.le_succ n)) hne (hK 0) (fun n => (hK n).isClosed)
  obtain ⟨p, hp⟩ := hnonempty
  refine ⟨p, subset_antisymm (fun q hq => ?_) (by simpa using hp)⟩
  -- Any two points of the intersection are within `diam (K n)` of each other, for every `n`.
  rw [mem_singleton_iff]
  have hbdd : ∀ n, dist q p ≤ diam (K n) := fun n =>
    dist_le_diam_of_mem (hK n).isBounded (mem_iInter.1 hq n) (mem_iInter.1 hp n)
  have : dist q p ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdiam hbdd
  exact dist_le_zero.1 this

/-- Lemma 1.7 (recognizing a component). A region inside an open set whose frontier misses that
open set is a connected component of it. -/
theorem connectedComponentIn_eq_of_frontier_disjoint (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hsub : U ⊆ V) (hfr : frontier U ∩ V = ∅) (hx : x ∈ U) :
    connectedComponentIn V x = U := by
  -- `U` is closed in `V`: `closure U ∩ V = (U ∪ ∂U) ∩ V = U`.
  have hclosed : closure U ∩ V ⊆ U := by
    rintro z ⟨hz1, hz2⟩
    by_contra hzU
    have : z ∈ frontier U ∩ V := ⟨by rw [hU.frontier_eq]; exact ⟨hz1, hzU⟩, hz2⟩
    rw [hfr] at this
    exact this
  refine subset_antisymm ?_ (hUconn.subset_connectedComponentIn hx hsub)
  -- The component `C` is covered by the disjoint open sets `U` and `(closure U)ᶜ`, and meets `U`.
  have hcover : connectedComponentIn V x ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases h : z ∈ closure U
    · exact Or.inl (hclosed ⟨h, connectedComponentIn_subset V x hz⟩)
    · exact Or.inr h
  have hmeet : (connectedComponentIn V x ∩ U).Nonempty :=
    ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
  have hempty : ¬ (connectedComponentIn V x ∩ (closure U)ᶜ).Nonempty := by
    intro hne
    obtain ⟨z, hz⟩ :=
      isPreconnected_connectedComponentIn U (closure U)ᶜ hU isClosed_closure.isOpen_compl
        hcover hmeet hne
    exact hz.2.2 (subset_closure hz.2.1)
  intro z hz
  by_contra hzU
  exact hempty ⟨z, hz, fun h => hzU (hclosed ⟨h, connectedComponentIn_subset V x hz⟩)⟩

end Plane

end Schoenflies
