/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.OneDimConvex
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Restrictions to affine lines

This file starts the bridge between ambient convex/subgradient statements and the
one-dimensional restrictions used in the Aleksandrov proof.
-/

@[expose] public section

namespace AleksandrovDifferentiability

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The one-dimensional restriction of `u` to the affine line `x + ℝ v`. -/
def lineRestriction (u : E → ℝ) (x v : E) : ℝ → ℝ :=
  fun t ↦ u (x + t • v)

/-- The set of line parameters whose corresponding points lie in `s`. -/
def lineDomain (s : Set E) (x v : E) : Set ℝ :=
  {t | x + t • v ∈ s}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Line restrictions commute with a linear isometry equivalence. This is the affine-line
bookkeeping needed to move fixed-direction slice predicates through an orthonormal coordinate
change. -/
theorem lineRestriction_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) (x v : E) :
    lineRestriction (u ∘ e) x v = lineRestriction u (e x) (e v) := by
  ext t
  simp [lineRestriction]

/-- Line domains commute with taking the preimage under a linear isometry equivalence. -/
theorem lineDomain_preimage_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) (s : Set F) (x v : E) :
    lineDomain (e ⁻¹' s) x v = lineDomain s (e x) (e v) := by
  ext t
  simp [lineDomain]

/-- The image of an open set under a linear isometry equivalence is open. This packages the
domain side of an orthonormal coordinate change. -/
theorem isOpen_image_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {s : Set E} (hs : IsOpen s) :
    IsOpen (e '' s) := by
  rw [e.image_eq_preimage_symm]
  exact hs.preimage e.symm.continuous

/-- The image of a convex set under a linear isometry equivalence is convex. -/
theorem convex_image_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (e '' s) :=
  hs.linear_image e.toLinearEquiv.toLinearMap

/-- Convexity of a function on a set is preserved by rebasing through a linear isometry
equivalence. -/
theorem ConvexOn.image_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {s : Set E} {u : E → ℝ} (hu : ConvexOn ℝ s u) :
    ConvexOn ℝ (e '' s) (u ∘ e.symm) := by
  refine ⟨convex_image_linearIsometryEquiv e hu.1, ?_⟩
  intro y hy z hz a b ha hb hab
  rcases hy with ⟨x, hx, rfl⟩
  rcases hz with ⟨w, hw, rfl⟩
  have hpoint : e (a • x + b • w) = a • e x + b • e w := by
    simp only [map_add, map_smul]
  have hconv := hu.2 hx hw ha hb hab
  rw [← hpoint]
  simpa [Function.comp_def] using hconv

/-- Rebase a line restriction at parameter `t`: evaluating at the new parameter `r` agrees with
the original line restriction at `t + r`. -/
theorem lineRestriction_rebase_apply (u : E → ℝ) (x v : E) (t r : ℝ) :
    lineRestriction u (x + t • v) v r = lineRestriction u x v (t + r) := by
  have hpoint : x + t • v + r • v = x + (t + r) • v := by
    rw [add_smul]
    abel
  simp [lineRestriction, hpoint]

/-- Rebase the line domain at parameter `t`. -/
theorem mem_lineDomain_rebase_iff {s : Set E} {x v : E} {t r : ℝ} :
    r ∈ lineDomain s (x + t • v) v ↔ t + r ∈ lineDomain s x v := by
  have hpoint : x + t • v + r • v = x + (t + r) • v := by
    rw [add_smul]
    abel
  constructor
  · intro hr
    simpa [lineDomain, hpoint] using hr
  · intro hr
    simpa [lineDomain, hpoint] using hr

/-- Set-level rebase formula for line domains. -/
theorem lineDomain_rebase (s : Set E) (x v : E) (t : ℝ) :
    lineDomain s (x + t • v) v = {r : ℝ | t + r ∈ lineDomain s x v} := by
  ext r
  exact mem_lineDomain_rebase_iff

/-- Replacing a line direction by a scalar multiple corresponds to scaling the line parameter. -/
theorem lineRestriction_smul_apply (u : E → ℝ) (x v : E) (c t : ℝ) :
    lineRestriction u x (c • v) t = lineRestriction u x v (c * t) := by
  have hpoint : x + t • c • v = x + (c * t) • v := by
    rw [smul_smul, mul_comm]
  simp [lineRestriction, hpoint]

/-- Domain version of `lineRestriction_smul_apply`. -/
theorem mem_lineDomain_smul_iff {s : Set E} {x v : E} {c t : ℝ} :
    t ∈ lineDomain s x (c • v) ↔ c * t ∈ lineDomain s x v := by
  have hpoint : x + t • c • v = x + (c * t) • v := by
    rw [smul_smul, mul_comm]
  constructor
  · intro ht
    simpa [lineDomain, hpoint] using ht
  · intro ht
    simpa [lineDomain, hpoint] using ht

/-- Set-level scalar-rescaling formula for line domains. -/
theorem lineDomain_smul (s : Set E) (x v : E) (c : ℝ) :
    lineDomain s x (c • v) = {t : ℝ | c * t ∈ lineDomain s x v} := by
  ext t
  exact mem_lineDomain_smul_iff

@[simp]
theorem lineRestriction_neg_direction (u : E → ℝ) (x v : E) (t : ℝ) :
    lineRestriction u x (-v) t = lineRestriction u x v (-t) := by
  simpa using lineRestriction_smul_apply (u := u) (x := x) (v := v) (c := (-1 : ℝ)) t

@[simp]
theorem lineDomain_neg_direction (s : Set E) (x v : E) :
    lineDomain s x (-v) = {t : ℝ | -t ∈ lineDomain s x v} := by
  simpa using lineDomain_smul (s := s) (x := x) (v := v) (c := (-1 : ℝ))

/-- The line domain of an open ambient set is open. -/
theorem isOpen_lineDomain {s : Set E} {x v : E} (hs : IsOpen s) :
    IsOpen (lineDomain s x v) := by
  have hcont : Continuous fun t : ℝ ↦ x + t • v := by
    fun_prop
  change IsOpen ((fun t : ℝ => x + t • v) ⁻¹' s)
  exact hs.preimage hcont

@[simp]
theorem lineRestriction_zero (u : E → ℝ) (x v : E) :
    lineRestriction u x v 0 = u x := by
  simp [lineRestriction]

theorem zero_mem_lineDomain {s : Set E} {x v : E} (hx : x ∈ s) :
    0 ∈ lineDomain s x v := by
  simpa [lineDomain]

/-- If the base point is interior to the ambient domain, then `0` is interior to the
line-restricted domain in every direction. -/
theorem zero_mem_interior_lineDomain {s : Set E} {x v : E} (hx : x ∈ interior s) :
    (0 : ℝ) ∈ interior (lineDomain s x v) := by
  rw [mem_interior_iff_mem_nhds]
  have hs : s ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  have hs0 : s ∈ nhds (x + (0 : ℝ) • v) := by
    simpa using hs
  have hcont : ContinuousAt (fun t : ℝ ↦ x + t • v) 0 :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  change ((fun t : ℝ => x + t • v) ⁻¹' s) ∈ nhds 0
  exact hcont.preimage_mem_nhds hs0

/-- If a point on the line lies in the interior of the ambient domain, then the corresponding
line parameter lies in the interior of the line domain. -/
theorem mem_interior_lineDomain_of_line_mem_interior
    {s : Set E} {x v : E} {t : ℝ} (ht : x + t • v ∈ interior s) :
    t ∈ interior (lineDomain s x v) := by
  rw [mem_interior_iff_mem_nhds]
  have hs : s ∈ nhds (x + t • v) := mem_interior_iff_mem_nhds.mp ht
  have hcont : ContinuousAt (fun r : ℝ ↦ x + r • v) t :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  change ((fun r : ℝ => x + r • v) ⁻¹' s) ∈ nhds t
  exact hcont.preimage_mem_nhds hs

/-- An ambient subgradient gives the supporting inequality along every line through the base
point. -/
theorem SubgradientOn.line_supporting_inequality
    {s : Set E} {u : E → ℝ} {x p v : E} (hp : SubgradientOn s u x p)
    {t : ℝ} (ht : t ∈ lineDomain s x v) :
    u x + inner ℝ p (t • v) ≤ lineRestriction u x v t := by
  have h := hp.supporting_inequality (s := s) (u := u) (x := x) (p := p)
    (y := x + t • v) ht
  simpa [lineRestriction, lineDomain] using h

/-- The line-restricted supporting inequality, written with the value at parameter `0`. -/
theorem SubgradientOn.lineRestriction_supporting_inequality
    {s : Set E} {u : E → ℝ} {x p v : E} (hp : SubgradientOn s u x p)
    {t : ℝ} (ht : t ∈ lineDomain s x v) :
    lineRestriction u x v 0 + inner ℝ p (t • v) ≤ lineRestriction u x v t := by
  simpa [lineRestriction_zero] using hp.line_supporting_inequality (v := v) ht

/-- An ambient subgradient restricts to a one-dimensional subgradient along every line through the
base point. -/
theorem SubgradientOn.lineRestriction_subgradientOn
    {s : Set E} {u : E → ℝ} {x p v : E} (hp : SubgradientOn s u x p) :
    SubgradientOn (lineDomain s x v) (lineRestriction u x v) 0 (inner ℝ p v) := by
  refine ⟨zero_mem_lineDomain hp.mem, ?_⟩
  intro t ht
  have h := hp.lineRestriction_supporting_inequality (v := v) ht
  rw [real_inner_smul_right] at h
  simpa [lineRestriction_zero] using h

/-- An ambient subgradient at the point with line parameter `t` restricts to a one-dimensional
subgradient at `t`. -/
theorem SubgradientOn.lineRestriction_subgradientOn_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) t
      (inner ℝ p v) := by
  refine ⟨hp.mem, ?_⟩
  intro r hr
  have hsupport := hp.supporting_inequality (y := x + r • v) hr
  have hdiff : x + r • v - (x + t • v) = (r - t) • v := by
    calc
      x + r • v - (x + t • v) = r • v - t • v := by abel
      _ = (r - t) • v := by rw [sub_smul]
  rw [hdiff] at hsupport
  have hlin :
      inner ℝ p ((r - t) • v) = inner ℝ (inner ℝ p v) (r - t) := by
    simp [real_inner_smul_right]
  simpa [AleksandrovDifferentiability.lineRestriction, lineDomain, hlin] using hsupport

/-- An ambient upper quadratic contact with a specified slope restricts to an upper quadratic
contact on every affine line, with slope paired against the line direction and opening scaled by
the squared length of the direction vector. -/
theorem HasUpperContactWithSlopeOn.lineRestriction
    {s : Set E} {u : E → ℝ} {x p v : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) :
    HasUpperContactWithSlopeOn (lineDomain s x v) (lineRestriction u x v) 0
      (inner ℝ p v) (a * ‖v‖ ^ 2) := by
  refine ⟨zero_mem_lineDomain h.mem, ?_⟩
  intro t ht
  have hline := h.upper_inequality (y := x + t • v) ht
  have hquad :
      (a / 2) * ‖t • v‖ ^ 2 =
        ((a * ‖v‖ ^ 2) / 2) * ‖t - 0‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, sub_zero, mul_pow]
    rw [sq_abs]
    ring
  have hlin : inner ℝ p (t • v) = inner ℝ (inner ℝ p v) (t - 0) := by
    simp [real_inner_smul_right]
  simp only [lineRestriction_zero]
  change u (x + t • v) ≤
    u x + inner ℝ (inner ℝ p v) (t - 0) +
      ((a * ‖v‖ ^ 2) / 2) * ‖t - 0‖ ^ 2
  simpa [hlin, hquad] using hline

/-- Shifted version of `HasUpperContactWithSlopeOn.lineRestriction`: an ambient contact at the
point with line parameter `t` restricts to a one-dimensional contact at `t`. -/
theorem HasUpperContactWithSlopeOn.lineRestriction_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t a : ℝ}
    (h : HasUpperContactWithSlopeOn s u (x + t • v) p a) :
    HasUpperContactWithSlopeOn (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) t
      (inner ℝ p v) (a * ‖v‖ ^ 2) := by
  refine ⟨h.mem, ?_⟩
  intro r hr
  have hline := h.upper_inequality (y := x + r • v) hr
  have hdiff : x + r • v - (x + t • v) = (r - t) • v := by
    calc
      x + r • v - (x + t • v) = r • v - t • v := by abel
      _ = (r - t) • v := by rw [sub_smul]
  rw [hdiff] at hline
  have hquad :
      (a / 2) * ‖(r - t) • v‖ ^ 2 =
        ((a * ‖v‖ ^ 2) / 2) * ‖r - t‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow]
    rw [sq_abs]
    ring
  have hlin :
      inner ℝ p ((r - t) • v) = inner ℝ (inner ℝ p v) (r - t) := by
    simp [real_inner_smul_right]
  simpa [AleksandrovDifferentiability.lineRestriction, lineDomain, hlin, hquad] using hline

/-- An ambient upper quadratic contact restricts to an upper quadratic contact on every affine
line, with the opening scaled by the squared length of the direction vector. -/
theorem HasUpperContactOn.lineRestriction
    {s : Set E} {u : E → ℝ} {x v : E} {a : ℝ} (h : HasUpperContactOn s u x a) :
    HasUpperContactOn (lineDomain s x v) (lineRestriction u x v) 0 (a * ‖v‖ ^ 2) := by
  rcases h.exists_slope_contact with ⟨p, hp⟩
  exact (hp.lineRestriction (v := v)).hasUpperContactOn

/-- Shifted version of `HasUpperContactOn.lineRestriction`: an ambient contact at the point with
line parameter `t` restricts to a one-dimensional contact at `t`. -/
theorem HasUpperContactOn.lineRestriction_at
    {s : Set E} {u : E → ℝ} {x v : E} {t a : ℝ}
    (h : HasUpperContactOn s u (x + t • v) a) :
    HasUpperContactOn (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) t (a * ‖v‖ ^ 2) := by
  rcases h.exists_slope_contact with ⟨p, hp⟩
  exact (hp.lineRestriction_at (x := x) (v := v)).hasUpperContactOn

/-- A bound on the upper-contact opening restricts to every nonconstant affine line, with the
opening scaled by the squared length of the direction vector. -/
theorem HasUpperContactOpeningAtMostOn.lineRestriction_of_norm_pos
    {s : Set E} {u : E → ℝ} {x v : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hv : 0 < ‖v‖) :
    HasUpperContactOpeningAtMostOn (lineDomain s x v) (lineRestriction u x v) 0
      (A * ‖v‖ ^ 2) := by
  intro η hη
  have hv2pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hv
  have hv2ne : ‖v‖ ^ 2 ≠ 0 := ne_of_gt hv2pos
  have hδ : 0 < η / ‖v‖ ^ 2 := div_pos hη hv2pos
  have hline := (h.hasUpperContactOn_add_pos hδ).lineRestriction (v := v)
  refine hline.mono_opening ?_
  have hscale : (A + η / ‖v‖ ^ 2) * ‖v‖ ^ 2 = A * ‖v‖ ^ 2 + η := by
    calc
      (A + η / ‖v‖ ^ 2) * ‖v‖ ^ 2
          = A * ‖v‖ ^ 2 + (η / ‖v‖ ^ 2) * ‖v‖ ^ 2 := by ring
      _ = A * ‖v‖ ^ 2 + η := by
        rw [div_mul_cancel₀ η hv2ne]
  exact le_of_eq hscale

/-- Unit-direction version of `HasUpperContactOpeningAtMostOn.lineRestriction_of_norm_pos`. -/
theorem HasUpperContactOpeningAtMostOn.lineRestriction_of_norm_eq_one
    {s : Set E} {u : E → ℝ} {x v : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hv : ‖v‖ = 1) :
    HasUpperContactOpeningAtMostOn (lineDomain s x v) (lineRestriction u x v) 0 A := by
  have hvpos : 0 < ‖v‖ := by
    simp [hv]
  simpa [hv] using h.lineRestriction_of_norm_pos (v := v) hvpos

/-- Shifted version of `HasUpperContactOpeningAtMostOn.lineRestriction_of_norm_pos`. -/
theorem HasUpperContactOpeningAtMostOn.lineRestriction_at_of_norm_pos
    {s : Set E} {u : E → ℝ} {x v : E} {t A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u (x + t • v) A) (hv : 0 < ‖v‖) :
    HasUpperContactOpeningAtMostOn (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) t
      (A * ‖v‖ ^ 2) := by
  intro η hη
  have hv2pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hv
  have hv2ne : ‖v‖ ^ 2 ≠ 0 := ne_of_gt hv2pos
  have hδ : 0 < η / ‖v‖ ^ 2 := div_pos hη hv2pos
  have hline := (h.hasUpperContactOn_add_pos hδ).lineRestriction_at (x := x) (v := v)
  refine hline.mono_opening ?_
  have hscale : (A + η / ‖v‖ ^ 2) * ‖v‖ ^ 2 = A * ‖v‖ ^ 2 + η := by
    calc
      (A + η / ‖v‖ ^ 2) * ‖v‖ ^ 2
          = A * ‖v‖ ^ 2 + (η / ‖v‖ ^ 2) * ‖v‖ ^ 2 := by ring
      _ = A * ‖v‖ ^ 2 + η := by
        rw [div_mul_cancel₀ η hv2ne]
  exact le_of_eq hscale

/-- Unit-direction version of
`HasUpperContactOpeningAtMostOn.lineRestriction_at_of_norm_pos`. -/
theorem HasUpperContactOpeningAtMostOn.lineRestriction_at_of_norm_eq_one
    {s : Set E} {u : E → ℝ} {x v : E} {t A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u (x + t • v) A) (hv : ‖v‖ = 1) :
    HasUpperContactOpeningAtMostOn (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) t A := by
  have hvpos : 0 < ‖v‖ := by
    simp [hv]
  simpa [hv] using h.lineRestriction_at_of_norm_pos (x := x) (v := v) hvpos

/-- Fixed-slope bounded upper-contact openings restrict to every nonconstant affine line, with
the slope paired against the line direction and the opening scaled by the squared direction
length. -/
theorem HasUpperContactWithSlopeOpeningAtMostOn.lineRestriction_of_norm_pos
    {s : Set E} {u : E → ℝ} {x p v : E} {A : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A) (hv : 0 < ‖v‖) :
    HasUpperContactWithSlopeOpeningAtMostOn (lineDomain s x v) (lineRestriction u x v) 0
      (inner ℝ p v) (A * ‖v‖ ^ 2) := by
  intro η hη
  have hv2pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hv
  have hv2ne : ‖v‖ ^ 2 ≠ 0 := ne_of_gt hv2pos
  have hδ : 0 < η / ‖v‖ ^ 2 := div_pos hη hv2pos
  have hline := (h.hasUpperContactWithSlopeOn_add_pos hδ).lineRestriction (v := v)
  refine hline.mono_opening ?_
  have hscale : (A + η / ‖v‖ ^ 2) * ‖v‖ ^ 2 = A * ‖v‖ ^ 2 + η := by
    calc
      (A + η / ‖v‖ ^ 2) * ‖v‖ ^ 2
          = A * ‖v‖ ^ 2 + (η / ‖v‖ ^ 2) * ‖v‖ ^ 2 := by ring
      _ = A * ‖v‖ ^ 2 + η := by
        rw [div_mul_cancel₀ η hv2ne]
  exact le_of_eq hscale

/-- Unit-direction version of
`HasUpperContactWithSlopeOpeningAtMostOn.lineRestriction_of_norm_pos`. -/
theorem HasUpperContactWithSlopeOpeningAtMostOn.lineRestriction_of_norm_eq_one
    {s : Set E} {u : E → ℝ} {x p v : E} {A : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A) (hv : ‖v‖ = 1) :
    HasUpperContactWithSlopeOpeningAtMostOn (lineDomain s x v) (lineRestriction u x v) 0
      (inner ℝ p v) A := by
  have hvpos : 0 < ‖v‖ := by
    simp [hv]
  simpa [hv] using h.lineRestriction_of_norm_pos (v := v) hvpos

/-- Shifted version of
`HasUpperContactWithSlopeOpeningAtMostOn.lineRestriction_of_norm_pos`. -/
theorem HasUpperContactWithSlopeOpeningAtMostOn.lineRestriction_at_of_norm_pos
    {s : Set E} {u : E → ℝ} {x p v : E} {t A : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u (x + t • v) p A) (hv : 0 < ‖v‖) :
    HasUpperContactWithSlopeOpeningAtMostOn (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) t
      (inner ℝ p v) (A * ‖v‖ ^ 2) := by
  intro η hη
  have hv2pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hv
  have hv2ne : ‖v‖ ^ 2 ≠ 0 := ne_of_gt hv2pos
  have hδ : 0 < η / ‖v‖ ^ 2 := div_pos hη hv2pos
  have hline := (h.hasUpperContactWithSlopeOn_add_pos hδ).lineRestriction_at
    (x := x) (v := v)
  refine hline.mono_opening ?_
  have hscale : (A + η / ‖v‖ ^ 2) * ‖v‖ ^ 2 = A * ‖v‖ ^ 2 + η := by
    calc
      (A + η / ‖v‖ ^ 2) * ‖v‖ ^ 2
          = A * ‖v‖ ^ 2 + (η / ‖v‖ ^ 2) * ‖v‖ ^ 2 := by ring
      _ = A * ‖v‖ ^ 2 + η := by
        rw [div_mul_cancel₀ η hv2ne]
  exact le_of_eq hscale

/-- Unit-direction version of
`HasUpperContactWithSlopeOpeningAtMostOn.lineRestriction_at_of_norm_pos`. -/
theorem HasUpperContactWithSlopeOpeningAtMostOn.lineRestriction_at_of_norm_eq_one
    {s : Set E} {u : E → ℝ} {x p v : E} {t A : ℝ}
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u (x + t • v) p A) (hv : ‖v‖ = 1) :
    HasUpperContactWithSlopeOpeningAtMostOn (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) t
      (inner ℝ p v) A := by
  have hvpos : 0 < ‖v‖ := by
    simp [hv]
  simpa [hv] using h.lineRestriction_at_of_norm_pos (x := x) (v := v) hvpos

/-- The preimage of an ambient slope-specific contact set along a line is contained in the
corresponding contact set for the one-dimensional restriction. -/
theorem preimage_lineMap_upperContactWithSlopeSet_subset
    {s : Set E} {u : E → ℝ} {x p v : E} {a : ℝ} :
    {t : ℝ | x + t • v ∈ upperContactWithSlopeSet s u p a} ⊆
      upperContactWithSlopeSet (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v)
        (inner ℝ p v) (a * ‖v‖ ^ 2) := by
  intro t ht
  exact ht.lineRestriction_at (x := x) (v := v)

/-- The preimage of an ambient contact set along a line is contained in the contact set for the
one-dimensional restriction. -/
theorem preimage_lineMap_upperContactSet_subset
    {s : Set E} {u : E → ℝ} {x v : E} {a : ℝ} :
    {t : ℝ | x + t • v ∈ upperContactSet s u a} ⊆
      upperContactSet (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v)
        (a * ‖v‖ ^ 2) := by
  intro t ht
  exact ht.lineRestriction_at (x := x) (v := v)

/-- Bounded upper-contact openings pass to line-restricted contact loci on nonconstant lines. -/
theorem preimage_lineMap_upperContactOpeningAtMostSet_subset_of_norm_pos
    {s : Set E} {u : E → ℝ} {x v : E} {A : ℝ} (hv : 0 < ‖v‖) :
    {t : ℝ | x + t • v ∈ upperContactOpeningAtMostSet s u A} ⊆
      upperContactOpeningAtMostSet (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v)
        (A * ‖v‖ ^ 2) := by
  intro t ht
  exact ht.lineRestriction_at_of_norm_pos (x := x) (v := v) hv

/-- Unit-direction version of
`preimage_lineMap_upperContactOpeningAtMostSet_subset_of_norm_pos`. -/
theorem preimage_lineMap_upperContactOpeningAtMostSet_subset_of_norm_eq_one
    {s : Set E} {u : E → ℝ} {x v : E} {A : ℝ} (hv : ‖v‖ = 1) :
    {t : ℝ | x + t • v ∈ upperContactOpeningAtMostSet s u A} ⊆
      upperContactOpeningAtMostSet (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v) A := by
  have hvpos : 0 < ‖v‖ := by
    simp [hv]
  simpa [hv] using
    preimage_lineMap_upperContactOpeningAtMostSet_subset_of_norm_pos
      (s := s) (u := u) (x := x) (v := v) (A := A) hvpos

/-- Fixed-slope bounded upper-contact openings pass to line-restricted contact loci on
nonconstant lines. -/
theorem preimage_lineMap_upperContactWithSlopeOpeningAtMostSet_subset_of_norm_pos
    {s : Set E} {u : E → ℝ} {x p v : E} {A : ℝ} (hv : 0 < ‖v‖) :
    {t : ℝ | x + t • v ∈ upperContactWithSlopeOpeningAtMostSet s u p A} ⊆
      upperContactWithSlopeOpeningAtMostSet (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v)
        (inner ℝ p v) (A * ‖v‖ ^ 2) := by
  intro t ht
  exact ht.lineRestriction_at_of_norm_pos (x := x) (v := v) hv

/-- Unit-direction version of
`preimage_lineMap_upperContactWithSlopeOpeningAtMostSet_subset_of_norm_pos`. -/
theorem preimage_lineMap_upperContactWithSlopeOpeningAtMostSet_subset_of_norm_eq_one
    {s : Set E} {u : E → ℝ} {x p v : E} {A : ℝ} (hv : ‖v‖ = 1) :
    {t : ℝ | x + t • v ∈ upperContactWithSlopeOpeningAtMostSet s u p A} ⊆
      upperContactWithSlopeOpeningAtMostSet (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v)
        (inner ℝ p v) A := by
  have hvpos : 0 < ‖v‖ := by
    simp [hv]
  simpa [hv] using
    preimage_lineMap_upperContactWithSlopeOpeningAtMostSet_subset_of_norm_pos
      (s := s) (u := u) (x := x) (p := p) (v := v) (A := A) hvpos

/-- Convexity restricts to every affine line. -/
theorem ConvexOn.lineRestriction
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u) :
    ConvexOn ℝ (lineDomain s x v) (lineRestriction u x v) := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + v)
  have hg : (fun t : ℝ ↦ g t) = fun t : ℝ ↦ x + t • v := by
    funext t
    simp [g, AffineMap.lineMap_apply_module', add_comm]
  have h := hu.comp_affineMap g
  change ConvexOn ℝ ((fun t : ℝ => x + t • v) ⁻¹' s)
    (u ∘ fun t : ℝ => x + t • v)
  simpa only [hg] using h

/-- Convex right-continuity of the line-restricted right derivative, restricted further to a
positive line filter through an arbitrary set `D`.

This is the filter form used in the cluster-gradient reduction: adding the differentiability-set
restriction to the positive ray only makes the filter smaller. -/
theorem ConvexOn.tendsto_lineRightDeriv_posLine
    {s D : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) :
    Filter.Tendsto (fun t : ℝ => rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t)
      (𝓝[{t : ℝ | 0 < t ∧ x + t • v ∈ D}] (0 : ℝ))
      (𝓝 (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0)) := by
  have hright :
      Filter.Tendsto
        (fun t : ℝ => rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t)
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ))
        (𝓝 (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0)) :=
    ConvexOn.tendsto_rightDeriv_nhdsGT
      (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
      (x := 0) (ConvexOn.lineRestriction (x := x) (v := v) hu)
      (zero_mem_interior_lineDomain hx)
  exact hright.mono_left
    (nhdsWithin_mono 0 (by
      intro t ht
      exact ht.1))

/-- If vector gradients cluster along a parameter filter, and their directional components
eventually realize the right derivative of a line restriction whose right derivatives converge
back to the endpoint, then the cluster value has exactly the endpoint right-derivative
directional component. -/
theorem lineRightDeriv_eq_inner_of_gradient_mapClusterPt
    {ι : Type*} {l : Filter ι} {u : E → ℝ} {x v q : E} {G : ι → E} {τ : ι → ℝ}
    (hq : MapClusterPt q l G)
    (hlim : Filter.Tendsto
      (fun a : ι => rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) (τ a)) l
      (𝓝 (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0)))
    (hrealize : ∀ᶠ a in l,
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) (τ a) =
        inner ℝ (G a) v) :
    rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0 = inner ℝ q v := by
  have hinnerCluster : MapClusterPt (inner ℝ q v) l (fun a : ι => inner ℝ (G a) v) := by
    have hcont : ContinuousAt (fun p : E => inner ℝ p v) q := by fun_prop
    simpa [Function.comp_def] using hq.continuousAt_comp hcont
  have hinnerLimit : Filter.Tendsto (fun a : ι => inner ℝ (G a) v) l
      (𝓝 (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0)) :=
    hlim.congr' hrealize
  have hne :
      Filter.NeBot (𝓝 (inner ℝ q v) ⊓
        𝓝 (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0)) :=
    hinnerCluster.clusterPt.neBot.mono (inf_le_inf_left _ hinnerLimit)
  exact (eq_of_nhds_neBot hne).symm

/-- Positive-line convex specialization of
`lineRightDeriv_eq_inner_of_gradient_mapClusterPt`. -/
theorem ConvexOn.lineRightDeriv_eq_inner_of_posLine_gradient_mapClusterPt
    {s D : Set E} {u : E → ℝ} {x v q : E} {G : ℝ → E}
    (hu : ConvexOn ℝ s u) (hx : x ∈ interior s)
    (hq : MapClusterPt q (𝓝[{t : ℝ | 0 < t ∧ x + t • v ∈ D}] (0 : ℝ)) G)
    (hrealize : ∀ᶠ t in 𝓝[{t : ℝ | 0 < t ∧ x + t • v ∈ D}] (0 : ℝ),
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t = inner ℝ (G t) v) :
    rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0 = inner ℝ q v :=
  lineRightDeriv_eq_inner_of_gradient_mapClusterPt
    (u := u) (x := x) (v := v) (q := q) (G := G) (τ := id) hq
    (ConvexOn.tendsto_lineRightDeriv_posLine (D := D) hu hx)
    hrealize

/-- Inequality form of `ConvexOn.lineRightDeriv_eq_inner_of_posLine_gradient_mapClusterPt`,
matching the current cube-level cluster-density boundary. -/
theorem ConvexOn.lineRightDeriv_le_inner_of_posLine_gradient_mapClusterPt
    {s D : Set E} {u : E → ℝ} {x v q : E} {G : ℝ → E}
    (hu : ConvexOn ℝ s u) (hx : x ∈ interior s)
    (hq : MapClusterPt q (𝓝[{t : ℝ | 0 < t ∧ x + t • v ∈ D}] (0 : ℝ)) G)
    (hrealize : ∀ᶠ t in 𝓝[{t : ℝ | 0 < t ∧ x + t • v ∈ D}] (0 : ℝ),
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t = inner ℝ (G t) v) :
    rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0 ≤ inner ℝ q v :=
  le_of_eq
    (ConvexOn.lineRightDeriv_eq_inner_of_posLine_gradient_mapClusterPt hu hx hq hrealize)

/-- An ordinary derivative realizes the project-local right derivative. -/
theorem rightDeriv_eq_of_hasDerivAt {f : ℝ → ℝ} {x p : ℝ} (h : HasDerivAt f p x) :
    rightDeriv f x = p := by
  simpa [rightDeriv] using h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

/-- Differentiability of `u` at a point of an affine line differentiates the corresponding line
restriction at that parameter. -/
theorem HasFDerivAt.lineRestriction_at
    {u : E → ℝ} {x v : E} {t : ℝ} {ℓ : E →L[ℝ] ℝ}
    (h : HasFDerivAt u ℓ (x + t • v)) :
    HasDerivAt (AleksandrovDifferentiability.lineRestriction u x v) (ℓ v) t := by
  have hlineMap : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  change HasDerivAt (u ∘ fun s : ℝ => x + s • v) (ℓ v) t
  exact h.comp_hasDerivAt t hlineMap

/-- At a Fréchet differentiability point on an affine line, the line-restricted right derivative
is the Fréchet derivative applied to the line direction. -/
theorem lineRestriction_rightDeriv_eq_fderiv_apply_of_differentiableAt
    {u : E → ℝ} {x v : E} {t : ℝ}
    (h : DifferentiableAt ℝ u (x + t • v)) :
    rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t =
      fderiv ℝ u (x + t • v) v :=
  rightDeriv_eq_of_hasDerivAt
    (HasFDerivAt.lineRestriction_at (x := x) (v := v) (t := t) h.hasFDerivAt)

/-- A differentiable convex function has its derivative as a subgradient, expressed with an
explicit inner-product representative of the Fréchet derivative. The proof follows the
source-document convex route: restrict to the line segment from `x` to `y` and apply the
one-dimensional supporting-line statement. -/
theorem ConvexOn.subgradientOn_of_hasFDerivAt_of_forall_eq_inner
    {s : Set E} {u : E → ℝ} {x p : E} {ℓ : E →L[ℝ] ℝ}
    (hu : ConvexOn ℝ s u) (hx : x ∈ interior s)
    (hd : HasFDerivAt u ℓ x) (hℓ : ∀ v : E, ℓ v = inner ℝ p v) :
    SubgradientOn s u x p := by
  refine ⟨interior_subset hx, ?_⟩
  intro y hy
  let v : E := y - x
  have hderLine :
      HasDerivAt (AleksandrovDifferentiability.lineRestriction u x v) (ℓ v) 0 := by
    have hline : HasLineDerivAt ℝ u (ℓ v) x v := hd.hasLineDerivAt v
    change HasDerivAt (fun t : ℝ => u (x + t • v)) (ℓ v) 0
    simpa only [HasLineDerivAt] using hline
  have hsubLine :
      SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) 0
        (ℓ v) :=
    AleksandrovDifferentiability.ConvexOn.subgradientOn_of_hasDerivAt
      (S := lineDomain s x v)
      (f := AleksandrovDifferentiability.lineRestriction u x v) (x := 0)
      (p := ℓ v)
      (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu)
      (zero_mem_interior_lineDomain hx) hderLine
  have h1 : (1 : ℝ) ∈ lineDomain s x v := by
    dsimp [lineDomain, v]
    simpa [one_smul] using hy
  have hsupport := hsubLine.supporting_inequality (y := 1) h1
  have hℓv : ℓ v = inner ℝ p (y - x) := by
    simpa [v] using hℓ v
  simpa [AleksandrovDifferentiability.lineRestriction, v, hℓv, Real.inner_apply, one_smul]
    using hsupport

/-- The right derivative of a convex affine-line restriction is differentiable almost everywhere
on the interior of the line domain, in implication form. -/
theorem ConvexOn.ae_lineRightDeriv_differentiableWithinAt_of_mem
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u) :
    ∀ᵐ t, t ∈ interior (lineDomain s x v) →
      DifferentiableWithinAt ℝ (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v))
        (interior (lineDomain s x v)) t :=
  AleksandrovDifferentiability.ConvexOn.ae_differentiableWithinAt_projectRightDeriv_of_mem
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- The left derivative of a convex affine-line restriction is differentiable almost everywhere
on the interior of the line domain, in implication form. -/
theorem ConvexOn.ae_lineLeftDeriv_differentiableWithinAt_of_mem
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u) :
    ∀ᵐ t, t ∈ interior (lineDomain s x v) →
      DifferentiableWithinAt ℝ (leftDeriv (AleksandrovDifferentiability.lineRestriction u x v))
        (interior (lineDomain s x v)) t :=
  AleksandrovDifferentiability.ConvexOn.ae_differentiableWithinAt_projectLeftDeriv_of_mem
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- Restricted-measure version of
`ConvexOn.ae_lineRightDeriv_differentiableWithinAt_of_mem`. -/
theorem ConvexOn.ae_lineRightDeriv_differentiableWithinAt
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u)
    (hline : MeasurableSet (interior (lineDomain s x v))) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (interior (lineDomain s x v)),
      DifferentiableWithinAt ℝ (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v))
        (interior (lineDomain s x v)) t :=
  AleksandrovDifferentiability.ConvexOn.ae_differentiableWithinAt_projectRightDeriv
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu) hline

/-- Restricted-measure version of
`ConvexOn.ae_lineLeftDeriv_differentiableWithinAt_of_mem`. -/
theorem ConvexOn.ae_lineLeftDeriv_differentiableWithinAt
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u)
    (hline : MeasurableSet (interior (lineDomain s x v))) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (interior (lineDomain s x v)),
      DifferentiableWithinAt ℝ (leftDeriv (AleksandrovDifferentiability.lineRestriction u x v))
        (interior (lineDomain s x v)) t :=
  AleksandrovDifferentiability.ConvexOn.ae_differentiableWithinAt_projectLeftDeriv
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu) hline

/-- Both one-sided derivative functions of a convex affine-line restriction are differentiable
almost everywhere on the interior of the line domain, in implication form. -/
theorem ConvexOn.ae_mem_lineOneSidedDerivDifferentiabilitySet_of_mem
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u) :
    ∀ᵐ t, t ∈ interior (lineDomain s x v) →
      t ∈ oneSidedDerivDifferentiabilitySet (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v) :=
  AleksandrovDifferentiability.ConvexOn.ae_mem_oneSidedDerivDifferentiabilitySet_of_mem
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- Restricted-measure version of
`ConvexOn.ae_mem_lineOneSidedDerivDifferentiabilitySet_of_mem`. -/
theorem ConvexOn.ae_mem_lineOneSidedDerivDifferentiabilitySet
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u)
    (hline : MeasurableSet (interior (lineDomain s x v))) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (interior (lineDomain s x v)),
      t ∈ oneSidedDerivDifferentiabilitySet (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v) :=
  AleksandrovDifferentiability.ConvexOn.ae_mem_oneSidedDerivDifferentiabilitySet
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu) hline

/-- The right-derivative differentiability good set for a convex affine-line restriction has full
measure in the interior of the line domain. -/
theorem ConvexOn.measure_interior_lineDomain_diff_rightDerivDifferentiabilitySet_eq_zero
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u) :
    MeasureTheory.volume
      (interior (lineDomain s x v) \
        rightDerivDifferentiabilitySet (lineDomain s x v)
          (AleksandrovDifferentiability.lineRestriction u x v)) = 0 :=
  AleksandrovDifferentiability.ConvexOn.measure_interior_diff_rightDerivDifferentiabilitySet_eq_zero
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- The left-derivative differentiability good set for a convex affine-line restriction has full
measure in the interior of the line domain. -/
theorem ConvexOn.measure_interior_lineDomain_diff_leftDerivDifferentiabilitySet_eq_zero
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u) :
    MeasureTheory.volume
      (interior (lineDomain s x v) \
        leftDerivDifferentiabilitySet (lineDomain s x v)
          (AleksandrovDifferentiability.lineRestriction u x v)) = 0 :=
  AleksandrovDifferentiability.ConvexOn.measure_interior_diff_leftDerivDifferentiabilitySet_eq_zero
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- The combined one-sided-derivative differentiability good set for a convex affine-line
restriction has full measure in the interior of the line domain. -/
theorem ConvexOn.measure_lineInterior_diff_oneSidedDerivDifferentiabilitySet_eq_zero
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u) :
    MeasureTheory.volume
      (interior (lineDomain s x v) \
        oneSidedDerivDifferentiabilitySet (lineDomain s x v)
          (AleksandrovDifferentiability.lineRestriction u x v)) = 0 := by
  exact
    AleksandrovDifferentiability.ConvexOn.measure_interior_diff_oneSided_eq_zero
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- On a line restriction of a convex function, a slope is a one-dimensional subgradient at `0`
exactly when it lies between the left and right derivatives there. -/
theorem ConvexOn.lineRestriction_subgradientOn_iff_deriv_bounds
    {s : Set E} {u : E → ℝ} {x v : E} {q : ℝ} (hu : ConvexOn ℝ s u)
    (h0 : (0 : ℝ) ∈ interior (lineDomain s x v)) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) 0 q ↔
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0 ≤ q ∧
        q ≤ rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0 := by
  have huLine := ConvexOn.lineRestriction (x := x) (v := v) hu
  exact AleksandrovDifferentiability.ConvexOn.subgradientOn_iff_leftDeriv_le_and_le_rightDeriv
    (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
    (x := 0) (p := q) huLine h0

/-- Interior-domain version of the derivative-bound characterization of subgradients on a line
restriction. -/
theorem ConvexOn.lineRestriction_subgradientOn_iff_deriv_bounds_of_mem_interior
    {s : Set E} {u : E → ℝ} {x v : E} {q : ℝ} (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) 0 q ↔
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0 ≤ q ∧
        q ≤ rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) 0 :=
  AleksandrovDifferentiability.ConvexOn.lineRestriction_subgradientOn_iff_deriv_bounds
    (s := s) (u := u) (x := x) (v := v) (q := q) hu (zero_mem_interior_lineDomain hx)

/-- For a convex affine-line restriction, the right derivative at an interior line parameter is
itself a one-dimensional subgradient. This is the one-dimensional half of the source-document
identity `d⁺/dt u(x + t z) = sup {p · z | p ∈ ∂u(x + t z)}`. -/
theorem ConvexOn.lineRestriction_rightDeriv_subgradientOn_at
    {s : Set E} {u : E → ℝ} {x v : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : t ∈ interior (lineDomain s x v)) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t) := by
  have huLine : ConvexOn ℝ (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) :=
    ConvexOn.lineRestriction (x := x) (v := v) hu
  exact
    AleksandrovDifferentiability.ConvexOn.subgradientOn_of_leftDeriv_le_of_le_rightDeriv
      (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
      (x := t) (p := rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t)
      huLine ht
      (AleksandrovDifferentiability.ConvexOn.leftDeriv_le_rightDeriv
        (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
        (x := t) huLine ht)
      le_rfl

/-- Ambient-interior version of
`ConvexOn.lineRestriction_rightDeriv_subgradientOn_at`. -/
theorem ConvexOn.lineRestriction_rightDeriv_subgradientOn_at_of_line_mem_interior
    {s : Set E} {u : E → ℝ} {x v : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • v ∈ interior s) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t) :=
  AleksandrovDifferentiability.ConvexOn.lineRestriction_rightDeriv_subgradientOn_at
    (s := s) (u := u) (x := x) (v := v) (t := t) hu
    (mem_interior_lineDomain_of_line_mem_interior ht)

/-- For a convex affine-line restriction, the left derivative at an interior line parameter is
itself a one-dimensional subgradient. -/
theorem ConvexOn.lineRestriction_leftDeriv_subgradientOn_at
    {s : Set E} {u : E → ℝ} {x v : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : t ∈ interior (lineDomain s x v)) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) t
      (leftDeriv (AleksandrovDifferentiability.lineRestriction u x v) t) := by
  have huLine : ConvexOn ℝ (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) :=
    ConvexOn.lineRestriction (x := x) (v := v) hu
  exact
    AleksandrovDifferentiability.ConvexOn.subgradientOn_of_leftDeriv_le_of_le_rightDeriv
      (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
      (x := t) (p := leftDeriv (AleksandrovDifferentiability.lineRestriction u x v) t)
      huLine ht le_rfl
      (AleksandrovDifferentiability.ConvexOn.leftDeriv_le_rightDeriv
        (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
        (x := t) huLine ht)

/-- Ambient-interior version of
`ConvexOn.lineRestriction_leftDeriv_subgradientOn_at`. -/
theorem ConvexOn.lineRestriction_leftDeriv_subgradientOn_at_of_line_mem_interior
    {s : Set E} {u : E → ℝ} {x v : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • v ∈ interior s) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) t
      (leftDeriv (AleksandrovDifferentiability.lineRestriction u x v) t) :=
  AleksandrovDifferentiability.ConvexOn.lineRestriction_leftDeriv_subgradientOn_at
    (s := s) (u := u) (x := x) (v := v) (t := t) hu
    (mem_interior_lineDomain_of_line_mem_interior ht)

end AleksandrovDifferentiability
