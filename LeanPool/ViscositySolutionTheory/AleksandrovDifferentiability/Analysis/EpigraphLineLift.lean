/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.EpigraphSeparation
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LineRestriction

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Line-lift consequences of epigraph separation

This file connects the epigraph-separation support functional with the line-lift interfaces used
later in the Aleksandrov proof. It still does not prove the endpoint-specific normalization
`q = ℓ z`; it packages the support and nonemptiness consequences needed by the compact endpoint
attainment wrappers.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On an open finite-dimensional convex domain, epigraph separation gives a functional line lift
at the directional value of the supporting functional. -/
theorem ConvexOn.exists_lineSubgradientLiftsToAmbientFunctional_supportingValue_of_isOpen
    [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ}
    (hu : ConvexOn ℝ s u) (hs : IsOpen s) (hpoint : x + t • z ∈ s) :
    ∃ q : ℝ, LineSubgradientLiftsToAmbientFunctional s u x z t q := by
  rcases ConvexOn.exists_supportingFunctionalAt_of_isOpen
      (s := s) (u := u) (x := x + t • z) hu hs hpoint with
    ⟨φ, hsupport⟩
  exact ⟨φ z, φ, hsupport, rfl⟩

/-- A scalar affine function is zero if it is bounded below on the whole real line. -/
private theorem linear_eq_zero_of_forall_le_add_mul {c A m : ℝ}
    (h : ∀ r : ℝ, c ≤ A + r * m) :
    m = 0 := by
  by_contra hm
  let r : ℝ := (c - A - 1) / m
  have hr := h r
  have hcalc : A + r * m = c - 1 := by
    dsimp [r]
    field_simp [hm]
    ring
  linarith

/-- A line subgradient lifts to an ambient supporting functional on open finite-dimensional
convex domains.

The proof separates Mathlib's strict epigraph from the affine line minorant determined by the
one-dimensional subgradient. Since the separated convex set is the whole affine line, the
separating functional is constant on its direction; after normalizing by the negative vertical
coefficient, this forces the horizontal supporting functional to take the prescribed value on
`z`.

This is the project-local Hahn-Banach step: it uses Mathlib separation via
`geometric_hahn_banach_open`, and does not reprove Hahn-Banach. -/
theorem ConvexOn.lineSubgradientLiftsToAmbientFunctional_of_isOpen
    [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x z : E} {t q : ℝ}
    (hu : ConvexOn ℝ s u) (hs : IsOpen s)
    (hq : SubgradientOn (lineDomain s x z)
      (AleksandrovDifferentiability.lineRestriction u x z) t q) :
    LineSubgradientLiftsToAmbientFunctional s u x z t q := by
  let x₀ : E := x + t • z
  let u₀ : ℝ := u x₀
  let lineMinorant : Set (E × ℝ) :=
    {p | ∃ r : ℝ, p = (x + r • z, u₀ + q * (r - t))}
  have hline_convex : Convex ℝ lineMinorant := by
    intro p hp p' hp' a b ha hb hab
    rcases hp with ⟨r, rfl⟩
    rcases hp' with ⟨r', rfl⟩
    refine ⟨a * r + b * r', ?_⟩
    ext
    · calc
        a • (x + r • z) + b • (x + r' • z)
            = (a • x + (a * r) • z) + (b • x + (b * r') • z) := by
              simp [smul_add, smul_smul]
        _ = (a • x + b • x) + ((a * r) • z + (b * r') • z) := by
              abel
        _ = (a + b) • x + (a * r + b * r') • z := by
              rw [add_smul, add_smul]
        _ = x + (a * r + b * r') • z := by
              rw [hab, one_smul]
    · change
        a * (u₀ + q * (r - t)) + b * (u₀ + q * (r' - t)) =
          u₀ + q * (a * r + b * r' - t)
      calc
        a * (u₀ + q * (r - t)) + b * (u₀ + q * (r' - t))
            = (a + b) * u₀ + q * (a * r + b * r' - (a + b) * t) := by
              ring
        _ = u₀ + q * (a * r + b * r' - t) := by
              rw [hab]
              ring
  have hdisjoint : Disjoint (strictEpigraphOn s u) lineMinorant := by
    rw [disjoint_left]
    rintro ⟨y, rheight⟩ hyepi ⟨r, hline⟩
    injection hline with hy_eq hheight_eq
    subst y
    subst rheight
    rcases hyepi with ⟨hr_mem, hlt⟩
    have hr_domain : r ∈ lineDomain s x z := by
      simpa [lineDomain] using hr_mem
    have hminorant :=
      SubgradientOn.lineRestriction_supporting_slope_inequality hq hr_domain
    linarith
  rcases geometric_hahn_banach_open
      (ConvexOn.convex_strictEpigraphOn hu)
      (isOpen_strictEpigraphOn_of_continuousOn hs (hu.continuousOn hs))
      hline_convex hdisjoint with
    ⟨Λ, c, hstrict, hline⟩
  have hx₀_mem : x₀ ∈ s := by
    simpa [x₀, lineDomain] using hq.mem
  have hbase_mem : (x₀, u₀) ∈ lineMinorant := by
    refine ⟨t, ?_⟩
    simp [x₀, u₀]
  have hbase_ge : c ≤ Λ (x₀, u₀) := hline (x₀, u₀) hbase_mem
  have hsep_base : ∀ p ∈ strictEpigraphOn s u, Λ p < Λ (x₀, u₀) :=
    fun p hp => lt_of_lt_of_le (hstrict p hp) hbase_ge
  have hvert : Λ (0, (1 : ℝ)) < 0 := by
    have hepi : (x₀, u₀ + 1) ∈ strictEpigraphOn s u := by
      exact ⟨hx₀_mem, by simp [u₀]⟩
    have hlt := hstrict (x₀, u₀ + 1) hepi
    have hdecomp : (x₀, u₀ + 1) = (x₀, u₀) + (0, (1 : ℝ)) := by
      ext <;> simp
    rw [hdecomp, map_add] at hlt
    linarith
  have hline_direction_zero : Λ (z, q) = 0 := by
    have hline_all : ∀ a : ℝ, c ≤ Λ ((x₀, u₀) + a • (z, q)) := by
      intro a
      apply hline
      refine ⟨t + a, ?_⟩
      ext
      · simp [x₀, add_smul, add_assoc]
      · simp
        ring
    have hlinear : ∀ a : ℝ, c ≤ Λ (x₀, u₀) + a * Λ (z, q) := by
      intro a
      have hmap :
          Λ (x₀ + a • z, u₀ + a * q) = Λ (x₀, u₀) + a * Λ (z, q) := by
        have hpair : (x₀ + a • z, u₀ + a * q) = (x₀, u₀) + a • (z, q) := by
          ext <;> simp
        rw [hpair, map_add, map_smul]
        simp [smul_eq_mul]
      simpa [hmap] using hline_all a
    exact linear_eq_zero_of_forall_le_add_mul hlinear
  refine
    ⟨strictEpigraphOn.normalizedHorizontalFunctional Λ, ?_, ?_⟩
  · intro y hy
    simpa [x₀, u₀] using
      strictEpigraphOn_normalizedHorizontalFunctional_supporting_inequality
        (s := s) (u := u) (x := x₀) (y := y) hy Λ hvert hsep_base
  · have hdir :
        Λ (z, (0 : ℝ)) + q * Λ (0, (1 : ℝ)) = 0 := by
      have hdecomp : (z, q) = (z, (0 : ℝ)) + q • (0, (1 : ℝ)) := by
        ext <;> simp
      rw [hdecomp, map_add, map_smul] at hline_direction_zero
      simpa [smul_eq_mul] using hline_direction_zero
    have hvne : Λ (0, (1 : ℝ)) ≠ 0 := ne_of_lt hvert
    rw [strictEpigraphOn.normalizedHorizontalFunctional_apply]
    field_simp [hvne]
    linarith

/-- On an open finite-dimensional convex domain in a complete real inner-product space, the
subdifferential is nonempty at every point of the domain.

This is the vector-valued Riesz form of the supporting functional produced by Mathlib epigraph
separation. -/
theorem ConvexOn.subgradient_set_nonempty_of_isOpen
    [CompleteSpace E] [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x : E}
    (hu : ConvexOn ℝ s u) (hs : IsOpen s) (hx : x ∈ s) :
    {p : E | SubgradientOn s u x p}.Nonempty := by
  rcases ConvexOn.exists_supportingFunctionalAt_of_isOpen
      (s := s) (u := u) (x := x) hu hs hx with
    ⟨φ, hsupport⟩
  let p : E := (InnerProductSpace.toDual ℝ E).symm φ
  refine ⟨p, hx, ?_⟩
  intro y hy
  simpa [p] using hsupport y hy

/-- Eventual subgradient nonemptiness along a family of short segments contained in an open
finite-dimensional convex domain. -/
theorem ConvexOn.eventually_subgradient_set_nonempty_of_isOpen
    [CompleteSpace E] [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x : E}
    (hu : ConvexOn ℝ s u) (hs : IsOpen s)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ s) :
    ∀ᶠ z in 𝓝 (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        {p : E | SubgradientOn s u (x + t • z) p}.Nonempty := by
  filter_upwards [hsegment] with z hz t ht
  exact ConvexOn.subgradient_set_nonempty_of_isOpen hu hs (hz t ht)

end AleksandrovDifferentiability
