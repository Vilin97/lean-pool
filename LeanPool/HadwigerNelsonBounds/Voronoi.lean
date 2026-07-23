/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.VoronoiQuadratic

/-!
# Triangular-lattice covering radius

This module converts the unit-square quadratic estimate into a covering-radius
theorem for the triangular lattice and defines the chosen nearest lattice cell.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/-- **Voronoi covering radius (the geometric heart of (G1)).**

    Constructive proof: given `p ∈ R²`, compute lattice coordinates
    `s := p₀/a − p₁/(a√3)`, `t := 2·p₁/(a√3)`. Let
    `i₀ := ⌊s⌋`, `j₀ := ⌊t⌋`,
    `α := s − i₀ ∈ [0, 1)`, `β := t − j₀ ∈ [0, 1)`. The squared distance from
    `p` to lattice point `(i₀ + Δi, j₀ + Δj)` is `a²·Q(α − Δi, β − Δj)` where
    `Q(u, v) = u² + uv + v²`.

    The unit square `[0, 1]²` is covered by four Voronoi cells centered at
    `(0,0), (1,0), (0,1), (1,1)` in `(α, β)` space. In each cell, the
    corresponding `Q` value is `≤ 1/3`. Case-split on the cell. -/
lemma exists_lattice_point_within_circumradius (p : R2) :
    ∃ (q : ℤ × ℤ), dist p (isbellLatticePoint q.1 q.2)
                    ≤ isbellLatticeStep / Real.sqrt 3 := by
  -- Abbreviations.
  set a := isbellLatticeStep with ha_def
  have ha_pos : 0 < a := by
    change (0 : ℝ) < isbellLatticeStep
    unfold isbellLatticeStep
    norm_num
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt3_ne : Real.sqrt 3 ≠ 0 := ne_of_gt hsqrt3_pos
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  -- Lattice coordinates of p.
  set s : ℝ := p 0 / a - p 1 / (a * Real.sqrt 3) with hs_def
  set t : ℝ := 2 * p 1 / (a * Real.sqrt 3) with ht_def
  -- Inverse: p 0 = s·a + t·a/2 and p 1 = t·a·√3/2.
  have hp0_eq : p 0 = s * a + t * (a / 2) := by
    change p 0 = (p 0 / a - p 1 / (a * Real.sqrt 3)) * a
      + (2 * p 1 / (a * Real.sqrt 3)) * (a / 2)
    field_simp
    ring
  have hp1_eq : p 1 = t * (a * Real.sqrt 3 / 2) := by
    change p 1 = (2 * p 1 / (a * Real.sqrt 3)) * (a * Real.sqrt 3 / 2)
    field_simp
  -- Floor + fractional part.
  set i₀ : ℤ := ⌊s⌋ with hi₀_def
  set j₀ : ℤ := ⌊t⌋ with hj₀_def
  set α : ℝ := s - (i₀ : ℝ) with hα_def
  set β : ℝ := t - (j₀ : ℝ) with hβ_def
  -- α, β ∈ [0, 1).
  have hα_lo : 0 ≤ α := by
    change 0 ≤ s - (i₀ : ℝ)
    have := Int.floor_le s
    linarith
  have hα_hi : α < 1 := by
    change s - (i₀ : ℝ) < 1
    have := Int.lt_floor_add_one s
    linarith
  have hβ_lo : 0 ≤ β := by
    change 0 ≤ t - (j₀ : ℝ)
    have := Int.floor_le t
    linarith
  have hβ_hi : β < 1 := by
    change t - (j₀ : ℝ) < 1
    have := Int.lt_floor_add_one t
    linarith
  -- Distance-squared formula (parametrized in Δi, Δj relative to (i₀, j₀)).
  -- Squared dist from p to lattice(i₀ + Δi, j₀ + Δj) = a² · Q(α - Δi, β - Δj).
  have dist_sq_formula : ∀ (Δi Δj : ℤ),
      dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) ^ 2
        = a ^ 2 * ((α - Δi) ^ 2 + (α - Δi) * (β - Δj) + (β - Δj) ^ 2) := by
    intro Δi Δj
    rw [dist_point_lattice_sq_cart p (i₀ + Δi) (j₀ + Δj)]
    rw [hp0_eq, hp1_eq]
    push_cast
    -- Now both sides are pure algebra in s, t, a, sqrt 3, i₀, j₀, Δi, Δj.
    -- Use ring with the substitution sqrt3 * sqrt3 = 3.
    have hexpand :
        (s * a + t * (a / 2)
          - (((i₀ : ℝ) + (Δi : ℝ)) * a + ((j₀ : ℝ) + (Δj : ℝ)) * (a / 2))) ^ 2
        + (t * (a * Real.sqrt 3 / 2) - ((j₀ : ℝ) + (Δj : ℝ)) * (a * Real.sqrt 3 / 2)) ^ 2
        = a ^ 2 * ((s - i₀ - Δi) ^ 2 + (s - i₀ - Δi) * (t - j₀ - Δj)
            + (t - j₀ - Δj) ^ 2 / 4)
          + a ^ 2 * (Real.sqrt 3 * Real.sqrt 3) / 4 * (t - j₀ - Δj) ^ 2 := by ring
    rw [hexpand, hsq3]
    change a ^ 2 * ((s - (i₀ : ℝ) - Δi) ^ 2 +
        (s - (i₀ : ℝ) - Δi) * (t - (j₀ : ℝ) - Δj)
            + (t - (j₀ : ℝ) - Δj) ^ 2 / 4)
          + a ^ 2 * 3 / 4 * (t - (j₀ : ℝ) - Δj) ^ 2
        = a ^ 2 * (((s - (i₀ : ℝ)) - (Δi : ℝ)) ^ 2
            + ((s - (i₀ : ℝ)) - (Δi : ℝ)) * ((t - (j₀ : ℝ)) - (Δj : ℝ))
            + ((t - (j₀ : ℝ)) - (Δj : ℝ)) ^ 2)
    ring
  -- Goal-completing helper: given Δi, Δj and Q(α - Δi, β - Δj) ≤ 1/3,
  -- conclude dist ≤ a/√3.
  have finish : ∀ (Δi Δj : ℤ),
      ((α - Δi) ^ 2 + (α - Δi) * (β - Δj) + (β - Δj) ^ 2 ≤ 1 / 3) →
      dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) ≤ a / Real.sqrt 3 := by
    intro Δi Δj hQ
    have hd_sq := dist_sq_formula Δi Δj
    -- a² · Q ≤ a² · (1/3), so dist² ≤ a²/3 = (a/√3)².
    have ha_sq_nn : 0 ≤ a ^ 2 := sq_nonneg _
    have hQ_nn : 0 ≤ (α - Δi) ^ 2 + (α - Δi) * (β - Δj) + (β - Δj) ^ 2 := by
      have h4Q : 4 * ((α - Δi) ^ 2 + (α - Δi) * (β - Δj) + (β - Δj) ^ 2)
          = (2 * (α - Δi) + (β - Δj)) ^ 2 + 3 * (β - Δj) ^ 2 := by ring
      nlinarith [sq_nonneg (2 * (α - Δi) + (β - Δj)), sq_nonneg (β - Δj), h4Q]
    have hd_sq_le : dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) ^ 2
        ≤ a ^ 2 / 3 := by
      rw [hd_sq]
      nlinarith [ha_sq_nn, hQ, hQ_nn]
    -- (a/√3)² = a²/3.
    have h_rhs_sq : (a / Real.sqrt 3) ^ 2 = a ^ 2 / 3 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
    have h_rhs_nn : 0 ≤ a / Real.sqrt 3 := by positivity
    have hd_nn : 0 ≤ dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) := dist_nonneg
    have : dist p (isbellLatticePoint (i₀ + Δi) (j₀ + Δj)) ^ 2
        ≤ (a / Real.sqrt 3) ^ 2 := by rw [h_rhs_sq]; exact hd_sq_le
    exact abs_le_of_sq_le_sq' this h_rhs_nn |>.2
  obtain ⟨Δi, Δj, hQuadratic⟩ :=
    unitSquare_has_near_lattice_corner hα_lo hα_hi hβ_lo hβ_hi
  refine ⟨(i₀ + Δi, j₀ + Δj), ?_⟩
  exact finish Δi Δj hQuadratic

/-- The lattice coordinates of a lattice point within the Voronoi
    circumradius of `p`. Built via classical choice on
    `exists_lattice_point_within_circumradius`. -/
noncomputable def nearestLatticeIdx (p : R2) : ℤ × ℤ :=
  (exists_lattice_point_within_circumradius p).choose

/-- The defining property of `nearestLatticeIdx`: it lies within the
    Voronoi circumradius. -/
lemma nearestLatticeIdx_spec (p : R2) :
    dist p (isbellLatticePoint (nearestLatticeIdx p).1 (nearestLatticeIdx p).2)
      ≤ isbellLatticeStep / Real.sqrt 3 :=
  (exists_lattice_point_within_circumradius p).choose_spec

/-- Cast an integer residue modulo seven to the corresponding finite color. -/
noncomputable def toFin7 (n : ℤ) : Fin 7 :=
  (ZMod.finEquiv 7).symm (n : ZMod 7)

/-- The Isbell 7-coloring assigns to each point `p ∈ R²` the color
    `(i + 3·j) mod 7`, where `(i, j) = nearestLatticeIdx p` are the
    integer coordinates of a nearest lattice point. -/
noncomputable def isbellColor : R2 → Fin 7 :=
  fun p => toFin7 ((nearestLatticeIdx p).1 + 3 * (nearestLatticeIdx p).2)

/-! ### The remaining geometric fact -/

/-- **(G1) Voronoi covering radius.** Every point of R² lies within
    distance `a/√3` of its assigned lattice point.

    Immediate corollary of `exists_lattice_point_within_circumradius`:
    by construction `nearestLatticeIdx` is *chosen* to satisfy this. -/
lemma dist_le_voronoi_circumradius (p : R2) :
    dist p (isbellLatticePoint (nearestLatticeIdx p).1 (nearestLatticeIdx p).2)
      ≤ isbellLatticeStep / Real.sqrt 3 :=
  nearestLatticeIdx_spec p

end HadwigerNelsonBounds
