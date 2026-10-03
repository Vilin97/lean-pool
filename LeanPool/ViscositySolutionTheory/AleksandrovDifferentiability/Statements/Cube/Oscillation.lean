/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Basic.Sets

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Oscillation bounds on source cubes

This file records source-cube order estimates involving `oscOn`. These are used in the
large-increment part of the upper-contact estimate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Project-local bridge from bornological boundedness of real values to order-boundedness
above. -/
theorem BoundedOn.bddAbove_image {E : Type*} {s : Set E} {u : E → ℝ}
    (h : BoundedOn s u) :
    BddAbove (u '' s) :=
  h.bddAbove

/-- Project-local bridge from bornological boundedness of real values to order-boundedness
below. -/
theorem BoundedOn.bddBelow_image {E : Type*} {s : Set E} {u : E → ℝ}
    (h : BoundedOn s u) :
    BddBelow (u '' s) :=
  h.bddBelow

/-- The source-cube oscillation is nonnegative under the boundedness hypothesis used by the
normalized cube theorem. -/
theorem sourceCubeOscillation_nonneg_of_boundedOn {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    0 ≤ sourceCubeOscillation n u := by
  have hx : (0 : SourceCubeSpace n) ∈ sourceOpenCube n 3 :=
    zero_mem_sourceOpenCube (by norm_num)
  have hupper : BddAbove (u '' sourceOpenCube n 3) :=
    hbounded.bddAbove_image
  have hlower : BddBelow (u '' sourceOpenCube n 3) :=
    hbounded.bddBelow_image
  have hle : sInf (u '' sourceOpenCube n 3) ≤ sSup (u '' sourceOpenCube n 3) := by
    exact (csInf_le hlower ⟨0, hx, rfl⟩).trans (le_csSup hupper ⟨0, hx, rfl⟩)
  dsimp [sourceCubeOscillation, oscOn]
  linarith

/-- ENNReal squeeze lemma for estimates bounded by `K / m` for every positive natural `m`. -/
theorem measure_eq_zero_of_forall_le_ofReal_const_div_nat
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {K : ℝ}
    (hK : 0 ≤ K)
    (hbound : ∀ m : ℕ, 0 < m → μ s ≤ ENNReal.ofReal (K / (m : ℝ))) :
    μ s = 0 := by
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _hzero_lt_top
  simp only [zero_add]
  rw [← @ENNReal.ofReal_coe_nnreal ε]
  by_cases hKzero : K = 0
  · have hμ0 := hbound (1 : ℕ) (by norm_num)
    have hzero : ENNReal.ofReal (K / (1 : ℝ)) = 0 := by
      simp [hKzero]
    calc
      μ s ≤ ENNReal.ofReal (K / (1 : ℝ)) := by simpa using hμ0
      _ = 0 := hzero
      _ ≤ ENNReal.ofReal (ε : ℝ) := bot_le
  · have hεreal : 0 < (ε : ℝ) := by
      exact_mod_cast hε
    rcases exists_nat_gt (K / (ε : ℝ)) with ⟨m, hm⟩
    have hquot_nonneg : 0 ≤ K / (ε : ℝ) := div_nonneg hK hεreal.le
    have hm_pos_real : 0 < (m : ℝ) := lt_of_le_of_lt hquot_nonneg hm
    have hm_pos : 0 < m := Nat.cast_pos.mp hm_pos_real
    have hmul : K < (m : ℝ) * (ε : ℝ) := by
      have := (div_lt_iff₀ hεreal).mp hm
      simpa [mul_comm] using this
    have hK_div_le : K / (m : ℝ) ≤ (ε : ℝ) := by
      rw [div_le_iff₀ hm_pos_real]
      nlinarith [hmul]
    calc
      μ s ≤ ENNReal.ofReal (K / (m : ℝ)) := hbound m hm_pos
      _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hK_div_le

/-- Points in `Q_1` without finite upper-contact opening lie in every upper-contact bad set. -/
theorem sourceOpenCube_diff_finiteUpperContactOpeningSet_subset_upperContactOpeningBadSet
    {n : ℕ} {u : SourceCubeSpace n → ℝ} (A : ℝ) :
    sourceOpenCube n 1 \ finiteUpperContactOpeningSet (sourceOpenCube n 3) u ⊆
      upperContactOpeningBadSet n u A := by
  intro x hx
  exact ⟨hx.1, fun hA => hx.2 ⟨A, hA⟩⟩

/-- The upper-contact estimate implies that the upper-contact opening is finite a.e. on `Q_1`.

This is the limiting step in the source proof: the exceptional set is contained in every bad set
`{Θ > C(t + osc)}`, while the estimate bounds those bad sets by `C osc / t`, which tends to zero
as `t` tends to infinity. -/
theorem ConvexFiniteUpperContactOpeningAEOnCubeStatement.of_upperContactEstimate {n : ℕ}
    (hestimate : ConvexUpperContactEstimateStatement n) :
    ConvexFiniteUpperContactOpeningAEOnCubeStatement n := by
  intro hn u hbounded hconvex
  rcases hestimate hn with ⟨C, hC_nonneg, hC⟩
  have hosc_nonneg : 0 ≤ sourceCubeOscillation n u :=
    sourceCubeOscillation_nonneg_of_boundedOn hbounded
  have hK_nonneg : 0 ≤ C * sourceCubeOscillation n u :=
    mul_nonneg hC_nonneg hosc_nonneg
  refine measure_eq_zero_of_forall_le_ofReal_const_div_nat (μ := volume) hK_nonneg ?_
  intro m hm
  have ht : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsubset :
      sourceOpenCube n 1 \ finiteUpperContactOpeningSet (sourceOpenCube n 3) u ⊆
        upperContactOpeningBadSet n u
          (C * ((m : ℝ) + sourceCubeOscillation n u)) :=
    sourceOpenCube_diff_finiteUpperContactOpeningSet_subset_upperContactOpeningBadSet
      (n := n) (u := u) _
  calc
    volume (sourceOpenCube n 1 \ finiteUpperContactOpeningSet (sourceOpenCube n 3) u) ≤
        volume
          (upperContactOpeningBadSet n u
            (C * ((m : ℝ) + sourceCubeOscillation n u))) :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal (C * sourceCubeOscillation n u / (m : ℝ)) :=
      hC u (m : ℝ) ht hbounded hconvex

/-- If the values of `u` on `Q_3` are order-bounded above and below, then the oscillation on
`Q_3` bounds all value differences from a fixed base point in `Q_3`. -/
theorem HasSourceCubeValueDifferenceUpperBound.of_sourceCubeOscillation
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hx : x ∈ sourceOpenCube n 3)
    (hupper : BddAbove (u '' sourceOpenCube n 3))
    (hlower : BddBelow (u '' sourceOpenCube n 3)) :
    HasSourceCubeValueDifferenceUpperBound n u x (sourceCubeOscillation n u) := by
  refine ⟨hx, ?_⟩
  intro y hy
  have hy_le_sup : u y ≤ sSup (u '' sourceOpenCube n 3) :=
    le_csSup hupper ⟨y, hy, rfl⟩
  have inf_le_hx : sInf (u '' sourceOpenCube n 3) ≤ u x :=
    csInf_le hlower ⟨x, hx, rfl⟩
  dsimp [sourceCubeOscillation, oscOn]
  linarith

/-- Boundedness of `u` on `Q_3`, in the project-local `BoundedOn` sense, supplies the
order-boundedness needed to bound value differences by the source-cube oscillation. -/
theorem HasSourceCubeValueDifferenceUpperBound.of_boundedOn_sourceCubeOscillation
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hx : x ∈ sourceOpenCube n 3) (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    HasSourceCubeValueDifferenceUpperBound n u x (sourceCubeOscillation n u) :=
  HasSourceCubeValueDifferenceUpperBound.of_sourceCubeOscillation hx
    hbounded.bddAbove_image hbounded.bddBelow_image

/-- Cube-local form of the source local gradient bound, stated for any subgradient. If values
above `u x` are bounded by `M` on `Q_3` and `x ∈ Q_1`, then a subgradient at `x` has norm at most
`M`. The proof tests the supporting inequality in the normalized direction of the subgradient. -/
theorem HasSourceCubeValueDifferenceUpperBound.subgradient_norm_le_of_mem_sourceOpenCube_one
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {M : ℝ}
    (hval : HasSourceCubeValueDifferenceUpperBound n u x M)
    (hp : SubgradientOn (sourceOpenCube n 3) u x p) (hx : x ∈ sourceOpenCube n 1) :
    ‖p‖ ≤ M := by
  have hM_nonneg : 0 ≤ M := by
    have hxx := hval.2 x hval.1
    simpa using hxx
  by_cases hpzero : p = 0
  · subst hpzero
    simpa using hM_nonneg
  let e : SourceCubeSpace n := (‖p‖)⁻¹ • p
  have hp_norm_ne : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hpzero
  have he_norm : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp_norm_ne]
  have he_mem : x + e ∈ sourceOpenCube n 3 :=
    sourceOpenCube_one_add_norm_le_one_mem_three hx (by rw [he_norm])
  have hsupport := hp.supporting_inequality he_mem
  have hdiff : x + e - x = e := by
    abel
  have hinner_eq : inner ℝ p e = ‖p‖ := by
    dsimp [e]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hp_norm_ne]
  have hle_diff : ‖p‖ ≤ u (x + e) - u x := by
    have hsupport' : u x + ‖p‖ ≤ u (x + e) := by
      simpa [hdiff, hinner_eq] using hsupport
    linarith
  exact hle_diff.trans (hval.2 (x + e) he_mem)

/-- Variant of the source local gradient bound for points in `Q_{3/2}`. The proof tests the
supporting inequality in a normalized direction for length `3 / 2`, which still remains inside
`Q_3`. -/
theorem HasSourceCubeValueDifferenceUpperBound.subgradient_norm_le_of_mem_three_halves
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {M : ℝ}
    (hval : HasSourceCubeValueDifferenceUpperBound n u x M)
    (hp : SubgradientOn (sourceOpenCube n 3) u x p)
    (hx : x ∈ sourceOpenCube n (3 / 2 : ℝ)) :
    ‖p‖ ≤ M := by
  have hM_nonneg : 0 ≤ M := by
    have hxx := hval.2 x hval.1
    simpa using hxx
  by_cases hpzero : p = 0
  · subst hpzero
    simpa using hM_nonneg
  let e : SourceCubeSpace n := (‖p‖)⁻¹ • p
  have hp_norm_ne : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hpzero
  have he_norm : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp_norm_ne]
  have hstep_norm : ‖(3 / 2 : ℝ) • e‖ ≤ (3 / 2 : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num), he_norm, mul_one]
  have he_mem : x + (3 / 2 : ℝ) • e ∈ sourceOpenCube n 3 :=
    sourceOpenCube_three_halves_add_norm_le_three_halves_mem_three hx hstep_norm
  have hsupport := hp.supporting_inequality he_mem
  have hdiff : x + (3 / 2 : ℝ) • e - x = (3 / 2 : ℝ) • e := by
    abel
  have hinner_eq : inner ℝ p e = ‖p‖ := by
    dsimp [e]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hp_norm_ne]
  have hle_diff : (3 / 2 : ℝ) * ‖p‖ ≤ u (x + (3 / 2 : ℝ) • e) - u x := by
    have hsupport' : u x + (3 / 2 : ℝ) * ‖p‖ ≤ u (x + (3 / 2 : ℝ) • e) := by
      simpa [hdiff, inner_smul_right, hinner_eq] using hsupport
    linarith
  have hle_M : (3 / 2 : ℝ) * ‖p‖ ≤ M :=
    hle_diff.trans (hval.2 (x + (3 / 2 : ℝ) • e) he_mem)
  have hnorm_nonneg : 0 ≤ ‖p‖ := norm_nonneg _
  nlinarith

/-- The source local subgradient bound gives bornological boundedness of the full
subdifferential at points in `Q_{3/2}`. -/
theorem HasSourceCubeValueDifferenceUpperBound.subgradient_set_isBounded_of_mem_three_halves
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {M : ℝ}
    (hval : HasSourceCubeValueDifferenceUpperBound n u x M)
    (hx : x ∈ sourceOpenCube n (3 / 2 : ℝ)) :
    Bornology.IsBounded {p : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u x p} := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : SourceCubeSpace n)).2 ⟨M, ?_⟩
  intro p hp
  have hp_norm : ‖p‖ ≤ M :=
    hval.subgradient_norm_le_of_mem_three_halves hp hx
  simpa [Metric.mem_closedBall, dist_eq_norm] using hp_norm

/-- Boundedness of `u` on `Q_3` gives boundedness of every subdifferential at points in
`Q_{3/2}`. This is the cube-local boundedness input for compact subdifferential extrema. -/
theorem sourceCube_subgradient_set_isBounded_of_boundedOn_three_halves
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hx : x ∈ sourceOpenCube n (3 / 2 : ℝ)) :
    Bornology.IsBounded {p : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u x p} := by
  have hx3 : x ∈ sourceOpenCube n 3 :=
    sourceOpenCube_subset_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hx
  have hval :
      HasSourceCubeValueDifferenceUpperBound n u x (sourceCubeOscillation n u) :=
    HasSourceCubeValueDifferenceUpperBound.of_boundedOn_sourceCubeOscillation hx3 hbounded
  exact hval.subgradient_set_isBounded_of_mem_three_halves hx

/-- Source-cube local gradient bound in the form used by the large-increment estimate. -/
theorem ConvexOn.norm_frechetGradient_le_sourceCubeOscillation_of_boundedOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) (hx : x ∈ sourceOpenCube n 1)
    (hderiv : DifferentiableAt ℝ u x) :
    ‖frechetGradient u x‖ ≤ sourceCubeOscillation n u := by
  have hx3 : x ∈ sourceOpenCube n 3 := sourceOpenCube_one_subset_three hx
  have hval :
      HasSourceCubeValueDifferenceUpperBound n u x (sourceCubeOscillation n u) :=
    HasSourceCubeValueDifferenceUpperBound.of_boundedOn_sourceCubeOscillation hx3 hbounded
  have hsub :
      SubgradientOn (sourceOpenCube n 3) u x (frechetGradient u x) :=
    AleksandrovDifferentiability.ConvexOn.sourceCube_subgradientOn_frechetGradient hu
      (sourceOpenCube_one_subset_interior_three hx) hderiv
  exact hval.subgradient_norm_le_of_mem_sourceOpenCube_one hsub hx

/-- Source-cube local gradient bound for differentiability points in `Q_{3/2}`. -/
theorem ConvexOn.norm_frechetGradient_le_sourceCubeOscillation_of_boundedOn_three_halves
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hx : x ∈ sourceOpenCube n (3 / 2 : ℝ))
    (hderiv : DifferentiableAt ℝ u x) :
    ‖frechetGradient u x‖ ≤ sourceCubeOscillation n u := by
  have hx3 : x ∈ sourceOpenCube n 3 :=
    sourceOpenCube_subset_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hx
  have hval :
      HasSourceCubeValueDifferenceUpperBound n u x (sourceCubeOscillation n u) :=
    HasSourceCubeValueDifferenceUpperBound.of_boundedOn_sourceCubeOscillation hx3 hbounded
  have hsub :
      SubgradientOn (sourceOpenCube n 3) u x (frechetGradient u x) :=
    AleksandrovDifferentiability.ConvexOn.sourceCube_subgradientOn_frechetGradient hu
      (sourceOpenCube_subset_interior_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3)
        (by norm_num) hx)
      hderiv
  exact hval.subgradient_norm_le_of_mem_three_halves hsub hx

/-- Large-increment estimate in the exact source-cube form obtained from oscillation and the
local gradient bound. -/
theorem ConvexOn.sourceCube_largeIncrementQuadraticBound_of_boundedOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {ρ : ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) (hx : x ∈ sourceOpenCube n 1)
    (hderiv : DifferentiableAt ℝ u x) (hρ : 0 < ρ) :
    HasSourceCubeLargeIncrementQuadraticBound n u x (frechetGradient u x) ρ
      (sourceCubeOscillation n u / ρ ^ 2 + sourceCubeOscillation n u / ρ) := by
  have hx3 : x ∈ sourceOpenCube n 3 := sourceOpenCube_one_subset_three hx
  have hval :
      HasSourceCubeValueDifferenceUpperBound n u x (sourceCubeOscillation n u) :=
    HasSourceCubeValueDifferenceUpperBound.of_boundedOn_sourceCubeOscillation hx3 hbounded
  have hgrad :
      ‖frechetGradient u x‖ ≤ sourceCubeOscillation n u :=
    AleksandrovDifferentiability.ConvexOn.norm_frechetGradient_le_sourceCubeOscillation_of_boundedOn
      hu hbounded hx hderiv
  have hosc_nonneg : 0 ≤ sourceCubeOscillation n u :=
    sourceCubeOscillation_nonneg_of_boundedOn hbounded
  exact hval.largeIncrementQuadraticBound_of_norm_le hgrad hρ hosc_nonneg hosc_nonneg

/-- Source-cube pointwise quadratic affine-remainder estimate obtained by combining the
coordinate endpoint bounds, the convexity maximum-principle step on the cross-polytope, and the
large-increment estimate from oscillation and the local gradient bound. -/
theorem ConvexOn.sourceCube_affineRemainderQuadraticBound_of_endpoint_of_boundedOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} {ρ K : ℝ}
    (hn : 1 ≤ n) (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1) (hK : 0 ≤ K)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) (hx : x ∈ sourceOpenCube n 1)
    (hderiv : DifferentiableAt ℝ u x)
    (hend :
      HasSourceCubeCoordinateEndpointQuadraticBound n u x (frechetGradient u x) ρ K) :
    HasSourceCubeAffineRemainderQuadraticBound n u x (frechetGradient u x)
      (K * (n : ℝ) +
        (sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
          sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)))) := by
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hradius_pos : 0 < ρ / Real.sqrt (n : ℝ) :=
    div_pos hρ hsqrt_pos
  have hendpoint :
      ∀ ⦃r : ℝ⦄, 0 < r → r < ρ →
        ∀ i : Fin n,
          x + r • sourceCoordinateVector i ∈ sourceOpenCube n 3 ∧
            x - r • sourceCoordinateVector i ∈ sourceOpenCube n 3 :=
    sourceCube_coordinateEndpointDomain_of_mem_sourceOpenCube_one hx hρ_le_one
  have hconv :
      ConvexOn ℝ ((fun z : SourceCubeSpace n => x + z) ⁻¹' sourceOpenCube n 3)
        (fun z => affineRemainder u x (frechetGradient u x) (x + z)) :=
    AleksandrovDifferentiability.ConvexOn.sourceCube_affineRemainderIncrement_frechetGradient hu
  have hsmall :
      HasSourceCubeSmallIncrementQuadraticBound n u x (frechetGradient u x)
        (ρ / Real.sqrt (n : ℝ)) (K * (n : ℝ)) :=
    hend.smallIncrementQuadraticBound_of_convex hn hρ hconv hendpoint
  have hlarge :
      HasSourceCubeLargeIncrementQuadraticBound n u x (frechetGradient u x)
        (ρ / Real.sqrt (n : ℝ))
        (sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
          sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ))) :=
    AleksandrovDifferentiability.ConvexOn.sourceCube_largeIncrementQuadraticBound_of_boundedOn
      hu hbounded hx hderiv hradius_pos
  have hosc_nonneg : 0 ≤ sourceCubeOscillation n u :=
    sourceCubeOscillation_nonneg_of_boundedOn hbounded
  have hlarge_const_nonneg :
      0 ≤ sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
          sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) := by
    exact add_nonneg
      (div_nonneg hosc_nonneg (sq_nonneg _))
      (div_nonneg hosc_nonneg hradius_pos.le)
  have hsmall_const_nonneg : 0 ≤ K * (n : ℝ) :=
    mul_nonneg hK (by positivity)
  exact hsmall.affineRemainderQuadraticBound_of_large hlarge
    (le_add_of_nonneg_right hlarge_const_nonneg)
    (le_add_of_nonneg_left hsmall_const_nonneg)

/-- At a point of `Q_1 \ E(t)`, the abstract endpoint-control property of the slice bad
predicate supplies the coordinate endpoint bounds needed by the combined source estimate. -/
theorem CoordinateSliceEndpointQuadraticControl.sourceCubeCoordinateEndpointQuadraticBound
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {x : SourceCubeSpace n} {ρ K t : ℝ}
    (hcontrol : CoordinateSliceEndpointQuadraticControl u sliceBad ρ K t)
    (hxQ : x ∈ sourceOpenCube n 1)
    (hxE : x ∉ upperContactEstimateTotalBadSet u sliceBad t) :
    HasSourceCubeCoordinateEndpointQuadraticBound n u x (frechetGradient u x) ρ K := by
  have hderiv : DifferentiableAt ℝ u x :=
    differentiableAt_of_mem_sourceOpenCube_of_not_mem_totalBadSet hxQ hxE
  have hnot : ∀ i : Fin n, ¬ sliceBad i (coordinateLineBase i x) (x i) t :=
    not_sliceBad_of_mem_sourceOpenCube_of_not_mem_totalBadSet hxQ hxE
  have hline :
      HasCoordinateLineEndpointQuadraticBound n u x (frechetGradient u x) ρ K :=
    hcontrol hxQ hderiv hnot
  exact hline.sourceCubeCoordinateEndpointQuadraticBound (sourceOpenCube_one_subset_three hxQ)

/-- Source-good-point pointwise affine-remainder estimate, with the coordinate endpoint bounds
derived from the abstract non-bad slice condition. -/
theorem ConvexOn.sourceCube_affineRemainderQuadraticBound_of_sliceControl_of_not_mem_totalBadSet
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {x : SourceCubeSpace n} {ρ K t : ℝ}
    (hn : 1 ≤ n) (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1) (hK : 0 ≤ K)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hcontrol : CoordinateSliceEndpointQuadraticControl u sliceBad ρ K t)
    (hxQ : x ∈ sourceOpenCube n 1)
    (hxE : x ∉ upperContactEstimateTotalBadSet u sliceBad t) :
    HasSourceCubeAffineRemainderQuadraticBound n u x (frechetGradient u x)
      (K * (n : ℝ) +
        (sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
          sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)))) := by
  have hderiv : DifferentiableAt ℝ u x :=
    differentiableAt_of_mem_sourceOpenCube_of_not_mem_totalBadSet hxQ hxE
  have hend :
      HasSourceCubeCoordinateEndpointQuadraticBound n u x (frechetGradient u x) ρ K :=
    hcontrol.sourceCubeCoordinateEndpointQuadraticBound hxQ hxE
  exact ConvexOn.sourceCube_affineRemainderQuadraticBound_of_endpoint_of_boundedOn
    hn hρ hρ_le_one hK hu hbounded hxQ hderiv hend

/-- Inclusion half of the source upper-contact estimate, assuming the abstract slice bad
predicate has the one-dimensional endpoint-control property. The factor `2` converts the
source-style `K * ‖y - x‖^2` affine-remainder bound to the project's opening convention. -/
theorem upperContactOpeningBadSet_subset_totalBadSet_of_sliceEndpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {ρ K t : ℝ}
    (hn : 1 ≤ n) (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1) (hK : 0 ≤ K)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hcontrol : CoordinateSliceEndpointQuadraticControl u sliceBad ρ K t) :
    upperContactOpeningBadSet n u
        (2 *
          (K * (n : ℝ) +
            (sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
              sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ))))) ⊆
      upperContactEstimateTotalBadSet u sliceBad t := by
  refine upperContactOpeningBadSet_subset_totalBadSet_of_affineRemainderQuadraticBound ?_
  intro x hxQ hxE
  exact ⟨frechetGradient u x,
    ConvexOn.sourceCube_affineRemainderQuadraticBound_of_sliceControl_of_not_mem_totalBadSet
      hn hρ hρ_le_one hK hu hbounded hcontrol hxQ hxE⟩

/-- Variant of `upperContactOpeningBadSet_subset_totalBadSet_of_sliceEndpointControl` with a
larger externally supplied opening threshold. This is the constant-absorption form needed when
the final dimensional constant is chosen after combining the measure and inclusion estimates. -/
theorem upperContactOpeningBadSet_subset_totalBadSet_of_sliceEndpointControl_of_le
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {ρ K t A : ℝ}
    (hn : 1 ≤ n) (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1) (hK : 0 ≤ K)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hcontrol : CoordinateSliceEndpointQuadraticControl u sliceBad ρ K t)
    (hA :
      2 *
          (K * (n : ℝ) +
            (sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
              sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)))) ≤ A) :
    upperContactOpeningBadSet n u A ⊆ upperContactEstimateTotalBadSet u sliceBad t := by
  exact (upperContactOpeningBadSet_mono_bound hA).trans
    (upperContactOpeningBadSet_subset_totalBadSet_of_sliceEndpointControl
      hn hρ hρ_le_one hK hu hbounded hcontrol)

/-- Assembly theorem for the upper-contact estimate decomposition from a source-route
coordinate-slice construction. A future maximal-function proof should instantiate `sliceBad`
and provide:

* endpoint quadratic control outside the slice bad sets,
* the Fubini/weak-type measure bound for `E(t)`, and
* the dimensional constant inequality comparing the source pointwise opening estimate with
  `C * (t + osc)`.
-/
theorem ConvexUpperContactEstimateDecompositionStatement.of_sliceEndpointControl
    {n : ℕ} {C ρ : ℝ}
    (hC_nonneg : 0 ≤ C) (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hslice :
      ∀ (u : SourceCubeSpace n → ℝ) (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexOn ℝ (sourceOpenCube n 3) u →
              ∃ (sliceBad : CoordinateSliceBadPredicate n) (K : ℝ),
                0 ≤ K ∧
                  CoordinateSliceEndpointQuadraticControl u sliceBad ρ K t ∧
                    volume (upperContactEstimateTotalBadSet u sliceBad t) ≤
                      ENNReal.ofReal (C * sourceCubeOscillation n u / t) ∧
                      2 *
                          (K * (n : ℝ) +
                            (sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
                              sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)))) ≤
                        C * (t + sourceCubeOscillation n u)) :
    ConvexUpperContactEstimateDecompositionStatement n := by
  intro hn
  refine ⟨C, hC_nonneg, ?_⟩
  intro u t ht hbounded hconvex
  rcases hslice u t ht hbounded hconvex with
    ⟨sliceBad, K, hK, hcontrol, hmeasure, hthreshold⟩
  refine ⟨sliceBad, hmeasure, ?_⟩
  exact upperContactOpeningBadSet_subset_totalBadSet_of_sliceEndpointControl_of_le
    hn hρ hρ_le_one hK hconvex hbounded hcontrol hthreshold

end AleksandrovDifferentiability
