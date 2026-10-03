/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Geometry.Cube
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.QuadraticTrap.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Cube-local Aleksandrov statement interfaces

This file names the source-proof local targets on the normalized cubes
`Q_3 = (-3,3)^n` and `Q_1 = (-1,1)^n`. These are statements and set interfaces, not axioms:
the proof route will fill these targets using the upper-contact estimate from the source
document.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Points where the first derivative exists in the ambient coordinate space. -/
def firstOrderDifferentiabilitySet {n : ℕ} (u : SourceCubeSpace n → ℝ) :
    Set (SourceCubeSpace n) :=
  {x | DifferentiableAt ℝ u x}

/-- Points where the source upper-contact opening is finite, encoded through the project
approximation-style predicate `HasUpperContactOpeningAtMostOn`. -/
def finiteUpperContactOpeningSet {n : ℕ} (s : Set (SourceCubeSpace n))
    (u : SourceCubeSpace n → ℝ) : Set (SourceCubeSpace n) :=
  {x | ∃ A : ℝ, HasUpperContactOpeningAtMostOn s u x A}

/-- The source bad set where the upper-contact opening on `Q_3` is not bounded by `A`, restricted
to the conclusion cube `Q_1`. This represents
`{x in Q_1 : \overline\Theta_{u,Q_3}(x) > A}` using the existing at-most-opening predicate. -/
def upperContactOpeningBadSet (n : ℕ) (u : SourceCubeSpace n → ℝ) (A : ℝ) :
    Set (SourceCubeSpace n) :=
  sourceOpenCube n 1 \ upperContactOpeningAtMostSet (sourceOpenCube n 3) u A

/-- The cube-local good set `Omega_A` from the source proof: differentiability points in `Q_1`
whose upper-contact opening relative to `Q_3` is at most `A`. -/
def cubeGoodSet (n : ℕ) (u : SourceCubeSpace n → ℝ) (A : ℝ) :
    Set (SourceCubeSpace n) :=
  sourceOpenCube n 1 ∩
    (firstOrderDifferentiabilitySet u ∩
      upperContactOpeningAtMostSet (sourceOpenCube n 3) u A)

/-- Oscillation of `u` on the large normalized source cube `Q_3`. -/
def sourceCubeOscillation (n : ℕ) (u : SourceCubeSpace n → ℝ) : ℝ :=
  oscOn u (sourceOpenCube n 3)

/-- The source-proof gradient vector, represented as the Fréchet-Riesz vector associated to the
Fréchet derivative. This names the object written `grad u(x)` in the source proof. -/
def frechetGradient {n : ℕ} (u : SourceCubeSpace n → ℝ) (x : SourceCubeSpace n) :
    SourceCubeSpace n :=
  (InnerProductSpace.toDual ℝ (SourceCubeSpace n)).symm (fderiv ℝ u x)

/-- The source gradient vector is Mathlib's `gradient`. -/
theorem frechetGradient_eq_gradient {n : ℕ} (u : SourceCubeSpace n → ℝ) :
    frechetGradient u = gradient u :=
  rfl

/-- The Fréchet derivative is represented by the source gradient vector. -/
theorem fderiv_apply_eq_inner_frechetGradient {n : ℕ} (u : SourceCubeSpace n → ℝ)
    (x z : SourceCubeSpace n) :
    fderiv ℝ u x z = inner ℝ (frechetGradient u x) z := by
  exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := SourceCubeSpace n)
    (x := z) (y := fderiv ℝ u x)).symm

/-- At an interior differentiability point of the source cube, the source Fréchet gradient is a
subgradient on `Q_3`. -/
theorem ConvexOn.sourceCube_subgradientOn_frechetGradient {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hx : x ∈ interior (sourceOpenCube n 3)) (hd : DifferentiableAt ℝ u x) :
    SubgradientOn (sourceOpenCube n 3) u x (frechetGradient u x) :=
  AleksandrovDifferentiability.ConvexOn.subgradientOn_of_hasFDerivAt_of_forall_eq_inner
    (s := sourceOpenCube n 3) (u := u) (x := x) (p := frechetGradient u x)
    hu hx hd.hasFDerivAt
    (fun z => fderiv_apply_eq_inner_frechetGradient u x z)

/-- Convexity makes the source affine remainder with the Fréchet-gradient slope nonnegative on
`Q_3` at every interior differentiability point. -/
theorem affineRemainder_nonneg_of_convex_of_differentiableAt_sourceCube {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x y : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hx : x ∈ interior (sourceOpenCube n 3)) (hd : DifferentiableAt ℝ u x)
    (hy : y ∈ sourceOpenCube n 3) :
    0 ≤ affineRemainder u x (frechetGradient u x) y :=
  (AleksandrovDifferentiability.ConvexOn.sourceCube_subgradientOn_frechetGradient
    hu hx hd).affineRemainder_nonneg hy

/-- Increment-coordinate version of
`affineRemainder_nonneg_of_convex_of_differentiableAt_sourceCube`, matching the source proof's
`\tilde u(z) ≥ 0` normalization. -/
theorem affineRemainder_nonneg_increment_of_convex_of_differentiableAt_sourceCube {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x z : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hx : x ∈ interior (sourceOpenCube n 3)) (hd : DifferentiableAt ℝ u x)
    (hz : x + z ∈ sourceOpenCube n 3) :
    0 ≤ affineRemainder u x (frechetGradient u x) (x + z) :=
  affineRemainder_nonneg_of_convex_of_differentiableAt_sourceCube hu hx hd hz

/-- The source-normalized affine remainder
`z ↦ u(x+z) - u(x) - grad u(x)·z` is convex on the increment domain inside `Q_3`. -/
theorem ConvexOn.sourceCube_affineRemainderIncrement_frechetGradient {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ConvexOn ℝ ((fun z : SourceCubeSpace n => x + z) ⁻¹' sourceOpenCube n 3)
      (fun z => affineRemainder u x (frechetGradient u x) (x + z)) :=
  ConvexOn.affineRemainder_increment hu

/-- Coordinate-line version of `affineRemainder_lineRestriction_at`, based at the coordinate
line through `x`. This is the bookkeeping needed to turn one-dimensional estimates on the
coordinate slice into estimates for the ambient normalized remainder. -/
theorem affineRemainder_coordinateLine_eq {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (x p : SourceCubeSpace n) (i : Fin n) (r : ℝ) :
    affineRemainder
        (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
        (x i) (inner ℝ p (sourceCoordinateVector i)) r =
      affineRemainder u x p (coordinateLinePoint i (coordinateLineBase i x) r) := by
  have hbase : coordinateLineBase i x + x i • sourceCoordinateVector i = x := by
    simpa [coordinateLinePoint] using coordinateLinePoint_base_self i x
  simpa [coordinateLinePoint, hbase] using
    affineRemainder_lineRestriction_at
      (u := u) (x := coordinateLineBase i x) (p := p)
      (v := sourceCoordinateVector i) (t := x i) (r := r)

/-- Positive coordinate increment form of `affineRemainder_coordinateLine_eq`. -/
theorem affineRemainder_coordinateLine_add_eq {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (x p : SourceCubeSpace n) (i : Fin n) (h : ℝ) :
    affineRemainder
        (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
        (x i) (inner ℝ p (sourceCoordinateVector i)) (x i + h) =
      affineRemainder u x p (x + h • sourceCoordinateVector i) := by
  simpa using affineRemainder_coordinateLine_eq (u := u) (x := x) (p := p) i (x i + h)

/-- Negative coordinate increment form of `affineRemainder_coordinateLine_eq`. -/
theorem affineRemainder_coordinateLine_sub_eq {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (x p : SourceCubeSpace n) (i : Fin n) (h : ℝ) :
    affineRemainder
        (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
        (x i) (inner ℝ p (sourceCoordinateVector i)) (x i - h) =
      affineRemainder u x p (x - h • sourceCoordinateVector i) := by
  simpa using affineRemainder_coordinateLine_eq (u := u) (x := x) (p := p) i (x i - h)

/-- Coordinate-slice endpoint upper bounds, in the one-dimensional language produced by the
localized maximal estimate in the source proof. -/
def HasCoordinateLineEndpointQuadraticBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (ρ K : ℝ) : Prop :=
  ∀ i : Fin n, ∀ h : ℝ, 0 < h → h < ρ →
    affineRemainder
        (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
        (x i) (inner ℝ p (sourceCoordinateVector i)) (x i + h) ≤ K * h ^ 2 ∧
      affineRemainder
        (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
        (x i) (inner ℝ p (sourceCoordinateVector i)) (x i - h) ≤ K * h ^ 2

/-- Ambient coordinate endpoint bounds for the normalized source remainder
`\tilde u(±h e_i)`. -/
def HasSourceCubeCoordinateEndpointQuadraticBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (ρ K : ℝ) : Prop :=
  x ∈ sourceOpenCube n 3 ∧
    ∀ i : Fin n, ∀ h : ℝ, 0 < h → h < ρ →
      affineRemainder u x p (x + h • sourceCoordinateVector i) ≤ K * h ^ 2 ∧
        affineRemainder u x p (x - h • sourceCoordinateVector i) ≤ K * h ^ 2

/-- The endpoint set `{± h e_i}` used in the source proof before taking the convex hull. -/
def sourceCrossPolytopeEndpointSet (n : ℕ) (h : ℝ) : Set (SourceCubeSpace n) :=
  {z | ∃ i : Fin n, z = h • sourceCoordinateVector i ∨
      z = -h • sourceCoordinateVector i}

/-- The source cross-polytope `K_h = conv {± h e_i}`. -/
def sourceCrossPolytope (n : ℕ) (h : ℝ) : Set (SourceCubeSpace n) :=
  convexHull ℝ (sourceCrossPolytopeEndpointSet n h)

/-- Membership in the source cross-polytope from the coordinate `l1` bound. This is the
coordinate form of `K_h = conv {± h e_i}` used before inserting the Euclidean ball
`B_{h / sqrt n}` in the source proof. -/
theorem mem_sourceCrossPolytope_of_sum_abs_le {n : ℕ} {h : ℝ} (hn : 1 ≤ n) (hh : 0 < h)
    {z : SourceCubeSpace n} (hz : (∑ i : Fin n, |z i|) ≤ h) :
    z ∈ sourceCrossPolytope n h := by
  classical
  let k : Fin n := ⟨0, hn⟩
  let S : ℝ := ∑ i : Fin n, |z i|
  let extra : ℝ := (1 - S / h) / 2
  let w : Sum (Fin n) (Fin n) → ℝ := fun a =>
    match a with
    | Sum.inl i => (z i + |z i|) / (2 * h) + if i = k then extra else 0
    | Sum.inr i => (|z i| - z i) / (2 * h) + if i = k then extra else 0
  let q : Sum (Fin n) (Fin n) → SourceCubeSpace n := fun a =>
    match a with
    | Sum.inl i => h • sourceCoordinateVector i
    | Sum.inr i => -h • sourceCoordinateVector i
  change z ∈ convexHull ℝ (sourceCrossPolytopeEndpointSet n h)
  refine mem_convexHull_of_exists_fintype (R := ℝ) (ι := Sum (Fin n) (Fin n)) w q ?_ ?_ ?_ ?_
  · intro a
    have hden : 0 ≤ 2 * h := by positivity
    have hS_div_le_one : S / h ≤ 1 := by
      rw [div_le_one₀ hh]
      exact hz
    have hextra_nonneg : 0 ≤ extra := by
      dsimp [extra]
      linarith
    cases a with
    | inl i =>
        have hnum : 0 ≤ z i + |z i| := by
          have := neg_le_abs (z i)
          linarith
        have hbase : 0 ≤ (z i + |z i|) / (2 * h) := div_nonneg hnum hden
        dsimp [w]
        split_ifs <;> linarith
    | inr i =>
        have hnum : 0 ≤ |z i| - z i := by
          have := le_abs_self (z i)
          linarith
        have hbase : 0 ≤ (|z i| - z i) / (2 * h) := div_nonneg hnum hden
        dsimp [w]
        split_ifs <;> linarith
  · have hS_eq : S = ∑ i : Fin n, |z i| := rfl
    have hsum_ite :
        (∑ i : Fin n, (if i = k then extra else 0)) = extra := by
      simp
    have hsum_base :
        (∑ i : Fin n, (z i + |z i|) / (2 * h)) +
            (∑ i : Fin n, (|z i| - z i) / (2 * h)) = S / h := by
      rw [← Finset.sum_add_distrib]
      simp only [← add_div]
      have hpoint :
          (∑ i : Fin n, ((z i + |z i|) + (|z i| - z i)) / (2 * h)) =
            (∑ i : Fin n, |z i|) / h := by
        calc
          (∑ i : Fin n, ((z i + |z i|) + (|z i| - z i)) / (2 * h))
              = ∑ i : Fin n, |z i| / h := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  field_simp [hh.ne']
                  ring
          _ = (∑ i : Fin n, |z i|) / h := by
                rw [Finset.sum_div]
      simpa [hS_eq] using hpoint
    calc
      ∑ a : Sum (Fin n) (Fin n), w a
          = ((∑ i : Fin n, (z i + |z i|) / (2 * h)) +
              ∑ i : Fin n, (if i = k then extra else 0)) +
              ((∑ i : Fin n, (|z i| - z i) / (2 * h)) +
                ∑ i : Fin n, (if i = k then extra else 0)) := by
                simp [w, Fintype.sum_sum_type, Finset.sum_add_distrib]
      _ = ((∑ i : Fin n, (z i + |z i|) / (2 * h)) +
              ∑ i : Fin n, (|z i| - z i) / (2 * h)) + 2 * extra := by
            rw [hsum_ite]
            ring
      _ = S / h + 2 * extra := by
            rw [hsum_base]
      _ = 1 := by
            dsimp [extra]
            ring
  · intro a
    cases a with
    | inl i =>
        exact ⟨i, Or.inl rfl⟩
    | inr i =>
        exact ⟨i, Or.inr rfl⟩
  · ext j
    have hdecomp :
        (∑ a : Sum (Fin n) (Fin n), w a • q a) =
          ((∑ i : Fin n, ((z i + |z i|) / (2 * h)) • (h • sourceCoordinateVector i)) +
              (∑ i : Fin n, (if i = k then extra else 0) • (h • sourceCoordinateVector i))) +
            ((∑ i : Fin n, ((|z i| - z i) / (2 * h)) • ((-h) • sourceCoordinateVector i)) +
              (∑ i : Fin n, (if i = k then extra else 0) • ((-h) • sourceCoordinateVector i))) := by
      simp [w, q, Fintype.sum_sum_type, Finset.sum_add_distrib, add_smul]
      abel
    have hsum_ite_smul_pos :
        (∑ i : Fin n, (if i = k then extra else 0) • (h • sourceCoordinateVector i)) =
          extra • (h • sourceCoordinateVector k) := by
      simp
    have hsum_ite_smul_neg :
        (∑ i : Fin n, (if i = k then extra else 0) • ((-h) • sourceCoordinateVector i)) =
          extra • ((-h) • sourceCoordinateVector k) := by
      simp
    rw [hdecomp, hsum_ite_smul_pos, hsum_ite_smul_neg]
    simp [sourceCoordinateVector, Finset.sum_apply, Pi.single_apply, add_assoc]
    field_simp [hh.ne']
    ring

/-- Cauchy-Schwarz comparison between the coordinate `l1` norm and the Euclidean norm in the
source cube model. -/
theorem source_sum_abs_le_sqrt_card_mul_norm {n : ℕ} (z : SourceCubeSpace n) :
    (∑ i : Fin n, |z i|) ≤ Real.sqrt (n : ℝ) * ‖z‖ := by
  have hcs :=
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n))
      (fun i : Fin n => |z i|) (fun _ : Fin n => (1 : ℝ))
  simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Finset.sum_const,
    Fintype.card_fin, mul_comm, mul_left_comm, mul_assoc] using hcs

/-- Euclidean radius form of the source inclusion `B_{h / sqrt n} ⊆ K_h`. -/
theorem mem_sourceCrossPolytope_of_norm_lt {n : ℕ} {h : ℝ} (hn : 1 ≤ n) (hh : 0 < h)
    {z : SourceCubeSpace n} (hz : ‖z‖ < h / Real.sqrt (n : ℝ)) :
    z ∈ sourceCrossPolytope n h := by
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsum_lt : (∑ i : Fin n, |z i|) < h := by
    calc
      (∑ i : Fin n, |z i|) ≤ Real.sqrt (n : ℝ) * ‖z‖ :=
        source_sum_abs_le_sqrt_card_mul_norm z
      _ < Real.sqrt (n : ℝ) * (h / Real.sqrt (n : ℝ)) :=
        mul_lt_mul_of_pos_left hz hsqrt_pos
      _ = h := by
        field_simp [hsqrt_pos.ne']
  exact mem_sourceCrossPolytope_of_sum_abs_le hn hh hsum_lt.le

/-- Metric-ball form of the source inclusion `B_{h / sqrt n} ⊆ K_h`. -/
theorem ball_subset_sourceCrossPolytope {n : ℕ} {h : ℝ} (hn : 1 ≤ n) (hh : 0 < h) :
    Metric.ball (0 : SourceCubeSpace n) (h / Real.sqrt (n : ℝ)) ⊆ sourceCrossPolytope n h := by
  intro z hz
  exact mem_sourceCrossPolytope_of_norm_lt hn hh (by simpa [dist_eq_norm] using hz)

/-- Transfer the coordinate endpoint estimates from the one-dimensional slice language to the
ambient normalized source remainder. -/
theorem HasCoordinateLineEndpointQuadraticBound.sourceCubeCoordinateEndpointQuadraticBound
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {ρ K : ℝ}
    (hline : HasCoordinateLineEndpointQuadraticBound n u x p ρ K)
    (hx : x ∈ sourceOpenCube n 3) :
    HasSourceCubeCoordinateEndpointQuadraticBound n u x p ρ K := by
  refine ⟨hx, ?_⟩
  intro i h hhpos hhρ
  rcases hline i h hhpos hhρ with ⟨hplus, hminus⟩
  constructor
  · simpa [affineRemainder_coordinateLine_add_eq] using hplus
  · simpa [affineRemainder_coordinateLine_sub_eq] using hminus

/-- Coordinate endpoint bounds are monotone in the quadratic constant. -/
theorem HasSourceCubeCoordinateEndpointQuadraticBound.mono_const {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {ρ K K' : ℝ}
    (h : HasSourceCubeCoordinateEndpointQuadraticBound n u x p ρ K) (hK : K ≤ K') :
    HasSourceCubeCoordinateEndpointQuadraticBound n u x p ρ K' := by
  refine ⟨h.1, ?_⟩
  intro i r hrpos hrρ
  rcases h.2 i r hrpos hrρ with ⟨hplus, hminus⟩
  have hmono : K * r ^ 2 ≤ K' * r ^ 2 :=
    mul_le_mul_of_nonneg_right hK (sq_nonneg r)
  exact ⟨hplus.trans hmono, hminus.trans hmono⟩

/-- Endpoint membership in the increment domain for the source cross-polytope, assuming the
corresponding coordinate endpoints lie in `Q_3`. -/
theorem sourceCrossPolytopeEndpointSet_subset_incrementDomain {n : ℕ}
    {x : SourceCubeSpace n} {h : ℝ}
    (hendpoint :
      ∀ i : Fin n,
        x + h • sourceCoordinateVector i ∈ sourceOpenCube n 3 ∧
          x - h • sourceCoordinateVector i ∈ sourceOpenCube n 3) :
    sourceCrossPolytopeEndpointSet n h ⊆
      (fun z : SourceCubeSpace n => x + z) ⁻¹' sourceOpenCube n 3 := by
  intro z hz
  rcases hz with ⟨i, rfl | rfl⟩
  · exact (hendpoint i).1
  · simpa [sub_eq_add_neg] using (hendpoint i).2

/-- Source proof maximum-principle step on `K_h = conv {± h e_i}`: if the normalized affine
remainder is convex and bounded by `K h^2` at all coordinate endpoints, then it has the same
upper bound throughout `K_h`. -/
theorem HasSourceCubeCoordinateEndpointQuadraticBound.affineRemainder_le_of_mem_crossPolytope
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p z : SourceCubeSpace n} {ρ K h : ℝ}
    (hend : HasSourceCubeCoordinateEndpointQuadraticBound n u x p ρ K)
    (hconv :
      ConvexOn ℝ ((fun z : SourceCubeSpace n => x + z) ⁻¹' sourceOpenCube n 3)
        (fun z => affineRemainder u x p (x + z)))
    (hhpos : 0 < h) (hhρ : h < ρ)
    (hendpoint :
      ∀ i : Fin n,
        x + h • sourceCoordinateVector i ∈ sourceOpenCube n 3 ∧
          x - h • sourceCoordinateVector i ∈ sourceOpenCube n 3)
    (hz : z ∈ sourceCrossPolytope n h) :
    affineRemainder u x p (x + z) ≤ K * h ^ 2 := by
  rcases ConvexOn.exists_ge_of_mem_convexHull hconv
      (sourceCrossPolytopeEndpointSet_subset_incrementDomain hendpoint)
      (by simpa [sourceCrossPolytope] using hz) with
    ⟨y, hyEndpoint, hzy⟩
  refine hzy.trans ?_
  rcases hyEndpoint with ⟨i, rfl | rfl⟩
  · exact (hend.2 i h hhpos hhρ).1
  · simpa [sub_eq_add_neg] using (hend.2 i h hhpos hhρ).2

/-- A cube-local affine-remainder upper bound with the source upper-contact normalization. -/
def HasSourceCubeAffineRemainderUpperBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (A : ℝ) : Prop :=
  x ∈ sourceOpenCube n 3 ∧
    ∀ y ∈ sourceOpenCube n 3,
      affineRemainder u x p y ≤ (A / 2) * ‖y - x‖ ^ 2

/-- Approximate version of `HasSourceCubeAffineRemainderUpperBound`, matching
`HasUpperContactOpeningAtMostOn`: every larger opening has the corresponding affine-remainder
upper bound. -/
def HasSourceCubeAffineRemainderOpeningAtMost (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (A : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → HasSourceCubeAffineRemainderUpperBound n u x p (A + η)

/-- Source-style affine-remainder bound, written as `K * ‖y - x‖^2`. The source proof obtains
this form first, then absorbs the factor of `2` into the dimensional opening constant. -/
def HasSourceCubeAffineRemainderQuadraticBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (K : ℝ) : Prop :=
  x ∈ sourceOpenCube n 3 ∧
    ∀ y ∈ sourceOpenCube n 3,
      affineRemainder u x p y ≤ K * ‖y - x‖ ^ 2

/-- Increment-coordinate version of the source-style affine-remainder bound. This is the
language of the source proof, where `tilde u(z)` is estimated for `x + z ∈ Q_3`. -/
def HasSourceCubeIncrementQuadraticBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (K : ℝ) : Prop :=
  x ∈ sourceOpenCube n 3 ∧
    ∀ z : SourceCubeSpace n, x + z ∈ sourceOpenCube n 3 →
      affineRemainder u x p (x + z) ≤ K * ‖z‖ ^ 2

/-- Small-increment part of the source estimate. -/
def HasSourceCubeSmallIncrementQuadraticBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (ρ K : ℝ) : Prop :=
  x ∈ sourceOpenCube n 3 ∧
    ∀ z : SourceCubeSpace n, x + z ∈ sourceOpenCube n 3 → ‖z‖ < ρ →
      affineRemainder u x p (x + z) ≤ K * ‖z‖ ^ 2

/-- Source large-increment input: on `Q_3`, the normalized affine remainder has at most affine
growth in the increment size. The source obtains this from bounded oscillation and a local
gradient bound. -/
def HasSourceCubeAffineRemainderLinearGrowthBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (K0 K1 : ℝ) : Prop :=
  x ∈ sourceOpenCube n 3 ∧
    ∀ z : SourceCubeSpace n, x + z ∈ sourceOpenCube n 3 →
      affineRemainder u x p (x + z) ≤ K0 + K1 * ‖z‖

/-- Source large-increment input before subtracting the affine part: values of `u` are bounded
above relative to `u x` on `Q_3`. The source later obtains this from the oscillation of `u` on
`Q_3`. -/
def HasSourceCubeValueDifferenceUpperBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x : SourceCubeSpace n) (M : ℝ) : Prop :=
  x ∈ sourceOpenCube n 3 ∧
    ∀ y ∈ sourceOpenCube n 3, u y - u x ≤ M

/-- A value-difference bound and a slope norm bound give the linear-growth estimate for the
normalized affine remainder. -/
theorem HasSourceCubeValueDifferenceUpperBound.affineRemainderLinearGrowthBound_of_norm_le
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {M G : ℝ}
    (hval : HasSourceCubeValueDifferenceUpperBound n u x M) (hp : ‖p‖ ≤ G) :
    HasSourceCubeAffineRemainderLinearGrowthBound n u x p M G := by
  refine ⟨hval.1, ?_⟩
  intro z hzQ
  have hu_bound : u (x + z) - u x ≤ M := hval.2 (x + z) hzQ
  have hinner_abs : |inner ℝ p z| ≤ ‖p‖ * ‖z‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) p z
  have hneg_inner : -inner ℝ p z ≤ G * ‖z‖ := by
    calc
      -inner ℝ p z ≤ |inner ℝ p z| := neg_le_abs _
      _ ≤ ‖p‖ * ‖z‖ := hinner_abs
      _ ≤ G * ‖z‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg z)
  have hdiff : x + z - x = z := by
    abel
  dsimp [affineRemainder]
  rw [hdiff]
  linarith

/-- Points in `Q_1` have all sufficiently short coordinate endpoints inside `Q_3`. This
discharges the endpoint-domain hypothesis in the source small-increment estimate. -/
theorem sourceCube_coordinateEndpointDomain_of_mem_sourceOpenCube_one {n : ℕ}
    {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) {ρ : ℝ} (hρ : ρ ≤ 1) :
    ∀ ⦃r : ℝ⦄, 0 < r → r < ρ →
      ∀ i : Fin n,
        x + r • sourceCoordinateVector i ∈ sourceOpenCube n 3 ∧
          x - r • sourceCoordinateVector i ∈ sourceOpenCube n 3 := by
  intro r hrpos hrρ i
  have hrabs : |r| < 2 := by
    rw [abs_of_pos hrpos]
    linarith
  exact ⟨sourceOpenCube_one_add_coordinate_mem_three (i := i) hx hrabs,
    sourceOpenCube_one_sub_coordinate_mem_three (i := i) hx hrabs⟩

/-- Source small-increment estimate from coordinate endpoint bounds. This packages the proof
line: choose `h = sqrt n * ‖z‖`, use `z ∈ K_h`, and then apply the convex-hull endpoint bound. -/
theorem HasSourceCubeCoordinateEndpointQuadraticBound.smallIncrementQuadraticBound_of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {ρ K : ℝ}
    (hn : 1 ≤ n) (_hρ : 0 < ρ)
    (hend : HasSourceCubeCoordinateEndpointQuadraticBound n u x p ρ K)
    (hconv :
      ConvexOn ℝ ((fun z : SourceCubeSpace n => x + z) ⁻¹' sourceOpenCube n 3)
        (fun z => affineRemainder u x p (x + z)))
    (hendpoint :
      ∀ ⦃r : ℝ⦄, 0 < r → r < ρ →
        ∀ i : Fin n,
          x + r • sourceCoordinateVector i ∈ sourceOpenCube n 3 ∧
            x - r • sourceCoordinateVector i ∈ sourceOpenCube n 3) :
    HasSourceCubeSmallIncrementQuadraticBound n u x p
      (ρ / Real.sqrt (n : ℝ)) (K * (n : ℝ)) := by
  refine ⟨hend.1, ?_⟩
  intro z _hzQ hzSmall
  by_cases hz0 : z = 0
  · subst hz0
    simp
  let r : ℝ := Real.sqrt (n : ℝ) * ‖z‖
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hrpos : 0 < r := by
    exact mul_pos hsqrt_pos (norm_pos_iff.mpr hz0)
  have hrρ : r < ρ := by
    calc
      r = Real.sqrt (n : ℝ) * ‖z‖ := rfl
      _ < Real.sqrt (n : ℝ) * (ρ / Real.sqrt (n : ℝ)) :=
        mul_lt_mul_of_pos_left hzSmall hsqrt_pos
      _ = ρ := by
        field_simp [hsqrt_pos.ne']
  have hzCross : z ∈ sourceCrossPolytope n r :=
    mem_sourceCrossPolytope_of_sum_abs_le hn hrpos
      (source_sum_abs_le_sqrt_card_mul_norm z)
  have hupper :=
    hend.affineRemainder_le_of_mem_crossPolytope hconv hrpos hrρ (hendpoint hrpos hrρ) hzCross
  have hcoeff :
      K * r ^ 2 = (K * (n : ℝ)) * ‖z‖ ^ 2 := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    ring
  simpa [hcoeff] using hupper

/-- Large-increment part of the source estimate. -/
def HasSourceCubeLargeIncrementQuadraticBound (n : ℕ) (u : SourceCubeSpace n → ℝ)
    (x p : SourceCubeSpace n) (ρ K : ℝ) : Prop :=
  x ∈ sourceOpenCube n 3 ∧
    ∀ z : SourceCubeSpace n, x + z ∈ sourceOpenCube n 3 → ρ ≤ ‖z‖ →
      affineRemainder u x p (x + z) ≤ K * ‖z‖ ^ 2

/-- Linear growth of the normalized remainder implies the source large-increment quadratic
estimate once the increment norm is bounded below by a positive radius. -/
theorem HasSourceCubeAffineRemainderLinearGrowthBound.largeIncrementQuadraticBound
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {ρ K0 K1 : ℝ}
    (h : HasSourceCubeAffineRemainderLinearGrowthBound n u x p K0 K1)
    (hρ : 0 < ρ) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) :
    HasSourceCubeLargeIncrementQuadraticBound n u x p ρ (K0 / ρ ^ 2 + K1 / ρ) := by
  refine ⟨h.1, ?_⟩
  intro z hzQ hzρ
  have hlinear := h.2 z hzQ
  let r : ℝ := ‖z‖
  have hr_nonneg : 0 ≤ r := norm_nonneg z
  have hr_pos : 0 < r := lt_of_lt_of_le hρ hzρ
  have hρsq_pos : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hρsq_le_rsq : ρ ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ hρ.le hr_nonneg).2 hzρ
  have hconst :
      K0 ≤ (K0 / ρ ^ 2) * r ^ 2 := by
    calc
      K0 = (K0 / ρ ^ 2) * ρ ^ 2 := by
        field_simp [hρsq_pos.ne']
      _ ≤ (K0 / ρ ^ 2) * r ^ 2 :=
        mul_le_mul_of_nonneg_left hρsq_le_rsq (div_nonneg hK0 hρsq_pos.le)
  have hlinear_term :
      K1 * r ≤ (K1 / ρ) * r ^ 2 := by
    have hr_le : r ≤ r ^ 2 / ρ := by
      rw [le_div_iff₀ hρ]
      nlinarith
    calc
      K1 * r ≤ K1 * (r ^ 2 / ρ) :=
        mul_le_mul_of_nonneg_left hr_le hK1
      _ = (K1 / ρ) * r ^ 2 := by
        ring
  have hquad :
      K0 + K1 * r ≤ (K0 / ρ ^ 2 + K1 / ρ) * r ^ 2 := by
    calc
      K0 + K1 * r ≤ (K0 / ρ ^ 2) * r ^ 2 + (K1 / ρ) * r ^ 2 :=
        add_le_add hconst hlinear_term
      _ = (K0 / ρ ^ 2 + K1 / ρ) * r ^ 2 := by
        ring
  exact hlinear.trans (by simpa [r] using hquad)

/-- Value-difference control plus a slope norm bound imply the source large-increment quadratic
estimate. This is the abstract Lean version of the source proof's large-`z` step from
oscillation and the local gradient bound. -/
theorem HasSourceCubeValueDifferenceUpperBound.largeIncrementQuadraticBound_of_norm_le
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {ρ M G : ℝ}
    (hval : HasSourceCubeValueDifferenceUpperBound n u x M) (hp : ‖p‖ ≤ G)
    (hρ : 0 < ρ) (hM : 0 ≤ M) (hG : 0 ≤ G) :
    HasSourceCubeLargeIncrementQuadraticBound n u x p ρ (M / ρ ^ 2 + G / ρ) :=
  (hval.affineRemainderLinearGrowthBound_of_norm_le hp).largeIncrementQuadraticBound hρ hM hG

/-- An abstract predicate representing the localized one-dimensional maximal bad condition
`M μ_{i,y}(s) > t` from the source proof. The arguments are the direction `i`, the coordinate-line
base point `y`, the line parameter `s`, and the threshold `t`. -/
abbrev CoordinateSliceBadPredicate (n : ℕ) :=
  Fin n → SourceCubeSpace n → ℝ → ℝ → Prop

end AleksandrovDifferentiability
