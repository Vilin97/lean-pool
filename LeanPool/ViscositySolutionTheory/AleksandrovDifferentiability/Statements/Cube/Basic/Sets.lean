/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Basic.Core
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Cube-local bad sets and estimates
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory
open scoped NNReal

namespace AleksandrovDifferentiability

/-- The bad-set predicate is jointly measurable in the transverse point and line parameter. -/
def CoordinateSliceBadPredicateMeasurable {n : ℕ}
    (sliceBad : CoordinateSliceBadPredicate n) (t : ℝ) : Prop :=
  ∀ i : Fin n, MeasurableSet {p : SourceCubeSpace n × ℝ | sliceBad i p.1 p.2 t}

/-- Analytic content required from the coordinate slice bad predicate: outside the slice bad
sets, the one-dimensional estimates give quadratic endpoint bounds for the ambient
Fréchet-gradient affine remainder on each coordinate line.

This is the source line where the localized one-dimensional maximal estimate gives
`0 ≤ \tilde u(± h e_i) ≤ C t h^2`. The actual maximal-function instantiation of `sliceBad`
will prove this interface later. -/
def CoordinateSliceEndpointQuadraticControl {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (sliceBad : CoordinateSliceBadPredicate n)
    (ρ K t : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄,
    x ∈ sourceOpenCube n 1 →
      DifferentiableAt ℝ u x →
        (∀ i : Fin n, ¬ sliceBad i (coordinateLineBase i x) (x i) t) →
          HasCoordinateLineEndpointQuadraticBound n u x (frechetGradient u x) ρ K

/-- The source bad set `E_i(t)` associated to a coordinate direction and an abstract slice bad
predicate. A point `x in Q_1` is tested by writing it as
`coordinateLineBase i x + (x i) e_i`. -/
def coordinateSliceBadSet {n : ℕ} (sliceBad : CoordinateSliceBadPredicate n)
    (i : Fin n) (t : ℝ) : Set (SourceCubeSpace n) :=
  {x | x ∈ sourceOpenCube n 1 ∧ sliceBad i (coordinateLineBase i x) (x i) t}

/-- The total source bad set
`E(t) = (Q_1 \ D) ∪ ⋃_i E_i(t)`, where `D` is the differentiability set. -/
def upperContactEstimateTotalBadSet {n : ℕ} (u : SourceCubeSpace n → ℝ)
    (sliceBad : CoordinateSliceBadPredicate n) (t : ℝ) : Set (SourceCubeSpace n) :=
  (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) ∪
    ⋃ i : Fin n, coordinateSliceBadSet sliceBad i t

/-- Source-local normalized cube theorem. This corresponds to the preparatory convex source
note's normalized cube theorem, formulated for global functions restricted to `Q_3`. -/
def ConvexAleksandrovNormalizedCubeStatement (n : ℕ) : Prop :=
  1 ≤ n →
    ∀ u : SourceCubeSpace n → ℝ,
      BoundedOn (sourceOpenCube n 3) u →
        ConvexOn ℝ (sourceOpenCube n 3) u →
          volume (sourceOpenCube n 1 \ secondOrderDifferentiabilitySet u) = 0

/-- Source-local upper-contact estimate target, corresponding to Proposition
`p.upper-contact-estimate`. The constant is packaged existentially as a dimensional constant. -/
def ConvexUpperContactEstimateStatement (n : ℕ) : Prop :=
  1 ≤ n →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : SourceCubeSpace n → ℝ) (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexOn ℝ (sourceOpenCube n 3) u →
              volume
                  (upperContactOpeningBadSet n u
                    (C * (t + sourceCubeOscillation n u))) ≤
                ENNReal.ofReal (C * sourceCubeOscillation n u / t)

/-- Source-proof decomposition of the upper-contact estimate. For each convex bounded `u` and
threshold `t`, one supplies an abstract coordinate-slice bad predicate such that:

* the total bad set `E(t)` has the desired measure bound, and
* the upper-contact bad set is contained in `E(t)`.

The next formalization work is to instantiate this predicate using the localized maximal
function of the one-dimensional second-derivative measure. -/
def ConvexUpperContactEstimateDecompositionStatement (n : ℕ) : Prop :=
  1 ≤ n →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : SourceCubeSpace n → ℝ) (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexOn ℝ (sourceOpenCube n 3) u →
              ∃ sliceBad : CoordinateSliceBadPredicate n,
                volume (upperContactEstimateTotalBadSet u sliceBad t) ≤
                    ENNReal.ofReal (C * sourceCubeOscillation n u / t) ∧
                  upperContactOpeningBadSet n u
                      (C * (t + sourceCubeOscillation n u)) ⊆
                    upperContactEstimateTotalBadSet u sliceBad t

/-- The limiting consequence of the upper-contact estimate: the upper-contact opening relative
to `Q_3` is finite almost everywhere in `Q_1`. -/
def ConvexFiniteUpperContactOpeningAEOnCubeStatement (n : ℕ) : Prop :=
  1 ≤ n →
    ∀ u : SourceCubeSpace n → ℝ,
      BoundedOn (sourceOpenCube n 3) u →
        ConvexOn ℝ (sourceOpenCube n 3) u →
          volume
              (sourceOpenCube n 1 \
                finiteUpperContactOpeningSet (sourceOpenCube n 3) u) = 0

@[simp]
theorem mem_firstOrderDifferentiabilitySet {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {x : SourceCubeSpace n} :
    x ∈ firstOrderDifferentiabilitySet u ↔ DifferentiableAt ℝ u x :=
  Iff.rfl

@[simp]
theorem mem_finiteUpperContactOpeningSet {n : ℕ} {s : Set (SourceCubeSpace n)}
    {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n} :
    x ∈ finiteUpperContactOpeningSet s u ↔
      ∃ A : ℝ, HasUpperContactOpeningAtMostOn s u x A :=
  Iff.rfl

@[simp]
theorem mem_upperContactOpeningBadSet {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {A : ℝ} {x : SourceCubeSpace n} :
    x ∈ upperContactOpeningBadSet n u A ↔
      x ∈ sourceOpenCube n 1 ∧
        ¬ HasUpperContactOpeningAtMostOn (sourceOpenCube n 3) u x A :=
  Iff.rfl

@[simp]
theorem mem_cubeGoodSet {n : ℕ} {u : SourceCubeSpace n → ℝ} {A : ℝ}
    {x : SourceCubeSpace n} :
    x ∈ cubeGoodSet n u A ↔
      x ∈ sourceOpenCube n 1 ∧ DifferentiableAt ℝ u x ∧
        HasUpperContactOpeningAtMostOn (sourceOpenCube n 3) u x A := by
  simp [cubeGoodSet, firstOrderDifferentiabilitySet]

@[simp]
theorem mem_coordinateSliceBadSet {n : ℕ} {sliceBad : CoordinateSliceBadPredicate n}
    {i : Fin n} {t : ℝ} {x : SourceCubeSpace n} :
    x ∈ coordinateSliceBadSet sliceBad i t ↔
      x ∈ sourceOpenCube n 1 ∧ sliceBad i (coordinateLineBase i x) (x i) t :=
  Iff.rfl

@[simp]
theorem mem_upperContactEstimateTotalBadSet {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {sliceBad : CoordinateSliceBadPredicate n} {t : ℝ} {x : SourceCubeSpace n} :
    x ∈ upperContactEstimateTotalBadSet u sliceBad t ↔
      x ∈ sourceOpenCube n 1 ∧ ¬ DifferentiableAt ℝ u x ∨
        ∃ i : Fin n, x ∈ coordinateSliceBadSet sliceBad i t := by
  simp [upperContactEstimateTotalBadSet, firstOrderDifferentiabilitySet]

theorem cubeGoodSet_subset_sourceOpenCube {n : ℕ} {u : SourceCubeSpace n → ℝ} {A : ℝ} :
    cubeGoodSet n u A ⊆ sourceOpenCube n 1 := by
  intro x hx
  exact hx.1

theorem cubeGoodSet_subset_finiteUpperContactOpeningSet {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {A : ℝ} :
    cubeGoodSet n u A ⊆ finiteUpperContactOpeningSet (sourceOpenCube n 3) u := by
  intro x hx
  exact ⟨A, hx.2.2⟩

theorem coordinateSliceBadSet_subset_sourceOpenCube {n : ℕ}
    {sliceBad : CoordinateSliceBadPredicate n} {i : Fin n} {t : ℝ} :
    coordinateSliceBadSet sliceBad i t ⊆ sourceOpenCube n 1 := by
  intro x hx
  exact hx.1

/-- Product-coordinate measurability of a slice bad predicate implies measurability of the
ambient coordinate bad set `E_i(t)`. -/
theorem MeasurableSet.coordinateSliceBadSet_of_product {n : ℕ}
    {sliceBad : CoordinateSliceBadPredicate n} {i : Fin n} {t : ℝ}
    (hbad : MeasurableSet {p : SourceCubeSpace n × ℝ | sliceBad i p.1 p.2 t}) :
    MeasurableSet (coordinateSliceBadSet sliceBad i t) := by
  have hcoord :
      Continuous (fun x : SourceCubeSpace n => (coordinateLineBase i x, x i)) :=
    (continuous_coordinateLineBase i).prodMk (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  exact (isOpen_sourceOpenCube (n := n) 1).measurableSet.inter
    (hbad.preimage hcoord.measurable)

/-- Named-obligation version of
`MeasurableSet.coordinateSliceBadSet_of_product`, for all coordinate directions. -/
theorem CoordinateSliceBadPredicateMeasurable.coordinateSliceBadSet {n : ℕ}
    {sliceBad : CoordinateSliceBadPredicate n} {t : ℝ}
    (hbad : CoordinateSliceBadPredicateMeasurable sliceBad t) :
    ∀ i : Fin n, MeasurableSet (coordinateSliceBadSet sliceBad i t) :=
  fun i => MeasurableSet.coordinateSliceBadSet_of_product (hbad i)

/-- The upper-contact bad set is antitone in the opening threshold: a larger allowed opening
leaves fewer bad points. -/
theorem upperContactOpeningBadSet_mono_bound {n : ℕ} {u : SourceCubeSpace n → ℝ} {A B : ℝ}
    (hAB : A ≤ B) :
    upperContactOpeningBadSet n u B ⊆ upperContactOpeningBadSet n u A := by
  intro x hx
  exact ⟨hx.1, fun hA => hx.2 (hA.mono_bound hAB)⟩

theorem coordinateSliceBadSet_base_mem_sourceOpenCube {n : ℕ}
    {sliceBad : CoordinateSliceBadPredicate n} {i : Fin n} {t : ℝ} {x : SourceCubeSpace n}
    (hx : x ∈ coordinateSliceBadSet sliceBad i t) :
    coordinateLineBase i x ∈ sourceOpenCube n 1 :=
  coordinateLineBase_mem_sourceOpenCube_one hx.1

theorem upperContactEstimateTotalBadSet_subset_sourceOpenCube {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n} {t : ℝ} :
    upperContactEstimateTotalBadSet u sliceBad t ⊆ sourceOpenCube n 1 := by
  intro x hx
  rcases hx with hxDiff | hxSlice
  · exact hxDiff.1
  · rcases Set.mem_iUnion.mp hxSlice with ⟨i, hi⟩
    exact hi.1

/-- If a point of `Q_1` is not in the source total bad set `E(t)`, then it belongs to the
differentiability set `D`. -/
theorem differentiableAt_of_mem_sourceOpenCube_of_not_mem_totalBadSet {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n} {t : ℝ}
    {x : SourceCubeSpace n} (hxQ : x ∈ sourceOpenCube n 1)
    (hxE : x ∉ upperContactEstimateTotalBadSet u sliceBad t) :
    DifferentiableAt ℝ u x := by
  by_contra hdiff
  exact hxE (Or.inl ⟨hxQ, hdiff⟩)

/-- If a point of `Q_1` is not in the source total bad set `E(t)`, then no coordinate slice is
bad at the corresponding base/parameter pair. -/
theorem not_sliceBad_of_mem_sourceOpenCube_of_not_mem_totalBadSet {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n} {t : ℝ}
    {x : SourceCubeSpace n} (hxQ : x ∈ sourceOpenCube n 1)
    (hxE : x ∉ upperContactEstimateTotalBadSet u sliceBad t) (i : Fin n) :
    ¬ sliceBad i (coordinateLineBase i x) (x i) t := by
  intro hbad
  exact hxE (Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨hxQ, hbad⟩⟩))

/-- At a source-good point `x ∈ Q_1 \ E(t)`, convexity makes the source Fréchet gradient a
subgradient on `Q_3`. -/
theorem ConvexOn.sourceCube_subgradientOn_frechetGradient_of_not_mem_totalBadSet {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {x : SourceCubeSpace n} {t : ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hxQ : x ∈ sourceOpenCube n 1)
    (hxE : x ∉ upperContactEstimateTotalBadSet u sliceBad t) :
    SubgradientOn (sourceOpenCube n 3) u x (frechetGradient u x) := by
  have hxInterior : x ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_one_subset_interior_three hxQ
  have hd : DifferentiableAt ℝ u x :=
    differentiableAt_of_mem_sourceOpenCube_of_not_mem_totalBadSet hxQ hxE
  exact AleksandrovDifferentiability.ConvexOn.sourceCube_subgradientOn_frechetGradient
    hu hxInterior hd

/-- Source-good-point version of the affine-remainder nonnegativity: if `x ∈ Q_1` is outside the
total bad set `E(t)`, then `x` is differentiable, lies in the interior of `Q_3`, and convexity
gives the lower support for the source normalized remainder. -/
theorem affineRemainder_nonneg_increment_of_convex_of_not_mem_totalBadSet {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {x z : SourceCubeSpace n} {t : ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hxQ : x ∈ sourceOpenCube n 1)
    (hxE : x ∉ upperContactEstimateTotalBadSet u sliceBad t)
    (hz : x + z ∈ sourceOpenCube n 3) :
    0 ≤ affineRemainder u x (frechetGradient u x) (x + z) := by
  have hp : SubgradientOn (sourceOpenCube n 3) u x (frechetGradient u x) :=
    ConvexOn.sourceCube_subgradientOn_frechetGradient_of_not_mem_totalBadSet hu hxQ hxE
  exact hp.affineRemainder_nonneg hz

/-- A source-normalized affine-remainder upper bound is exactly an upper contact with the same
opening and slope. -/
theorem HasSourceCubeAffineRemainderUpperBound.hasUpperContactWithSlopeOn {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {A : ℝ}
    (h : HasSourceCubeAffineRemainderUpperBound n u x p A) :
    HasUpperContactWithSlopeOn (sourceOpenCube n 3) u x p A := by
  refine ⟨h.1, ?_⟩
  intro y hy
  have hupper := h.2 y hy
  dsimp [affineRemainder] at hupper
  linarith

/-- Increment-coordinate bounds imply pointwise source-style bounds on `Q_3`. -/
theorem HasSourceCubeIncrementQuadraticBound.affineRemainderQuadraticBound {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {K : ℝ}
    (h : HasSourceCubeIncrementQuadraticBound n u x p K) :
    HasSourceCubeAffineRemainderQuadraticBound n u x p K := by
  refine ⟨h.1, ?_⟩
  intro y hy
  have hinc := h.2 (y - x) (by simpa [add_comm, add_left_comm, add_assoc] using hy)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hinc

/-- Pointwise source-style bounds on `Q_3` imply the increment-coordinate formulation. -/
theorem HasSourceCubeAffineRemainderQuadraticBound.incrementQuadraticBound {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {K : ℝ}
    (h : HasSourceCubeAffineRemainderQuadraticBound n u x p K) :
    HasSourceCubeIncrementQuadraticBound n u x p K := by
  refine ⟨h.1, ?_⟩
  intro z hz
  simpa using h.2 (x + z) hz

/-- Combine the small- and large-increment cases from the source proof into a global
increment-coordinate quadratic bound. -/
theorem HasSourceCubeSmallIncrementQuadraticBound.combine_large {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {ρ Ksmall Klarge K : ℝ}
    (hsmall : HasSourceCubeSmallIncrementQuadraticBound n u x p ρ Ksmall)
    (hlarge : HasSourceCubeLargeIncrementQuadraticBound n u x p ρ Klarge)
    (hKsmall : Ksmall ≤ K) (hKlarge : Klarge ≤ K) :
    HasSourceCubeIncrementQuadraticBound n u x p K := by
  refine ⟨hsmall.1, ?_⟩
  intro z hz
  have hsmall_le : Ksmall * ‖z‖ ^ 2 ≤ K * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hKsmall (sq_nonneg _)
  have hlarge_le : Klarge * ‖z‖ ^ 2 ≤ K * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hKlarge (sq_nonneg _)
  rcases lt_or_ge ‖z‖ ρ with hρ | hρ
  · exact (hsmall.2 z hz hρ).trans hsmall_le
  · exact (hlarge.2 z hz hρ).trans hlarge_le

/-- Combine the small- and large-increment source estimates directly into the pointwise
source-style affine-remainder bound on `Q_3`. -/
theorem HasSourceCubeSmallIncrementQuadraticBound.affineRemainderQuadraticBound_of_large
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {ρ Ksmall Klarge K : ℝ}
    (hsmall : HasSourceCubeSmallIncrementQuadraticBound n u x p ρ Ksmall)
    (hlarge : HasSourceCubeLargeIncrementQuadraticBound n u x p ρ Klarge)
    (hKsmall : Ksmall ≤ K) (hKlarge : Klarge ≤ K) :
    HasSourceCubeAffineRemainderQuadraticBound n u x p K :=
  (hsmall.combine_large hlarge hKsmall hKlarge).affineRemainderQuadraticBound

/-- Source-style `K * ‖y - x‖^2` control gives the normalized opening `2*K`. -/
theorem HasSourceCubeAffineRemainderQuadraticBound.upperBound_two_mul {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {K : ℝ}
    (h : HasSourceCubeAffineRemainderQuadraticBound n u x p K) :
    HasSourceCubeAffineRemainderUpperBound n u x p (2 * K) := by
  refine ⟨h.1, ?_⟩
  intro y hy
  have hupper := h.2 y hy
  have hfactor : ((2 * K) / 2) * ‖y - x‖ ^ 2 = K * ‖y - x‖ ^ 2 := by
    ring
  simpa [hfactor] using hupper

/-- Source-style `K * ‖y - x‖^2` control gives approximate opening at most `2*K`. -/
theorem HasSourceCubeAffineRemainderQuadraticBound.openingAtMost_two_mul {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {K : ℝ}
    (h : HasSourceCubeAffineRemainderQuadraticBound n u x p K) :
    HasSourceCubeAffineRemainderOpeningAtMost n u x p (2 * K) := by
  intro η hη
  refine ⟨h.1, ?_⟩
  intro y hy
  have hupper := h.2 y hy
  have hle :
      K * ‖y - x‖ ^ 2 ≤ ((2 * K + η) / 2) * ‖y - x‖ ^ 2 := by
    have hcoeff : K ≤ (2 * K + η) / 2 := by linarith
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
  exact hupper.trans hle

/-- Approximate affine-remainder opening bounds give the project upper-contact-opening predicate
with fixed slope. -/
theorem HasSourceCubeAffineRemainderOpeningAtMost.hasUpperContactWithSlopeOpeningAtMostOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {A : ℝ}
    (h : HasSourceCubeAffineRemainderOpeningAtMost n u x p A) :
    HasUpperContactWithSlopeOpeningAtMostOn (sourceOpenCube n 3) u x p A := by
  intro η hη
  exact (h η hη).hasUpperContactWithSlopeOn

/-- Approximate affine-remainder opening bounds give the slope-free upper-contact-opening
predicate used in the upper-contact bad set. -/
theorem HasSourceCubeAffineRemainderOpeningAtMost.hasUpperContactOpeningAtMostOn {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {A : ℝ}
    (h : HasSourceCubeAffineRemainderOpeningAtMost n u x p A) :
    HasUpperContactOpeningAtMostOn (sourceOpenCube n 3) u x A :=
  h.hasUpperContactWithSlopeOpeningAtMostOn.hasUpperContactOpeningAtMostOn

/-- If a point in `Q_1` carries an approximate source affine-remainder upper bound with opening
`A`, then it is not in the source upper-contact bad set at threshold `A`. -/
theorem not_mem_upperContactOpeningBadSet_of_affineRemainderOpeningAtMost {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {x p : SourceCubeSpace n} {A : ℝ}
    (h : HasSourceCubeAffineRemainderOpeningAtMost n u x p A) :
    x ∉ upperContactOpeningBadSet n u A := by
  intro hx
  exact hx.2 h.hasUpperContactOpeningAtMostOn

/-- Source inclusion principle: to prove the upper-contact bad set is contained in `E(t)`, it
suffices to construct the affine-remainder opening bound at each point of `Q_1 \ E(t)`.
This packages the contradiction step at the end of the source proof of
Proposition `p.upper-contact-estimate`. -/
theorem upperContactOpeningBadSet_subset_totalBadSet_of_affineRemainderOpeningAtMost
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {A t : ℝ}
    (hgood :
      ∀ ⦃x : SourceCubeSpace n⦄,
        x ∈ sourceOpenCube n 1 →
          x ∉ upperContactEstimateTotalBadSet u sliceBad t →
            ∃ p : SourceCubeSpace n,
              HasSourceCubeAffineRemainderOpeningAtMost n u x p A) :
    upperContactOpeningBadSet n u A ⊆ upperContactEstimateTotalBadSet u sliceBad t := by
  intro x hxBad
  by_contra hxE
  rcases hgood hxBad.1 hxE with ⟨p, hp⟩
  exact not_mem_upperContactOpeningBadSet_of_affineRemainderOpeningAtMost hp hxBad

/-- Source-style inclusion principle with the bound as it appears in the proof:
`affineRemainder <= K * ‖y - x‖^2`. The resulting upper-contact opening threshold is `2*K`;
the factor is later absorbed into the dimensional constant. -/
theorem upperContactOpeningBadSet_subset_totalBadSet_of_affineRemainderQuadraticBound
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {K t : ℝ}
    (hgood :
      ∀ ⦃x : SourceCubeSpace n⦄,
        x ∈ sourceOpenCube n 1 →
          x ∉ upperContactEstimateTotalBadSet u sliceBad t →
            ∃ p : SourceCubeSpace n,
              HasSourceCubeAffineRemainderQuadraticBound n u x p K) :
    upperContactOpeningBadSet n u (2 * K) ⊆
      upperContactEstimateTotalBadSet u sliceBad t := by
  refine upperContactOpeningBadSet_subset_totalBadSet_of_affineRemainderOpeningAtMost ?_
  intro x hxQ hxE
  rcases hgood hxQ hxE with ⟨p, hp⟩
  exact ⟨p, hp.openingAtMost_two_mul⟩

/-- The source proof reduces the upper-contact estimate to the inclusion
`{Theta > C(t + osc)} ⊆ E(t)` and the total bad-set estimate for `E(t)`. -/
theorem measure_upperContactOpeningBadSet_le_of_subset_totalBadSet
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {sliceBad : CoordinateSliceBadPredicate n}
    {C t bound : ℝ}
    (hsubset :
      upperContactOpeningBadSet n u (C * (t + sourceCubeOscillation n u)) ⊆
        upperContactEstimateTotalBadSet u sliceBad t)
    (hmeasure :
      volume (upperContactEstimateTotalBadSet u sliceBad t) ≤ ENNReal.ofReal bound) :
    volume (upperContactOpeningBadSet n u (C * (t + sourceCubeOscillation n u))) ≤
      ENNReal.ofReal bound :=
  (measure_mono hsubset).trans hmeasure

/-- The decomposition used in the source proof implies the packaged upper-contact estimate. -/
theorem ConvexUpperContactEstimateStatement.of_decomposition {n : ℕ}
    (h : ConvexUpperContactEstimateDecompositionStatement n) :
    ConvexUpperContactEstimateStatement n := by
  intro hn
  rcases h hn with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro u t ht hbounded hconvex
  rcases hC u t ht hbounded hconvex with ⟨sliceBad, hmeasure, hsubset⟩
  exact measure_upperContactOpeningBadSet_le_of_subset_totalBadSet hsubset hmeasure

end AleksandrovDifferentiability
