/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Incidence.Fibers
import LeanPool.MarkoffModP.BGS.Markoff.Core.ParabolicFibers

/-!
# The normalized incidence graph and its parabolic vertices

The published proof of Proposition 8 dismisses the case `p ≡ 1 (mod 4)` as simpler
because of the parabolic lines.  This file records the missing argument without folding
normalized trace coordinates back into the original Markoff coordinates.

The key fact is stronger than mere connectivity: after choosing `i² = -1`, a fiber whose
normalized coordinate is `2` or `-2` meets every fiber on either different coordinate axis.
-/

namespace BGS.Markoff

universe u

/-- The three coordinate axes used to index normalized conic fibers. -/
inductive NormalizedCoordinateAxis
  | first
  | second
  | third
  deriving DecidableEq, Repr

instance : Fintype NormalizedCoordinateAxis where
  elems := {.first, .second, .third}
  complete x := by cases x <;> simp

/-- A normalized conic fiber, indexed without identifying normalized and original coordinates. -/
def normalizedFiberAt {R : Type u} [CommRing R] :
    NormalizedCoordinateAxis → R → Set (NormalizedPoint R)
  | .first, a => normalizedFiber1 a
  | .second, a => normalizedFiber2 a
  | .third, a => normalizedFiber3 a

/-- The action of swapping the first two coordinates on axis labels. -/
def normalizedSwap12Axis : NormalizedCoordinateAxis → NormalizedCoordinateAxis
  | .first => .second
  | .second => .first
  | .third => .third

/-- The action of swapping the last two coordinates on axis labels. -/
def normalizedSwap23Axis : NormalizedCoordinateAxis → NormalizedCoordinateAxis
  | .first => .first
  | .second => .third
  | .third => .second

theorem normalizedSwap12_mem_fiberAt
    {R : Type u} [CommRing R] {axis : NormalizedCoordinateAxis} {a : R}
    {x : NormalizedPoint R} (hx : x ∈ normalizedFiberAt axis a) :
    normalizedSwap12 x ∈ normalizedFiberAt (normalizedSwap12Axis axis) a := by
  rcases axis with _ | _ | _
  all_goals
    refine ⟨?_, hx.2⟩
    change normalizedPolynomial (normalizedSwap12 x) = 0
    rw [normalizedPolynomial_swap12]
    exact hx.1

theorem normalizedSwap23_mem_fiberAt
    {R : Type u} [CommRing R] {axis : NormalizedCoordinateAxis} {a : R}
    {x : NormalizedPoint R} (hx : x ∈ normalizedFiberAt axis a) :
    normalizedSwap23 x ∈ normalizedFiberAt (normalizedSwap23Axis axis) a := by
  rcases axis with _ | _ | _
  all_goals
    refine ⟨?_, hx.2⟩
    change normalizedPolynomial (normalizedSwap23 x) = 0
    rw [normalizedPolynomial_swap23]
    exact hx.1

/-- Two normalized conic fibers meet when their set-theoretic intersection is nonempty. -/
def NormalizedFibersMeet {R : Type u} (s t : Set (NormalizedPoint R)) : Prop :=
  (s ∩ t).Nonempty

theorem normalizedFibersMeet_comm {R : Type u} {s t : Set (NormalizedPoint R)} :
    NormalizedFibersMeet s t ↔ NormalizedFibersMeet t s := by
  simp only [NormalizedFibersMeet, Set.inter_comm]

/-- Coordinate swapping transports a meeting of normalized fibers. -/
theorem normalizedFibersMeet_swap12
    {R : Type u} [CommRing R]
    {axis other : NormalizedCoordinateAxis} {a b : R}
    (h : NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt other b)) :
    NormalizedFibersMeet
      (normalizedFiberAt (normalizedSwap12Axis axis) a)
      (normalizedFiberAt (normalizedSwap12Axis other) b) := by
  rcases h with ⟨x, hx, hy⟩
  exact ⟨normalizedSwap12 x, normalizedSwap12_mem_fiberAt hx,
    normalizedSwap12_mem_fiberAt hy⟩

/-- Swapping the last two coordinates transports a meeting of normalized fibers. -/
theorem normalizedFibersMeet_swap23
    {R : Type u} [CommRing R]
    {axis other : NormalizedCoordinateAxis} {a b : R}
    (h : NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt other b)) :
    NormalizedFibersMeet
      (normalizedFiberAt (normalizedSwap23Axis axis) a)
      (normalizedFiberAt (normalizedSwap23Axis other) b) := by
  rcases h with ⟨x, hx, hy⟩
  exact ⟨normalizedSwap23 x, normalizedSwap23_mem_fiberAt hx,
    normalizedSwap23_mem_fiberAt hy⟩

/-- The intrinsic normalized-coordinate condition for a parabolic trace. -/
def IsNormalizedParabolicCoordinate {R : Type u} [OfNat R 4] [Pow R ℕ]
    (a : R) : Prop :=
  a ^ 2 = 4

/-- The normalized coordinates excluded by the existing admissible-incidence argument. -/
def IsNormalizedExceptionalCoordinate {R : Type u} [OfNat R 0] [OfNat R 4] [Pow R ℕ]
    (a : R) : Prop :=
  a = 0 ∨ IsNormalizedParabolicCoordinate a

/-- Divide a normalized trace coordinate by three without identifying its type with an
original Markoff coordinate. -/
def unscaleNormalizedCoordinate {R : Type u} [CommRing R] [Invertible (3 : R)]
    (u : R) : R :=
  ⅟(3 : R) * u

@[simp]
theorem three_mul_unscaleNormalizedCoordinate
    {R : Type u} [CommRing R] [Invertible (3 : R)] (u : R) :
    3 * unscaleNormalizedCoordinate u = u := by
  simp [unscaleNormalizedCoordinate, ← mul_assoc]

@[simp]
theorem unscaleNormalizedCoordinate_three_mul
    {R : Type u} [CommRing R] [Invertible (3 : R)] (a : R) :
    unscaleNormalizedCoordinate (3 * a) = a := by
  simp [unscaleNormalizedCoordinate, ← mul_assoc]

/-- Original-coordinate admissibility is exactly the complement of the zero and parabolic
normalized trace values. -/
theorem isAdmissibleCoordinate_unscaleNormalizedCoordinate_iff
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (u : ZMod p) :
    IsAdmissibleCoordinate (unscaleNormalizedCoordinate u) ↔
      ¬ IsNormalizedExceptionalCoordinate u := by
  rw [show (¬ IsNormalizedExceptionalCoordinate u) ↔
      u ≠ 0 ∧ ¬ IsNormalizedParabolicCoordinate u by
        simp [IsNormalizedExceptionalCoordinate]]
  simp only [IsAdmissibleCoordinate, IsNormalizedParabolicCoordinate,
    three_mul_unscaleNormalizedCoordinate]
  constructor
  · rintro ⟨hu, hsquare⟩
    refine ⟨?_, hsquare⟩
    intro hzero
    apply hu
    simp [hzero, unscaleNormalizedCoordinate]
  · rintro ⟨hu, hsquare⟩
    refine ⟨?_, hsquare⟩
    intro hzero
    apply hu
    calc
      u = 3 * unscaleNormalizedCoordinate u :=
        (three_mul_unscaleNormalizedCoordinate u).symm
      _ = 0 := by rw [hzero, mul_zero]

/-- Scaling a meeting of an original first-axis and third-axis fiber gives the corresponding
meeting in normalized trace coordinates. -/
theorem normalizedFibersMeet_fiber1_fiber3_of_original
    {R : Type u} [Field R] [Invertible (3 : R)] {a c : R}
    (h : FibersMeet (fiber1 a) (fiber3 c)) :
    NormalizedFibersMeet (normalizedFiber1 (3 * a)) (normalizedFiber3 (3 * c)) := by
  rcases h with ⟨x, hx1, hx3⟩
  have hsurface : IsNormalizedMarkoff (toNormalized x) :=
    (isNormalizedMarkoff_toNormalized_iff x).2 hx1.1
  exact ⟨toNormalized x,
    ⟨hsurface, by simp [toNormalized, hx1.2]⟩,
    ⟨hsurface, by simp [toNormalized, hx3.2]⟩⟩

/-- Scaling a meeting of an original second-axis and third-axis fiber gives the corresponding
meeting in normalized trace coordinates. -/
theorem normalizedFibersMeet_fiber2_fiber3_of_original
    {R : Type u} [Field R] [Invertible (3 : R)] {b c : R}
    (h : FibersMeet (fiber2 b) (fiber3 c)) :
    NormalizedFibersMeet (normalizedFiber2 (3 * b)) (normalizedFiber3 (3 * c)) := by
  rcases h with ⟨x, hx2, hx3⟩
  have hsurface : IsNormalizedMarkoff (toNormalized x) :=
    (isNormalizedMarkoff_toNormalized_iff x).2 hx2.1
  exact ⟨toNormalized x,
    ⟨hsurface, by simp [toNormalized, hx2.2]⟩,
    ⟨hsurface, by simp [toNormalized, hx3.2]⟩⟩

/-- The normalized, type-distinct form of the existing admissible bridge for the first two
axes. -/
def NormalizedAdmissibleBridgeAt (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ u v : ZMod p,
    ¬ IsNormalizedExceptionalCoordinate u →
    ¬ IsNormalizedExceptionalCoordinate v →
      ∃ w : ZMod p,
        ¬ IsNormalizedExceptionalCoordinate w ∧
          NormalizedFibersMeet (normalizedFiber1 u) (normalizedFiber3 w) ∧
          NormalizedFibersMeet (normalizedFiber2 v) (normalizedFiber3 w)

/-- Transport the proved original-coordinate admissible bridge through the explicit scaling
equivalence. -/
theorem normalizedAdmissibleBridgeAt_of_incidenceBridgeAt
    (p : ℕ) (hp : p.Prime) [Invertible (3 : ZMod p)]
    (hbridge : IncidenceBridgeAt p hp) : NormalizedAdmissibleBridgeAt p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  intro u v hu hv
  let a := unscaleNormalizedCoordinate u
  let b := unscaleNormalizedCoordinate v
  have ha : IsAdmissibleCoordinate a :=
    (isAdmissibleCoordinate_unscaleNormalizedCoordinate_iff u).2 hu
  have hb : IsAdmissibleCoordinate b :=
    (isAdmissibleCoordinate_unscaleNormalizedCoordinate_iff v).2 hv
  obtain ⟨c, hc, hac, hbc⟩ := hbridge a b ha hb
  have hw : ¬ IsNormalizedExceptionalCoordinate (3 * c) := by
    apply (isAdmissibleCoordinate_unscaleNormalizedCoordinate_iff (3 * c)).1
    simpa using hc
  refine ⟨3 * c, hw, ?_, ?_⟩
  · simpa [a] using normalizedFibersMeet_fiber1_fiber3_of_original hac
  · simpa [b] using normalizedFibersMeet_fiber2_fiber3_of_original hbc

/-- The normalized admissible bridge for primes congruent to one modulo four. -/
theorem normalizedAdmissibleBridge_mod_one
    (hHasse : ZModLegendrePointCardHasseBound) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → p % 4 = 1 →
      NormalizedAdmissibleBridgeAt p hp := by
  obtain ⟨p0, hbridge⟩ := incidenceBridge_mod_one_admissible hHasse
  refine ⟨p0, ?_⟩
  intro p hp hpLarge hmod
  letI : Fact p.Prime := ⟨hp⟩
  have hpThree : 3 < p := by
    by_contra h
    have hpLe : p ≤ 3 := by omega
    have hpTwo : 2 ≤ p := hp.two_le
    have hpCases : p = 2 ∨ p = 3 := by omega
    rcases hpCases with rfl | rfl <;> norm_num at hmod
  letI : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) hpThree)
  exact normalizedAdmissibleBridgeAt_of_incidenceBridgeAt p hp
    (hbridge p hp hpLarge hmod)

/-- The graph-level admissible bridge, with coordinate permutations made explicit. -/
def NormalizedAdmissibleGraphBridgeAt (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ (axis other : NormalizedCoordinateAxis) (u v : ZMod p),
    ¬ IsNormalizedExceptionalCoordinate u →
    ¬ IsNormalizedExceptionalCoordinate v →
      ∃ middle : NormalizedCoordinateAxis, ∃ w : ZMod p,
        middle ≠ axis ∧ middle ≠ other ∧
          NormalizedFibersMeet (normalizedFiberAt axis u) (normalizedFiberAt middle w) ∧
          NormalizedFibersMeet (normalizedFiberAt other v) (normalizedFiberAt middle w)

/-- The fixed-axis admissible bridge implies the full graph-level bridge.  Every coordinate
permutation is applied to the actual intersection witness. -/
theorem normalizedAdmissibleGraphBridgeAt_of_fixedAxes
    {p : ℕ} {hp : p.Prime}
    (hbridge : NormalizedAdmissibleBridgeAt p hp) :
    NormalizedAdmissibleGraphBridgeAt p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  intro axis other u v hu hv
  rcases axis with _ | _ | _ <;> rcases other with _ | _ | _
  · obtain ⟨w, hw, h13, h23⟩ := hbridge u v hu hv
    refine ⟨.third, w, by decide, by decide, h13, ?_⟩
    simpa [normalizedSwap12Axis] using
      normalizedFibersMeet_swap12 (axis := .second) (other := .third) h23
  · obtain ⟨w, hw, h13, h23⟩ := hbridge u v hu hv
    exact ⟨.third, w, by decide, by decide, h13, h23⟩
  · obtain ⟨w, hw, h13, h23⟩ := hbridge u v hu hv
    refine ⟨.second, w, by decide, by decide, ?_, ?_⟩
    · simpa [normalizedSwap23Axis] using
        normalizedFibersMeet_swap23 (axis := .first) (other := .third) h13
    · simpa [normalizedSwap23Axis] using
        normalizedFibersMeet_swap23 (axis := .second) (other := .third) h23
  · obtain ⟨w, hw, h13, h23⟩ := hbridge v u hv hu
    exact ⟨.third, w, by decide, by decide, h23, h13⟩
  · obtain ⟨w, hw, h13, h23⟩ := hbridge u v hu hv
    refine ⟨.third, w, by decide, by decide, ?_, h23⟩
    simpa [normalizedSwap12Axis] using
      normalizedFibersMeet_swap12 (axis := .first) (other := .third) h13
  · obtain ⟨w, hw, h13, h23⟩ := hbridge u v hu hv
    refine ⟨.first, w, by decide, by decide, ?_, ?_⟩
    · simpa [normalizedSwap12Axis, normalizedSwap23Axis] using
        normalizedFibersMeet_swap12 (axis := .first) (other := .second)
          (normalizedFibersMeet_swap23 (axis := .first) (other := .third) h13)
    · simpa [normalizedSwap12Axis, normalizedSwap23Axis] using
        normalizedFibersMeet_swap12 (axis := .third) (other := .second)
          (normalizedFibersMeet_swap23 (axis := .second) (other := .third) h23)
  · obtain ⟨w, hw, h13, h23⟩ := hbridge v u hv hu
    refine ⟨.second, w, by decide, by decide, ?_, ?_⟩
    · simpa [normalizedSwap23Axis] using
        normalizedFibersMeet_swap23 (axis := .second) (other := .third) h23
    · simpa [normalizedSwap23Axis] using
        normalizedFibersMeet_swap23 (axis := .first) (other := .third) h13
  · obtain ⟨w, hw, h13, h23⟩ := hbridge v u hv hu
    refine ⟨.first, w, by decide, by decide, ?_, ?_⟩
    · simpa [normalizedSwap12Axis, normalizedSwap23Axis] using
        normalizedFibersMeet_swap12 (axis := .third) (other := .second)
          (normalizedFibersMeet_swap23 (axis := .second) (other := .third) h23)
    · simpa [normalizedSwap12Axis, normalizedSwap23Axis] using
        normalizedFibersMeet_swap12 (axis := .first) (other := .second)
          (normalizedFibersMeet_swap23 (axis := .first) (other := .third) h13)
  · obtain ⟨w, hw, h13, h23⟩ := hbridge u v hu hv
    refine ⟨.first, w, by decide, by decide, ?_, ?_⟩
    · simpa [normalizedSwap12Axis, normalizedSwap23Axis] using
        normalizedFibersMeet_swap12 (axis := .third) (other := .second)
          (normalizedFibersMeet_swap23 (axis := .second) (other := .third)
            (normalizedFibersMeet_swap12 (axis := .first) (other := .third) h13))
    · simpa [normalizedSwap12Axis, normalizedSwap23Axis] using
        normalizedFibersMeet_swap12 (axis := .third) (other := .second)
          (normalizedFibersMeet_swap23 (axis := .second) (other := .third) h23)

/-- The graph-level admissible bridge for all sufficiently large primes congruent to one modulo
four. -/
theorem normalizedAdmissibleGraphBridge_mod_one
    (hHasse : ZModLegendrePointCardHasseBound) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → p % 4 = 1 →
      NormalizedAdmissibleGraphBridgeAt p hp := by
  obtain ⟨p0, hbridge⟩ := normalizedAdmissibleBridge_mod_one hHasse
  exact ⟨p0, fun p hp hpLarge hmod =>
    normalizedAdmissibleGraphBridgeAt_of_fixedAxes (hbridge p hp hpLarge hmod)⟩

private theorem parabolic_eq_two_or_neg_two
    {R : Type u} [CommRing R] [NoZeroDivisors R] {a : R}
    (ha : IsNormalizedParabolicCoordinate a) : a = 2 ∨ a = -2 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  calc
    a ^ 2 = 4 := ha
    _ = (2 : R) ^ 2 := by norm_num

/-- The trace-`2` fiber on the first axis meets every second-axis fiber. -/
theorem normalizedFiber1_two_meets_fiber2
    {R : Type u} [CommRing R] [NoZeroDivisors R] (i b : R) (hi : i ^ 2 = -1) :
    NormalizedFibersMeet (normalizedFiber1 (2 : R)) (normalizedFiber2 b) := by
  let x := parabolicLineAtTwo i b
  have hx : IsNormalizedMarkoff x := by
    change IsNormalizedMarkoff (⟨2, b, b + 2 * i⟩ : NormalizedPoint R)
    rw [isNormalizedMarkoff_at_two_iff_on_parabolic_lines hi]
    exact Or.inl rfl
  exact ⟨x, ⟨hx, rfl⟩, ⟨hx, rfl⟩⟩

/-- The trace-`-2` fiber on the first axis meets every second-axis fiber. -/
theorem normalizedFiber1_neg_two_meets_fiber2
    {R : Type u} [CommRing R] [NoZeroDivisors R] (i b : R) (hi : i ^ 2 = -1) :
    NormalizedFibersMeet (normalizedFiber1 (-2 : R)) (normalizedFiber2 b) := by
  let x := parabolicLineAtNegTwo i b
  have hx : IsNormalizedMarkoff x := by
    change IsNormalizedMarkoff (⟨-2, b, -b + 2 * i⟩ : NormalizedPoint R)
    rw [isNormalizedMarkoff_at_neg_two_iff_on_parabolic_lines hi]
    exact Or.inl rfl
  exact ⟨x, ⟨hx, rfl⟩, ⟨hx, rfl⟩⟩

/-- A parabolic first-axis fiber meets every second-axis fiber. -/
theorem normalizedFiber1_parabolic_meets_fiber2
    {R : Type u} [CommRing R] [NoZeroDivisors R]
    (i : R) (hi : i ^ 2 = -1) {a : R} (ha : IsNormalizedParabolicCoordinate a)
    (b : R) :
    NormalizedFibersMeet (normalizedFiber1 a) (normalizedFiber2 b) := by
  rcases parabolic_eq_two_or_neg_two ha with rfl | rfl
  · exact normalizedFiber1_two_meets_fiber2 i b hi
  · exact normalizedFiber1_neg_two_meets_fiber2 i b hi

/-- The trace-`2` fiber on the first axis meets every third-axis fiber. -/
theorem normalizedFiber1_two_meets_fiber3
    {R : Type u} [CommRing R] [NoZeroDivisors R] (i c : R) (hi : i ^ 2 = -1) :
    NormalizedFibersMeet (normalizedFiber1 (2 : R)) (normalizedFiber3 c) := by
  let x := parabolicLineAtTwo i (c - 2 * i)
  have hx : IsNormalizedMarkoff x := by
    change IsNormalizedMarkoff
      (⟨2, c - 2 * i, (c - 2 * i) + 2 * i⟩ : NormalizedPoint R)
    rw [isNormalizedMarkoff_at_two_iff_on_parabolic_lines hi]
    exact Or.inl rfl
  refine ⟨x, ⟨hx, rfl⟩, hx, ?_⟩
  simp [x, parabolicLineAtTwo]

/-- The trace-`-2` fiber on the first axis meets every third-axis fiber. -/
theorem normalizedFiber1_neg_two_meets_fiber3
    {R : Type u} [CommRing R] [NoZeroDivisors R] (i c : R) (hi : i ^ 2 = -1) :
    NormalizedFibersMeet (normalizedFiber1 (-2 : R)) (normalizedFiber3 c) := by
  let x := parabolicLineAtNegTwo i (2 * i - c)
  have hx : IsNormalizedMarkoff x := by
    change IsNormalizedMarkoff
      (⟨-2, 2 * i - c, -(2 * i - c) + 2 * i⟩ : NormalizedPoint R)
    rw [isNormalizedMarkoff_at_neg_two_iff_on_parabolic_lines hi]
    exact Or.inl rfl
  refine ⟨x, ⟨hx, rfl⟩, hx, ?_⟩
  simp [x, parabolicLineAtNegTwo]

/-- A parabolic first-axis fiber meets every third-axis fiber. -/
theorem normalizedFiber1_parabolic_meets_fiber3
    {R : Type u} [CommRing R] [NoZeroDivisors R]
    (i : R) (hi : i ^ 2 = -1) {a : R} (ha : IsNormalizedParabolicCoordinate a)
    (c : R) :
    NormalizedFibersMeet (normalizedFiber1 a) (normalizedFiber3 c) := by
  rcases parabolic_eq_two_or_neg_two ha with rfl | rfl
  · exact normalizedFiber1_two_meets_fiber3 i c hi
  · exact normalizedFiber1_neg_two_meets_fiber3 i c hi

/-- When `i² = -1`, the zero fiber on the first axis meets every second-axis fiber. -/
theorem normalizedFiber1_zero_meets_fiber2
    {R : Type u} [CommRing R] (i b : R) (hi : i ^ 2 = -1) :
    NormalizedFibersMeet (normalizedFiber1 (0 : R)) (normalizedFiber2 b) := by
  let x : NormalizedPoint R := ⟨0, b, i * b⟩
  have hx : IsNormalizedMarkoff x := by
    simp only [IsNormalizedMarkoff, normalizedPolynomial, x]
    rw [mul_pow, hi]
    ring
  exact ⟨x, ⟨hx, rfl⟩, ⟨hx, rfl⟩⟩

/-- When `i² = -1`, the zero fiber on the first axis meets every third-axis fiber. -/
theorem normalizedFiber1_zero_meets_fiber3
    {R : Type u} [CommRing R] (i c : R) (hi : i ^ 2 = -1) :
    NormalizedFibersMeet (normalizedFiber1 (0 : R)) (normalizedFiber3 c) := by
  let x : NormalizedPoint R := ⟨0, i * c, c⟩
  have hx : IsNormalizedMarkoff x := by
    simp only [IsNormalizedMarkoff, normalizedPolynomial, x]
    rw [mul_pow, hi]
    ring
  exact ⟨x, ⟨hx, rfl⟩, ⟨hx, rfl⟩⟩

/-- A parabolic fiber on any axis meets every fiber on a different axis. -/
theorem normalizedParabolicFiber_meets_distinctAxis
    {R : Type u} [CommRing R] [NoZeroDivisors R]
    (i : R) (hi : i ^ 2 = -1)
    {axis other : NormalizedCoordinateAxis} (haxis : axis ≠ other)
    {a : R} (ha : IsNormalizedParabolicCoordinate a) (b : R) :
    NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt other b) := by
  rcases axis with _ | _ | _ <;> rcases other with _ | _ | _
  · exact (haxis rfl).elim
  · exact normalizedFiber1_parabolic_meets_fiber2 i hi ha b
  · exact normalizedFiber1_parabolic_meets_fiber3 i hi ha b
  · -- Swap the first two coordinates in a first/second-axis witness.
    rcases normalizedFiber1_parabolic_meets_fiber2 i hi ha b with ⟨x, hx1, hx2⟩
    let y := normalizedSwap12 x
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 x) = 0
      rw [normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx2.2⟩⟩
  · exact (haxis rfl).elim
  · -- Swap the first two coordinates in the preceding first/third-axis witness.
    rcases normalizedFiber1_parabolic_meets_fiber3 i hi ha b with ⟨x, hx1, hx3⟩
    let y := normalizedSwap12 x
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 x) = 0
      rw [normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx3.2⟩⟩
  · -- Swap the first and third coordinates in a first/third-axis witness.
    rcases normalizedFiber1_parabolic_meets_fiber3 i hi ha b with ⟨x, hx1, hx3⟩
    let y := normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))) = 0
      rw [normalizedPolynomial_swap12, normalizedPolynomial_swap23,
        normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx3.2⟩⟩
  · -- Swap the first and third coordinates in a first/second-axis witness.
    rcases normalizedFiber1_parabolic_meets_fiber2 i hi ha b with ⟨x, hx1, hx2⟩
    let y := normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))) = 0
      rw [normalizedPolynomial_swap12, normalizedPolynomial_swap23,
        normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx2.2⟩⟩
  · exact (haxis rfl).elim

/-- A zero-coordinate fiber meets every fiber on a different axis when `-1` is a square. -/
theorem normalizedZeroFiber_meets_distinctAxis
    {R : Type u} [CommRing R]
    (i : R) (hi : i ^ 2 = -1)
    {axis other : NormalizedCoordinateAxis} (haxis : axis ≠ other) (b : R) :
    NormalizedFibersMeet (normalizedFiberAt axis 0) (normalizedFiberAt other b) := by
  rcases axis with _ | _ | _ <;> rcases other with _ | _ | _
  · exact (haxis rfl).elim
  · exact normalizedFiber1_zero_meets_fiber2 i b hi
  · exact normalizedFiber1_zero_meets_fiber3 i b hi
  · rcases normalizedFiber1_zero_meets_fiber2 i b hi with ⟨x, hx1, hx2⟩
    let y := normalizedSwap12 x
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 x) = 0
      rw [normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx2.2⟩⟩
  · exact (haxis rfl).elim
  · rcases normalizedFiber1_zero_meets_fiber3 i b hi with ⟨x, hx1, hx3⟩
    let y := normalizedSwap12 x
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 x) = 0
      rw [normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx3.2⟩⟩
  · rcases normalizedFiber1_zero_meets_fiber3 i b hi with ⟨x, hx1, hx3⟩
    let y := normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))) = 0
      rw [normalizedPolynomial_swap12, normalizedPolynomial_swap23,
        normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx3.2⟩⟩
  · rcases normalizedFiber1_zero_meets_fiber2 i b hi with ⟨x, hx1, hx2⟩
    let y := normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))
    have hy : IsNormalizedMarkoff y := by
      change normalizedPolynomial (normalizedSwap12 (normalizedSwap23 (normalizedSwap12 x))) = 0
      rw [normalizedPolynomial_swap12, normalizedPolynomial_swap23,
        normalizedPolynomial_swap12]
      exact hx1.1
    exact ⟨y, ⟨hy, hx1.2⟩, ⟨hy, hx2.2⟩⟩
  · exact (haxis rfl).elim

/-- Every coordinate excluded by admissibility meets every fiber on a different axis when
`-1` is a square. -/
theorem normalizedExceptionalFiber_meets_distinctAxis
    {R : Type u} [CommRing R] [NoZeroDivisors R]
    (i : R) (hi : i ^ 2 = -1)
    {axis other : NormalizedCoordinateAxis} (haxis : axis ≠ other)
    {a : R} (ha : IsNormalizedExceptionalCoordinate a) (b : R) :
    NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt other b) := by
  rcases ha with rfl | ha
  · exact normalizedZeroFiber_meets_distinctAxis i hi haxis b
  · exact normalizedParabolicFiber_meets_distinctAxis i hi haxis ha b

/-- If one vertex is parabolic and the other vertex is on the same axis, any point of the
other fiber supplies a common neighbor on either different axis. -/
theorem normalizedParabolicFiber_commonNeighbor_sameAxis
    {R : Type u} [CommRing R] [NoZeroDivisors R]
    (i : R) (hi : i ^ 2 = -1) (axis other : NormalizedCoordinateAxis)
    (haxis : axis ≠ other) {a b : R} (ha : IsNormalizedParabolicCoordinate a)
    (hb : (normalizedFiberAt axis b).Nonempty) :
    ∃ c : R,
      NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt other c) ∧
        NormalizedFibersMeet (normalizedFiberAt axis b) (normalizedFiberAt other c) := by
  rcases hb with ⟨x, hx⟩
  rcases axis with _ | _ | _ <;> rcases other with _ | _ | _
  · exact (haxis rfl).elim
  · refine ⟨x.u2, normalizedParabolicFiber_meets_distinctAxis i hi haxis ha x.u2, ?_⟩
    exact ⟨x, hx, ⟨hx.1, rfl⟩⟩
  · refine ⟨x.u3, normalizedParabolicFiber_meets_distinctAxis i hi haxis ha x.u3, ?_⟩
    exact ⟨x, hx, ⟨hx.1, rfl⟩⟩
  · refine ⟨x.u1, normalizedParabolicFiber_meets_distinctAxis i hi haxis ha x.u1, ?_⟩
    exact ⟨x, hx, ⟨hx.1, rfl⟩⟩
  · exact (haxis rfl).elim
  · refine ⟨x.u3, normalizedParabolicFiber_meets_distinctAxis i hi haxis ha x.u3, ?_⟩
    exact ⟨x, hx, ⟨hx.1, rfl⟩⟩
  · refine ⟨x.u1, normalizedParabolicFiber_meets_distinctAxis i hi haxis ha x.u1, ?_⟩
    exact ⟨x, hx, ⟨hx.1, rfl⟩⟩
  · refine ⟨x.u2, normalizedParabolicFiber_meets_distinctAxis i hi haxis ha x.u2, ?_⟩
    exact ⟨x, hx, ⟨hx.1, rfl⟩⟩
  · exact (haxis rfl).elim

/-- A deterministic choice of an axis different from each of two supplied axes. -/
def normalizedBridgeAxis :
    NormalizedCoordinateAxis → NormalizedCoordinateAxis → NormalizedCoordinateAxis
  | .first, .first => .second
  | .first, .second => .third
  | .first, .third => .second
  | .second, .first => .third
  | .second, .second => .first
  | .second, .third => .first
  | .third, .first => .second
  | .third, .second => .first
  | .third, .third => .first

theorem normalizedBridgeAxis_ne_left (axis other : NormalizedCoordinateAxis) :
    normalizedBridgeAxis axis other ≠ axis := by
  cases axis <;> cases other <;> decide

theorem normalizedBridgeAxis_ne_right (axis other : NormalizedCoordinateAxis) :
    normalizedBridgeAxis axis other ≠ other := by
  cases axis <;> cases other <;> decide

/-- A nonempty fiber meets some fiber on every different axis: use the corresponding
coordinate of a point already in the first fiber. -/
theorem normalizedFiber_meets_some_fiber_on_distinctAxis
    {R : Type u} [CommRing R]
    {axis other : NormalizedCoordinateAxis} (haxis : axis ≠ other) {b : R}
    (hb : (normalizedFiberAt axis b).Nonempty) :
    ∃ c : R, NormalizedFibersMeet (normalizedFiberAt axis b) (normalizedFiberAt other c) := by
  rcases hb with ⟨x, hx⟩
  rcases axis with _ | _ | _ <;> rcases other with _ | _ | _
  · exact (haxis rfl).elim
  · exact ⟨x.u2, x, hx, ⟨hx.1, rfl⟩⟩
  · exact ⟨x.u3, x, hx, ⟨hx.1, rfl⟩⟩
  · exact ⟨x.u1, x, hx, ⟨hx.1, rfl⟩⟩
  · exact (haxis rfl).elim
  · exact ⟨x.u3, x, hx, ⟨hx.1, rfl⟩⟩
  · exact ⟨x.u1, x, hx, ⟨hx.1, rfl⟩⟩
  · exact ⟨x.u2, x, hx, ⟨hx.1, rfl⟩⟩
  · exact (haxis rfl).elim

/-- The complete parabolic bridge suppressed by the published proof.

For a parabolic vertex on `axis` and any nonempty vertex on `other`, this produces a common
neighbor on an axis different from both.  Thus all interactions involving a parabolic vertex
have graph distance at most two; no admissibility hypothesis is imposed on the other vertex. -/
theorem normalizedParabolicFiber_has_commonNeighbor
    {R : Type u} [CommRing R] [NoZeroDivisors R]
    (i : R) (hi : i ^ 2 = -1)
    (axis other : NormalizedCoordinateAxis) {a b : R}
    (ha : IsNormalizedParabolicCoordinate a)
    (hb : (normalizedFiberAt other b).Nonempty) :
    ∃ middle : NormalizedCoordinateAxis, ∃ c : R,
      middle ≠ axis ∧ middle ≠ other ∧
        NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt middle c) ∧
        NormalizedFibersMeet (normalizedFiberAt other b) (normalizedFiberAt middle c) := by
  let middle := normalizedBridgeAxis axis other
  have hleft : middle ≠ axis := normalizedBridgeAxis_ne_left axis other
  have hright : middle ≠ other := normalizedBridgeAxis_ne_right axis other
  obtain ⟨c, hc⟩ := normalizedFiber_meets_some_fiber_on_distinctAxis hright.symm hb
  exact ⟨middle, c, hleft, hright,
    normalizedParabolicFiber_meets_distinctAxis i hi hleft.symm ha c, hc⟩

/-- The same graph-level bridge for every coordinate omitted by the admissible argument,
including the zero-coordinate lines that also occur when `-1` is a square. -/
theorem normalizedExceptionalFiber_has_commonNeighbor
    {R : Type u} [CommRing R] [NoZeroDivisors R]
    (i : R) (hi : i ^ 2 = -1)
    (axis other : NormalizedCoordinateAxis) {a b : R}
    (ha : IsNormalizedExceptionalCoordinate a)
    (hb : (normalizedFiberAt other b).Nonempty) :
    ∃ middle : NormalizedCoordinateAxis, ∃ c : R,
      middle ≠ axis ∧ middle ≠ other ∧
        NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt middle c) ∧
        NormalizedFibersMeet (normalizedFiberAt other b) (normalizedFiberAt middle c) := by
  let middle := normalizedBridgeAxis axis other
  have hleft : middle ≠ axis := normalizedBridgeAxis_ne_left axis other
  have hright : middle ≠ other := normalizedBridgeAxis_ne_right axis other
  obtain ⟨c, hc⟩ := normalizedFiber_meets_some_fiber_on_distinctAxis hright.symm hb
  exact ⟨middle, c, hleft, hright,
    normalizedExceptionalFiber_meets_distinctAxis i hi hleft.symm ha c, hc⟩

/-- For primes congruent to one modulo four, every parabolic incidence vertex has a common
neighbor with every nonempty incidence vertex, uniformly over all coordinate axes. -/
theorem normalizedParabolicIncidenceBridge_mod_one
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) :
    ∀ (axis other : NormalizedCoordinateAxis) {a b : ZMod p},
      IsNormalizedParabolicCoordinate a →
      (normalizedFiberAt other b).Nonempty →
      ∃ middle : NormalizedCoordinateAxis, ∃ c : ZMod p,
        middle ≠ axis ∧ middle ≠ other ∧
          NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt middle c) ∧
          NormalizedFibersMeet (normalizedFiberAt other b) (normalizedFiberAt middle c) := by
  obtain ⟨i, hi, _, _⟩ := exists_parabolic_line_decomposition_of_mod_four_eq_one p hmod
  intro axis other a b ha hb
  exact normalizedParabolicFiber_has_commonNeighbor i hi axis other ha hb

/-- At primes congruent to one modulo four, the zero and parabolic fibers omitted by the
admissible incidence argument all have distance at most two from every nonempty fiber. -/
theorem normalizedExceptionalIncidenceBridge_mod_one
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) :
    ∀ (axis other : NormalizedCoordinateAxis) {a b : ZMod p},
      IsNormalizedExceptionalCoordinate a →
      (normalizedFiberAt other b).Nonempty →
      ∃ middle : NormalizedCoordinateAxis, ∃ c : ZMod p,
        middle ≠ axis ∧ middle ≠ other ∧
          NormalizedFibersMeet (normalizedFiberAt axis a) (normalizedFiberAt middle c) ∧
          NormalizedFibersMeet (normalizedFiberAt other b) (normalizedFiberAt middle c) := by
  obtain ⟨i, hi, _, _⟩ := exists_parabolic_line_decomposition_of_mod_four_eq_one p hmod
  intro axis other a b ha hb
  exact normalizedExceptionalFiber_has_commonNeighbor i hi axis other ha hb

/-- A full-surface fiber bridge.  This does not yet remove the normalized origin from
intersection witnesses, so it is intentionally not called the punctured incidence graph. -/
def NormalizedFullSurfaceFiberBridgeAt (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ (axis other : NormalizedCoordinateAxis) (u v : ZMod p),
    (normalizedFiberAt axis u).Nonempty →
    (normalizedFiberAt other v).Nonempty →
      ∃ middle : NormalizedCoordinateAxis, ∃ w : ZMod p,
        middle ≠ axis ∧ middle ≠ other ∧
          NormalizedFibersMeet (normalizedFiberAt axis u) (normalizedFiberAt middle w) ∧
          NormalizedFibersMeet (normalizedFiberAt other v) (normalizedFiberAt middle w)

/-- The complete incidence bridge for sufficiently large primes congruent to one modulo four.
The proof combines the transported admissible bridge with the separately proved zero and
parabolic line geometry. -/
theorem normalizedFullSurfaceFiberBridge_mod_one
    (hHasse : ZModLegendrePointCardHasseBound) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → p % 4 = 1 →
      NormalizedFullSurfaceFiberBridgeAt p hp := by
  obtain ⟨p0, hadmissible⟩ := normalizedAdmissibleGraphBridge_mod_one hHasse
  refine ⟨p0, ?_⟩
  intro p hp hpLarge hmod
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, _, _⟩ := exists_parabolic_line_decomposition_of_mod_four_eq_one p hmod
  have hgood := hadmissible p hp hpLarge hmod
  intro axis other u v huNonempty hvNonempty
  by_cases hu : IsNormalizedExceptionalCoordinate u
  · exact normalizedExceptionalFiber_has_commonNeighbor i hi axis other hu hvNonempty
  · by_cases hv : IsNormalizedExceptionalCoordinate v
    · obtain ⟨middle, w, hmiddleOther, hmiddleAxis, hvMeet, huMeet⟩ :=
        normalizedExceptionalFiber_has_commonNeighbor i hi other axis hv huNonempty
      exact ⟨middle, w, hmiddleAxis, hmiddleOther, huMeet, hvMeet⟩
    · exact hgood axis other u v hu hv

end BGS.Markoff
