/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Scalar translations of the numerical radius

On a nontrivial Hilbert space, scalar operators have their expected
numerical radius.  Consequently scalar translation changes numerical radius
by at most the modulus of the scalar, and centered numerical radii are
Lipschitz in the center.
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import LeanPool.OperatorTheory.Operator.NumericalRange.Affine
import LeanPool.OperatorTheory.Operator.NumericalRange.RadiusAdjoint

open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]

/-- The identity operator has numerical radius one. -/
@[simp] theorem numericalRadius_one :
    numericalRadius (1 : E →L[ℂ] E) = 1 := by
  apply le_antisymm
  · simpa only [norm_one] using
      numericalRadius_le_norm (1 : E →L[ℂ] E)
  · have hmem : (1 : ℂ) ∈ numericalRange (1 : E →L[ℂ] E) := by
      rw [show (1 : E →L[ℂ] E) = (1 : ℂ) • 1 by simp,
        numericalRange_scalar]
      exact Set.mem_singleton 1
    simpa only [norm_one] using
      norm_le_numericalRadius (1 : E →L[ℂ] E) hmem

/-- A scalar operator has numerical radius equal to the scalar modulus. -/
@[simp] theorem numericalRadius_smul_one (c : ℂ) :
    numericalRadius (c • (1 : E →L[ℂ] E)) = ‖c‖ := by
  rw [numericalRadius_smul, numericalRadius_one, mul_one]

/-- Adding a scalar operator changes numerical radius by at most the scalar
modulus. -/
theorem abs_numericalRadius_add_smul_one_sub_le
    (A : E →L[ℂ] E) (c : ℂ) :
    |numericalRadius (A + c • 1) - numericalRadius A| ≤ ‖c‖ := by
  have h := abs_numericalRadius_sub_le_norm (A + c • 1) A
  simpa only [add_sub_cancel_left, norm_smul, norm_one, mul_one] using h

/-- Subtracting a scalar operator changes numerical radius by at most the
scalar modulus. -/
theorem abs_numericalRadius_sub_smul_one_sub_le
    (A : E →L[ℂ] E) (c : ℂ) :
    |numericalRadius (A - c • 1) - numericalRadius A| ≤ ‖c‖ := by
  simpa only [sub_eq_add_neg, neg_smul, norm_neg] using
    abs_numericalRadius_add_smul_one_sub_le A (-c)

/-- The centered numerical radius differs from the modulus of its center by
at most `w(A)`. -/
theorem abs_numericalRadius_sub_smul_one_sub_norm_le_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    |numericalRadius (A - c • 1) - ‖c‖| ≤ numericalRadius A := by
  rw [abs_le]
  constructor
  · have h := numericalRadius_sub_le A (A - c • 1)
    have hop : A - (A - c • 1) = c • 1 := by module
    rw [hop, numericalRadius_smul_one] at h
    linarith
  · have h := numericalRadius_sub_le A (c • 1)
    rw [numericalRadius_smul_one] at h
    linarith

/-- In particular, the centered numerical radius grows at least linearly in
the modulus of the center. -/
theorem norm_sub_numericalRadius_le_numericalRadius_sub_smul_one
    (A : E →L[ℂ] E) (c : ℂ) :
    ‖c‖ - numericalRadius A ≤ numericalRadius (A - c • 1) := by
  have h :=
    abs_numericalRadius_sub_smul_one_sub_norm_le_numericalRadius A c
  rw [abs_le] at h
  linarith

/-- Centering at two scalars changes numerical radius by at most the distance
between the centers. -/
theorem abs_numericalRadius_sub_smul_one_sub_numericalRadius_sub_smul_one_le
    (A : E →L[ℂ] E) (c d : ℂ) :
    |numericalRadius (A - c • 1) - numericalRadius (A - d • 1)| ≤ ‖c - d‖ := by
  have h := abs_numericalRadius_sub_le_norm (A - c • 1) (A - d • 1)
  have hop : (A - c • 1) - (A - d • 1) = (d - c) • 1 := by
    module
  rw [hop, norm_smul, norm_one, mul_one, norm_sub_rev] at h
  exact h

/-- The numerical radius of `A - cI` is `1`-Lipschitz as a function of the
center `c`. -/
theorem lipschitzWith_numericalRadius_sub_smul_one (A : E →L[ℂ] E) :
    LipschitzWith 1 (fun c : ℂ => numericalRadius (A - c • 1)) := by
  apply LipschitzWith.mk_one
  intro c d
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
    abs_numericalRadius_sub_smul_one_sub_numericalRadius_sub_smul_one_le A c d

/-- The centered numerical radius depends continuously on the center. -/
theorem continuous_numericalRadius_sub_smul_one (A : E →L[ℂ] E) :
    Continuous (fun c : ℂ => numericalRadius (A - c • 1)) :=
  (lipschitzWith_numericalRadius_sub_smul_one A).continuous

omit [Nontrivial E] in
/-- The numerical radius of the scalar translate `A-cI` is convex as a
function of the center `c`. -/
theorem convexOn_numericalRadius_sub_smul_one (A : E →L[ℂ] E) :
    ConvexOn ℝ Set.univ (fun c : ℂ => numericalRadius (A - c • 1)) := by
  refine ⟨convex_univ, fun c _ d _ a b ha hb hab => ?_⟩
  have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  have hop :
      A - (a • c + b • d) • 1 =
        (a : ℂ) • (A - c • 1) + (b : ℂ) • (A - d • 1) := by
    calc
      A - (a • c + b • d) • 1 =
          ((a : ℂ) + (b : ℂ)) • A - (a • c + b • d) • 1 := by
        rw [habC, one_smul]
      _ = (a : ℂ) • (A - c • 1) + (b : ℂ) • (A - d • 1) := by
        simp only [Complex.real_smul]
        module
  change numericalRadius (A - (a • c + b • d) • 1) ≤
    a * numericalRadius (A - c • 1) +
      b * numericalRadius (A - d • 1)
  rw [hop]
  calc
    numericalRadius
        ((a : ℂ) • (A - c • 1) + (b : ℂ) • (A - d • 1)) ≤
        numericalRadius ((a : ℂ) • (A - c • 1)) +
          numericalRadius ((b : ℂ) • (A - d • 1)) :=
      numericalRadius_add_le _ _
    _ = a * numericalRadius (A - c • 1) +
        b * numericalRadius (A - d • 1) := by
      rw [numericalRadius_smul, numericalRadius_smul, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

omit [Nontrivial E] in
/-- Every sublevel set of the centered numerical radius is convex. -/
theorem convex_setOf_numericalRadius_sub_smul_one_le
    (A : E →L[ℂ] E) (r : ℝ) :
    Convex ℝ {c : ℂ | numericalRadius (A - c • 1) ≤ r} := by
  simpa only [Set.mem_univ, true_and] using
    (convexOn_numericalRadius_sub_smul_one A).convex_le r

/-- Every sublevel set of the centered numerical radius is compact. -/
theorem isCompact_setOf_numericalRadius_sub_smul_one_le
    (A : E →L[ℂ] E) (r : ℝ) :
    IsCompact {c : ℂ | numericalRadius (A - c • 1) ≤ r} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact isClosed_le (continuous_numericalRadius_sub_smul_one A)
      continuous_const
  · apply (Metric.isBounded_closedBall :
      Bornology.IsBounded
        (Metric.closedBall (0 : ℂ) (r + numericalRadius A))).subset
    intro c hc
    rw [Metric.mem_closedBall, dist_zero_right]
    change numericalRadius (A - c • 1) ≤ r at hc
    have hcoercive :=
      norm_sub_numericalRadius_le_numericalRadius_sub_smul_one A c
    linarith

/-- The centered numerical radius tends to infinity as the center leaves
compact subsets of the complex plane. -/
theorem tendsto_numericalRadius_sub_smul_one_cocompact_atTop
    (A : E →L[ℂ] E) :
    Tendsto (fun c : ℂ => numericalRadius (A - c • 1))
      (cocompact ℂ) atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards
      [tendsto_norm_cocompact_atTop.eventually
        (eventually_ge_atTop (b + numericalRadius A))] with c hc
  exact le_trans (by linarith)
    (norm_sub_numericalRadius_le_numericalRadius_sub_smul_one A c)

/-- There is a center minimizing the numerical radius of the scalar
translate `A-cI`. -/
theorem exists_center_minimizing_numericalRadius (A : E →L[ℂ] E) :
    ∃ c : ℂ, ∀ d : ℂ,
      numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1) :=
  (continuous_numericalRadius_sub_smul_one A).exists_forall_le
    (tendsto_numericalRadius_sub_smul_one_cocompact_atTop A)

omit [Nontrivial E] in
/-- The set of scalar centers that globally minimize `w(A-cI)`. -/
def centeredNumericalRadiusMinimizers (A : E →L[ℂ] E) : Set ℂ :=
  {c | ∀ d : ℂ,
    numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)}

omit [Nontrivial E] in
/-- Once a minimizing center is fixed, the full minimizer set is its
centered-radius sublevel set. -/
theorem centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer
    (A : E →L[ℂ] E) {c : ℂ}
    (hc : ∀ d : ℂ,
      numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)) :
    centeredNumericalRadiusMinimizers A =
      {d : ℂ |
        numericalRadius (A - d • 1) ≤ numericalRadius (A - c • 1)} := by
  ext d
  simp only [centeredNumericalRadiusMinimizers, Set.mem_ofPred_eq]
  constructor
  · exact fun hd => hd c
  · exact fun hd e => hd.trans (hc e)

/-- The set of globally minimizing scalar centers is nonempty. -/
theorem centeredNumericalRadiusMinimizers_nonempty (A : E →L[ℂ] E) :
    (centeredNumericalRadiusMinimizers A).Nonempty := by
  obtain ⟨c, hc⟩ := exists_center_minimizing_numericalRadius A
  exact ⟨c, hc⟩

/-- The set of globally minimizing scalar centers is compact. -/
theorem isCompact_centeredNumericalRadiusMinimizers (A : E →L[ℂ] E) :
    IsCompact (centeredNumericalRadiusMinimizers A) := by
  obtain ⟨c, hc⟩ := exists_center_minimizing_numericalRadius A
  rw [centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer A hc]
  exact isCompact_setOf_numericalRadius_sub_smul_one_le A
    (numericalRadius (A - c • 1))

/-- The set of globally minimizing scalar centers is convex. -/
theorem convex_centeredNumericalRadiusMinimizers (A : E →L[ℂ] E) :
    Convex ℝ (centeredNumericalRadiusMinimizers A) := by
  obtain ⟨c, hc⟩ := exists_center_minimizing_numericalRadius A
  rw [centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer A hc]
  exact convex_setOf_numericalRadius_sub_smul_one_le A
    (numericalRadius (A - c • 1))

/-- Every globally minimizing scalar center has modulus at most `2w(A)`. -/
theorem norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers
    (A : E →L[ℂ] E) {c : ℂ}
    (hc : c ∈ centeredNumericalRadiusMinimizers A) :
    ‖c‖ ≤ 2 * numericalRadius A := by
  have hmin := hc 0
  simp only [zero_smul, sub_zero] at hmin
  have hcoercive :=
    norm_sub_numericalRadius_le_numericalRadius_sub_smul_one A c
  linarith

/-- The full minimizer set lies in the explicit disk of radius `2w(A)`. -/
theorem centeredNumericalRadiusMinimizers_subset_closedBall_two_mul
    (A : E →L[ℂ] E) :
    centeredNumericalRadiusMinimizers A ⊆
      Metric.closedBall 0 (2 * numericalRadius A) := by
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers A hc

/-- There is a globally minimizing center in the explicit numerical-radius
disk of radius `2w(A)`. -/
theorem exists_mem_centeredNumericalRadiusMinimizers_norm_le
    (A : E →L[ℂ] E) :
    ∃ c ∈ centeredNumericalRadiusMinimizers A,
      ‖c‖ ≤ 2 * numericalRadius A := by
  obtain ⟨c, hc⟩ := centeredNumericalRadiusMinimizers_nonempty A
  exact ⟨c, hc,
    norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers A hc⟩

omit [Nontrivial E] in
/-- Adding `bI` to an operator translates every optimal center by `b`. -/
theorem centeredNumericalRadiusMinimizers_add_smul_one
    (A : E →L[ℂ] E) (b : ℂ) :
    centeredNumericalRadiusMinimizers (A + b • 1) =
      (fun c : ℂ => c + b) '' centeredNumericalRadiusMinimizers A := by
  ext c
  constructor
  · intro hc
    refine ⟨c - b, ?_, by ring⟩
    intro d
    have h := hc (d + b)
    have hleft : A + b • 1 - c • 1 = A - (c - b) • 1 := by module
    have hright : A + b • 1 - (d + b) • 1 = A - d • 1 := by module
    rw [hleft, hright] at h
    exact h
  · rintro ⟨d, hd, rfl⟩
    intro e
    have h := hd (e - b)
    have hleft : A + b • 1 - (d + b) • 1 = A - d • 1 := by module
    have hright : A + b • 1 - e • 1 = A - (e - b) • 1 := by module
    rw [hleft, hright]
    exact h

omit [Nontrivial E] in
/-- Multiplying an operator by a nonzero scalar multiplies every optimal
center by the same scalar. -/
theorem centeredNumericalRadiusMinimizers_smul
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) :
    centeredNumericalRadiusMinimizers (a • A) =
      (fun c : ℂ => a * c) '' centeredNumericalRadiusMinimizers A := by
  have hscale (z : ℂ) :
      a • A - (a * z) • 1 = a • (A - z • 1) := by module
  ext c
  constructor
  · intro hc
    let d := a⁻¹ * c
    have hac : a * d = c := by
      dsimp only [d]
      field_simp [ha]
    refine ⟨d, ?_, hac⟩
    intro e
    have h := hc (a * e)
    rw [← hac, hscale d, hscale e, numericalRadius_smul,
      numericalRadius_smul] at h
    exact (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr ha)).mp h
  · rintro ⟨d, hd, rfl⟩
    intro e
    let q := a⁻¹ * e
    have haq : a * q = e := by
      dsimp only [q]
      field_simp [ha]
    have h := hd q
    rw [← haq, hscale d, hscale q, numericalRadius_smul,
      numericalRadius_smul]
    exact (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr ha)).mpr h

omit [Nontrivial E] in
/-- Negating an operator negates every optimal scalar center. -/
@[simp] theorem centeredNumericalRadiusMinimizers_neg (A : E →L[ℂ] E) :
    centeredNumericalRadiusMinimizers (-A) =
      (fun c : ℂ => -c) '' centeredNumericalRadiusMinimizers A := by
  simpa only [neg_one_smul, neg_one_mul] using
    centeredNumericalRadiusMinimizers_smul A (a := -1) (by norm_num)

omit [Nontrivial E] in
/-- An invertible affine change `A ↦ aA+bI` carries optimal centers by the
same affine map. -/
theorem centeredNumericalRadiusMinimizers_smul_add_smul_one
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    centeredNumericalRadiusMinimizers (a • A + b • 1) =
      (fun c : ℂ => a * c + b) '' centeredNumericalRadiusMinimizers A := by
  rw [centeredNumericalRadiusMinimizers_add_smul_one,
    centeredNumericalRadiusMinimizers_smul A ha, Set.image_image]

/-- The zero operator has the unique optimal center zero. -/
@[simp] theorem centeredNumericalRadiusMinimizers_zero :
    centeredNumericalRadiusMinimizers (0 : E →L[ℂ] E) = {0} := by
  ext c
  rw [Set.mem_singleton_iff]
  constructor
  · intro hc
    have h := hc 0
    have hc0 : ‖c‖ ≤ 0 := by
      simpa only [zero_smul, sub_zero, numericalRadius_zero, zero_sub,
        numericalRadius_neg, numericalRadius_smul_one] using h
    exact norm_eq_zero.mp (le_antisymm hc0 (norm_nonneg c))
  · rintro rfl
    intro d
    simpa only [zero_smul, sub_zero, numericalRadius_zero] using
      numericalRadius_nonneg (0 - d • (1 : E →L[ℂ] E))

/-- A scalar operator `cI` has the unique optimal center `c`. -/
@[simp] theorem centeredNumericalRadiusMinimizers_smul_one (c : ℂ) :
    centeredNumericalRadiusMinimizers (c • (1 : E →L[ℂ] E)) = {c} := by
  have h := centeredNumericalRadiusMinimizers_add_smul_one
    (0 : E →L[ℂ] E) c
  simpa only [zero_add, centeredNumericalRadiusMinimizers_zero,
    Set.image_singleton, zero_add] using h

omit [Nontrivial E] in
/-- Taking the adjoint conjugates every optimal scalar center. -/
theorem centeredNumericalRadiusMinimizers_adjoint [CompleteSpace E]
    (A : E →L[ℂ] E) :
    centeredNumericalRadiusMinimizers (A†) =
      (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A := by
  have hradius (c : ℂ) :
      numericalRadius (A† - c • 1) =
        numericalRadius (A - star c • 1) := by
    have hop : (A - star c • (1 : E →L[ℂ] E))† = A† - c • 1 := by
      rw [map_sub,
        (adjoint (𝕜 := ℂ) (E := E) (F := E)).map_smulₛₗ,
        adjoint_one, starRingEnd_apply, star_star]
    have h := numericalRadius_adjoint (A - star c • (1 : E →L[ℂ] E))
    rw [hop] at h
    exact h
  ext c
  constructor
  · intro hc
    refine ⟨star c, ?_, by simp⟩
    intro d
    have h := hc (star d)
    rw [hradius c, hradius (star d)] at h
    simpa only [star_star] using h
  · rintro ⟨d, hd, rfl⟩
    intro e
    change numericalRadius (A† - star d • 1) ≤
      numericalRadius (A† - e • 1)
    have h := hd (star e)
    rw [hradius (star d), hradius e]
    simpa only [star_star] using h

omit [Nontrivial E] in
/-- Unitary conjugation preserves every optimal scalar center. -/
theorem centeredNumericalRadiusMinimizers_unitary_conjugate [CompleteSpace E]
    (A U : E →L[ℂ] E) (hU : U ∈ unitary (E →L[ℂ] E)) :
    centeredNumericalRadiusMinimizers (U† * A * U) =
      centeredNumericalRadiusMinimizers A := by
  have hcenter (c : ℂ) :
      U† * A * U - c • 1 = U† * (A - c • 1) * U := by
    rw [mul_sub, sub_mul]
    congr 1
    rw [mul_smul_comm, smul_mul_assoc, mul_one]
    change c • 1 = c • (star U * U)
    rw [Unitary.star_mul_self_of_mem hU]
  have hradius (c : ℂ) :
      numericalRadius (U† * A * U - c • 1) =
        numericalRadius (A - c • 1) := by
    rw [hcenter]
    exact numericalRadius_unitary_conjugate (A - c • 1) U hU
  ext c
  constructor
  · intro hc d
    have h := hc d
    rwa [hradius c, hradius d] at h
  · intro hc d
    have h := hc d
    rwa [hradius c, hradius d]

omit [Nontrivial E] in
/-- The alternate orientation of unitary conjugation also preserves every
optimal scalar center. -/
theorem centeredNumericalRadiusMinimizers_unitary_conjugate' [CompleteSpace E]
    (A U : E →L[ℂ] E) (hU : U ∈ unitary (E →L[ℂ] E)) :
    centeredNumericalRadiusMinimizers (U * A * U†) =
      centeredNumericalRadiusMinimizers A := by
  simpa only [adjoint_adjoint] using
    centeredNumericalRadiusMinimizers_unitary_conjugate A (U†)
      (Unitary.star_mem hU)

omit [Nontrivial E] in
/-- The optimal centers of a self-adjoint operator are invariant under complex
conjugation. -/
theorem image_starRingEnd_centeredNumericalRadiusMinimizers_eq
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A =
      centeredNumericalRadiusMinimizers A := by
  rw [← centeredNumericalRadiusMinimizers_adjoint A, hA.adjoint_eq]

omit [Nontrivial E] in
/-- Membership among the optimal centers of a self-adjoint operator is
preserved and reflected by complex conjugation. -/
@[simp] theorem star_mem_centeredNumericalRadiusMinimizers_iff
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (c : ℂ) :
    star c ∈ centeredNumericalRadiusMinimizers A ↔
      c ∈ centeredNumericalRadiusMinimizers A := by
  have hmap {z : ℂ} (hz : z ∈ centeredNumericalRadiusMinimizers A) :
      star z ∈ centeredNumericalRadiusMinimizers A := by
    have himage :
        star z ∈ (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A :=
      ⟨z, hz, rfl⟩
    rwa [image_starRingEnd_centeredNumericalRadiusMinimizers_eq A hA] at himage
  constructor
  · intro hc
    simpa only [star_star] using hmap hc
  · exact hmap

/-- A self-adjoint operator has a real globally optimal scalar center. -/
theorem exists_real_mem_centeredNumericalRadiusMinimizers
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ r : ℝ, (r : ℂ) ∈ centeredNumericalRadiusMinimizers A := by
  obtain ⟨c, hc⟩ := centeredNumericalRadiusMinimizers_nonempty A
  have hcstar : star c ∈ centeredNumericalRadiusMinimizers A := by
    have himage :
        star c ∈ (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A := by
      exact ⟨c, hc, rfl⟩
    rw [image_starRingEnd_centeredNumericalRadiusMinimizers_eq A hA] at himage
    exact himage
  refine ⟨c.re, ?_⟩
  have hmid :=
    (convex_centeredNumericalRadiusMinimizers A).midpoint_mem hc hcstar
  rw [midpoint_eq_smul_add] at hmid
  have heq : (c.re : ℂ) = (⅟2 : ℝ) • (c + star c) := by
    apply Complex.ext
    · norm_num [invOf_eq_inv]
      ring
    · norm_num [invOf_eq_inv]
  rw [← heq] at hmid
  exact hmid

/-- A self-adjoint operator has a real optimal center in the explicit
numerical-radius disk. -/
theorem exists_real_mem_centeredNumericalRadiusMinimizers_norm_le
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ r : ℝ, (r : ℂ) ∈ centeredNumericalRadiusMinimizers A ∧
      ‖(r : ℂ)‖ ≤ 2 * numericalRadius A := by
  obtain ⟨r, hr⟩ := exists_real_mem_centeredNumericalRadiusMinimizers A hA
  exact ⟨r, hr,
    norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers A hr⟩

/-- For a self-adjoint operator, the centered numerical radius attains its
global minimum at a real center. -/
theorem exists_real_center_minimizing_numericalRadius_of_isSelfAdjoint
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ r : ℝ, ∀ c : ℂ,
      numericalRadius (A - (r : ℂ) • 1) ≤
        numericalRadius (A - c • 1) := by
  exact exists_real_mem_centeredNumericalRadiusMinimizers A hA

omit [Nontrivial E] in
/-- The optimal centers of a skew-adjoint operator are preserved and
reflected by reflection across the imaginary axis. -/
@[simp] theorem neg_star_mem_centeredNumericalRadiusMinimizers_iff
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) (c : ℂ) :
    -star c ∈ centeredNumericalRadiusMinimizers A ↔
      c ∈ centeredNumericalRadiusMinimizers A := by
  have hAadj : A† = -A := skewAdjoint.mem_iff.mp hA
  have himages :
      (fun z : ℂ => -z) '' centeredNumericalRadiusMinimizers A =
        (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A := by
    calc
      _ = centeredNumericalRadiusMinimizers (-A) :=
        (centeredNumericalRadiusMinimizers_neg A).symm
      _ = centeredNumericalRadiusMinimizers (A†) := by rw [hAadj]
      _ = _ := centeredNumericalRadiusMinimizers_adjoint A
  have hmap {z : ℂ} (hz : z ∈ centeredNumericalRadiusMinimizers A) :
      -star z ∈ centeredNumericalRadiusMinimizers A := by
    have hzstar :
        star z ∈ (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A :=
      ⟨z, hz, rfl⟩
    rw [← himages] at hzstar
    obtain ⟨d, hd, hdz⟩ := hzstar
    have hd_eq : d = -star z := by
      rw [← hdz]
      simp only [neg_neg]
    rwa [← hd_eq]
  constructor
  · intro hc
    simpa only [star_neg, star_star, neg_neg] using hmap hc
  · exact hmap

omit [Nontrivial E] in
/-- Reflection across the imaginary axis fixes the optimal-center set of a
skew-adjoint operator. -/
theorem image_neg_star_centeredNumericalRadiusMinimizers_eq
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    (fun c : ℂ => -star c) '' centeredNumericalRadiusMinimizers A =
      centeredNumericalRadiusMinimizers A := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (neg_star_mem_centeredNumericalRadiusMinimizers_iff A hA d).2 hd
  · intro hc
    refine ⟨-star c,
      (neg_star_mem_centeredNumericalRadiusMinimizers_iff A hA c).2 hc, ?_⟩
    simp only [star_neg, star_star, neg_neg]

/-- A skew-adjoint operator has a purely imaginary globally optimal scalar
center. -/
theorem exists_imaginary_mem_centeredNumericalRadiusMinimizers
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    ∃ r : ℝ, (r : ℂ) * Complex.I ∈ centeredNumericalRadiusMinimizers A := by
  have hAstar : star A = -A := skewAdjoint.mem_iff.mp hA
  have hIA : IsSelfAdjoint (Complex.I • A) := by
    rw [isSelfAdjoint_iff, star_smul, hAstar]
    simp only [RCLike.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]
  obtain ⟨r, hr⟩ := exists_real_mem_centeredNumericalRadiusMinimizers
    (Complex.I • A) hIA
  rw [centeredNumericalRadiusMinimizers_smul A (a := Complex.I)
    Complex.I_ne_zero] at hr
  obtain ⟨c, hc, hIc⟩ := hr
  change Complex.I * c = (r : ℂ) at hIc
  refine ⟨-r, ?_⟩
  have hc_eq : c = ((-r : ℝ) : ℂ) * Complex.I := by
    calc
      c = -Complex.I * (Complex.I * c) := by
        simp only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
      _ = -Complex.I * (r : ℂ) := by rw [hIc]
      _ = ((-r : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
  rwa [← hc_eq]

/-- A skew-adjoint operator has a purely imaginary optimal center in the
explicit numerical-radius disk. -/
theorem exists_imaginary_mem_centeredNumericalRadiusMinimizers_norm_le
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    ∃ r : ℝ,
      (r : ℂ) * Complex.I ∈ centeredNumericalRadiusMinimizers A ∧
        ‖(r : ℂ) * Complex.I‖ ≤ 2 * numericalRadius A := by
  obtain ⟨r, hr⟩ := exists_imaginary_mem_centeredNumericalRadiusMinimizers A hA
  exact ⟨r, hr,
    norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers A hr⟩

/-- For a skew-adjoint operator, the centered numerical radius attains its
global minimum at a purely imaginary center. -/
theorem exists_imaginary_center_minimizing_numericalRadius_of_mem_skewAdjoint
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : A ∈ skewAdjoint (E →L[ℂ] E)) :
    ∃ r : ℝ, ∀ c : ℂ,
      numericalRadius (A - ((r : ℂ) * Complex.I) • 1) ≤
        numericalRadius (A - c • 1) := by
  exact exists_imaginary_mem_centeredNumericalRadiusMinimizers A hA

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
