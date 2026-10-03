/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Operators

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Polarized directional quadratic coefficients

Coordinate identities for recovering mixed quadratic models from finite directional data.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Mapping all directions and the increment through a linear isometry equivalence preserves the
mixed quadratic form. -/
theorem inner_mixedDirectionalQuadraticSum_self_linearIsometryEquiv
    {ι : Type*} (s : Finset ι) (v : ι → E) (a : ι → ι → ℝ)
    (e : E ≃ₗᵢ[ℝ] F) (z : E) :
    inner ℝ (e z)
        (mixedDirectionalQuadraticSum s (fun i ↦ e (v i)) a (e z)) =
      inner ℝ z (mixedDirectionalQuadraticSum s v a z) := by
  rw [inner_mixedDirectionalQuadraticSum_self, inner_mixedDirectionalQuadraticSum_self]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  refine Finset.sum_congr rfl fun j _hj ↦ ?_
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

/-- Mapping all directions and the increment through a linear isometry equivalence preserves the
polarized mixed quadratic form. -/
theorem inner_polarizedMixedQuadraticSum_self_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E)
    (q : ι → ℝ) (r : ι → ι → ℝ) (e : E ≃ₗᵢ[ℝ] F) (z : E) :
    inner ℝ (e z)
        (polarizedMixedQuadraticSum s (fun i ↦ e (v i)) q r (e z)) =
      inner ℝ z (polarizedMixedQuadraticSum s v q r z) := by
  exact inner_mixedDirectionalQuadraticSum_self_linearIsometryEquiv
    s v (polarizedMixedCoefficient q r) e z

/-- Bound for the polarized mixed-directional quadratic form in terms of the sum of absolute
polarized coefficients. -/
theorem abs_inner_polarizedMixedQuadraticSum_self_le
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (q : ι → ℝ) (r : ι → ι → ℝ) (z : E) :
    |inner ℝ z (polarizedMixedQuadraticSum s v q r z)| ≤
      (∑ i ∈ s, ∑ j ∈ s, |polarizedMixedCoefficient q r i j|) * ‖z‖ ^ 2 :=
  abs_inner_mixedDirectionalQuadraticSum_self_le hv (polarizedMixedCoefficient q r) z

/-- Constant-bound form of `abs_inner_polarizedMixedQuadraticSum_self_le`. -/
theorem exists_const_abs_inner_polarizedMixedQuadraticSum_self_le
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (q : ι → ℝ) (r : ι → ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : E, |inner ℝ z (polarizedMixedQuadraticSum s v q r z)| ≤ C * ‖z‖ ^ 2 := by
  exact exists_const_abs_inner_mixedDirectionalQuadraticSum_self_le hv
    (polarizedMixedCoefficient q r)

/-- Constant-bound form for the polarized half-quadratic term used in second-order expansions. -/
theorem exists_const_norm_half_inner_polarizedMixedQuadraticSum_le
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (q : ι → ℝ) (r : ι → ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : E, ‖(1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum s v q r z)‖ ≤
        C * ‖z‖ ^ 2 := by
  exact exists_const_norm_half_inner_mixedDirectionalQuadraticSum_le hv
    (polarizedMixedCoefficient q r)

/-- A finite orthonormal coordinate family collapses the quadratic form of a mixed-directional
sum on one of its coordinate directions to the corresponding diagonal coefficient. The
orthonormality hypothesis is written only on the finite set `s`, which is the form needed for
finite slicing. -/
theorem inner_mixedDirectionalQuadraticSum_self_apply_of_finite_orthonormal
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (a : ι → ι → ℝ)
    (hinner : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (v j) = if i = j then 1 else 0)
    {k : ι} (hk : k ∈ s) :
    inner ℝ (v k) (mixedDirectionalQuadraticSum s v a (v k)) = a k k := by
  rw [inner_mixedDirectionalQuadraticSum_self]
  rw [Finset.sum_eq_single k]
  · rw [hinner hk hk]
    simp only [↓reduceIte, mul_one]
    rw [Finset.sum_eq_single k]
    · rw [hinner hk hk]
      simp
    · intro j hj hjk
      rw [hinner hj hk]
      simp [hjk]
    · intro hk_not
      exact (hk_not hk).elim
  · intro i hi hik
    rw [hinner hi hk]
    simp [hik]
  · intro hk_not
    exact (hk_not hk).elim

/-- Predicate-wrapper form of
`inner_mixedDirectionalQuadraticSum_self_apply_of_finite_orthonormal`. -/
theorem FiniteOrthonormalOn.inner_mixedDirectionalQuadraticSum_self_apply
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) (a : ι → ι → ℝ)
    {k : ι} (hk : k ∈ s) :
    inner ℝ (v k) (mixedDirectionalQuadraticSum s v a (v k)) = a k k :=
  AleksandrovDifferentiability.inner_mixedDirectionalQuadraticSum_self_apply_of_finite_orthonormal
    a hv hk

/-- The polarized coefficient matrix has the prescribed pure directional quadratic coefficient on
each selected orthonormal direction. -/
theorem inner_mixedDirectionalQuadraticSum_polarized_self_apply
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (q : ι → ℝ) (r : ι → ι → ℝ)
    (hinner : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (v j) = if i = j then 1 else 0)
    {k : ι} (hk : k ∈ s) :
    inner ℝ (v k)
        (mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r) (v k)) =
      q k := by
  rw [inner_mixedDirectionalQuadraticSum_self_apply_of_finite_orthonormal
    (a := polarizedMixedCoefficient q r) hinner hk]
  simp

/-- Named-model version of `inner_mixedDirectionalQuadraticSum_polarized_self_apply`. -/
theorem inner_polarizedMixedQuadraticSum_self_apply
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (q : ι → ℝ) (r : ι → ι → ℝ)
    (hinner : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (v j) = if i = j then 1 else 0)
    {k : ι} (hk : k ∈ s) :
    inner ℝ (v k) (polarizedMixedQuadraticSum s v q r (v k)) = q k :=
  inner_mixedDirectionalQuadraticSum_polarized_self_apply q r hinner hk

/-- Predicate-wrapper form of
`inner_mixedDirectionalQuadraticSum_polarized_self_apply`. -/
theorem FiniteOrthonormalOn.inner_mixedDirectionalQuadraticSum_polarized_self_apply
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) (q : ι → ℝ) (r : ι → ι → ℝ)
    {k : ι} (hk : k ∈ s) :
    inner ℝ (v k)
        (mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r) (v k)) =
      q k :=
  AleksandrovDifferentiability.inner_mixedDirectionalQuadraticSum_polarized_self_apply
    q r hv hk

/-- Predicate-wrapper form of `inner_polarizedMixedQuadraticSum_self_apply`. -/
theorem FiniteOrthonormalOn.inner_polarizedMixedQuadraticSum_self_apply
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) (q : ι → ℝ) (r : ι → ι → ℝ)
    {k : ι} (hk : k ∈ s) :
    inner ℝ (v k) (polarizedMixedQuadraticSum s v q r (v k)) = q k :=
  AleksandrovDifferentiability.inner_polarizedMixedQuadraticSum_self_apply q r hv hk

/-- A finite sum whose support is contained in two selected points is the sum of the two selected
values. -/
theorem finset_sum_eq_add_of_eq_zero_off_two
    {ι α : Type*} [AddCommMonoid α] {s : Finset ι}
    {f : ι → α} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hzero : ∀ ⦃k : ι⦄, k ∈ s → k ≠ i → k ≠ j → f k = 0) :
    ∑ k ∈ s, f k = f i + f j := by
  classical
  rw [← Finset.add_sum_erase s f hi]
  congr 1
  rw [Finset.sum_eq_single j]
  · intro k hk hkj
    exact hzero (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk) hkj
  · intro hj_not
    exact (hj_not (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)).elim

/-- Coordinates of the sum of two selected orthonormal directions against a finite orthonormal
family. -/
theorem inner_add_pair_of_finite_orthonormal
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hinner : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (v j) = if i = j then 1 else 0)
    {i j k : ι} (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (hij : i ≠ j) :
    inner ℝ (v k) (v i + v j) = if k = i then 1 else if k = j then 1 else 0 := by
  rw [inner_add_right, hinner hk hi, hinner hk hj]
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hij.symm]
    · simp [hki, hkj]

/-- Predicate-wrapper form of `inner_add_pair_of_finite_orthonormal`. -/
theorem FiniteOrthonormalOn.inner_add_pair
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v)
    {i j k : ι} (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (hij : i ≠ j) :
    inner ℝ (v k) (v i + v j) = if k = i then 1 else if k = j then 1 else 0 :=
  AleksandrovDifferentiability.inner_add_pair_of_finite_orthonormal hv hi hj hk hij

/-- On the sum of two selected orthonormal directions, the quadratic form of a mixed-directional
sum is the four-entry combination expected from polarization. -/
theorem inner_mixedDirectionalQuadraticSum_self_add_of_finite_orthonormal
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (a : ι → ι → ℝ)
    (hinner : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (v j) = if i = j then 1 else 0)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    inner ℝ (v i + v j) (mixedDirectionalQuadraticSum s v a (v i + v j)) =
      a i i + a i j + a j i + a j j := by
  rw [inner_mixedDirectionalQuadraticSum_self]
  let c : ι → ℝ := fun k => inner ℝ (v k) (v i + v j)
  have hc : ∀ ⦃k : ι⦄, k ∈ s → c k = if k = i then 1 else if k = j then 1 else 0 := by
    intro k hk
    exact inner_add_pair_of_finite_orthonormal hinner hi hj hk hij
  have hinner_sum :
      ∀ k ∈ s, (∑ l ∈ s, a k l * c k * c l) = a k i * c k + a k j * c k := by
    intro k hk
    rw [finset_sum_eq_add_of_eq_zero_off_two hi hj hij]
    · rw [hc hi, hc hj]
      simp [hij.symm]
    · intro l hl hli hlj
      rw [hc hl]
      simp [hli, hlj]
  calc
    ∑ k ∈ s, ∑ l ∈ s,
        a k l * inner ℝ (v k) (v i + v j) * inner ℝ (v l) (v i + v j)
        = ∑ k ∈ s, (a k i * c k + a k j * c k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [c]
          exact hinner_sum k hk
    _ = (a i i * c i + a i j * c i) + (a j i * c j + a j j * c j) := by
          rw [finset_sum_eq_add_of_eq_zero_off_two hi hj hij]
          intro k hk hki hkj
          rw [hc hk]
          simp [hki, hkj]
    _ = a i i + a i j + a j i + a j j := by
          rw [hc hi, hc hj]
          simp [hij.symm]
          ring

/-- Predicate-wrapper form of
`inner_mixedDirectionalQuadraticSum_self_add_of_finite_orthonormal`. -/
theorem FiniteOrthonormalOn.inner_mixedDirectionalQuadraticSum_self_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) (a : ι → ι → ℝ)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    inner ℝ (v i + v j) (mixedDirectionalQuadraticSum s v a (v i + v j)) =
      a i i + a i j + a j i + a j j :=
  AleksandrovDifferentiability.inner_mixedDirectionalQuadraticSum_self_add_of_finite_orthonormal
    a hv hi hj hij

/-- The polarized coefficient matrix has the prescribed pairwise-sum quadratic coefficient on
selected orthonormal directions, provided the supplied pairwise coefficients are symmetric. -/
theorem inner_mixedDirectionalQuadraticSum_polarized_self_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (q : ι → ℝ) (r : ι → ι → ℝ)
    (hinner : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (hr : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → r j i = r i j)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    inner ℝ (v i + v j)
        (mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r) (v i + v j)) =
      r i j := by
  rw [inner_mixedDirectionalQuadraticSum_self_add_of_finite_orthonormal
    (a := polarizedMixedCoefficient q r) hinner hi hj hij]
  rw [polarizedMixedCoefficient_self, polarizedMixedCoefficient_self,
    polarizedMixedCoefficient_of_ne q r hij, polarizedMixedCoefficient_of_ne q r hij.symm,
    hr hi hj]
  ring

/-- Named-model version of `inner_mixedDirectionalQuadraticSum_polarized_self_add`. -/
theorem inner_polarizedMixedQuadraticSum_self_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (q : ι → ℝ) (r : ι → ι → ℝ)
    (hinner : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s →
      inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (hr : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → r j i = r i j)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    inner ℝ (v i + v j) (polarizedMixedQuadraticSum s v q r (v i + v j)) =
      r i j :=
  inner_mixedDirectionalQuadraticSum_polarized_self_add q r hinner hr hi hj hij

/-- Predicate-wrapper form of `inner_mixedDirectionalQuadraticSum_polarized_self_add`. -/
theorem FiniteOrthonormalOn.inner_mixedDirectionalQuadraticSum_polarized_self_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) (q : ι → ℝ) (r : ι → ι → ℝ)
    (hr : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → r j i = r i j)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    inner ℝ (v i + v j)
        (mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r) (v i + v j)) =
      r i j :=
  AleksandrovDifferentiability.inner_mixedDirectionalQuadraticSum_polarized_self_add
    q r hv hr hi hj hij

/-- Predicate-wrapper form of `inner_polarizedMixedQuadraticSum_self_add`. -/
theorem FiniteOrthonormalOn.inner_polarizedMixedQuadraticSum_self_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalOn s v) (q : ι → ℝ) (r : ι → ι → ℝ)
    (hr : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → r j i = r i j)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    inner ℝ (v i + v j) (polarizedMixedQuadraticSum s v q r (v i + v j)) =
      r i j :=
  AleksandrovDifferentiability.inner_polarizedMixedQuadraticSum_self_add
    q r hv hr hi hj hij

namespace FiniteOrthonormalSpanningOn

/-- Spanning-frame wrapper for the pure-direction polarized quadratic coefficient identity. -/
theorem inner_mixedDirectionalQuadraticSum_polarized_self_apply
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (q : ι → ℝ) (r : ι → ι → ℝ)
    {k : ι} (hk : k ∈ s) :
    inner ℝ (v k)
        (mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r) (v k)) =
      q k :=
  hv.1.inner_mixedDirectionalQuadraticSum_polarized_self_apply q r hk

/-- Spanning-frame wrapper for the pure-direction named polarized quadratic coefficient
identity. -/
theorem inner_polarizedMixedQuadraticSum_self_apply
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (q : ι → ℝ) (r : ι → ι → ℝ)
    {k : ι} (hk : k ∈ s) :
    inner ℝ (v k) (polarizedMixedQuadraticSum s v q r (v k)) = q k :=
  hv.1.inner_polarizedMixedQuadraticSum_self_apply q r hk

/-- Spanning-frame wrapper for the pairwise-sum polarized quadratic coefficient identity. -/
theorem inner_mixedDirectionalQuadraticSum_polarized_self_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (q : ι → ℝ) (r : ι → ι → ℝ)
    (hr : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → r j i = r i j)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    inner ℝ (v i + v j)
        (mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r) (v i + v j)) =
      r i j :=
  hv.1.inner_mixedDirectionalQuadraticSum_polarized_self_add q r hr hi hj hij

/-- Spanning-frame wrapper for the pairwise-sum named polarized quadratic coefficient
identity. -/
theorem inner_polarizedMixedQuadraticSum_self_add
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) (q : ι → ℝ) (r : ι → ι → ℝ)
    (hr : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → r j i = r i j)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    inner ℝ (v i + v j) (polarizedMixedQuadraticSum s v q r (v i + v j)) =
      r i j :=
  hv.1.inner_polarizedMixedQuadraticSum_self_add q r hr hi hj hij

/-- A symmetric operator is the polarized mixed-directional model determined by its pure and
off-diagonal pairwise-sum quadratic coefficients on a finite orthonormal spanning frame. -/
theorem eq_polarizedMixedQuadraticSum_of_quadraticForm_eq_on_frame_and_add_offDiagonal
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn s v) {B : E →L[ℝ] E}
    (hB : IsSymmetricOperator B) {q : ι → ℝ} {r : ι → ι → ℝ}
    (hr : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → r j i = r i j)
    (hpure : ∀ ⦃i : ι⦄, i ∈ s → inner ℝ (v i) (B (v i)) = q i)
    (hpair : ∀ ⦃i : ι⦄, i ∈ s → ∀ ⦃j : ι⦄, j ∈ s → i ≠ j →
      inner ℝ (v i + v j) (B (v i + v j)) = r i j) :
    B = polarizedMixedQuadraticSum s v q r := by
  refine hv.ext_of_quadraticForm_eq_on_frame_and_add_offDiagonal hB
    (isSymmetricOperator_polarizedMixedQuadraticSum s v q r) ?_ ?_
  · intro i hi
    rw [hpure hi, hv.inner_polarizedMixedQuadraticSum_self_apply q r hi]
  · intro i hi j hj hij
    rw [hpair hi hj hij, hv.inner_polarizedMixedQuadraticSum_self_add q r hr hi hj hij]

end FiniteOrthonormalSpanningOn

end AleksandrovDifferentiability
