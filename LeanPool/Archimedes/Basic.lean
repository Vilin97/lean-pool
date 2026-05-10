/-
Copyright (c) 2026 misaka10987. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: misaka10987
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional


namespace A

/--
A point (vector) in a 3-dimensional Euclidean space.
For declaring a point, simply use `p : Point`.

This is an alias for Mathlib's `EuclideanSpace ℝ (Fin 3)`,
and thus has exactly the same behaviour.
-/
abbrev Point := EuclideanSpace ℝ (Fin 3)

namespace Point

/--
The x-component of the vector, defined as `self 0` .
-/
abbrev x (self : Point) : ℝ := self 0

/--
The y-component of the vector, defined as `self 1` .
-/
abbrev y (self : Point) : ℝ := self 1

/--
The z-component of the vector, defined as `self 2` .
-/
abbrev z (self : Point) : ℝ := self 2

/--
A non-zero vector.
-/
abbrev NonZero := { p : Point // p ≠ 0 }

namespace NonZero

instance : Neg NonZero where
  neg v := ⟨ -v.val, by simp [v.prop] ⟩

@[simp]
lemma neg_val (v : NonZero) : (-v).val = -v.val := by
  simp [Neg.neg]

end NonZero

/--
Introduce a non-zero vector with the provided proof.
-/
def non_zero (self : Point) (h : self ≠ 0) : NonZero := ⟨ self, h ⟩

/--
The dot product.
-/
@[simp]
noncomputable abbrev dot (self : Point) (v : Point) : ℝ :=
  Inner.inner ℝ self v

/--
The dot product.
-/
infix:69 " ∘ " => dot

/--
The cross product.
-/
@[simp]
abbrev cross (self : Point) (v : Point) : Point :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp self) (WithLp.ofLp v))

/--
The cross product.
-/
infix:69 " ⨯ " => cross

/--
Naive definition of dot product of 3-dimensional vectors,
i.e. sum of product of corresponding components.
-/
theorem inner_product (v w : Point) : v ∘ w = v.x • w.x + v.y • w.y + v.z • w.z := by
  simp [Inner.inner, Fin.sum_univ_succ]
  ring

/--
Naive definition of cross product of 3-dimensional vectors.
-/
theorem vector_product (v w : Point) :
    v ⨯ w = WithLp.toLp 2
      (![ v.y • w.z - v.z • w.y, v.z • w.x - v.x • w.z, v.x • w.y - v.y • w.x ] :
        Fin 3 → ℝ) := by
  simp [crossProduct]

/--
A vector's inner product with itself $\left< \mathbf v, \mathbf v \right>$ is non-negative.
-/
theorem dot_self_nn (v : Point) : 0 ≤ v ∘ v :=
  real_inner_self_nonneg

/--
The length, or norm of the vector.
-/
noncomputable abbrev len (v : Point) : ℝ := ‖v‖

/--
Naive definition of norm of 3-dimensional vector,
i.e. square root of sum of components squared.
-/
theorem norm (v : Point) : ‖v‖ = √ (v.x ^ 2 + v.y ^ 2 + v.z ^ 2) := by
  simp [Norm.norm, Fin.sum_univ_succ, Real.sqrt_eq_rpow]
  ring_nf

/--
The length, or norm of the vector is non-negative.
-/
theorem len_nn (v : Point) : 0 ≤ ‖v‖ := by
  simp [norm]

/--
A vector dot products itself equals square of its normal.
-/
theorem sq_norm_eq_dot_self (v : Point) : ‖v‖ ^ 2 = v ∘ v := by
  simp [norm]

/--
The unit vector of a specific vector.
Note that this is undefined for zero vector.
-/
noncomputable def unit (self : Point) : Point :=
  (1 / ‖self‖) • self

/--
The norm of a unit vector, if defined, is $1$ .
-/
@[simp]
theorem unit_norm_one (v : Point) (nonzero : v ≠ 0) : ‖v.unit‖ = 1 := by
  simp [unit, norm_smul]
  field_simp

/--
A vector's length equals dot product with its unit vector.
-/
theorem len_dot_unit (v : Point) (nonzero : v ≠ 0) : ‖v‖ = v ∘ v.unit := by
  simp [unit, norm, inner_product]
  have : ‖v‖ ≠ 0 := fun h ↦ nonzero (norm_eq_zero.mp h)
  rw [norm] at this
  field_simp
  rw [Real.sq_sqrt]
  positivity

/--
Distance between points.
-/
noncomputable abbrev dist (self : Point) (v : Point) : ℝ := Dist.dist self v

/--
Distance between points.
-/
infix:69 "ᵈ" => dist

/--
Naive definition of the metric function of Euclidean space.
-/
theorem metric (v w : Point) : vᵈw = ‖w - v‖ := by
  rw [←norm_neg]
  simp [dist, norm, Dist.dist, Real.sqrt_eq_rpow, Fin.sum_univ_three]

/--
The parallel relation.

Note that the zero vector is defined to be not parallel with any vectors other than the zero vector.
This is for parallel to be an equivalence relation.
-/
def parallel (v w : Point) : Prop :=
  (∃ k : ℝ , w = k • v) ∧ (∃ k : ℝ , v = k • w)

/--
The parallel relation.
-/
infix:49 " ∥ " => parallel

/--
The non-parallel relation.
-/
infix:49 " ∦ " => ¬parallel

/--
Parallel relation is reflective.
-/
theorem parallel_refl (v : Point) : v ∥ v :=
  ⟨⟨1, by rw [one_smul]⟩, ⟨1, by rw [one_smul]⟩⟩

/--
Parallel relation is symmetric.
-/
theorem parallel_symm (v w : Point) : v ∥ w → w ∥ v
  | ⟨hvw, hwv⟩ => ⟨hwv, hvw⟩

/--
Parallel relation is transitive.
-/
theorem parallel_trans (v w u : Point) : v ∥ w → w ∥ u → v ∥ u
  | ⟨⟨k_w, h_w⟩, ⟨k_v, h_v⟩⟩, ⟨⟨k_u, h_u⟩, ⟨k_w', h_w'⟩⟩ =>
    ⟨⟨k_u * k_w, by rw [h_u, h_w, mul_smul]⟩,
     ⟨k_v * k_w', by rw [h_v, h_w', mul_smul]⟩⟩

/-- The parallel relation on points is an equivalence relation. -/
theorem parallel_eq : Equivalence parallel where
  refl := parallel_refl
  symm := @parallel_symm
  trans := @parallel_trans

/--
Parallel relation is commutative.
-/
theorem parallel_comm (v w : Point) : v ∥ w ↔ w ∥ v :=
  ⟨ parallel_symm v w, parallel_symm w v ⟩

/--
The zero vector is the only one parallel to zero vector.
-/
theorem zero_parallel_zero (v : Point) : v ∥ 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, ⟨k, hk⟩⟩ := h
    rw [hk, smul_zero]
  · subst h
    exact parallel_refl 0

/--
Linear independence.
-/
abbrev lnindep (v w : Point) := LinearIndependent ℝ ![v, w]

/--
Linear independence is symmetric.
-/
theorem lnindep_symm (v w : Point) : lnindep v w → lnindep w v := by
  intro h
  rw [lnindep, LinearIndependent.pair_symm_iff (R := ℝ)]
  exact h

/--
Linear independence is commutative.
-/
theorem lnindep_comm (v w : Point) : lnindep v w ↔ lnindep w v :=
  ⟨ lnindep_symm v w, lnindep_symm w v ⟩

/--
Linear dependence.
-/
abbrev lndep (v w : Point) := ¬LinearIndependent ℝ ![v, w]

/--
Linear dependence is reflective.
-/
theorem lndep_refl (v : Point) : lndep v v := by
  rw [lndep, not_linearIndependent_iff]
  refine ⟨Finset.univ, ![1, -1], ?_, ⟨0, Finset.mem_univ _, ?_⟩⟩
  · simp [Fin.sum_univ_succ]
  · simp

/--
Linear dependence is symmetric.
-/
theorem lndep_symm (v w : Point) : lndep v w → lndep w v := by
  simp [lndep, lnindep_comm]

/--
Linear dependence is commutative.
-/
theorem lndep_comm (v w : Point) : lndep v w ↔ lndep w v :=
  ⟨ lndep_symm v w, lndep_symm w v ⟩

/--
Parallel vectors are linear dependent.
-/
theorem parallel_lndep (v w : Point) : v ∥ w → lndep v w := by
  rintro ⟨⟨x, hx⟩, _⟩
  rw [lndep, not_linearIndependent_iff]
  refine ⟨Finset.univ, ![-x, 1], ?_, ⟨1, Finset.mem_univ _, ?_⟩⟩
  · simp [Fin.sum_univ_succ, hx, neg_smul]
  · simp

/--
The perpendicularity.
-/
def perp (v w : Point) : Prop := v ∘ w = 0

/--
The perpendicularity.
-/
infix:49 " ⟂ " => perp

/--
Perpendicularity is symmetric.
-/
theorem perp_symm (v w : Point) : v ⟂ w → w ⟂ v := by
  simp [perp, real_inner_comm]

/--
Perpendicularity is commutative.
-/
theorem perp_comm (v w : Point) : v ⟂ w ↔ w ⟂ v :=
  ⟨ perp_symm v w, perp_symm w v ⟩

/--
A vector with all-zero components is a zero vector.
-/
@[simp]
lemma zero_components : ![(0 : ℝ), 0, 0] = 0 := by
  funext i
  fin_cases i <;> simp

/--
The one to be asymmmetrically chosen from a pair of opposite vectors.

See `NonZero.asymm_choose` for specifications.
-/
def asymm_chosen (v : Point) : Prop :=
  v.x > 0 ∨ v.x = 0 ∧ (v.y > 0 ∨ v.y = 0 ∧ v.z > 0)

/--
The asymmmetrical choice is decidable.
-/
noncomputable instance asymm_chosen_decidable (v : Point) : Decidable v.asymm_chosen := by
  unfold asymm_chosen
  infer_instance

/--
An asymmetrically chosen vector is never zero.
-/
theorem asymm_chosen_non_zero (v : Point) : v.asymm_chosen → v ≠ 0 := by
  intro h
  simp [asymm_chosen] at h
  by_contra this
  simp [this] at h

/--
An asymmetrically chosen vector.
-/
abbrev AsymmChosen := { p : Point // p.asymm_chosen }

/--
Exactly one of a vector and its opposite is asymmetrically chosen.
-/
private lemma _asymm_chosen_iff_aux (a b c : ℝ) (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    (a > 0 ∨ a = 0 ∧ (b > 0 ∨ b = 0 ∧ c > 0)) ↔
      ¬(-a > 0 ∨ -a = 0 ∧ (-b > 0 ∨ -b = 0 ∧ -c > 0)) := by
  by_cases h_a : a = 0
  · subst h_a
    by_cases h_b : b = 0
    · subst h_b
      have h_c : c ≠ 0 := fun hc => h ⟨rfl, rfl, hc⟩
      refine ⟨?_, ?_⟩
      · rintro (h | ⟨_, h | ⟨_, h⟩⟩)
        · exact absurd h (lt_irrefl 0)
        · exact absurd h (lt_irrefl 0)
        · rintro (k | ⟨_, k | ⟨_, k⟩⟩)
          · linarith
          · linarith
          · linarith
      · intro hneg
        rcases lt_or_gt_of_ne h_c with hc | hc
        · exact absurd (Or.inr ⟨neg_zero, Or.inr ⟨neg_zero, neg_pos.mpr hc⟩⟩) hneg
        · exact Or.inr ⟨rfl, Or.inr ⟨rfl, hc⟩⟩
    · refine ⟨?_, ?_⟩
      · rintro (h | ⟨_, h | ⟨h, _⟩⟩)
        · exact absurd h (lt_irrefl 0)
        · rintro (k | ⟨_, k | ⟨k, _⟩⟩)
          · linarith
          · linarith
          · exact absurd k.symm (by linarith)
        · exact absurd h h_b
      · intro hneg
        rcases lt_or_gt_of_ne h_b with hb | hb
        · exact absurd (Or.inr ⟨neg_zero, Or.inl (neg_pos.mpr hb)⟩) hneg
        · exact Or.inr ⟨rfl, Or.inl hb⟩
  · refine ⟨?_, ?_⟩
    · rintro (h | ⟨h, _⟩)
      · rintro (k | ⟨k, _⟩)
        · linarith
        · exact absurd k.symm (by linarith)
      · exact absurd h h_a
    · intro hneg
      rcases lt_or_gt_of_ne h_a with ha | ha
      · exact absurd (Or.inl (neg_pos.mpr ha)) hneg
      · exact Or.inl ha

theorem NonZero.asymm_chosen_iff_not_opposite (v : NonZero) :
    v.val.asymm_chosen ↔ ¬(-v).val.asymm_chosen := by
  have hx : (-v).val.x = -v.val.x := by simp
  have hy : (-v).val.y = -v.val.y := by simp
  have hz : (-v).val.z = -v.val.z := by simp
  unfold asymm_chosen
  rw [hx, hy, hz]
  apply _asymm_chosen_iff_aux
  rintro ⟨h_x, h_y, h_z⟩
  apply v.prop
  ext i
  fin_cases i
  · exact h_x
  · exact h_y
  · exact h_z

/--
Asymmetrically choose one from a non-zero vector and its opposite.

The choice is done under the following algorithm:

- Choose the vector with positive x-component;

- If the x-components are both zero, choose the vector with positive y-component;

- If the y-components are also both zero, choose the vector with positive z-component.
-/
noncomputable def NonZero.asymm_choose (v : NonZero) : AsymmChosen :=
  if h : v.val.asymm_chosen then
    ⟨ v, h ⟩
  else by
    refine ⟨-v, ?_⟩
    by_contra hn
    exact h ((NonZero.asymm_chosen_iff_not_opposite v).mpr hn)

/--
The asymmetrical choice is an even function.
-/
theorem NonZero.asymm_choose_even (v : NonZero) : v.asymm_choose = (-v).asymm_choose := by
  simp [asymm_choose]
  by_cases v.val.asymm_chosen <;> simp [asymm_chosen_iff_not_opposite]

/--
The asymmetrical choice either chooses a non-zero vector itself or its opposite.
-/
theorem NonZero.asymm_choose_either (v : NonZero) :
    v.asymm_choose.val = v ∨ v.asymm_choose.val = -v := by
  simp [asymm_choose]
  by_cases h : v.val.asymm_chosen <;> simp [h]

end Point

end A
