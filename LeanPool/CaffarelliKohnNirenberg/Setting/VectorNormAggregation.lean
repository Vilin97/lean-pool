/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.VectorInequalities

/-!
# Vector Norm Aggregation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section
namespace CKN

/-!
# Aggregation of componentwise vector inequalities to the Euclidean norm

The Poincare and `H¹` interpolation inequalities of `CKN.Setting.VectorInequalities` are
stated componentwise: each coordinate `u_i` of a velocity field `u : Vec3 → Vec3` is
controlled by the scalar theorems.  The estimates of `paper/ckn.tex` instead use the
Euclidean norm `|u|` and the Frobenius norm of the spatial gradient,
`|∇u|² = spatialGradientSq`.  This file supplies the finite-dimensional norm comparisons
that turn the componentwise statements into their Euclidean counterparts.

The two elementary inequalities on `ℝ³` are

* `|u|^p ≤ 3^{max(0,p/2-1)} Σ_i |u_i|^p` (the sharp comparison of the Euclidean norm
  with the component `ℓᵖ` mass), and
* `Σ_i |u_i|^p ≤ 3 |u|^p`.

Both are proved pointwise and then integrated, first on the `ℝ≥0∞` side (the form in which
the scale quantities `γ`, `α`, `β` store their local `Lᵖ` masses) and then for the
spatial balls used by the Poincare and Sobolev statements.
-/

/-! ### Pointwise comparison on `ℝ³` -/

private lemma vec3EuclideanNorm_sq_eq_sum (x : Vec3) :
    vec3EuclideanNorm x ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

/-- The Euclidean norm raised to `p ≥ 1` is controlled by the component `ℓᵖ` mass with
the sharp finite-dimensional constant: `|u|^p ≤ 3^{max(0,p/2-1)} Σ_i |u_i|^p`. -/
theorem vec3EuclideanNorm_rpow_le_sum_rpow (x : Vec3) {p : ℝ} (hp : 1 ≤ p) :
    vec3EuclideanNorm x ^ p ≤
      (3 : ℝ) ^ (max 0 (p / 2 - 1)) * ∑ i : Fin 3, |x i| ^ p := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rcases lt_or_ge p 2 with hp2 | hp2
  · -- `p ≤ 2`: the Euclidean norm is dominated by the `ℓᵖ` norm, with constant one.
    have hmax : max 0 (p / 2 - 1) = 0 := by
      apply max_eq_left
      nlinarith only [hp2]
    rw [hmax, Real.rpow_zero, one_mul]
    have hSnn : 0 ≤ ∑ j : Fin 3, |x j| ^ p :=
      Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg (x j)) p)
    have hexp : 0 ≤ 2 / p - 1 := by
      rw [sub_nonneg, one_le_div hp_pos]
      linarith only [hp2]
    have hterm (i : Fin 3) :
        |x i| ^ 2 ≤ (∑ j : Fin 3, |x j| ^ p) ^ (2 / p - 1) * |x i| ^ p := by
      have hbase : 0 ≤ |x i| ^ p := Real.rpow_nonneg (abs_nonneg (x i)) p
      have hle : |x i| ^ p ≤ ∑ j : Fin 3, |x j| ^ p :=
        Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg (x j)) p)
          (Finset.mem_univ i)
      have h1 : |x i| ^ 2 = (|x i| ^ p) ^ (2 / p) := by
        have he : ((2 : ℕ) : ℝ) = p * (2 / p) := by field_simp; norm_num
        nth_rewrite 1 [← Real.rpow_natCast |x i| 2]
        nth_rewrite 1 [he]
        exact Real.rpow_mul (abs_nonneg (x i)) p (2 / p)
      have h2 : (|x i| ^ p) ^ (2 / p) =
          (|x i| ^ p) ^ (2 / p - 1) * |x i| ^ p := by
        calc
          (|x i| ^ p) ^ (2 / p) = (|x i| ^ p) ^ (2 / p - 1 + 1) := by
            congr 1
            ring
          _ = (|x i| ^ p) ^ (2 / p - 1) * (|x i| ^ p) ^ (1 : ℝ) :=
            Real.rpow_add_of_nonneg hbase hexp (by norm_num : (0 : ℝ) ≤ 1)
          _ = (|x i| ^ p) ^ (2 / p - 1) * |x i| ^ p := by rw [Real.rpow_one]
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hbase hle hexp)
        (Real.rpow_nonneg (abs_nonneg (x i)) p)
    have hsum2 : (∑ j : Fin 3, |x j| ^ p) ^ (2 / p) =
        (∑ j : Fin 3, |x j| ^ p) ^ (2 / p - 1) * ∑ j : Fin 3, |x j| ^ p := by
      calc
        (∑ j : Fin 3, |x j| ^ p) ^ (2 / p) =
            (∑ j : Fin 3, |x j| ^ p) ^ (2 / p - 1 + 1) := by
          congr 1
          ring
        _ = (∑ j : Fin 3, |x j| ^ p) ^ (2 / p - 1) *
            (∑ j : Fin 3, |x j| ^ p) ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg hSnn hexp (by norm_num : (0 : ℝ) ≤ 1)
        _ = (∑ j : Fin 3, |x j| ^ p) ^ (2 / p - 1) * ∑ j : Fin 3, |x j| ^ p := by
          rw [Real.rpow_one]
    have hsum : ∑ i : Fin 3, |x i| ^ 2 ≤
        (∑ j : Fin 3, |x j| ^ p) ^ (2 / p) := by
      calc
        ∑ i : Fin 3, |x i| ^ 2 ≤
            ∑ i : Fin 3, (∑ j : Fin 3, |x j| ^ p) ^ (2 / p - 1) * |x i| ^ p :=
          Finset.sum_le_sum (fun i _ => hterm i)
        _ = (∑ j : Fin 3, |x j| ^ p) ^ (2 / p - 1) * ∑ i : Fin 3, |x i| ^ p := by
          rw [Finset.mul_sum]
        _ = (∑ j : Fin 3, |x j| ^ p) ^ (2 / p) := hsum2.symm
    have hpow : vec3EuclideanNorm x ^ p = (vec3EuclideanNorm x ^ 2) ^ (p / 2) := by
      have hbase : vec3EuclideanNorm x ^ 2 = vec3EuclideanNorm x ^ (2 : ℝ) :=
        (Real.rpow_natCast (vec3EuclideanNorm x) 2).symm
      rw [hbase]
      have he : p = 2 * (p / 2) := by ring
      nth_rewrite 1 [he]
      exact Real.rpow_mul (vec3EuclideanNorm_nonneg x) 2 (p / 2)
    calc
      vec3EuclideanNorm x ^ p = (vec3EuclideanNorm x ^ 2) ^ (p / 2) := hpow
      _ = (∑ i : Fin 3, x i ^ 2) ^ (p / 2) := by
        congr 1
        exact vec3EuclideanNorm_sq_eq_sum x
      _ = (∑ i : Fin 3, |x i| ^ 2) ^ (p / 2) := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by rw [sq_abs])
      _ ≤ ((∑ j : Fin 3, |x j| ^ p) ^ (2 / p)) ^ (p / 2) :=
        Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => sq_nonneg (|x i|))) hsum
          (by positivity)
      _ = ∑ j : Fin 3, |x j| ^ p := by
        rw [← Real.rpow_mul hSnn]
        rw [show 2 / p * (p / 2) = 1 by field_simp]
        rw [Real.rpow_one]
  · -- `p ≥ 2`: convexity of `t ↦ t^{p/2}` applied to the squares of the coordinates.
    have hr : 1 ≤ p / 2 := by linarith only [hp2]
    have hsum := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
      (f := fun i : Fin 3 => x i ^ 2) hr (fun i _ => sq_nonneg (x i))
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hsum
    have hrpow (i : Fin 3) : (x i ^ 2) ^ (p / 2) = |x i| ^ p := by
      have hbase : x i ^ 2 = |x i| ^ (2 : ℕ) := by rw [sq_abs]
      rw [hbase, ← Real.rpow_natCast |x i| 2, ← Real.rpow_mul (abs_nonneg (x i))]
      congr 1
      ring
    have hpow : vec3EuclideanNorm x ^ p = (∑ i : Fin 3, x i ^ 2) ^ (p / 2) := by
      have he : p = 2 * (p / 2) := by ring
      nth_rewrite 1 [he]
      rw [Real.rpow_mul (vec3EuclideanNorm_nonneg x) 2 (p / 2)]
      exact congrArg (fun t : ℝ => t ^ (p / 2))
        ((Real.rpow_natCast (vec3EuclideanNorm x) 2).trans
          (vec3EuclideanNorm_sq_eq_sum x))
    calc
      vec3EuclideanNorm x ^ p = (∑ i : Fin 3, x i ^ 2) ^ (p / 2) := hpow
      _ ≤ (3 : ℝ) ^ (p / 2 - 1) * ∑ i : Fin 3, (x i ^ 2) ^ (p / 2) := hsum
      _ = (3 : ℝ) ^ (p / 2 - 1) * ∑ i : Fin 3, |x i| ^ p := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hrpow i)
      _ = (3 : ℝ) ^ (max 0 (p / 2 - 1)) * ∑ i : Fin 3, |x i| ^ p := by
        rw [max_eq_right]
        linarith only [hp2]

/-! ### The `ℝ≥0∞` integrable form used by the scale quantities -/

private lemma aemeasurable_component_enorm_rpow {μ : Measure Vec3} {u : Vec3 → Vec3}
    {p : ℝ} (hu : ∀ i : Fin 3, AEMeasurable (fun x => u x i) μ) (i : Fin 3) :
    AEMeasurable (fun x => ‖u x i‖ₑ ^ p) μ := by
  have hnorm : AEMeasurable (fun x => ‖u x i‖ₑ) μ := by
    simpa only [ofReal_norm] using (hu i).norm.ennreal_ofReal
  exact ((ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable hnorm)

/-- Pointwise comparison on the `ℝ≥0∞` side: the `p`-th power of the Euclidean density
is dominated by the component `ℓᵖ` mass with the sharp finite-dimensional constant. -/
theorem ofReal_vec3EuclideanNorm_rpow_le_sum {u : Vec3} {p : ℝ} (hp : 1 ≤ p) :
    ENNReal.ofReal (vec3EuclideanNorm u) ^ p ≤
      ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) *
        ∑ i : Fin 3, ‖u i‖ₑ ^ p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hbase := vec3EuclideanNorm_rpow_le_sum_rpow u hp
  have hconst : 0 ≤ (3 : ℝ) ^ max 0 (p / 2 - 1) := Real.rpow_nonneg (by norm_num) _
  calc
    ENNReal.ofReal (vec3EuclideanNorm u) ^ p
        = ENNReal.ofReal (vec3EuclideanNorm u ^ p) :=
          ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg u) hp0
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1) * ∑ i : Fin 3, |u i| ^ p) :=
          ENNReal.ofReal_le_ofReal hbase
    _ = ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) *
          ENNReal.ofReal (∑ i : Fin 3, |u i| ^ p) :=
          ENNReal.ofReal_mul hconst
    _ = ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) *
          ∑ i : Fin 3, ENNReal.ofReal (|u i| ^ p) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg (u i)) p)]
    _ = ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) *
          ∑ i : Fin 3, ‖u i‖ₑ ^ p := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ => by
            rw [Real.enorm_eq_ofReal_abs,
              ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (u i)) hp0])

/-- Integrated form of the sharp comparison: the `Lᵖ` mass of the Euclidean density is
controlled by the sum of the component `Lᵖ` masses. -/
theorem lintegral_vec3EuclideanNorm_rpow_le_sum {s : Set Vec3} {u : Vec3 → Vec3}
    {p : ℝ} (hp : 1 ≤ p)
    (hu : ∀ i : Fin 3, AEMeasurable (fun x => u x i) (volume.restrict s)) :
    ∫⁻ x in s, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ p ≤
      ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) *
        ∑ i : Fin 3, ∫⁻ x in s, ‖u x i‖ₑ ^ p := by
  have hconst_ne : ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  calc
    ∫⁻ x in s, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ p ≤
        ∫⁻ x in s, ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) *
          ∑ i : Fin 3, ‖u x i‖ₑ ^ p :=
      lintegral_mono (fun x => ofReal_vec3EuclideanNorm_rpow_le_sum (u := u x) hp)
    _ = ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) *
          ∫⁻ x in s, ∑ i : Fin 3, ‖u x i‖ₑ ^ p :=
      lintegral_const_mul' _ _ hconst_ne
    _ = ENNReal.ofReal ((3 : ℝ) ^ max 0 (p / 2 - 1)) *
          ∑ i : Fin 3, ∫⁻ x in s, ‖u x i‖ₑ ^ p := by
      rw [lintegral_finsetSum' _ (fun i _ => aemeasurable_component_enorm_rpow hu i)]

end CKN
