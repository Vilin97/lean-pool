/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import LeanPool.LeanBooleanfun.AuxLemmas
import LeanPool.LeanBooleanfun.ToMathlib.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi

/-!
# Analysis on Boolean functions

This file contains some basic definitions and theorems for analysis
of real-valued Boolean functions mainly following Ryan O'Donnell's book [odonnell2014].
The Hamming cube is represented by the function type `Fin n → Fin 2`, so that
a `BooleanFunc n` is a `(Fin n → Fin 2) → ℝ`.

Thanks to Mathlib, it is relatively straightforward to get started with Fourier analysis:
* Typeclass inference automatically equips `BooleanFunc n` with the appropriate ℝ-vector
  space structure.
* We define inner product space structure via `InnerProductSpace.Core` and show that
  the `walshCharacter`s form an orthonormal basis.
* Then Plancherel's theorem follows from Mathlib's `OrthogonalFamily.inner_sum`.

Even if there was a general framework for Fourier transforms on LCA groups in Mathlib,
it may be preferrable to use this ad-hoc definition due to slightly different notational
conventions in the context of Boolean functions, and the simplicity of working with finite sums.

## Main results

* `walsh_fourier` expresses a Boolean function in terms of its Walsh-Fourier transform
* `variance_le_totalInfluence` is a version of the classical L² Poincaré inequality
* `fourier_convolution` is the convolution theorem for the Walsh-Fourier transform

## Notation

* `𝐄` denotes expectation with respect to uniform probability measure
* `χ S` denotes the Walsh character associated with an `S : Finset (Fin n)`
* `𝓕` denotes the Walsh-Fourier transform `fourierTransform`
* `⟨⬝, ⬝⟩` denotes the inner product defined as expectation of product
* `‖⬝‖` denotes the (normalized) L² norm
* `⋆` denotes convolution
-/

namespace LeanPool.LeanBooleanfun.BooleanFun

open Real BigOperators Function Finset Pi Module
open RealInnerProductSpace

/-- A Boolean function maps an `n`-tuple of bits (of type `Fin n → Fin 2`) to a real number. -/
abbrev BooleanFunc (n : ℕ) : Type := (Fin n → Fin 2) → ℝ

noncomputable section

variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)}

lemma add_self_eq_zero (a : Fin n → Fin 2) : a + a = 0 := by
  funext i
  change a i + a i = (0 : Fin 2)
  obtain h | h : a i = 0 ∨ a i = 1 := by omega
  · rw [h]; rfl
  · rw [h]; rfl

/-- Translation invariance -/
lemma sum_translate (a : Fin n → Fin 2) : ∑ x, f x = ∑ x, f (x + a) := by
  apply sum_bijective (fun x ↦ x + a)
  · constructor
    · intro x y; simp
    · intro y; refine ⟨y + a, ?_⟩
      change y + a + a = y
      rw [add_assoc, add_self_eq_zero, add_zero]
  · simp
  · intro i _
    rw [add_assoc, add_self_eq_zero, add_zero]

/-- The expectation of a Boolean function is its average value with respect to the uniform
probability measure on `Fin n → Fin 2`. -/
def expectation : BooleanFunc n →ₗ[ℝ] ℝ where
  toFun := fun f ↦ (1 / 2) ^ n * ∑ i, f i
  map_add' := by
    intro f g
    simp only [one_div, inv_pow, Pi.add_apply]
    rw [sum_add_distrib]
    ring
  map_smul' := by
    intro c f
    dsimp
    rw [← mul_sum]
    ring

/-- Expectation of a Boolean function -/
scoped notation "𝐄" => expectation

/-- Definition of Walsh character -/
abbrev walshCharacter (S : Finset (Fin n)) : BooleanFunc n := fun x ↦ ∏ i ∈ S, (-1) ^ (x i).val

/-- Walsh character -/
scoped notation "χ" => walshCharacter

lemma walsh_def : χ S x = ∏ i ∈ S, (-1) ^ (x i).val := by rfl

lemma walsh_ne_zero : χ S x ≠ 0 := by apply prod_ne_zero_iff.mpr; intro i _; simp

lemma walsh_eq_neg_one_pow_sum : χ S x = (-1) ^ ∑ i ∈ S, (x i).val := prod_pow_eq_pow_sum _ _ _

/-- Walsh characters are characters. -/
lemma walsh_add : χ S (x + y) = (χ S x) * (χ S y) := by
  rw [← prod_mul_distrib, prod_congr (by rfl)]
  have (v : Fin 2) : v = 0 ∨ v = 1 := by omega
  intro i _
  dsimp
  obtain ⟨hx|hx, hy|hy⟩ := And.intro (this (x i)) (this (y i)) <;>
    { rw [hx, hy]; simp }

/-- Dual space of Boolean functions as the type of real-valued functions on `Finset (Fin n)`. -/
abbrev BooleanFunc' (n : ℕ) := Finset (Fin n) → ℝ

/-- The Walsh-Fourier transform of a Boolean function `f` is defined on sets of coordinates
`S : Finset (Fin n)` as expectation of the Walsh character `χ S` times `f`. -/
def fourierTransform : BooleanFunc n →ₗ[ℝ] BooleanFunc' n where
  toFun := fun f ↦ fun S ↦ 𝐄 (χ S * f)
  map_add' := by
    intro f g
    funext S
    simp
    ring_nf
    simp
  map_smul' := by
    intro c f
    funext S
    simp

/-- Walsh-Fourier transform on Boolean functions -/
scoped notation "𝓕" => fourierTransform

theorem expectation_eq_fourier : 𝐄 f = 𝓕 f ∅ := by
  unfold fourierTransform
  unfold walshCharacter
  unfold expectation
  simp only [one_div, inv_pow, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.mul_apply, prod_empty, one_mul]

theorem expectation_prod_self_nonneg : 0 ≤ 𝐄 (f * f) := by
  apply mul_nonneg
  · norm_num
  · apply sum_nonneg
    intros x _
    apply mul_self_nonneg

/-- Boolean functions form an inner product space. -/
instance instCoreReal : InnerProductSpace.Core ℝ (BooleanFunc n) where
  inner := fun f g ↦ 𝐄 (f * g)
  conj_inner_symm := by
    intros f g
    simp only [RCLike.conj_to_real]
    rw [mul_comm]
  re_inner_nonneg := by
    intro f
    simp only [RCLike.re_to_real, expectation_prod_self_nonneg]
  add_left := by simp only [add_mul, map_add, implies_true]
  smul_left := by
    simp only [Algebra.smul_mul_assoc, map_smul, smul_eq_mul, RCLike.conj_to_real, implies_true]
  definite := by
    intro f hf
    change 𝐄 (f * f) = 0 at hf
    simp only [expectation, one_div, inv_pow, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply,
      mul_eq_zero, inv_eq_zero] at hf
    have hsum : ∑ i, f i * f i = 0 := by
      rcases hf with hf | hf
      · exact absurd hf (pow_ne_zero _ (by norm_num))
      · exact hf
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ mul_self_nonneg (f i))).mp hsum
    funext i
    have := hzero i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp this

instance (priority := 10000) instNormedAddCommGroupReal : NormedAddCommGroup (BooleanFunc n) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := BooleanFunc n)

instance (priority := 10000) instSeminormedReal : SeminormedAddCommGroup (BooleanFunc n) :=
  NormedAddCommGroup.toSeminormedAddCommGroup

instance (priority := 10000) instNormReal : Norm (BooleanFunc n) :=
  instSeminormedReal.toNorm

instance (priority := 10000) instInnerProductSpaceReal : InnerProductSpace ℝ (BooleanFunc n) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (BooleanFunc n))

/-- Cauchy-Schwarz inequality on Boolean functions -/
theorem cauchy_schwarz : |⟪f, g⟫| ≤ ‖f‖ * ‖g‖ :=
  norm_inner_le_norm (𝕜 := ℝ) f g

@[simp]
lemma walsh_sq_eq_one : (χ S) ^ 2 = 1 := by
  funext x
  unfold walshCharacter
  simp only [Pi.pow_apply, Pi.one_apply]
  rw [← prod_pow]
  ring_nf
  simp

@[simp]
lemma expectation_one : @expectation n 1 = 1 := by simp [expectation]

lemma norm_sq_eq_inner : ‖f‖ ^ 2 = ⟪f, f⟫ := by
  rw [← RCLike.re_to_real (x := ⟪f, f⟫), ← InnerProductSpace.norm_sq_eq_re_inner]

/-- Walsh characters are L² normalized. -/
@[simp]
theorem walsh_norm_one (S : Finset (Fin n)) : ‖χ S‖ = 1 := by
  simp only [norm_eq_sqrt_real_inner, sqrt_eq_one]
  change 𝐄 _ = 1
  rw [← pow_two, walsh_sq_eq_one]
  simp

theorem walsh_inner_self_eq_one : ⟪χ S, χ S⟫ = 1 := by
  rw [← norm_sq_eq_inner, walsh_norm_one, one_pow]

theorem walsh_mul_eq : χ S * χ S' = χ (symmDiff S S') := by
  funext x
  unfold walshCharacter
  simp only [Pi.mul_apply]
  nth_rewrite 1 [← sdiff_union_inter S S']
  nth_rewrite 3 [← sdiff_union_inter S' S]
  repeat rw [prod_union (disjoint_sdiff_inter _ _)]
  rw [inter_comm S]
  ring_nf
  have haux : (∏ i ∈ S' ∩ S, ((-1 : ℝ) ^ (x i).val)) ^ 2 = 1 := by
    rw [← prod_pow]; ring_nf; simp
  rw [haux, mul_one, ← prod_union]
  · rfl
  · simp only [disjoint_iff_ne, mem_sdiff, ne_eq, and_imp]
    intro _ ha _ _ _ _ h
    rw [h] at ha
    contradiction

lemma inner_eq_expectation : ⟪f, g⟫ = 𝐄 (f * g) := rfl

lemma fourier_eq_inner : 𝓕 f S = ⟪χ S, f⟫ := rfl

/-- Flip the `i₀`th bit of `x`. -/
def flipAt (i₀ : Fin n) (x : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i ↦ if i = i₀ then 1 - x i else x i

/-- The `i₀`th bit of `x` is flipped. -/
@[simp]
lemma flipAt_flipped {i₀ : Fin n} {x : Fin n → Fin 2} : flipAt i₀ x i₀ = 1 - x i₀ := by
  unfold flipAt
  split_ifs <;> tauto

/-- Bits that are not the `i₀`th bits remain unchanged. -/
lemma flipAt_unflipped {i i₀ : Fin n} {x : Fin n → Fin 2} (h : i ≠ i₀) : flipAt i₀ x i = x i := by
  unfold flipAt
  split_ifs <;> tauto

/-- Flipping a bit twice results in no change. -/
@[simp]
lemma flipAt_flipAt_eq {i₀ : Fin n} {x : Fin n → Fin 2} : flipAt i₀ (flipAt i₀ x) = x := by
  unfold flipAt
  funext i
  split_ifs
  · rw [sub_sub_cancel]
  · rfl

/-- Flipping a bit is an involution on `Fin n → Fin 2`. -/
theorem flipAt_involutive {i₀ : Fin n} : Function.Involutive (flipAt i₀) := fun _ ↦ flipAt_flipAt_eq

/-- Flipping a bit is a bijection on `Fin n → Fin 2`. -/
theorem flipAt_bijective {i₀ : Fin n} : Function.Bijective (flipAt i₀) :=
    Function.Involutive.bijective (flipAt_involutive)

/-- Expectation of `χ S` is zero if `S` is nonempty -/
@[simp]
theorem expectation_walsh_eq_zero (hS : S.Nonempty) : 𝐄 (χ S) = 0 := by
  change (1 / 2) ^ n * ∑ x, χ S x = 0
  rw [mul_eq_zero]
  right
  obtain ⟨i₀, hi₀⟩ := hS
  let v : Fin n → Fin 2 := Pi.single i₀ 1
  let e : (Fin n → Fin 2) ≃ (Fin n → Fin 2) := Equiv.addRight v
  have h_add_one (b : Fin 2) : (-1 : ℝ) ^ (b + 1).val = - ((-1) ^ b.val) := by
    fin_cases b <;> simp
  have hv_self : v i₀ = 1 := Pi.single_eq_same _ _
  have hv_other : ∀ i, i ≠ i₀ → v i = 0 := fun i hi => Pi.single_eq_of_ne hi _
  have hneg : ∀ x : Fin n → Fin 2, χ S (e x) = - χ S x := by
    intro x
    change ∏ i ∈ S, (-1 : ℝ) ^ (x i + v i).val = - ∏ i ∈ S, (-1) ^ (x i).val
    rw [← Finset.prod_erase_mul S _ hi₀]
    rw [hv_self, h_add_one (x i₀), mul_neg, neg_inj]
    rw [← Finset.prod_erase_mul S _ hi₀]
    refine congr_arg (· * _) ?_
    apply Finset.prod_congr rfl
    intro i hi
    rw [hv_other i (Finset.ne_of_mem_erase hi), add_zero]
  have h_sum := e.sum_comp (χ S)
  simp_rw [hneg, Finset.sum_neg_distrib] at h_sum
  linarith

theorem walsh_orthogonal {S S' : Finset (Fin n)} (h : S ≠ S') : ⟪χ S, χ S'⟫ = 0 := by
  change 𝐄 _ = 0
  rw [walsh_mul_eq]
  apply expectation_walsh_eq_zero
  rwa [symmDiff_nonempty, ne_eq]

theorem walsh_inner_eq : ⟪χ S, χ S'⟫ = oneOn (S = S') := by
  unfold oneOn
  split_ifs with h
  · rw [← h]; exact walsh_inner_self_eq_one
  · exact walsh_orthogonal h

theorem walsh_orthonormal : Orthonormal (ι := Finset (Fin n)) ℝ χ :=
  ⟨walsh_norm_one, @walsh_orthogonal _⟩

/-- Basis of Walsh characters on `BooleanFunc n`. -/
abbrev walshBasis : Basis (ι := Finset (Fin n)) ℝ (BooleanFunc n) :=
  basisOfOrthonormalOfCardEqFinrank (v := χ) walsh_orthonormal (by simp)

/-- Orthonormal basis of Walsh characters on `BooleanFunc n`. -/
abbrev walshOrthonormalBasis : OrthonormalBasis (ι := Finset (Fin n)) ℝ (BooleanFunc n) :=
  Basis.toOrthonormalBasis (basisOfOrthonormalOfCardEqFinrank (v := χ) walsh_orthonormal (by simp))
    (by simp [walsh_orthonormal])

/-- Walsh-Fourier expansion : Every Boolean function is equal to a linear combination of Walsh
characters. -/
theorem walsh_fourier (f : BooleanFunc n) : f = ∑ S : Finset (Fin n), (𝓕 f S) • χ S := by
  convert (OrthonormalBasis.sum_repr' walshOrthonormalBasis f).symm <;> simp; rfl

lemma fourier_walsh : 𝓕 (χ S) S' = oneOn (S' = S) := walsh_inner_eq

/-- Plancherel/Parseval theorem for Boolean functions. -/
theorem inner_eq_sum_fourier : ⟪f, g⟫ = ∑ S : Finset (Fin n), (𝓕 f S) * (𝓕 g S) := by
  conv_lhs => rw [walsh_fourier f, walsh_fourier g]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [inner_smul_left, inner_sum, RCLike.conj_to_real]
  simp_rw [inner_smul_right, walsh_inner_eq]
  rw [Finset.sum_eq_single S]
  · rw [oneOn_true rfl]; ring
  · intros b _ hb
    rw [oneOn_false (fun h => hb h.symm)]; ring
  · intro h; exact absurd (Finset.mem_univ S) h

/-- Plancherel/Parseval theorem for Boolean functions. -/
theorem walsh_plancherel : ‖f‖^2 = ∑ S : Finset (Fin n), |𝓕 f S|^2 := by
  simp_rw [norm_sq_eq_inner, inner_eq_sum_fourier (f := f) (g := f), sq_abs, pow_two]

/-- Set the `i₀`th bit of `x` to `v`. -/
abbrev setAt (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i ↦ if i = i₀ then v else x i

/-- The `i₀`th bit of `setAt i₀ v x` has value `v`. -/
@[simp]
lemma setAt_it (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) : setAt i₀ v x i₀ = v := by
  unfold setAt; split_ifs <;> tauto

/-- Bits other than the `i₀`th bit are unaffected by `setAt`. -/
lemma setAt_other (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) (i : Fin n) (h : i₀ ≠ i) :
    setAt i₀ v x i = x i := by
  unfold setAt; split_ifs <;> tauto

/-- Discrete partial "derivative" of a Boolean function with respect to the `i`th coordinate.
See Def. 2.16 in [odonnell2014]. -/
def dderiv (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun := fun f ↦ fun x ↦ (f (setAt i 0 x) - f (setAt i 1 x)) / 2
  map_add' := by intros; funext; simp only [Pi.add_apply]; ring
  map_smul' := by intros; funext; dsimp; ring

lemma walsh_setAt_eq_ite {v : Fin 2} :
    χ S (setAt i v x) = ite (i ∈ S) ((-1) ^ v.val * χ (S \ {i}) x) (χ S x) := by
  unfold walshCharacter
  split_ifs with h
  · rw [← mul_prod_erase S _ h, setAt_it, erase_eq]
    congr! 4 with j hj
    rw [setAt_other]
    rw [mem_sdiff, mem_singleton] at hj
    symm
    exact hj.right
  · congr! 3 with j hj
    rw [setAt_other]
    by_contra hc
    rw [hc] at h
    exact h hj

theorem dderiv_walsh (i : Fin n) (S : Finset (Fin n)) :
    dderiv i (χ S) = ite (i ∈ S) (χ (S \ {i})) 0 := by
  funext
  simp only [dderiv, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk]
  repeat rw [walsh_setAt_eq_ite]
  split_ifs <;> simp

theorem dderiv_eq_sum_fourier (i : Fin n) (f : BooleanFunc n) :
    dderiv i f = ∑ S ∈ {S | i ∈ S}, 𝓕 f S • χ (S \ {i}) := by
  nth_rewrite 1 [walsh_fourier f]
  rw [map_sum, sum_filter]
  simp_rw [map_smul, dderiv_walsh]
  congr! 1; simp

/-- The `i`th coordinate Laplacian operator as in Def. 2.25 [odonnell2014]. -/
def laplace (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun := fun f ↦ fun x ↦ (f x - f (flipAt i x)) / 2
  map_add' := by intros; funext; simp only [Pi.add_apply]; ring
  map_smul' := by intros; funext; dsimp; ring

lemma setAt_eq_id {v : Fin 2} (h : x i = v) : setAt i v x = x := by
  funext j
  unfold setAt
  split_ifs with hj
  · rw [hj]; symm; assumption
  · rfl

lemma setAt_eq_flipAt {v : Fin 2} (h : x i ≠ v) : setAt i v x = flipAt i x := by
  funext j
  unfold setAt flipAt
  split_ifs with hj
  · rw [hj]; omega
  · rfl

lemma laplace_eq_dderiv (i : Fin n) (f : BooleanFunc n) (x : Fin n → Fin 2) :
    laplace i f x = (-1) ^ (x i).val * (dderiv i f x) := by
  change (f x - _) / 2 = (-1)^_ * ((_ - _) / 2)
  by_cases hx : x i = 0
  · simp only [hx, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_mul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj']
    rw [setAt_eq_id hx, setAt_eq_flipAt (by rw [hx]; trivial)]
  · have hx1 := Fin.eq_one_of_ne_zero (x i) hx
    rw [setAt_eq_id hx1, setAt_eq_flipAt hx]
    simp [hx1]; ring

theorem laplace_walsh (i : Fin n) (S : Finset (Fin n)) :
    laplace i (χ S) = ite (i ∈ S) (χ S) 0 := by
  funext x
  rw [laplace_eq_dderiv, dderiv_walsh]
  split_ifs with h
  · unfold walshCharacter
    rw [← erase_eq, mul_prod_erase (s := S) (a := i) (f := fun i ↦ (-1 : ℝ) ^ (x i).val) h]
  · simp only [Pi.zero_apply, mul_zero]

theorem laplace_eq_sum_fourier (i : Fin n) (f : BooleanFunc n) :
    laplace i f = ∑ S ∈ {S | i ∈ S}, 𝓕 f S • χ (S) := by
  nth_rewrite 1 [walsh_fourier f]
  rw [map_sum, sum_filter, sum_congr (by rfl)]
  intros
  rw [map_smul, laplace_walsh]
  simp

/-- The `i`th influence of a Boolean function is defined as the expectation of the `i`th Laplacian
squared. -/
abbrev influence (f : BooleanFunc n) (i : Fin n) : ℝ := 𝐄 ((laplace i f) ^ 2)

theorem influence_eq_sum_fourier (f : BooleanFunc n) (i : Fin n) :
    influence f i = ∑ S ∈ {S | i ∈ S}, (𝓕 f S) ^ 2 := by
  unfold influence
  nth_rewrite 1 [laplace_eq_sum_fourier]
  rw [pow_two, sum_mul_sum, map_sum, sum_filter]
  conv =>
    enter [1, 2, S]
    conv =>
      arg 2
      rw [map_sum]
      enter [2, S']
      rw [mul_smul_comm, map_smul, smul_mul_assoc, map_smul]
      rw [← inner_eq_expectation, walsh_inner_eq]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_filter,
      mem_univ, true_and, ite_ite_same]
  rw [← sum_filter]
  congr! 1; ring

/-- The total influence of a Boolean function is defined as the sum of the `i`th influences. -/
abbrev totalInfluence (f : BooleanFunc n) : ℝ := ∑ i, influence f i

theorem totalInfluence_eq_sum_fourier (f : BooleanFunc n) :
    totalInfluence f = ∑ S, S.card * (𝓕 f S) ^ 2 := by
  unfold totalInfluence
  conv =>
    enter [1, 2, i]
    rw [influence_eq_sum_fourier f i, sum_filter]
  rw [sum_comm]
  simp

/-- Covariance of two Boolean functions -/
abbrev covariance (f g : BooleanFunc n) : ℝ := 𝐄 (f * g) - 𝐄 f * 𝐄 g

/-- Variance of a Boolean function defined via covariance -/
abbrev variance (f : BooleanFunc n) : ℝ := covariance f f

theorem covariance_eq_sum_fourier (f g : BooleanFunc n) :
    covariance f g = ∑ S ∈ {S : Finset (Fin n) | S.Nonempty}, 𝓕 f S * 𝓕 g S := by
  unfold covariance
  rw [← inner_eq_expectation, inner_eq_sum_fourier]
  simp [Finset.nonempty_iff_ne_empty, Finset.filter_ne', expectation_eq_fourier]

theorem variance_eq_sum_fourier (f : BooleanFunc n) :
    variance f = ∑ S ∈ {S : Finset (Fin n) | S.Nonempty}, (𝓕 f S) ^ 2 := by
  convert covariance_eq_sum_fourier f f; exact pow_two _

/-- L² Poincaré inequality : variance of a Boolean function is ≤ total Influence.
See [odonnell2014], Sec. 2.3. -/
theorem variance_le_totalInfluence (f : BooleanFunc n) : variance f ≤ totalInfluence f := by
  rw [variance_eq_sum_fourier, totalInfluence_eq_sum_fourier, sum_filter]
  gcongr with S
  split_ifs with h
  · nth_rewrite 1 [← one_mul ((𝓕 f S)^2)]
    gcongr
    simp only [Nat.one_le_cast, one_le_card, h]
  · rw [← zero_mul 0]
    gcongr
    · simp only [Nat.cast_nonneg]
    · exact sq_nonneg (𝓕 f S)

/-- The `k`th Fourier weight is the sum of squares of degree `k` Fourier coefficients -/
abbrev fourierWeight (k : ℕ) (f : BooleanFunc n) : ℝ := ∑ S ∈ {S | S.card = k}, |𝓕 f S| ^ 2

/-- Alternative expression for degree one Fourier weight in terms in terms of sum over
coordinates -/
abbrev fourierWeightOne (f : BooleanFunc n) : ℝ := ∑ i, |𝓕 f {i}| ^ 2

lemma fourier_weight_one {f : BooleanFunc n} : fourierWeight 1 f = fourierWeightOne f := by
  apply sum_singletons; intro; rfl

lemma fourier_eq_zero_iff_fourier_weight_eq {k : ℕ} {f : BooleanFunc n} :
    (∀ S, S.card ≠ k → 𝓕 f S = 0) ↔ fourierWeight k f = ‖f‖ ^ 2 := by
  constructor
  · intro h
    have h : ∀ S, S.card ≠ k → |𝓕 f S|^2 = 0 := by
      intro S hS
      simp only [sq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      exact h S hS
    symm
    rw [walsh_plancherel]
    calc
      _ = fourierWeight k f + ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2 := by
        rw [sum_filter_add_sum_filter_not]
      _ = fourierWeight k f + ∑ S, if S.card ≠ k then |𝓕 f S|^2 else 0 := by
        rw [sum_filter]
      _ = fourierWeight k f := by
        conv => {enter [1, 2, 2, S]; rw [rw_ite_left (h S), ite_self]}; simp
  · intro h S hS
    have : ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2 = 0 := by
      symm
      calc
        0 = ‖f‖^2 - ‖f‖^2                           := (sub_self _).symm
        _ = ∑ S, |𝓕 f S|^2 - fourierWeight k f      := by rw [h, walsh_plancherel]
        _ = ∑ S ∈ {S | S.card = k}, |𝓕 f S|^2 + ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2
          - fourierWeight k f                       := by rw [sum_filter_add_sum_filter_not]
        _ = ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2       := by
              rw [add_comm, add_sub_assoc, sub_self, add_zero]
    have := (sum_eq_zero_iff_of_nonneg <| by intro S _; apply pow_two_nonneg).mp this
    specialize this S (by simp [hS])
    rw [sq_abs, pow_eq_zero_iff (by trivial)] at this
    assumption

lemma eq_sum_fourier_of_fourier_weight {k : ℕ} {f : BooleanFunc n}
    (h : fourierWeight k f = ‖f‖ ^ 2) :
    f = ∑ S ∈ {S | S.card = k}, 𝓕 f S • χ S := by
  have hf : ∑ S ∈ {S | S.card ≠ k}, 𝓕 f S • χ S = 0 := by
    rw [sum_eq_zero]
    intro S hS
    rw [smul_eq_zero]
    left
    simp only [ne_eq, mem_filter, mem_univ, true_and] at hS
    exact fourier_eq_zero_iff_fourier_weight_eq.mpr h S hS
  calc
    f = ∑ S, 𝓕 f S • χ S                     := walsh_fourier f
    _ = ∑ S ∈ {S | S.card = k}, 𝓕 f S • χ S +
      ∑ S ∈ {S | S.card ≠ k}, 𝓕 f S • χ S     := by rw [sum_filter_add_sum_filter_not]
    _ = ∑ S ∈ {S | S.card = k}, 𝓕 f S • χ S    := by rw [hf, add_zero]

lemma eq_sum_degree_one_of_fourier_weight_one {f : BooleanFunc n}
    (h : fourierWeight 1 f = ‖f‖ ^ 2) :
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val := by
  intro
  nth_rewrite 1 [eq_sum_fourier_of_fourier_weight h, sum_apply]
  apply sum_singletons
  intro
  simp only [Pi.smul_apply, prod_singleton, smul_eq_mul]

lemma eq_sum_degree_one_of_fourier_eq_zero {f : BooleanFunc n}
    (h : ∀ S, S.card ≠ 1 → 𝓕 f S = 0) :
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val :=
  eq_sum_degree_one_of_fourier_weight_one (fourier_eq_zero_iff_fourier_weight_eq.mp h)

/-- Walsh-Fourier multiplier as an ℝ-linear operator on Boolean functions -/
def multiplier (m : ℕ → ℝ) : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun := fun f ↦ ∑ S : Finset (Fin n), (m S.card) • 𝓕 f S • χ S
  map_add' := by
    intros; ext; dsimp
    repeat rw [sum_apply]
    rw [← sum_add_distrib, sum_congr (by rfl)]
    intros
    simp only [map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' := by
    intros; ext
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, sum_apply, RingHom.id_apply, mul_sum]
    congr! 1; ring

/-- Walsh characters are eigenfunctions of multipliers. -/
lemma multiplier_walsh {m : ℕ → ℝ} {S : Finset (Fin n)} :
    multiplier m (χ S) = (m S.card) • χ S := by
  unfold multiplier
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [1, 2, S']; rw [fourier_walsh]
  simp

/-- The noise operator defined via Fourier expansion. See Prop. 2.47 in [odonnell2014]. -/
abbrev noiseOperator (ρ : ℝ) : BooleanFunc n →ₗ[ℝ] BooleanFunc n := multiplier (ρ^·)

/-- Noise stability -/
abbrev noiseStability (ρ : ℝ) (f : BooleanFunc n) := ⟪f, noiseOperator ρ f⟫

lemma noise_stability_eq_sum_fourier {ρ : ℝ} :
    noiseStability ρ f = ∑ S, ρ^(S.card) * |𝓕 f S|^2 := by
  unfold noiseStability
  nth_rewrite 1 [walsh_fourier f]
  simp only [noiseOperator, multiplier, LinearMap.coe_mk, AddHom.coe_mk]
  rewrite [sum_inner]
  conv => enter [1, 2, S]; rw [inner_smul_left, inner_sum];
          enter [2, 2, S']; rw [inner_smul_right, inner_smul_right, walsh_inner_eq]
  congr! 1; simp; ring

/-- Discrete convolution of Boolean functions -/
abbrev convolution (f g : BooleanFunc n) : BooleanFunc n :=
  fun x ↦ 𝐄 (fun y ↦ (f y) * (g (x + y)))

/-- Discrete convolution of Boolean functions -/
infixl:67 "⋆" => convolution

/-- Convolution theorem : the Walsh-Fourier transform turns convolution into pointwise product. -/
lemma fourier_convolution : 𝓕 (f ⋆ g) = (𝓕 f) * (𝓕 g) := by
  funext S
  unfold fourierTransform convolution expectation
  dsimp
  simp_rw [mul_sum]; rw [sum_comm]
  conv => enter [1, 2, y]; rw [sum_translate y]
  simp_rw [walsh_add]
  rw [sum_comm]
  simp_rw [sum_mul]
  apply sum_congr (by rfl)
  intro y _
  apply sum_congr (by rfl)
  intro x _
  rw [show y + x + x = y by rw [add_assoc, add_self_eq_zero, add_zero]]
  ring

end

end LeanPool.LeanBooleanfun.BooleanFun
