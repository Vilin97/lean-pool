/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Abel
import LeanPool.Monlib4.LinearAlgebra.Matrix.Basic
import LeanPool.Monlib4.LinearAlgebra.Matrix.Conj

/-!
 # Almost Hermitian Matrices

 This file contains the definition and some basic results about almost Hermitian matrices.

 We say a matrix `x` is `is_almost_hermitian` if there exists some scalar `α ∈ ℂ`.
-/


namespace Matrix

variable {𝕜 n : Type _}

open scoped Matrix

/--
a matrix $x \in M_n(\mathbb{k})$ is ``almost Hermitian'' if there exists some $\alpha\in\mathbb{k}$
  and $y\in M_n(\mathbb{k})$ such that $\alpha y = x$ and $y$ is Hermitian -/
def IsAlmostHermitian [Star 𝕜] [SMul 𝕜 (Matrix n n 𝕜)] (x : Matrix n n 𝕜) : Prop :=
  ∃ (α : 𝕜) (y : Matrix n n 𝕜), α • y = x ∧ y.IsHermitian

open scoped Kronecker

open Complex

open scoped ComplexConjugate

/-- $x\in M_n(\mathbb{C})$ is almost Hermitian if and only if $x \otimes_k \bar{x}$ is Hermitian -/
theorem isAlmostHermitian_iff (x : Matrix n n ℂ) : x.IsAlmostHermitian ↔ (x ⊗ₖ xᴴᵀ).IsHermitian :=
  by
  constructor
  · rintro ⟨α, y, ⟨rfl, h⟩⟩
    simp_rw [IsHermitian, conjTranspose_kronecker, conj_conjTranspose, conj_smul, transpose_smul,
      conjTranspose_smul, h.eq, kronecker_smul, smul_kronecker, smul_smul, mul_comm, h.conj]
  · intro h
    simp_rw [IsHermitian, ← Matrix.ext_iff, conjTranspose_apply, kroneckerMap, of_apply,
      conj_apply, star_mul', star_star, mul_comm _ (star _)] at h
    have : ∀ i j : n, x i j = 0 ↔ x j i = 0 := by
      intro i j
      specialize h (i, i) (j, j)
      simp_rw [RCLike.star_def, RCLike.conj_mul] at h
      norm_cast at h
      constructor <;> intro H
      · rw [H, norm_zero, zero_pow (two_ne_zero), sq_eq_zero_iff, norm_eq_zero] at h
        exact h
      · rw [H, norm_zero, zero_pow (two_ne_zero), eq_comm, sq_eq_zero_iff, norm_eq_zero] at h
        exact h
    -- have this1 : ∀ i j : n, x i j = 0 ↔ xᴴ i j = 0 := by
    --   simp_rw [conjTranspose_apply, star_eq_zero, this, forall₂_true_iff]
    by_cases h' : x = 0
    · rw [h']
      use 0; use 0
      simp_rw [zero_smul, isHermitian_zero, true_and]
    -- have hα_pre :
    --   ∀ i j k l : n, x i j ≠ 0 → x k l ≠ 0 → x i j / star (x j i) = x k l / star (x l k) :=
    --   by
    --   intro m₁ m₂ m₃ m₄ hx₁ hx₂
    --   rw [ne_eq, this] at hx₁ hx₂
    --   simp_rw [div_eq_div_iff (star_ne_zero.mpr hx₁) (star_ne_zero.mpr hx₂), mul_comm _ (star _),
    --     RCLike.star_def]
    --   exact h (_, _) (_, _)
    have nonzero_ : ∃ i j : n, x i j ≠ 0 :=
      by
      contrapose! h'
      ext i j
      exact h' i j
    rcases nonzero_ with ⟨i, k, hik⟩
    let α := x i k / star (x k i)
    have hα' : α ≠ 0 :=
      by
      simp_rw [α, div_ne_zero_iff, star_ne_zero, ne_eq, this k i]
      exact ⟨hik, hik⟩
    have Hα : α⁻¹ = conj α := by
      simp_rw [α, ← RCLike.star_def, star_div₀, star_star, inv_div, RCLike.star_def,
        div_eq_div_iff hik ((not_iff_not.mpr (this i k)).mp hik), ← RCLike.star_def,
        h (k, k) (i, i)]
    have conj_ : ∀ α : ℂ, RCLike.normSq α = RCLike.re (conj α * α) := fun α => by
      simp_rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re,
        RCLike.normSq_eq_def']
    have Hα' : Real.sqrt (RCLike.normSq α) = 1 := by
      simp_rw [Real.sqrt_eq_iff_eq_sq (RCLike.normSq_nonneg _) zero_le_one, one_pow, conj_, ← Hα,
        inv_mul_cancel₀ hα', RCLike.one_re]
    have another_hα : ∀ p q : n, x p q ≠ 0 → x p q = α * conj (x q p) :=
      by
      intro p q _
      simp_rw [α, div_mul_eq_mul_div, mul_comm (x i k), ← RCLike.star_def, h (p, _) (_, _), ←
        div_mul_eq_mul_div, ← star_div₀, div_self ((not_iff_not.mpr (this i k)).mp hik), star_one,
        one_mul]
    have : ∃ β : ℂ, β ^ 2 = α := by
      exists α ^ ((2 : ℕ) : ℂ)⁻¹
      exact Complex.cpow_nat_inv_pow α two_ne_zero
    rcases this with ⟨β, hβ⟩
    have hβ' : β ≠ 0 := by
      rw [ne_eq, ← sq_eq_zero_iff, hβ]
      exact hα'
    have hβ'' : β⁻¹ = conj β :=
      by
      rw [← mul_left_inj' hβ', inv_mul_cancel₀ hβ', ← Complex.normSq_eq_conj_mul_self]
      norm_cast
      simp_rw [Complex.normSq_eq_norm_sq, ← Complex.norm_pow, hβ]
      exact Hα'.symm
    have hαβ : β * α⁻¹ = β⁻¹ := by
      rw [← hβ, pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hβ', one_mul]
    use β
    use β⁻¹ • x
    simp_rw [IsHermitian, conjTranspose_smul, ← Matrix.ext_iff, Matrix.smul_apply,
      conjTranspose_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hβ', one_mul,
      forall₂_true_iff, true_and, hβ'', ← Complex.star_def, star_star]
    · intro p q
      by_cases H : x p q = 0
      · simp_rw [H, (this p q).mp H, star_zero, MulZeroClass.mul_zero]
      · calc
          β * star (x q p) = β * star (α * star (x p q)) := ?_
          _ = β * α⁻¹ * x p q := ?_
          _ = star β * x p q := ?_
        · rw [another_hα _ _ ((not_iff_not.mpr (this p q)).mp H), Complex.star_def]
        · rw [star_mul', star_star, mul_comm (star _) (x p q), mul_assoc,
            mul_comm _ (star _), Hα, ← Complex.star_def]
        · simp_rw [hαβ, hβ'', ← Complex.star_def]

/-- 0 is almost Hermitian -/
theorem isAlmostHermitian_zero [Semiring 𝕜] [StarRing 𝕜] : (0 : Matrix n n 𝕜).IsAlmostHermitian :=
  by
  use 0; use 0
  simp_rw [isHermitian_zero, zero_smul, and_true]

/-- if $x$ is almost Hermitian, then it is also normal -/
theorem _root_.Matrix.AlmostHermitian.isStarNormal [Fintype n] [CommSemiring 𝕜] [StarRing 𝕜]
    {M : Matrix n n 𝕜} (hM : M.IsAlmostHermitian) : IsStarNormal M :=
  by
  obtain ⟨α, N, ⟨rfl, hN⟩⟩ := hM
  apply IsStarNormal.mk
  simp_rw [Commute, SemiconjBy, star_smul, smul_mul_smul_comm, star_eq_conjTranspose,
    hN.eq, mul_comm]

/-- $x$ is almost Hermitian if and only if $\beta \cdot x$ is almost Hermitian for any $\beta$ -/
theorem almost_hermitian_iff_smul [CommSemiring 𝕜] [StarRing 𝕜] {M : Matrix n n 𝕜} :
    M.IsAlmostHermitian ↔ ∀ β : 𝕜, (β • M).IsAlmostHermitian :=
  by
  constructor
  · rintro ⟨α, N, ⟨rfl, hN⟩⟩ β
    use β * α
    use N
    simp_rw [smul_smul, true_and, hN]
  · intro h
    specialize h (1 : 𝕜)
    simp_rw [one_smul] at h
    exact h

/-- A matrix whose off-diagonal entries are zero. -/
def IsDiagonal {R n : Type _} [Zero R] (A : Matrix n n R) : Prop :=
  ∀ i j : n, i ≠ j → A i j = 0

theorem isDiagonal_eq {R : Type _} [Zero R] [DecidableEq n] (A : Matrix n n R) :
    A.IsDiagonal ↔ diagonal A.diag = A :=
  by
  simp_rw [← ext_iff, IsDiagonal, diagonal]
  constructor
  · intro h i j
    by_cases H : i = j
    · simp_rw [H, of_apply, if_true, diag]
    · rw [of_apply, h _ _ H, ite_eq_right_iff]
      intros
      contradiction
  · rintro h i j hij
    specialize h i j
    simp_rw [of_apply, hij, if_false] at h
    exact h.symm

open scoped BigOperators

/-- an almost Hermitian matrix is upper-triangular if and only if it is diagonal -/
theorem _root_.Matrix.IsAlmostHermitian.upper_triangular_iff_diagonal [Field 𝕜] [StarRing 𝕜]
    [LinearOrder n] {M : Matrix n n 𝕜} (hM : M.IsAlmostHermitian) :
    M.BlockTriangular id ↔ M.IsDiagonal :=
  by
  rcases hM with ⟨α, N, ⟨rfl, hN⟩⟩
  simp_rw [BlockTriangular, Function.id_def, Matrix.smul_apply]
  constructor
  · intro h i j hij
    by_cases H : j < i
    · exact h H
    · simp_rw [not_lt, le_iff_eq_or_lt, hij, false_or] at H
      specialize h H
      by_cases Hα : α = 0
      · simp_rw [Hα, zero_smul, Matrix.zero_apply]
      · simp_rw [smul_eq_zero, Hα, false_or] at h
        rw [← hN.eq]
        simp_rw [Matrix.smul_apply, conjTranspose_apply, h, star_zero, smul_zero]
  · intro h i j hij
    exact h i j (ne_of_lt hij).symm

theorem _root_.Matrix.IsHermitian.isAlmostHermitian [Semiring 𝕜] [Star 𝕜] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) : x.IsAlmostHermitian :=
  by
  use 1
  use x
  rw [one_smul]
  exact ⟨rfl, hx⟩

end Matrix
