/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef

/-!
# Three-column kernel data

Feature vectors, the Gram matrix `𝒜`, moment scalars, and the auxiliary
functions of `docs/sol.tex` §3 (`sec:kernel`, `eq:functions`). Coordinates of
`ℝ³` are numbered `0,1,2`.
-/

@[expose] public section

namespace BollobasNikiforov

open Matrix
open scoped Matrix

noncomputable section

/-- Feature vector `v(t) = (1, -√2 t, t²)ᵀ`. -/
def v (t : ℝ) : Fin 3 → ℝ :=
  ![1, -Real.sqrt 2 * t, t ^ 2]

/-- Feature vector `b(x) = (x², √2 x, 1)ᵀ`. -/
def b (x : ℝ) : Fin 3 → ℝ :=
  ![x ^ 2, Real.sqrt 2 * x, 1]

/-- Truncated square `aᵢ(x) = (x - tᵢ)₊²`. -/
def truncSq (ti x : ℝ) : ℝ :=
  (max (x - ti) 0) ^ 2

/-- The outer product `v vᵀ` is Hermitian. -/
lemma isHermitian_vecMulVec_self (w : Fin 3 → ℝ) :
    (vecMulVec w w).IsHermitian := by
  ext i j
  simp [conjTranspose_apply, vecMulVec_apply, mul_comm]

/-- `(v vᵀ) x = (v ⬝ x) v`. -/
lemma mulVec_vecMulVec_self (w x : Fin 3 → ℝ) :
    vecMulVec w w *ᵥ x = (w ⬝ᵥ x) • w := by
  simp [vecMulVec_mulVec]

/-- The quadratic form of an outer product is a square: `x ⬝ (v vᵀ) x = (v ⬝ x)²`. -/
lemma dotProduct_mulVec_vecMulVec_self (w x : Fin 3 → ℝ) :
    x ⬝ᵥ vecMulVec w w *ᵥ x = (w ⬝ᵥ x) ^ 2 := by
  rw [mulVec_vecMulVec_self, dotProduct_smul, smul_eq_mul, dotProduct_comm x, ← sq]

/-- The outer product `v vᵀ` is positive semidefinite. -/
lemma posSemidef_vecMulVec_self_fin3 (w : Fin 3 → ℝ) :
    (vecMulVec w w).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_vecMulVec_self w) fun x ↦ ?_
  simpa [show star x = x from funext fun _ ↦ star_trivial _,
    dotProduct_mulVec_vecMulVec_self] using sq_nonneg (w ⬝ᵥ x)

@[simp] lemma v_zero (s : ℝ) : v s 0 = 1 := by simp [v]
@[simp] lemma v_one (s : ℝ) : v s 1 = -Real.sqrt 2 * s := by simp [v]
@[simp] lemma v_two (s : ℝ) : v s 2 = s ^ 2 := by simp [v]

variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)

/-- Gram matrix `𝒜 = I₃ + ∑ᵢ qᵢ v(tᵢ) v(tᵢ)ᵀ`. -/
def 𝒜 : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + ∑ i, q i • vecMulVec (v (t i)) (v (t i))

/-- `𝒜` is positive definite: the identity is PD and each summand is PSD. -/
lemma 𝒜_posDef (hq : ∀ i, 0 < q i) : (𝒜 t q).PosDef := by
  unfold 𝒜
  refine PosDef.add_posSemidef PosDef.one ?_
  exact posSemidef_sum _ fun i _ ↦
    PosSemidef.smul (posSemidef_vecMulVec_self_fin3 (v (t i))) (hq i).le

/-- Positive definite matrices are invertible. -/
lemma 𝒜_isUnit (hq : ∀ i, 0 < q i) : IsUnit (𝒜 t q) :=
  (𝒜_posDef t q hq).isUnit

/-- Moments `mⱼ = ∑ᵢ qᵢ tᵢʲ`. -/
def m (j : ℕ) : ℝ :=
  ∑ i, q i * t i ^ j

lemma m_zero : m t q 0 = ∑ i, q i := by
  simp [m]

/-- Scalar `a₀ = 1 + m₀`. -/
def a0 : ℝ :=
  1 + m t q 0

/-- Scalar `D₂ = a₀(1 + 2 m₂) - 2 m₁²`. -/
def D2 : ℝ :=
  a0 t q * (1 + 2 * m t q 2) - 2 * m t q 1 ^ 2

/-- Scalar `Δ = det 𝒜`. -/
def Δ : ℝ :=
  (𝒜 t q).det

/-- Vector `V = 𝒜 e₀`. -/
def Vvec : Fin 3 → ℝ :=
  𝒜 t q *ᵥ Pi.single 0 1

/-! ### KR04: principal minors of `𝒜` -/

lemma 𝒜_apply (i j : Fin 3) :
    𝒜 t q i j =
      (if i = j then (1 : ℝ) else 0) + ∑ r, q r * v (t r) i * v (t r) j := by
  simp only [𝒜, Matrix.add_apply, Matrix.one_apply, add_right_inj]
  rw [Matrix.sum_apply]
  simp [Matrix.smul_apply, vecMulVec_apply, mul_assoc]

lemma 𝒜_00 : 𝒜 t q 0 0 = a0 t q := by
  rw [𝒜_apply, a0, m_zero]
  simp

lemma 𝒜_11 : 𝒜 t q 1 1 = 1 + 2 * m t q 2 := by
  rw [𝒜_apply]
  simp only [↓reduceIte, v_one, m]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine congrArg (1 + ·) ?_
  calc
    ∑ r, q r * (-Real.sqrt 2 * t r) * (-Real.sqrt 2 * t r)
        = ∑ r, 2 * (q r * t r ^ 2) := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          calc
            q r * (-Real.sqrt 2 * t r) * (-Real.sqrt 2 * t r)
                = q r * (Real.sqrt 2 * t r) * (Real.sqrt 2 * t r) := by ring
              _ = q r * (Real.sqrt 2 * Real.sqrt 2 * (t r * t r)) := by ring
              _ = q r * (2 * t r ^ 2) := by simp [hsq, sq]
              _ = 2 * (q r * t r ^ 2) := by ring
    _ = 2 * ∑ r, q r * t r ^ 2 := (Finset.mul_sum _ _ _).symm

lemma 𝒜_01 : 𝒜 t q 0 1 = -Real.sqrt 2 * m t q 1 := by
  rw [𝒜_apply, ite_eq_right (by decide : (0 : Fin 3) ≠ 1)]
  simp only [v_zero, v_one, mul_one, zero_add, m, pow_one]
  calc
    ∑ r, q r * (-Real.sqrt 2 * t r)
        = ∑ r, -Real.sqrt 2 * (q r * t r) := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          ring
    _ = -Real.sqrt 2 * ∑ r, q r * t r := (Finset.mul_sum _ _ _).symm

lemma 𝒜_10 : 𝒜 t q 1 0 = -Real.sqrt 2 * m t q 1 := by
  rw [𝒜_apply, ite_eq_right (by decide : (1 : Fin 3) ≠ 0)]
  simp only [v_zero, v_one, mul_one, zero_add, m, pow_one]
  calc
    ∑ r, q r * (-Real.sqrt 2 * t r)
        = ∑ r, -Real.sqrt 2 * (q r * t r) := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          ring
    _ = -Real.sqrt 2 * ∑ r, q r * t r := (Finset.mul_sum _ _ _).symm

/-- `D₂` is the leading `2×2` principal minor of `𝒜`. -/
lemma D2_eq_det_leading :
    D2 t q = ((𝒜 t q).submatrix Fin.castSucc Fin.castSucc).det := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have c0 : Fin.castSucc (0 : Fin 2) = 0 := rfl
  have c1 : Fin.castSucc (1 : Fin 2) = 1 := rfl
  have hprod :
      (-Real.sqrt 2 * m t q 1) * (-Real.sqrt 2 * m t q 1) = 2 * m t q 1 ^ 2 := by
    calc
      (-Real.sqrt 2 * m t q 1) * (-Real.sqrt 2 * m t q 1)
          = Real.sqrt 2 * m t q 1 * (Real.sqrt 2 * m t q 1) := by ring
      _ = Real.sqrt 2 * Real.sqrt 2 * (m t q 1 * m t q 1) := by ring
      _ = 2 * m t q 1 ^ 2 := by simp [hsq, sq]
  rw [det_fin_two]
  simp only [submatrix_apply, c0, c1, 𝒜_00, 𝒜_11, 𝒜_01, 𝒜_10, D2, hprod]

lemma Δ_pos (hq : ∀ i, 0 < q i) : 0 < Δ t q :=
  PosDef.det_pos (𝒜_posDef t q hq)

lemma D2_pos (hq : ∀ i, 0 < q i) : 0 < D2 t q := by
  rw [D2_eq_det_leading]
  exact PosDef.det_pos ((𝒜_posDef t q hq).submatrix (Fin.castSucc_injective 2))

/-! ### KR05: auxiliary functions -/

/-- `h(x) = ∑ᵢ qᵢ aᵢ(x)`. -/
def h (x : ℝ) : ℝ :=
  ∑ i, q i * truncSq (t i) x

/-- `h₁(x) = ∑ᵢ qᵢ tᵢ aᵢ(x)`. -/
def h1 (x : ℝ) : ℝ :=
  ∑ i, q i * t i * truncSq (t i) x

/-- `b̂(x) = b(x) + ∑ᵢ qᵢ aᵢ(x) v(tᵢ)`. -/
def bhat (x : ℝ) : Fin 3 → ℝ :=
  b x + ∑ i, (q i * truncSq (t i) x) • v (t i)

/-- `U(x) = b̂(x) + (h(x)/γ) V`. -/
def U (γ x : ℝ) : Fin 3 → ℝ :=
  bhat t q x + (h t q x / γ) • Vvec t q

/-- The Gram update `𝒜 + VVᵀ/γ` before inversion. -/
def 𝒦Mat (γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  𝒜 t q + (1 / γ) • vecMulVec (Vvec t q) (Vvec t q)

lemma 𝒦Mat_posDef (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    (𝒦Mat t q γ).PosDef := by
  unfold 𝒦Mat
  refine PosDef.add_posSemidef (𝒜_posDef t q hq) ?_
  exact PosSemidef.smul (posSemidef_vecMulVec_self_fin3 _) (div_nonneg zero_le_one hγ.le)

lemma 𝒦Mat_isUnit (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) :
    IsUnit (𝒦Mat t q γ) :=
  (𝒦Mat_posDef t q γ hq hγ).isUnit

/-- `𝒦 = (𝒜 + VVᵀ/γ)⁻¹`. -/
def 𝒦 (γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (𝒦Mat t q γ)⁻¹

/-- `N(x) = Δ e₂ᵀ 𝒜⁻¹ b̂(x)`. -/
def N (x : ℝ) : ℝ :=
  Δ t q * ((𝒜 t q)⁻¹ *ᵥ bhat t q x) 2

/-- `P(x) = a₀ x + m₁ x² + m₁ h(x) − a₀ h₁(x)`. -/
def P (x : ℝ) : ℝ :=
  a0 t q * x + m t q 1 * x ^ 2 + m t q 1 * h t q x - a0 t q * h1 t q x

/-- `Z(x) = γ x² + (γ + a₀) h(x)`. -/
def Z (γ x : ℝ) : ℝ :=
  γ * x ^ 2 + (γ + a0 t q) * h t q x

/-! ### KR06: `𝒜⁻¹ V = e₀` -/

lemma 𝒜_inv_mulVec_Vvec (hq : ∀ i, 0 < q i) :
    (𝒜 t q)⁻¹ *ᵥ Vvec t q = Pi.single 0 1 := by
  have := (𝒜_isUnit t q hq).invertible
  exact inv_mulVec_eq_vec rfl

end

end BollobasNikiforov
