/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import LeanPool.Monlib4.LinearAlgebra.End
import LeanPool.Monlib4.LinearAlgebra.Ips.Pos
import LeanPool.Monlib4.LinearAlgebra.Ips.RankOne
import LeanPool.Monlib4.LinearAlgebra.Matrix.Basic
import LeanPool.Monlib4.Preq.Ites
import LeanPool.Monlib4.Preq.RCLikeLe

/-!
# Positivity of matrices and linear maps

Compatibility wrappers for the part of Monlib's matrix-positive API now covered by Mathlib.
-/

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the map associated to its conjugate
transpose. -/
theorem conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    A.conjTranspose.toEuclideanLin = LinearMap.adjoint A.toEuclideanLin :=
  Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

end Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜]

open Matrix
open scoped Matrix ComplexOrder

alias Matrix.posSemidef_star_mul_self := Matrix.posSemidef_conjTranspose_mul_self
alias Matrix.posSemidef_mul_star_self := Matrix.posSemidef_self_mul_conjTranspose

theorem Matrix.toEuclideanLin_eq_piLp_linearEquiv [Fintype n] [DecidableEq n] :
    Matrix.toEuclideanLin (𝕜 := 𝕜) (m := n) (n := n) =
      Matrix.toLin (PiLp.basisFun 2 𝕜 n) (PiLp.basisFun 2 𝕜 n) := by
  simpa [Matrix.toEuclideanLin] using
    Matrix.toLpLin_eq_toLin (R := 𝕜) (m := n) (n := n) 2 2

open scoped InnerProductSpace

lemma Matrix.of_isHermitian' [Fintype n] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    ∀ x_1 : n → 𝕜, ↑(RCLike.re (Finset.sum Finset.univ fun i ↦
      (star x_1 i * Finset.sum Finset.univ fun x_2 ↦ x i x_2 * x_1 x_2))) =
          Finset.sum Finset.univ fun x_2 ↦
            star x_1 x_2 * Finset.sum Finset.univ fun x_3 ↦ x x_2 x_3 * x_1 x_3 := by
  classical
  simp_rw [← RCLike.conj_eq_iff_re]
  have hinner : ∀ x_1 : n → 𝕜,
      (Finset.sum Finset.univ fun i ↦ star x_1 i *
        Finset.sum Finset.univ fun x_2 ↦ x i x_2 * x_1 x_2) =
        ⟪(EuclideanSpace.equiv n 𝕜).symm x_1,
          (toEuclideanLin x) ((EuclideanSpace.equiv n 𝕜).symm x_1)⟫_𝕜 := fun x_1 => by
    calc (Finset.sum Finset.univ fun i ↦ star x_1 i *
        Finset.sum Finset.univ fun x_2 ↦ x i x_2 * x_1 x_2)
        = ⟪x_1, x *ᵥ x_1⟫_𝕜 := by simp [inner, mul_comm, mulVec, dotProduct]
      _ = ⟪(EuclideanSpace.equiv n 𝕜).symm x_1,
          (EuclideanSpace.equiv n 𝕜).symm (x *ᵥ x_1)⟫_𝕜 := rfl
      _ = ⟪(EuclideanSpace.equiv n 𝕜).symm x_1,
          (toEuclideanLin x) ((EuclideanSpace.equiv n 𝕜).symm x_1)⟫_𝕜 := rfl
  simp_rw [hinner, inner_conj_symm, ← LinearMap.adjoint_inner_left,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hx.eq, forall_true_iff]

theorem Matrix.posSemidef_eq_linearMap_positive' [Fintype n] [DecidableEq n]
    (x : Matrix n n 𝕜) :
    x.PosSemidef ↔ x.toEuclideanLin.IsPositive' := by
  rw [LinearMap.isPositive'_iff_isPositive]
  exact Matrix.isPositive_toEuclideanLin_iff.symm

open scoped MatrixOrder

theorem Matrix.posSemidef_iff [Fintype n] (x : Matrix n n 𝕜) :
    x.PosSemidef ↔ ∃ y : Matrix n n 𝕜, x = yᴴ * y := by
  classical
  rw [← Matrix.nonneg_iff_posSemidef]
  simpa [Matrix.star_eq_conjTranspose] using
    (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := x))

local notation "⟪" x "," y "⟫_𝕜" => @inner 𝕜 _ _ x y

open scoped BigOperators

theorem Matrix.dotProduct_eq_inner {n : Type*} [Fintype n] (x y : n → 𝕜) :
    dotProduct (star x) y = ∑ i : n, ⟪x i, y i⟫_𝕜 := by
  simp [dotProduct, RCLike.inner_apply, mul_comm]

theorem Matrix.isHermitian_self_hMul_conjTranspose {m n : Type*} [Fintype m]
    (A : Matrix m n 𝕜) :
    (Aᴴ * A).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self A

theorem Matrix.trace_star [Fintype n] {A : Matrix n n 𝕜} : star A.trace = Aᴴ.trace := by
  rw [Matrix.trace_conjTranspose]

theorem Matrix.nonneg_eigenvalues_of_posSemidef [Fintype n] [DecidableEq n]
    {μ : ℝ} {A : Matrix n n 𝕜}
    (hμ : Module.End.HasEigenvalue (toEuclideanLin A) ↑μ) (H : A.PosSemidef) :
    0 ≤ μ := by
  have hpos := Matrix.isPositive_toEuclideanLin_iff.mpr H
  exact eigenvalue_nonneg_of_nonneg hμ fun v => by
    rw [← hpos.1 v v]
    exact hpos.2 v

theorem Matrix.IsHermitian.nonneg_eigenvalues_of_posSemidef [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i : n) :
    0 ≤ hA.1.eigenvalues i :=
  hA.eigenvalues_nonneg i

/-- A matrix is invertible when its associated linear map is bijective. -/
@[reducible]
noncomputable def Matrix.invertibleOfBijToLin' [Fintype n] [DecidableEq n]
    {Q : Matrix n n 𝕜} (h : Function.Bijective (toLin' Q)) :
    Invertible Q := by
  have h : Invertible (toLin' Q) := by
    refine IsUnit.invertible ?_
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective h.1
  refine IsUnit.invertible ?_
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [← LinearMap.det_toLin']
  apply LinearMap.isUnit_det
  rw [← nonempty_invertible_iff_isUnit]
  exact Nonempty.intro h

lemma Matrix.bij_toLin'_of_invertible [Fintype n] [DecidableEq n]
    {Q : Matrix n n 𝕜} (h : Invertible Q) :
    Function.Bijective (toLin' Q) := by
  simp_rw [Function.bijective_iff_has_inverse]
  use (toLin' ⅟ Q)
  simp only [Function.LeftInverse, Function.RightInverse, ← toLin'_mul_apply,
    Invertible.invOf_mul_self, mul_invOf_self, toLin'_one, and_self,
    LinearMap.id_apply, forall_true_iff]

theorem Matrix.PosSemidef.invertibleIff_posDef {n : Type*} [Fintype n]
    [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.PosSemidef) :
    Function.Bijective (toLin' x) ↔ x.PosDef := by
  have hbij_isUnit : Function.Bijective (toLin' x) ↔ IsUnit x := by
    constructor
    · intro h
      exact (nonempty_invertible_iff_isUnit x).mp ⟨Matrix.invertibleOfBijToLin' h⟩
    · intro h
      rcases (nonempty_invertible_iff_isUnit x).mpr h with ⟨hInv⟩
      exact Matrix.bij_toLin'_of_invertible hInv
  rw [hbij_isUnit, hx.posDef_iff_isUnit]

/-- A positive definite matrix is invertible. -/
@[reducible]
noncomputable def Matrix.PosDef.invertible [Fintype n] [DecidableEq n] {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) :
    Invertible Q :=
  hQ.isUnit.invertible

theorem Matrix.posSemidef_iff_vecMulVec [Finite n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
        x = ∑ i : Fin m, vecMulVec (v i : n → 𝕜) (star (v i : n → 𝕜)) := by
  constructor
  · intro h
    rcases (Matrix.posSemidef_iff_eq_sum_vecMulVec (𝕜 := 𝕜) (M := x)).mp h with
      ⟨m, v, hv⟩
    exact ⟨m, fun i => WithLp.toLp 2 (v i), by simpa using hv⟩
  · rintro ⟨m, v, hv⟩
    apply (Matrix.posSemidef_iff_eq_sum_vecMulVec (𝕜 := 𝕜) (M := x)).mpr
    exact ⟨m, fun i => (v i : n → 𝕜), by simpa using hv⟩

theorem vecMulVec_posSemidef [Finite n] (x : n → 𝕜) :
    (vecMulVec x (star x)).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star x

/-- The identity is a positive definite matrix. -/
theorem Matrix.posDefOne [DecidableEq n] : (1 : Matrix n n 𝕜).PosDef :=
  Matrix.PosDef.one

alias Matrix.PosDef.pos_eigenvalues := Matrix.PosDef.eigenvalues_pos

theorem Matrix.PosDef.trace_ne_zero [Fintype n] [Nonempty n]
    {x : Matrix n n 𝕜} (hx : x.PosDef) :
    x.trace ≠ 0 := by
  exact ne_of_gt hx.trace_pos

/-- A positive definite matrix has trace with positive real part. -/
theorem Matrix.PosDef.pos_trace [Fintype n] [Nonempty n]
    {x : Matrix n n 𝕜} (hx : x.PosDef) :
    0 < RCLike.re x.trace :=
  (RCLike.pos_def.mp hx.trace_pos).1

/-- The Euclidean linear map associated to a matrix acts by matrix-vector multiplication. -/
lemma Matrix.toEuclideanLin_apply' [Fintype n] [DecidableEq n]
    (x : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) :
    x.toEuclideanLin v = x.mulVec v :=
  rfl

namespace rankOne

theorem _root_.rankOne.EuclideanSpace.toEuclideanLin_symm {𝕜 : Type*} [RCLike 𝕜] {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    Matrix.toEuclideanLin.symm (rankOne 𝕜 x y).toLinearMap =
      Matrix.replicateCol (Fin 1) (x : n → 𝕜) *
        (Matrix.replicateCol (Fin 1) (y : m → 𝕜))ᴴ := by
  have hrank : (rankOne 𝕜 x y).toLinearMap =
      (InnerProductSpace.rankOne 𝕜 x y).toLinearMap := by
    ext z i
    rfl
  rw [hrank, InnerProductSpace.symm_toEuclideanLin_rankOne]
  rw [Matrix.vecMulVec_eq (Fin 1), Matrix.conjTranspose_replicateCol]
  rfl

theorem _root_.rankOne.EuclideanSpace.toMatrix' {𝕜 : Type*} [RCLike 𝕜] {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    Matrix.toEuclideanLin.symm (rankOne 𝕜 x y).toLinearMap =
      Matrix.replicateCol (Fin 1) (x : n → 𝕜) *
        (Matrix.replicateCol (Fin 1) (y : m → 𝕜))ᴴ :=
  rankOne.EuclideanSpace.toEuclideanLin_symm x y

theorem _root_.rankOne.Pi.toMatrix'' {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] (x y : n → 𝕜) :
    Matrix.toEuclideanLin.symm
        (rankOne 𝕜 ((EuclideanSpace.equiv n 𝕜).symm x)
          ((EuclideanSpace.equiv n 𝕜).symm y)).toLinearMap =
      Matrix.replicateCol (Fin 1) x * (Matrix.replicateCol (Fin 1) y)ᴴ :=
  rankOne.EuclideanSpace.toEuclideanLin_symm _ _

end rankOne

theorem Matrix.vecMulVec_eq_replicateCol_conjTranspose (v : n → 𝕜) :
    vecMulVec v (star v) = replicateCol (Fin 1) v * (replicateCol (Fin 1) v)ᴴ := by
  rw [Matrix.conjTranspose_replicateCol]
  rw [Matrix.vecMulVec_eq (Fin 1)]
  rfl

theorem Matrix.posSemidef_iff_replicateCol_mul_conjTranspose_replicateCol [Finite n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
        x =
          ∑ i : Fin m,
            replicateCol (Fin 1) (v i : n → 𝕜) *
              (replicateCol (Fin 1) (v i : n → 𝕜))ᴴ := by
  rw [Matrix.posSemidef_iff_vecMulVec]
  constructor <;> rintro ⟨m, v, hv⟩ <;> refine ⟨m, v, ?_⟩
  · simpa only [Matrix.vecMulVec_eq_replicateCol_conjTranspose] using hv
  · simpa only [Matrix.vecMulVec_eq_replicateCol_conjTranspose] using hv

theorem Matrix.posSemidef_iff_vecMulVec' [Finite n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : Type) (_hm : Fintype m) (v : m → EuclideanSpace 𝕜 n),
        x = ∑ i : m, vecMulVec (v i : n → 𝕜) (star (v i : n → 𝕜)) := by
  constructor
  · intro hx
    rcases (Matrix.posSemidef_iff_vecMulVec.mp hx) with ⟨m, v, hv⟩
    exact ⟨Fin m, inferInstance, v, hv⟩
  · rintro ⟨m, hm, v, hv⟩
    letI := hm
    rw [Matrix.posSemidef_iff_vecMulVec]
    let v' : Fin (Fintype.card m) → EuclideanSpace 𝕜 n :=
      fun i => v ((Fintype.equivFin m).symm i)
    refine ⟨Fintype.card m, v', ?_⟩
    rw [hv]
    exact Fintype.sum_equiv (Fintype.equivFin m)
      (fun i => vecMulVec (v i : n → 𝕜) (star (v i : n → 𝕜)))
      (fun i => vecMulVec (v' i : n → 𝕜) (star (v' i : n → 𝕜)))
      (by intro i; simp [v'])

theorem Matrix.posSemidef_iff_replicateCol_mul_conjTranspose_replicateCol' [Finite n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : Type) (_hm : Fintype m) (v : m → EuclideanSpace 𝕜 n),
        x =
          ∑ i : m,
            replicateCol (Fin 1) (v i : n → 𝕜) *
              (replicateCol (Fin 1) (v i : n → 𝕜))ᴴ := by
  rw [Matrix.posSemidef_iff_vecMulVec']
  constructor <;> rintro ⟨m, hm, v, hv⟩ <;> refine ⟨m, hm, v, ?_⟩
  · simpa only [Matrix.vecMulVec_eq_replicateCol_conjTranspose] using hv
  · simpa only [Matrix.vecMulVec_eq_replicateCol_conjTranspose] using hv

theorem Matrix.posSemidef_iff_eq_rankOne [Fintype n] [DecidableEq n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
        x = ∑ i : Fin m, Matrix.toEuclideanLin.symm (rankOne 𝕜 (v i) (v i)).toLinearMap := by
  rw [Matrix.posSemidef_iff_replicateCol_mul_conjTranspose_replicateCol]
  simp_rw [rankOne.EuclideanSpace.toEuclideanLin_symm]

theorem Matrix.posSemidef_iff_eq_rankOne' [Fintype n] [DecidableEq n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → (n → 𝕜)),
        x =
          ∑ i : Fin m,
            Matrix.toEuclideanLin.symm
              (rankOne 𝕜 ((EuclideanSpace.equiv n 𝕜).symm (v i))
                ((EuclideanSpace.equiv n 𝕜).symm (v i))).toLinearMap := by
  rw [Matrix.posSemidef_iff_eq_rankOne]
  constructor
  · rintro ⟨m, v, hv⟩
    exact ⟨m, fun i => (v i : n → 𝕜), by simpa using hv⟩
  · rintro ⟨m, v, hv⟩
    exact ⟨m, fun i => (EuclideanSpace.equiv n 𝕜).symm (v i), by simpa using hv⟩

theorem Matrix.posSemidef_iff_eq_rankOne'' [Fintype n] [DecidableEq n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : Type) (_hm : Fintype m) (v : m → (n → 𝕜)),
        x =
          ∑ i : m,
            Matrix.toEuclideanLin.symm
              (rankOne 𝕜 ((EuclideanSpace.equiv n 𝕜).symm (v i))
                ((EuclideanSpace.equiv n 𝕜).symm (v i))).toLinearMap := by
  rw [Matrix.posSemidef_iff_replicateCol_mul_conjTranspose_replicateCol']
  constructor
  · rintro ⟨m, hm, v, hv⟩
    exact ⟨m, hm, fun i => (v i : n → 𝕜), by simpa only [← rankOne.Pi.toMatrix''] using hv⟩
  · rintro ⟨m, hm, v, hv⟩
    exact ⟨m, hm, fun i => (EuclideanSpace.equiv n 𝕜).symm (v i),
      by
        rw [hv]
        simp_rw [rankOne.Pi.toMatrix'']
        rfl⟩

/-- For complex matrices, positive semidefiniteness is equivalent to nonnegative quadratic
forms. -/
theorem Matrix.PosSemidef.complex [Fintype n] (x : Matrix n n ℂ) :
    x.PosSemidef ↔ ∀ y : n → ℂ, 0 ≤ star y ⬝ᵥ x.mulVec y := by
  classical
  rw [Matrix.posSemidef_eq_linearMap_positive' x, LinearMap.complex_isPositive']
  constructor
  · intro h y
    specialize h (WithLp.toLp 2 y)
    simpa [Matrix.toLpLin_toLp, PiLp.inner_apply, Matrix.dotProduct_eq_inner,
      RCLike.inner_apply, Matrix.mulVec] using h
  · intro h v
    let y : n → ℂ := v
    specialize h y
    simpa [y, Matrix.toLpLin_toLp, PiLp.inner_apply, Matrix.dotProduct_eq_inner,
      RCLike.inner_apply, Matrix.mulVec] using h

theorem PosSemidef.complex [Fintype n] (x : Matrix n n ℂ) :
    x.PosSemidef ↔ ∀ y : n → ℂ, 0 ≤ star y ⬝ᵥ x.mulVec y :=
  Matrix.PosSemidef.complex x

theorem single.sum_eq_one [Fintype n] [DecidableEq n] (a : 𝕜) :
    ∑ k : n, single k k a = a • 1 := by
  rw [Matrix.one_eq_sum_std_matrix]
  simp_rw [Finset.smul_sum, Matrix.smul_single, smul_eq_mul, mul_one]

theorem single_hMul [Fintype n] [DecidableEq n] (i j k l : n) (a b : 𝕜) :
    single i j a * single k l b =
      ite (j = k) (1 : 𝕜) (0 : 𝕜) • single i l (a * b) := by
  ext p q
  rw [Matrix.single.hMul_stdBasisMatrix i p j k l q a b]
  by_cases hip : i = p <;> by_cases hjk : j = k <;> by_cases hlq : l = q <;>
    simp [Matrix.smul_apply, Matrix.single, smul_eq_mul, hip, hjk, hlq]

theorem Matrix.smul_single' {n R : Type*} [CommSemiring R] [DecidableEq n] (i j : n)
    (c : R) :
    single i j c = c • single i j 1 := by
  rw [smul_single, smul_eq_mul, mul_one]

theorem Matrix.trace_iff' [Fintype n] (x : Matrix n n 𝕜) : x.trace = ∑ i : n, x i i :=
  rfl

theorem existsUnique_trace [Fintype n] [DecidableEq n] [Nontrivial n] :
    ∃! φ : Matrix n n 𝕜 →ₗ[𝕜] 𝕜,
      (∀ a b : Matrix n n 𝕜, φ (a * b) = φ (b * a)) ∧ φ 1 = 1 := by
  use (1 / Fintype.card n : 𝕜) • traceLinearMap n 𝕜 𝕜
  have trace_functional_iff :
      ∀ φ : Matrix n n 𝕜 →ₗ[𝕜] 𝕜,
        (∀ a b : Matrix n n 𝕜, φ (a * b) = φ (b * a)) ∧ φ 1 = 1 ↔
          φ = (1 / Fintype.card n : 𝕜) • traceLinearMap n 𝕜 𝕜 := by
    intro φ
    have hcard_inv : (↑(Fintype.card n) : 𝕜)⁻¹ * ↑(@Finset.univ n _).card = 1 := by
      rw [inv_mul_eq_one₀]
      · rfl
      · simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero]
        exact not_false
    constructor
    · intro h
      rw [LinearMap.ext_iff]
      intro x
      have hsingle :
          ∀ i j : n,
            φ (single i j (1 : 𝕜)) =
              (1 / (Fintype.card n : 𝕜)) • ite (j = i) (1 : 𝕜) (0 : 𝕜) := by
        intro i j
        calc
          φ (single i j (1 : 𝕜)) =
              (1 / (Fintype.card n : 𝕜)) •
                ∑ k, φ (single i k 1 * (single k j 1 : Matrix n n 𝕜)) := ?_
          _ =
              (1 / (Fintype.card n : 𝕜)) •
                ∑ k, φ (single k j 1 * single i k 1) := ?_
          _ = (1 / (Fintype.card n : 𝕜)) •
              ite (j = i) (φ (∑ k, single k k 1)) 0 := ?_
          _ = (1 / (Fintype.card n : 𝕜)) • ite (j = i) (φ 1) 0 := ?_
          _ = (1 / (Fintype.card n : 𝕜)) • ite (j = i) 1 0 := ?_
        · simp_rw [single_mul_single_same, one_mul]
          simp only [one_div, Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
          rw [← mul_assoc]
          simp_rw [hcard_inv, one_mul]
        · simp_rw [h.1]
        · simp_rw [single_hMul, one_mul, _root_.map_smul, smul_eq_mul, boole_mul,
            Finset.sum_ite_irrel, Finset.sum_const_zero, map_sum]
        · simp_rw [single.sum_eq_one, one_smul]
        · simp_rw [h.2]
      rw [LinearMap.smul_apply, Matrix.traceLinearMap_apply]
      nth_rw 1 [matrix_eq_sum_single x]
      simp_rw [Matrix.smul_single' _ _ (x _ _), map_sum, _root_.map_smul]
      calc
        ∑ x_1, ∑ x_2, x x_1 x_2 • φ (single x_1 x_2 1) =
            ∑ x_1, ∑ x_2,
              x x_1 x_2 • (1 / (Fintype.card n : 𝕜)) •
                ite (x_2 = x_1) (1 : 𝕜) 0 := ?_
        _ = ∑ x_1, x x_1 x_1 • (1 / Fintype.card n : 𝕜) := ?_
        _ = (1 / Fintype.card n : 𝕜) • x.trace := ?_
      · simp_rw [← hsingle]
      · simp_rw [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          smul_eq_mul, mul_one]
      · simp_rw [← Finset.sum_smul, Matrix.trace_iff' x, smul_eq_mul, mul_comm]
    · rintro rfl
      simp_rw [LinearMap.smul_apply, traceLinearMap_apply, Matrix.trace_iff' 1, one_apply_eq,
        Finset.sum_const, one_div, nsmul_eq_mul, mul_one]
      refine ⟨fun x y => ?_, hcard_inv⟩
      rw [trace_mul_comm]
  simp only [trace_functional_iff, imp_self, forall_true_iff, and_true]

theorem Matrix.single.trace [Fintype n] [DecidableEq n] (i j : n) (a : 𝕜) :
    (single i j a).trace = ite (i = j) a 0 := by
  by_cases h : i = j
  · subst h
    simp [Matrix.trace_single_eq_same]
  · simp [Matrix.trace_single_eq_of_ne i j a h, h]

theorem Matrix.single_eq {R n m : Type*} [Semiring R] [DecidableEq n] [DecidableEq m]
    (i : n) (j : m) (a : R) :
    single i j a = fun i' j' => ite (i = i' ∧ j = j') a 0 :=
  rfl

theorem vecMulVec_eq_zero_iff (x : n → 𝕜) : vecMulVec x (star x) = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact Matrix.vecMulVec_ne_zero hx (by simpa using hx) h
  · intro h
    simp [h]

lemma norm_ite {α : Type*} [Norm α] (P : Prop) [Decidable P] (a b : α) :
    ‖(ite P a b : α)‖ = (ite P ‖a‖ ‖b‖) := by
  split_ifs <;> rfl

theorem Matrix.PosSemidef.diagonal_iff [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosSemidef ↔ ∀ i, 0 ≤ x i :=
  Matrix.posSemidef_diagonal_iff

theorem Matrix.PosDef.diagonal_iff [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosDef ↔ ∀ i, 0 < x i :=
  Matrix.posDef_diagonal_iff

theorem Matrix.toLin_piLp_eq_toLin' {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.toLpLin (R := 𝕜) (m := n) (n := n) 2 2 =
      Matrix.toLin (PiLp.basisFun 2 𝕜 n) (PiLp.basisFun 2 𝕜 n) := by
  exact Matrix.toLpLin_eq_toLin (R := 𝕜) (m := n) (n := n) 2 2

alias Matrix.commute_iff := Matrix.IsHermitian.commute_iff

namespace Matrix

theorem _root_.Matrix.Finset.sum_abs_eq_zero_iff' {s : Type*} [Fintype s] {x : s → 𝕜} :
    ∑ i, ‖x i‖ ^ 2 = 0 ↔ ∀ i : s, ‖x i‖ ^ 2 = 0 := by
  have hnonneg : ∀ i : s, 0 ≤ ‖x i‖ ^ 2 := fun i => sq_nonneg _
  constructor
  · intro h i
    have hnonneg_mem : ∀ i : s, i ∈ Finset.univ → 0 ≤ ‖x i‖ ^ 2 := by
      intro i _
      exact hnonneg i
    have hsum : ∑ i, ‖(x i : 𝕜)‖ ^ 2 = 0 := h
    rw [Finset.sum_eq_zero_iff_of_nonneg hnonneg_mem] at hsum
    simp only [Finset.mem_univ, forall_true_left] at hsum
    exact hsum i
  · intro h
    simp_rw [h, Finset.sum_const_zero]

/-- The trace of `xᴴ * x` is nonnegative. -/
theorem trace_conjTranspose_hMul_self_nonneg {m : Type*} [Fintype m] [Fintype n]
    (x : Matrix m n 𝕜) :
    0 ≤ (xᴴ * x).trace :=
  (Matrix.posSemidef_conjTranspose_mul_self x).trace_nonneg

/-- A positive semidefinite matrix gives a nonnegative weighted `xᴴ * x` trace. -/
theorem _root_.Matrix.PosSemidef.trace_conjTranspose_hMul_self_nonneg {m : Type*}
    [Fintype m] [Fintype n] {Q : Matrix m m 𝕜}
    (hQ : Q.PosSemidef) (x : Matrix n m 𝕜) :
    0 ≤ (Q * xᴴ * x).trace := by
  classical
  rcases (Matrix.posSemidef_iff Q).mp hQ with ⟨y, rfl⟩
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  nth_rw 1 [← conjTranspose_conjTranspose x]
  rw [← Matrix.conjTranspose_mul]
  simp_rw [Matrix.mul_assoc]
  exact Matrix.trace_conjTranspose_hMul_self_nonneg _

/-- The trace of `xᴴ * x` vanishes exactly when `x` is zero. -/
theorem trace_conjTranspose_hMul_self_eq_zero {m : Type*} [Fintype n] [Fintype m]
    (x : Matrix n m 𝕜) :
    (xᴴ * x).trace = 0 ↔ x = 0 :=
  Matrix.trace_conjTranspose_mul_self_eq_zero_iff

/-- A positive definite matrix gives a faithful weighted `xᴴ * x` trace. -/
theorem _root_.Matrix.PosDef.trace_conjTranspose_hMul_self_eq_zero {m : Type*}
    [Fintype m] [Fintype n] {Q : Matrix m m 𝕜}
    (hQ : Q.PosDef) {x : Matrix n m 𝕜} :
    (Q * xᴴ * x).trace = 0 ↔ x = 0 := by
  classical
  rcases (Matrix.posSemidef_iff Q).mp hQ.posSemidef with ⟨y, hy⟩
  rw [hy, trace_mul_cycle, ← Matrix.mul_assoc]
  nth_rw 1 [← conjTranspose_conjTranspose x]
  rw [← conjTranspose_mul]
  simp_rw [Matrix.mul_assoc]
  rw [Matrix.trace_conjTranspose_hMul_self_eq_zero _]
  constructor
  · intro h
    have hQx : Q * xᴴ = 0 := by
      rw [hy, Matrix.mul_assoc, h, Matrix.mul_zero]
    letI := hQ.invertible
    have hxT : xᴴ = 0 := by
      exact (Matrix.mul_right_injective_of_invertible (A := Q)) (by simpa using hQx)
    rwa [← Matrix.conjTranspose_eq_zero]
  · intro h
    rw [h, conjTranspose_zero, Matrix.mul_zero]

alias _root_.Matrix.Nontracial.trace_conjTranspose_hMul_self_eq_zero :=
  _root_.Matrix.PosDef.trace_conjTranspose_hMul_self_eq_zero

/-- Hermitian weighted traces are conjugate symmetric. -/
theorem _root_.Matrix.IsHermitian.trace_conj_symm_star_hMul {m : Type*} [Fintype m] [Fintype n]
    {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (x y : Matrix n m 𝕜) :
    (starRingEnd 𝕜) (Q * yᴴ * x).trace = (Q * xᴴ * y).trace := by
  simp_rw [starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, hQ.eq, Matrix.mul_assoc]
  rw [trace_mul_cycle']

/-- `xᴴ * x` vanishes exactly when `x` is zero. -/
theorem conjTranspose_hMul_self_eq_zero {m : Type*} [Fintype n]
    (x : Matrix n m 𝕜) :
    xᴴ * x = 0 ↔ x = 0 :=
  Matrix.conjTranspose_mul_self_eq_zero

theorem _root_.Matrix.PosSemidef.replicateColMulConjTransposereplicateCol [Finite n]
    (x : n → 𝕜) :
    (replicateCol (Fin 1) x * (replicateCol (Fin 1) x)ᴴ : Matrix n n 𝕜).PosSemidef := by
  rw [← Matrix.vecMulVec_eq_replicateCol_conjTranspose]
  exact Matrix.posSemidef_vecMulVec_self_star x

end Matrix
