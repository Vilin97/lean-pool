/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.BlockMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Hilbert Finite -/

namespace Homogenization

/-!
This file provides finite-dimensional Hilbert realizations of `\R^d` and
`\R^{2d}` that stay compatible with the project's anti-`EuclideanSpace`
architecture.

The ambient algebraic carriers remain

- `Vec d = Fin d → ℝ`,
- `BlockVec d = Vec d × Vec d`.

Those are excellent lightweight types for most of the development, but their
default normed-space instances are not the Euclidean `L²` ones needed for the
Hilbert-space part of the coarse-graining theory. For that role we introduce
separate wrappers built from `PiLp 2`.
-/

/-- The Euclidean Hilbert realization of `\R^d`, presented without exposing
`EuclideanSpace` in the public API. -/
abbrev HilbertVec (d : ℕ) := PiLp 2 (fun _ : Fin d => ℝ)

namespace HilbertVec

/-- Promote the project's algebraic vector carrier into the Euclidean Hilbert
carrier. -/
abbrev ofVec {d : ℕ} (x : Vec d) : HilbertVec d :=
  WithLp.toLp 2 x

/-- Forget the Hilbert structure and return to the project's algebraic vector
carrier. -/
abbrev toVec {d : ℕ} (x : HilbertVec d) : Vec d :=
  fun i => x i

@[simp] theorem toVec_ofVec {d : ℕ} (x : Vec d) : (ofVec x).toVec = x := by
  funext i
  exact PiLp.toLp_apply 2 (fun _ : Fin d => ℝ) x i

@[simp] theorem ofVec_toVec {d : ℕ} (x : HilbertVec d) : ofVec x.toVec = x := by
  apply PiLp.ext
  intro i
  simp [toVec]

@[ext] theorem ext {d : ℕ} {x y : HilbertVec d} (h : ∀ i, x i = y i) : x = y :=
  PiLp.ext h

/-- Algebraic identification between the Euclidean Hilbert carrier and the
project's lightweight vector carrier. -/
def linearEquivVec (d : ℕ) : HilbertVec d ≃ₗ[ℝ] Vec d where
  toFun := toVec
  invFun := ofVec
  left_inv := ofVec_toVec
  right_inv := toVec_ofVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Continuous linear identification between the Euclidean Hilbert carrier and
the project's lightweight vector carrier. -/
noncomputable def continuousLinearEquivVec (d : ℕ) : HilbertVec d ≃L[ℝ] Vec d :=
  (linearEquivVec d).toContinuousLinearEquiv

@[simp] theorem continuousLinearEquivVec_apply {d : ℕ} (x : HilbertVec d) :
    continuousLinearEquivVec d x = x.toVec :=
  rfl

@[simp] theorem continuousLinearEquivVec_symm_apply {d : ℕ} (x : Vec d) :
    (continuousLinearEquivVec d).symm x = ofVec x :=
  rfl

@[simp] theorem inner_def {d : ℕ} (x y : HilbertVec d) :
    inner ℝ x y = vecDot x.toVec y.toVec := by
  rw [PiLp.inner_apply, vecDot]
  simp_rw [RCLike.inner_apply]
  congr with i
  simp [toVec, mul_comm]

@[simp] theorem norm_sq_eq_sum_sq {d : ℕ} (x : HilbertVec d) :
    ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  simpa [sq_abs] using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin d => ℝ) x)

theorem abs_apply_le_norm {d : ℕ} (x : HilbertVec d) (i : Fin d) :
    |x i| ≤ ‖x‖ := by
  have hcoord :
      |x i| ^ 2 ≤ ∑ j : Fin d, x j ^ 2 := by
    calc
      |x i| ^ 2 = x i ^ 2 := by rw [sq_abs]
      _ ≤ ∑ j : Fin d, x j ^ 2 := by
            simpa using
              (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (by simp : i ∈ Finset.univ))
  have hsq : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    calc
      |x i| ^ 2 ≤ ∑ j : Fin d, x j ^ 2 := hcoord
      _ = ‖x‖ ^ 2 := by rw [← norm_sq_eq_sum_sq]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

theorem norm_toVec_le_norm {d : ℕ} (x : HilbertVec d) :
    ‖x.toVec‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_
  intro i
  simpa [toVec, Real.norm_eq_abs] using abs_apply_le_norm x i

theorem norm_le_norm_ofVec {d : ℕ} (x : Vec d) :
    ‖x‖ ≤ ‖ofVec x‖ := by
  simpa using norm_toVec_le_norm (ofVec x)

theorem norm_ofVec_le_mul_norm {d : ℕ} (x : Vec d) :
    ‖ofVec x‖ ≤ (d : ℝ) * ‖x‖ := by
  have hcoord : ∀ i : Fin d, x i ^ 2 ≤ ‖x‖ ^ 2 := by
    intro i
    exact sq_le_sq.mpr <| by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using norm_le_pi_norm x i
  have hsum :
      ∑ i : Fin d, x i ^ 2 ≤ (d : ℝ) * ‖x‖ ^ 2 := by
    calc
      ∑ i : Fin d, x i ^ 2 ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
            exact Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * ‖x‖ ^ 2 := by
            simp [nsmul_eq_mul]
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  have hd_le_sq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    cases Nat.eq_zero_or_pos d with
    | inl hd0 =>
        simp [hd0]
    | inr hdpos =>
        exact_mod_cast (show d ≤ d ^ 2 by
          simpa [pow_two] using Nat.le_mul_of_pos_left d hdpos)
  have hsq :
      ‖ofVec x‖ ^ 2 ≤ ((d : ℝ) * ‖x‖) ^ 2 := by
    calc
      ‖ofVec x‖ ^ 2 = ∑ i : Fin d, x i ^ 2 := by
            exact norm_sq_eq_sum_sq (ofVec x)
      _ ≤ (d : ℝ) * ‖x‖ ^ 2 := hsum
      _ ≤ (d : ℝ) ^ 2 * ‖x‖ ^ 2 := by
            gcongr
      _ = ((d : ℝ) * ‖x‖) ^ 2 := by
            ring
  have hright_nonneg : 0 ≤ (d : ℝ) * ‖x‖ := mul_nonneg hd_nonneg (norm_nonneg _)
  exact le_of_sq_le_sq hsq hright_nonneg

/-- Continuous linear promotion from the project's algebraic vector carrier to
the Euclidean Hilbert carrier. -/
noncomputable abbrev ofVecL (d : ℕ) : Vec d →L[ℝ] HilbertVec d :=
  ((continuousLinearEquivVec d).symm).toContinuousLinearMap

@[simp] theorem ofVecL_apply {d : ℕ} (x : Vec d) :
    ofVecL d x = ofVec x :=
  rfl

theorem norm_ofVecL_le (d : ℕ) : ‖ofVecL d‖ ≤ (d : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  simpa [ofVecL_apply] using norm_ofVec_le_mul_norm x

theorem norm_continuousLinearEquivVec_le (d : ℕ) :
    ‖(continuousLinearEquivVec d).toContinuousLinearMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simpa using norm_toVec_le_norm x

end HilbertVec

/-- The Euclidean Hilbert realization of `d × d` real matrices. The algebraic
carrier `Mat d` keeps its lightweight pointwise role; this wrapper is for
Hilbert-space measurability and `L²` arguments. -/
abbrev HilbertMat (d : ℕ) := PiLp 2 (fun _ : Fin d => HilbertVec d)

namespace HilbertMat

/-- Promote the project's algebraic matrix carrier into the Euclidean Hilbert
matrix carrier. -/
abbrev ofMat {d : ℕ} (A : Mat d) : HilbertMat d :=
  WithLp.toLp 2 (fun i : Fin d => HilbertVec.ofVec (fun j : Fin d => A i j))

/-- Forget the Hilbert structure and return to the project's algebraic matrix
carrier. -/
abbrev toMat {d : ℕ} (A : HilbertMat d) : Mat d :=
  fun i j => A i j

@[simp] theorem toMat_ofMat {d : ℕ} (A : Mat d) : (ofMat A).toMat = A := by
  ext i j
  simp [toMat]

@[simp] theorem ofMat_toMat {d : ℕ} (A : HilbertMat d) : ofMat A.toMat = A := by
  apply PiLp.ext
  intro i
  apply HilbertVec.ext
  intro j
  simp [toMat]

@[ext] theorem ext {d : ℕ} {A B : HilbertMat d} (h : ∀ i j, A i j = B i j) :
    A = B := by
  apply PiLp.ext
  intro i
  apply HilbertVec.ext
  intro j
  exact h i j

/-- Algebraic identification between the Euclidean Hilbert matrix carrier and
the project's lightweight matrix carrier. -/
def linearEquivMat (d : ℕ) : HilbertMat d ≃ₗ[ℝ] Mat d where
  toFun := toMat
  invFun := ofMat
  left_inv := ofMat_toMat
  right_inv := toMat_ofMat
  map_add' _ _ := by
    ext i j
    simp [toMat]
  map_smul' _ _ := by
    ext i j
    simp [toMat]

/-- Continuous linear identification between the Euclidean Hilbert matrix
carrier and the project's lightweight matrix carrier. -/
noncomputable def continuousLinearEquivMat (d : ℕ) : HilbertMat d ≃L[ℝ] Mat d :=
  (linearEquivMat d).toContinuousLinearEquiv

@[simp] theorem continuousLinearEquivMat_apply {d : ℕ} (A : HilbertMat d) :
    continuousLinearEquivMat d A = A.toMat :=
  rfl

@[simp] theorem continuousLinearEquivMat_symm_apply {d : ℕ} (A : Mat d) :
    (continuousLinearEquivMat d).symm A = ofMat A :=
  rfl

/-- The `(i,j)` matrix coordinate as a continuous linear functional on the
Hilbert matrix carrier. -/
noncomputable def entryL {d : ℕ} (i j : Fin d) : HilbertMat d →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => HilbertVec d) i)

@[simp] theorem entryL_apply {d : ℕ} (i j : Fin d) (A : HilbertMat d) :
    entryL i j A = A i j :=
  rfl

@[simp] theorem entryL_ofMat {d : ℕ} (i j : Fin d) (A : Mat d) :
    entryL i j (ofMat A) = A i j := by
  simp [entryL, ofMat]

theorem abs_apply_sub_apply_le_norm {d : ℕ} (A B : HilbertMat d) (i j : Fin d) :
    |A i j - B i j| ≤ ‖A - B‖ := by
  calc
    |A i j - B i j| = |(A - B) i j| := by simp
    _ ≤ ‖(A - B) i‖ := HilbertVec.abs_apply_le_norm ((A - B) i) j
    _ ≤ ‖A - B‖ := PiLp.norm_apply_le (A - B) i

theorem lipschitzWith_entry {d : ℕ} (i j : Fin d) :
    LipschitzWith 1 (fun A : HilbertMat d => A i j) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro A B
  simpa [Real.dist_eq, dist_eq_norm] using abs_apply_sub_apply_le_norm A B i j

@[simp] theorem inner_def {d : ℕ} (A B : HilbertMat d) :
    inner ℝ A B = ∑ i, ∑ j, A i j * B i j := by
  rw [PiLp.inner_apply]
  simp [HilbertVec.inner_def, vecDot]

end HilbertMat

/-- The Euclidean Hilbert realization of `\R^{2d}`, viewed as a doubled
potential/flux carrier. -/
abbrev HilbertBlockVec (d : ℕ) := PiLp 2 (fun _ : Fin 2 => HilbertVec d)

namespace HilbertBlockVec

/-- The potential component of a doubled Hilbert vector. -/
abbrev potential {d : ℕ} (X : HilbertBlockVec d) : HilbertVec d :=
  X 0

/-- The flux component of a doubled Hilbert vector. -/
abbrev flux {d : ℕ} (X : HilbertBlockVec d) : HilbertVec d :=
  X 1

/-- Promote the project's algebraic doubled vector carrier into the Euclidean
Hilbert carrier. -/
abbrev ofBlockVec {d : ℕ} (X : BlockVec d) : HilbertBlockVec d :=
  WithLp.toLp 2 ![HilbertVec.ofVec X.1, HilbertVec.ofVec X.2]

/-- Forget the Hilbert structure and return to the project's algebraic doubled
vector carrier. -/
abbrev toBlockVec {d : ℕ} (X : HilbertBlockVec d) : BlockVec d :=
  (X.potential.toVec, X.flux.toVec)

@[simp] theorem potential_ofBlockVec {d : ℕ} (X : BlockVec d) :
    (ofBlockVec X).potential = HilbertVec.ofVec X.1 := by
  simp [potential]

@[simp] theorem flux_ofBlockVec {d : ℕ} (X : BlockVec d) :
    (ofBlockVec X).flux = HilbertVec.ofVec X.2 := by
  simp [flux]

@[simp] theorem toBlockVec_ofBlockVec {d : ℕ} (X : BlockVec d) :
    (ofBlockVec X).toBlockVec = X := by
  rcases X with ⟨p, q⟩
  simp [toBlockVec]

@[simp] theorem ofBlockVec_toBlockVec {d : ℕ} (X : HilbertBlockVec d) :
    ofBlockVec X.toBlockVec = X := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [potential, flux]

@[ext] theorem ext {d : ℕ} {X Y : HilbertBlockVec d}
    (hpot : X.potential = Y.potential) (hflux : X.flux = Y.flux) : X = Y := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simpa [potential] using hpot
  · simpa [flux] using hflux

/-- Algebraic identification between the Euclidean doubled Hilbert carrier and
the project's lightweight block carrier. -/
def linearEquivBlockVec (d : ℕ) : HilbertBlockVec d ≃ₗ[ℝ] BlockVec d where
  toFun := toBlockVec
  invFun := ofBlockVec
  left_inv := ofBlockVec_toBlockVec
  right_inv := toBlockVec_ofBlockVec
  map_add' X Y := by
    ext i <;> simp [toBlockVec, potential, flux]
  map_smul' c X := by
    ext i <;> simp [toBlockVec, potential, flux]

/-- Continuous linear identification between the Euclidean doubled Hilbert
carrier and the project's lightweight block carrier. -/
noncomputable def continuousLinearEquivBlockVec (d : ℕ) : HilbertBlockVec d ≃L[ℝ] BlockVec d :=
  (linearEquivBlockVec d).toContinuousLinearEquiv

@[simp] theorem continuousLinearEquivBlockVec_apply {d : ℕ} (X : HilbertBlockVec d) :
    continuousLinearEquivBlockVec d X = X.toBlockVec :=
  rfl

@[simp] theorem continuousLinearEquivBlockVec_symm_apply {d : ℕ} (X : BlockVec d) :
    (continuousLinearEquivBlockVec d).symm X = ofBlockVec X :=
  rfl

/-- A block matrix acts continuously on the Euclidean Hilbert realization of
`\R^{2d}` by conjugating the algebraic action through the canonical
identification `HilbertBlockVec d ≃L[ℝ] BlockVec d`. -/
noncomputable def applyBlockMat {d : ℕ} (A : BlockMat d) :
    HilbertBlockVec d →L[ℝ] HilbertBlockVec d :=
  ((continuousLinearEquivBlockVec d).symm.toContinuousLinearMap).comp
    ((blockMatContinuousLinearMap A).comp
      (continuousLinearEquivBlockVec d).toContinuousLinearMap)

@[simp] theorem applyBlockMat_apply {d : ℕ} (A : BlockMat d) (X : HilbertBlockVec d) :
    applyBlockMat A X = ofBlockVec (blockMatVecMul A X.toBlockVec) := by
  simp [applyBlockMat]

@[simp] theorem inner_def {d : ℕ} (X Y : HilbertBlockVec d) :
    inner ℝ X Y = blockVecDot X.toBlockVec Y.toBlockVec := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [blockVecDot, HilbertVec.inner_def]

@[simp] theorem inner_ofBlockVec_applyBlockMat {d : ℕ} (A : BlockMat d)
    (X Y : BlockVec d) :
    inner ℝ (ofBlockVec X) (applyBlockMat A (ofBlockVec Y)) =
      blockVecDot X (blockMatVecMul A Y) := by
  simp [applyBlockMat_apply, inner_def]

@[simp] theorem norm_sq_ofBlockVec {d : ℕ} (X : BlockVec d) :
    ‖ofBlockVec X‖ ^ 2 = blockVecDot X X := by
  rw [← real_inner_self_eq_norm_sq, inner_def, toBlockVec_ofBlockVec]

@[simp] theorem norm_sq_eq_blockVecDot {d : ℕ} (X : HilbertBlockVec d) :
    ‖X‖ ^ 2 = blockVecDot X.toBlockVec X.toBlockVec := by
  simpa [ofBlockVec_toBlockVec X] using norm_sq_ofBlockVec X.toBlockVec

@[simp] theorem norm_sq_applyBlockMat {d : ℕ} (A : BlockMat d) (X : HilbertBlockVec d) :
    ‖applyBlockMat A X‖ ^ 2 =
      blockVecDot (blockMatVecMul A X.toBlockVec) (blockMatVecMul A X.toBlockVec) := by
  rw [applyBlockMat_apply, norm_sq_ofBlockVec]

theorem opNorm_applyBlockMat_le_of_block_bound {d : ℕ} {A : BlockMat d} {C : ℝ}
    (hC : 0 ≤ C)
    (hA : ∀ X : BlockVec d,
      blockVecDot (blockMatVecMul A X) (blockMatVecMul A X) ≤ C ^ 2 * blockVecDot X X) :
    ‖applyBlockMat A‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC ?_
  intro X
  have hsq :
      ‖applyBlockMat A X‖ ^ 2 ≤ (C * ‖X‖) ^ 2 := by
    calc
      ‖applyBlockMat A X‖ ^ 2
        = blockVecDot (blockMatVecMul A X.toBlockVec) (blockMatVecMul A X.toBlockVec) := by
            rw [norm_sq_applyBlockMat]
      _ ≤ C ^ 2 * blockVecDot X.toBlockVec X.toBlockVec := hA X.toBlockVec
      _ = C ^ 2 * ‖X‖ ^ 2 := by
            rw [norm_sq_eq_blockVecDot]
      _ = (C * ‖X‖) ^ 2 := by
            ring
  have hCnorm_nonneg : 0 ≤ C * ‖X‖ := mul_nonneg hC (norm_nonneg X)
  have habs : |‖applyBlockMat A X‖| ≤ |C * ‖X‖| := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCnorm_nonneg] using habs

@[simp] theorem norm_sq_eq_components {d : ℕ} (X : HilbertBlockVec d) :
    ‖X‖ ^ 2 = ‖X.potential‖ ^ 2 + ‖X.flux‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

@[simp] theorem norm_sq_eq_sum_sq {d : ℕ} (X : HilbertBlockVec d) :
    ‖X‖ ^ 2 = ∑ i, X.potential i ^ 2 + ∑ i, X.flux i ^ 2 := by
  rw [norm_sq_eq_components, HilbertVec.norm_sq_eq_sum_sq, HilbertVec.norm_sq_eq_sum_sq]

end HilbertBlockVec

end Homogenization
