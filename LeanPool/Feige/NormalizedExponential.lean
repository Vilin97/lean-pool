/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.SimplexGeometry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Normalized exponentials and simplex coordinates

This file begins the change of variables behind the identification of
normalized independent exponentials with the uniform simplex law.  We use
the product model `ℝ × (Fin n → ℝ)`: the first target coordinate is `E₀`,
and the remaining coordinates are `Eᵢ`.

The forward map is

`(t,x) ↦ (t(1-∑xᵢ), fun i ↦ t xᵢ)`,

and its inverse divides all nonzero-total vectors by their total mass.
-/

open scoped BigOperators ENNReal
open Set
open MeasureTheory

namespace Feige

variable {n : ℕ}

/-- Total mass of an `E₀,E₁,...,Eₙ` vector in product coordinates. -/
def exponentialTotal (e : ℝ × (Fin n → ℝ)) : ℝ :=
  e.1 + ∑ i, e.2 i

/-- Polar/simplex coordinate map used for normalized exponentials. -/
def exponentialSimplexForward
    (z : ℝ × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (z.1 * (1 - ∑ i, z.2 i), fun i ↦ z.1 * z.2 i)

/-- Inverse normalized-coordinate map.  It is used only on the domain where
the total is positive. -/
noncomputable def exponentialSimplexInverse
    (e : ℝ × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (exponentialTotal e, fun i ↦ e.2 i / exponentialTotal e)

/-- Natural source domain for the change of variables. -/
def exponentialSimplexSource : Set (ℝ × (Fin n → ℝ)) :=
  {z | 0 < z.1 ∧ z.2 ∈ fullSimplex (Fin n)}

/-- Nonnegative exponential vectors with nonzero total mass. -/
def positiveExponentialOrthant : Set (ℝ × (Fin n → ℝ)) :=
  {e | 0 ≤ e.1 ∧ (∀ i, 0 ≤ e.2 i) ∧ 0 < exponentialTotal e}

theorem continuous_exponentialTotal :
    Continuous (exponentialTotal : (ℝ × (Fin n → ℝ)) → ℝ) := by
  unfold exponentialTotal
  fun_prop

theorem continuous_exponentialSimplexForward :
    Continuous (exponentialSimplexForward :
      (ℝ × (Fin n → ℝ)) → ℝ × (Fin n → ℝ)) := by
  unfold exponentialSimplexForward
  fun_prop

theorem measurable_exponentialSimplexForward :
    Measurable (exponentialSimplexForward :
      (ℝ × (Fin n → ℝ)) → ℝ × (Fin n → ℝ)) :=
  continuous_exponentialSimplexForward.measurable

theorem measurable_exponentialSimplexInverse :
    Measurable (exponentialSimplexInverse :
      (ℝ × (Fin n → ℝ)) → ℝ × (Fin n → ℝ)) := by
  unfold exponentialSimplexInverse exponentialTotal
  fun_prop

theorem isMeasurableSet_exponentialSimplexSource :
    MeasurableSet (exponentialSimplexSource :
      Set (ℝ × (Fin n → ℝ))) := by
  exact (isOpen_lt continuous_const continuous_fst).measurableSet.inter
    (measurableSet_fullSimplex.preimage measurable_snd)

theorem isMeasurableSet_positiveExponentialOrthant :
    MeasurableSet (positiveExponentialOrthant :
      Set (ℝ × (Fin n → ℝ))) := by
  have hfirst : MeasurableSet {e : ℝ × (Fin n → ℝ) | 0 ≤ e.1} :=
    measurableSet_le measurable_const measurable_fst
  have hcoords : MeasurableSet {e : ℝ × (Fin n → ℝ) | ∀ i, 0 ≤ e.2 i} := by
    simp only [← Set.mem_Ici]
    exact isClosed_Ici.measurableSet.preimage measurable_snd
  have htotal : MeasurableSet
      {e : ℝ × (Fin n → ℝ) | 0 < exponentialTotal e} :=
    measurableSet_lt measurable_const continuous_exponentialTotal.measurable
  exact hfirst.inter (hcoords.inter htotal)

theorem exponentialTotal_forward (z : ℝ × (Fin n → ℝ)) :
    exponentialTotal (exponentialSimplexForward z) = z.1 := by
  simp only [exponentialTotal, exponentialSimplexForward]
  rw [← Finset.mul_sum]
  ring

theorem exponentialSimplexForward_mem
    {z : ℝ × (Fin n → ℝ)} (hz : z ∈ exponentialSimplexSource) :
    exponentialSimplexForward z ∈ positiveExponentialOrthant := by
  rcases hz with ⟨ht, hx0, hxsum⟩
  refine ⟨mul_nonneg ht.le (sub_nonneg.mpr hxsum), ?_, ?_⟩
  · intro i
    exact mul_nonneg ht.le (hx0 i)
  · rw [exponentialTotal_forward]
    exact ht

theorem exponentialSimplexInverse_mem
    {e : ℝ × (Fin n → ℝ)} (he : e ∈ positiveExponentialOrthant) :
    exponentialSimplexInverse e ∈ exponentialSimplexSource := by
  rcases he with ⟨he0, hei, ht⟩
  refine ⟨ht, ?_⟩
  rw [mem_fullSimplex_iff]
  constructor
  · intro i
    exact div_nonneg (hei i) ht.le
  · simp only [exponentialSimplexInverse]
    rw [← Finset.sum_div]
    rw [div_le_one ht]
    unfold exponentialTotal
    linarith

theorem exponentialSimplexInverse_forward
    {z : ℝ × (Fin n → ℝ)} (hz : z ∈ exponentialSimplexSource) :
    exponentialSimplexInverse (exponentialSimplexForward z) = z := by
  rcases hz with ⟨ht, hx⟩
  apply Prod.ext
  · exact exponentialTotal_forward z
  · funext i
    change
      (exponentialSimplexForward z).2 i /
          exponentialTotal (exponentialSimplexForward z) = z.2 i
    rw [exponentialTotal_forward]
    simp only [exponentialSimplexForward]
    exact mul_div_cancel_left₀ (z.2 i) ht.ne'

theorem exponentialSimplexForward_inverse
    {e : ℝ × (Fin n → ℝ)} (he : e ∈ positiveExponentialOrthant) :
    exponentialSimplexForward (exponentialSimplexInverse e) = e := by
  rcases he with ⟨he0, hei, ht⟩
  apply Prod.ext
  · change exponentialTotal e *
        (1 - ∑ i, e.2 i / exponentialTotal e) = e.1
    rw [← Finset.sum_div]
    field_simp [ht.ne']
    unfold exponentialTotal
    ring
  · funext i
    simp only [exponentialSimplexForward, exponentialSimplexInverse]
    exact mul_div_cancel₀ (e.2 i) ht.ne'

/-- The coordinate change is a bijection between its natural source and
target domains. -/
theorem exponentialSimplex_bijOn :
    Set.BijOn (exponentialSimplexForward (n := n))
      (exponentialSimplexSource (n := n))
      (positiveExponentialOrthant (n := n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact exponentialSimplexForward_mem hz
  · intro z hz w hw hzw
    rw [← exponentialSimplexInverse_forward hz,
      ← exponentialSimplexInverse_forward hw, hzw]
  · intro e he
    exact ⟨exponentialSimplexInverse e,
      exponentialSimplexInverse_mem he, exponentialSimplexForward_inverse he⟩

/-! ## Fréchet derivative of the coordinate change -/

/-- Differential of the total simplex-coordinate sum. -/
noncomputable def simplexCoordinateSumDerivative :
    (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ :=
  ∑ i : Fin n,
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))

/-- The explicit Fréchet derivative of `exponentialSimplexForward`.

Applied to an increment `(dt,dx)`, it is

`(dt(1-∑x)-t∑dx, fun i ↦ dt*xᵢ+t*dxᵢ)`.
-/
noncomputable def exponentialSimplexForwardDerivative
    (z : ℝ × (Fin n → ℝ)) :
    (ℝ × (Fin n → ℝ)) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
  let dt := ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)
  let dx : Fin n → (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ :=
    fun i ↦ (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))
  ((z.1 • (-simplexCoordinateSumDerivative) +
      (1 - ∑ i, z.2 i) • dt).prod
    (ContinuousLinearMap.pi fun i ↦ z.1 • dx i + z.2 i • dt))

@[simp]
theorem simplexCoordinateSumDerivative_apply
    (h : ℝ × (Fin n → ℝ)) :
    simplexCoordinateSumDerivative h = ∑ i, h.2 i := by
  simp [simplexCoordinateSumDerivative]

theorem exponentialSimplexForwardDerivative_apply
    (z h : ℝ × (Fin n → ℝ)) :
    exponentialSimplexForwardDerivative z h =
      (h.1 * (1 - ∑ i, z.2 i) - z.1 * ∑ i, h.2 i,
        fun i ↦ h.1 * z.2 i + z.1 * h.2 i) := by
  ext <;> simp [exponentialSimplexForwardDerivative,
    simplexCoordinateSumDerivative_apply] <;> ring

theorem hasFDerivAt_exponentialSimplexForward
    (z : ℝ × (Fin n → ℝ)) :
    HasFDerivAt exponentialSimplexForward
      (exponentialSimplexForwardDerivative z) z := by
  have h :
      HasFDerivAt exponentialSimplexForward
        (exponentialSimplexForwardDerivative z) z := by
    unfold exponentialSimplexForward
    dsimp [exponentialSimplexForwardDerivative,
      simplexCoordinateSumDerivative]
    fun_prop
  exact h

theorem fderiv_exponentialSimplexForward
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ exponentialSimplexForward z =
      exponentialSimplexForwardDerivative z :=
  (hasFDerivAt_exponentialSimplexForward z).fderiv

/-! ## Matrix of the derivative -/

/-- Identify an `Option (Fin n)` coordinate vector with radial/product
coordinates. -/
def optionVectorToProduct (v : Option (Fin n) → ℝ) :
    ℝ × (Fin n → ℝ) :=
  (v none, fun i ↦ v (some i))

/-- The inverse coordinate identification. -/
def productToOptionVector (z : ℝ × (Fin n → ℝ)) :
    Option (Fin n) → ℝ
  | none => z.1
  | some i => z.2 i

@[simp]
theorem productToOptionVector_optionVectorToProduct
    (v : Option (Fin n) → ℝ) :
    productToOptionVector (optionVectorToProduct v) = v := by
  funext i
  cases i <;> rfl

@[simp]
theorem optionVectorToProduct_productToOptionVector
    (z : ℝ × (Fin n → ℝ)) :
    optionVectorToProduct (productToOptionVector z) = z := by
  ext <;> rfl

/-- Jacobian matrix of `exponentialSimplexForward` in the basis indexed by
`none, some 0, ..., some (n-1)`. -/
noncomputable def exponentialSimplexJacobianMatrix
    (z : ℝ × (Fin n → ℝ)) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℝ
  | none, none => 1 - ∑ i, z.2 i
  | none, some _ => -z.1
  | some i, none => z.2 i
  | some i, some j => if i = j then z.1 else 0

@[simp]
theorem exponentialSimplexJacobianMatrix_none_none
    (z : ℝ × (Fin n → ℝ)) :
    exponentialSimplexJacobianMatrix z none none =
      1 - ∑ i, z.2 i :=
  rfl

@[simp]
theorem exponentialSimplexJacobianMatrix_none_some
    (z : ℝ × (Fin n → ℝ)) (j : Fin n) :
    exponentialSimplexJacobianMatrix z none (some j) = -z.1 :=
  rfl

@[simp]
theorem exponentialSimplexJacobianMatrix_some_none
    (z : ℝ × (Fin n → ℝ)) (i : Fin n) :
    exponentialSimplexJacobianMatrix z (some i) none = z.2 i :=
  rfl

@[simp]
theorem exponentialSimplexJacobianMatrix_some_some
    (z : ℝ × (Fin n → ℝ)) (i j : Fin n) :
    exponentialSimplexJacobianMatrix z (some i) (some j) =
      if i = j then z.1 else 0 :=
  rfl

theorem exponentialSimplexJacobianMatrix_mulVec_none
    (z : ℝ × (Fin n → ℝ)) (v : Option (Fin n) → ℝ) :
    (exponentialSimplexJacobianMatrix z).mulVec v none =
      v none * (1 - ∑ i, z.2 i) - z.1 * ∑ i, v (some i) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, mul_comm,
    Finset.mul_sum]
  ring

theorem exponentialSimplexJacobianMatrix_mulVec_some
    (z : ℝ × (Fin n → ℝ)) (v : Option (Fin n) → ℝ) (i : Fin n) :
    (exponentialSimplexJacobianMatrix z).mulVec v (some i) =
      v none * z.2 i + z.1 * v (some i) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, mul_comm]

/-- The explicit Jacobian matrix represents the Fréchet derivative proved
above. -/
theorem productToOptionVector_derivative_eq_mulVec
    (z : ℝ × (Fin n → ℝ)) (v : Option (Fin n) → ℝ) :
    productToOptionVector
        (exponentialSimplexForwardDerivative z (optionVectorToProduct v)) =
      (exponentialSimplexJacobianMatrix z).mulVec v := by
  funext i
  cases i with
  | none =>
      rw [exponentialSimplexJacobianMatrix_mulVec_none]
      simp [productToOptionVector, optionVectorToProduct,
        exponentialSimplexForwardDerivative_apply]
  | some i =>
      rw [exponentialSimplexJacobianMatrix_mulVec_some]
      simp [productToOptionVector, optionVectorToProduct,
        exponentialSimplexForwardDerivative_apply]

/-! ## Determinant of the Jacobian -/

/-- Add all rows of the Jacobian to its `none` row.  This elementary row
operation leaves the determinant unchanged and makes the matrix triangular.
-/
noncomputable def reducedExponentialSimplexJacobianMatrix
    (z : ℝ × (Fin n → ℝ)) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℝ :=
  (exponentialSimplexJacobianMatrix z).updateRow none
    (∑ k, (1 : ℝ) • (exponentialSimplexJacobianMatrix z) k)

theorem det_reducedExponentialSimplexJacobianMatrix
    (z : ℝ × (Fin n → ℝ)) :
    (reducedExponentialSimplexJacobianMatrix z).det =
      (exponentialSimplexJacobianMatrix z).det := by
  unfold reducedExponentialSimplexJacobianMatrix
  simpa using Matrix.det_updateRow_sum
    (exponentialSimplexJacobianMatrix z) none (fun _ ↦ (1 : ℝ))

@[simp]
theorem reducedExponentialSimplexJacobianMatrix_none_none
    (z : ℝ × (Fin n → ℝ)) :
    reducedExponentialSimplexJacobianMatrix z none none = 1 := by
  classical
  rw [reducedExponentialSimplexJacobianMatrix, Matrix.updateRow_self]
  rw [Fintype.sum_apply]
  simp only [Pi.smul_apply, one_smul]
  rw [Fintype.sum_option]
  simp

@[simp]
theorem reducedExponentialSimplexJacobianMatrix_none_some
    (z : ℝ × (Fin n → ℝ)) (j : Fin n) :
    reducedExponentialSimplexJacobianMatrix z none (some j) = 0 := by
  classical
  rw [reducedExponentialSimplexJacobianMatrix, Matrix.updateRow_self]
  rw [Fintype.sum_apply]
  simp only [Pi.smul_apply, one_smul]
  rw [Fintype.sum_option]
  simp

@[simp]
theorem reducedExponentialSimplexJacobianMatrix_some_none
    (z : ℝ × (Fin n → ℝ)) (i : Fin n) :
    reducedExponentialSimplexJacobianMatrix z (some i) none = z.2 i := by
  rw [reducedExponentialSimplexJacobianMatrix, Matrix.updateRow_ne (by simp)]
  rfl

@[simp]
theorem reducedExponentialSimplexJacobianMatrix_some_some
    (z : ℝ × (Fin n → ℝ)) (i j : Fin n) :
    reducedExponentialSimplexJacobianMatrix z (some i) (some j) =
      if i = j then z.1 else 0 := by
  rw [reducedExponentialSimplexJacobianMatrix, Matrix.updateRow_ne (by simp)]
  rfl

theorem det_reducedExponentialSimplexJacobianMatrix_eq_pow
    (z : ℝ × (Fin n → ℝ)) :
    (reducedExponentialSimplexJacobianMatrix z).det = z.1 ^ n := by
  let : LinearOrder (Option (Fin n)) :=
    LinearOrder.lift' (finSuccEquiv' (0 : Fin (n + 1))).symm
      (finSuccEquiv' (0 : Fin (n + 1))).symm.injective
  rw [Matrix.det_of_isLowerTriangular _ (by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => simp at hij
        | some j => exact reducedExponentialSimplexJacobianMatrix_none_some z j
    | some i =>
        cases j with
        | none =>
            exfalso
            change
              (finSuccEquiv' (0 : Fin (n + 1))).symm (some i) <
                (finSuccEquiv' (0 : Fin (n + 1))).symm none at hij
            simp at hij
        | some j =>
            simp only [reducedExponentialSimplexJacobianMatrix_some_some]
            rw [ite_eq_right]
            intro h
            subst j
            simp at hij)]
  simp [Fintype.prod_option]

/-- The Jacobian determinant of the radial--simplex coordinate map is
`t ^ n`. -/
theorem det_exponentialSimplexJacobianMatrix
    (z : ℝ × (Fin n → ℝ)) :
    (exponentialSimplexJacobianMatrix z).det = z.1 ^ n := by
  rw [← det_reducedExponentialSimplexJacobianMatrix z,
    det_reducedExponentialSimplexJacobianMatrix_eq_pow]

/-! ## Change of variables -/

/-- The coordinate basis whose `none` coordinate is the radial coordinate
and whose `some i` coordinates are the simplex coordinates. -/
noncomputable def exponentialCoordinateBasis :
    Module.Basis (Option (Fin n)) ℝ (ℝ × (Fin n → ℝ)) :=
  (Pi.basisFun ℝ (Option (Fin n))).map
    (LinearEquiv.piOptionEquivProd ℝ)

/-- The determinant of the Fréchet derivative, in the intrinsic
finite-dimensional determinant used by Mathlib's change-of-variables
theorem. -/
theorem det_exponentialSimplexForwardDerivative
    (z : ℝ × (Fin n → ℝ)) :
    (exponentialSimplexForwardDerivative z).det = z.1 ^ n := by
  classical
  change LinearMap.det
    (exponentialSimplexForwardDerivative z).toLinearMap = _
  rw [← LinearMap.det_toMatrix (exponentialCoordinateBasis (n := n))]
  rw [← det_exponentialSimplexJacobianMatrix z]
  congr 1
  ext i j
  simp only [LinearMap.toMatrix_apply]
  cases i <;> cases j <;>
    simp [exponentialCoordinateBasis,
      exponentialSimplexForwardDerivative_apply,
      exponentialSimplexJacobianMatrix, LinearEquiv.piOptionEquivProd,
      Equiv.piOptionEquivProd, Pi.single_apply]

/-- The coordinate Haar measure is exactly the default product Lebesgue
measure, not merely a nonzero scalar multiple of it. -/
theorem exponentialCoordinateBasis_addHaar_eq_volume :
    (exponentialCoordinateBasis (n := n)).addHaar =
      (volume : Measure (ℝ × (Fin n → ℝ))) := by
  classical
  let e : (Option (Fin n) → ℝ) ≃L[ℝ] (ℝ × (Fin n → ℝ)) :=
    (LinearEquiv.piOptionEquivProd ℝ).toContinuousLinearEquiv
  unfold exponentialCoordinateBasis
  change ((Pi.basisFun ℝ (Option (Fin n))).map e.toLinearEquiv).addHaar = _
  rw [← Module.Basis.map_addHaar (Pi.basisFun ℝ (Option (Fin n))) e]
  have hpi : (Pi.basisFun ℝ (Option (Fin n))).addHaar =
      (volume : Measure (Option (Fin n) → ℝ)) := by
    rw [Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  rw [hpi]
  have hg : Measure.map (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin n) ↦ ℝ))
      (volume : Measure (Option (Fin n) → ℝ)) =
      (volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ) := by
    rw [(MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) ↦ ℝ)).map_apply_eq_iff_map_symm_apply_eq]
    simpa only [volume_pi] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Fin n) ↦ (volume : Measure ℝ))).symm
  rw [show (e : (Option (Fin n) → ℝ) → (ℝ × (Fin n → ℝ))) =
      Prod.swap ∘ (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin n) ↦ ℝ)) by rfl]
  rw [← Measure.map_map measurable_swap (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option (Fin n) ↦ ℝ)).measurable]
  rw [hg, Measure.prod_swap]
  exact (Measure.volume_eq_prod ℝ (Fin n → ℝ)).symm

/-- Restricted change of variables from radial--simplex coordinates to the
positive exponential orthant.  This is the nonnegative integral formula
directly supplied by Mathlib's finite-dimensional Jacobian theorem, with
all geometric and differentiability hypotheses discharged here. -/
theorem lintegral_positiveExponentialOrthant_eq
    (g : (ℝ × (Fin n → ℝ)) → ℝ≥0∞) :
    ∫⁻ e in positiveExponentialOrthant (n := n), g e ∂volume =
      ∫⁻ z in exponentialSimplexSource (n := n),
        ENNReal.ofReal (z.1 ^ n) * g (exponentialSimplexForward z)
          ∂volume := by
  rw [← exponentialCoordinateBasis_addHaar_eq_volume (n := n)]
  rw [← exponentialSimplex_bijOn.image_eq]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (exponentialCoordinateBasis (n := n)).addHaar
    isMeasurableSet_exponentialSimplexSource
    (fun z _ ↦ (hasFDerivAt_exponentialSimplexForward z).hasFDerivWithinAt)
    exponentialSimplex_bijOn.injOn g]
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [
    MeasureTheory.ae_restrict_mem
      isMeasurableSet_exponentialSimplexSource] with z hz
  rw [det_exponentialSimplexForwardDerivative]
  rw [abs_of_nonneg (pow_nonneg hz.1.le n)]

/-! ## The radial Gamma integral -/

/-- The elementary radial integral appearing after the normalized
exponential change of variables. -/
theorem integral_exp_neg_mul_pow_Ioi (n : ℕ) :
    ∫ t : ℝ in Ioi 0, Real.exp (-t) * t ^ n =
      (n.factorial : ℝ) := by
  rw [show (fun t : ℝ => Real.exp (-t) * t ^ n) =
      fun t => t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(1 * t)) by
    funext t
    rw [add_sub_cancel_right, Real.rpow_natCast]
    simp [mul_comm]]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) zero_lt_one]
  simp [Real.Gamma_nat_eq_factorial]

/-- `ENNReal`/Tonelli form of the radial Gamma integral. -/
theorem lintegral_ofReal_exp_neg_mul_pow_Ioi (n : ℕ) :
    ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-t) * t ^ n) =
      (n.factorial : ℝ≥0∞) := by
  have hint : IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ n) (Ioi 0) := by
    convert Real.GammaIntegral_convergent
      (s := (n : ℝ) + 1) (by positivity) using 1
    funext t
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
      mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le n))]
  rw [integral_exp_neg_mul_pow_Ioi]
  simp

/-! ## Normalized exponential coordinates -/

theorem exponentialSimplexSource_eq_prod :
    exponentialSimplexSource (n := n) =
      Ioi (0 : ℝ) ×ˢ fullSimplex (Fin n) := by
  ext z
  simp [exponentialSimplexSource]

/-- Tonelli separation of the radial factor from an arbitrary measurable
nonnegative test function on the simplex. -/
theorem lintegral_exponentialRadial_mul_test
    (h : (Fin n → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z in exponentialSimplexSource (n := n),
        ENNReal.ofReal (Real.exp (-z.1) * z.1 ^ n) * h z.2 ∂volume =
      (n.factorial : ℝ≥0∞) *
        ∫⁻ x in fullSimplex (Fin n), h x ∂volume := by
  rw [exponentialSimplexSource_eq_prod]
  rw [Measure.volume_eq_prod]
  rw [setLIntegral_prod]
  · simp_rw [lintegral_const_mul _ hh]
    rw [lintegral_mul_const]
    · rw [lintegral_ofReal_exp_neg_mul_pow_Ioi]
    · fun_prop
  · fun_prop

/-- The measure on simplex coordinates obtained from independent unit-rate
exponentials: factorial times Lebesgue measure restricted to the full
simplex. -/
noncomputable def normalizedExponentialSimplexMeasure :
    Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞) •
    (volume.restrict (fullSimplex (Fin n)))

/-- Identification of normalized independent exponentials with the
factorial-density uniform simplex measure, formulated against arbitrary
measurable nonnegative test functions. -/
theorem lintegral_normalizedExponential_eq_simplex
    (h : (Fin n → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ e in positiveExponentialOrthant (n := n),
        ENNReal.ofReal (Real.exp (-exponentialTotal e)) *
          h (exponentialSimplexInverse e).2 ∂volume =
      ∫⁻ x, h x ∂(normalizedExponentialSimplexMeasure (n := n)) := by
  rw [lintegral_positiveExponentialOrthant_eq]
  calc
    _ = ∫⁻ z in exponentialSimplexSource (n := n),
        ENNReal.ofReal (Real.exp (-z.1) * z.1 ^ n) * h z.2
          ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [
        ae_restrict_mem isMeasurableSet_exponentialSimplexSource] with z hz
      rw [exponentialTotal_forward, exponentialSimplexInverse_forward hz]
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      ac_rfl
    _ = (n.factorial : ℝ≥0∞) *
        ∫⁻ x in fullSimplex (Fin n), h x ∂volume :=
      lintegral_exponentialRadial_mul_test h hh
    _ = _ := by
      rw [normalizedExponentialSimplexMeasure, lintegral_smul_measure]
      rfl

/-- The unit-rate exponential density, extended by zero to the negative
half-line. -/
noncomputable def unitExponentialDensity (t : ℝ) : ℝ :=
  (Ici (0 : ℝ)).indicator (fun t ↦ Real.exp (-t)) t

theorem integral_unitExponentialDensity :
    ∫ t : ℝ, unitExponentialDensity t = 1 := by
  change ∫ t : ℝ, (Ici (0 : ℝ)).indicator
    (fun t ↦ Real.exp (-t)) t = 1
  rw [integral_indicator measurableSet_Ici]
  rw [integral_Ici_eq_integral_Ioi]
  simpa using integral_exp_neg_mul_pow_Ioi 0

/-- A finite product of unit exponential densities has total mass one. -/
theorem integral_pi_unitExponentialDensity :
    ∫ x : Fin n → ℝ, ∏ i, unitExponentialDensity (x i) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_unitExponentialDensity]

end Feige
