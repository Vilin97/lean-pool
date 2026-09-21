/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField
import LeanPool.CoarseGraining.Homogenization.Ambient.HilbertFinite
import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Instances.Matrix

/-! # Coefficient Field Hilbert -/

namespace Homogenization

noncomputable section

local instance matMeasurableSpace {d : ℕ} : MeasurableSpace (Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

local instance matBorelSpace {d : ℕ} : BorelSpace (Mat d) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

local instance hilbertVecOperatorMeasurableSpace {d : ℕ} :
    MeasurableSpace (HilbertVec d →L[ℝ] HilbertVec d) :=
  borel (HilbertVec d →L[ℝ] HilbertVec d)

local instance hilbertVecOperatorBorelSpace {d : ℕ} :
    BorelSpace (HilbertVec d →L[ℝ] HilbertVec d) :=
  ⟨rfl⟩

/-- A matrix acts continuously on the project's algebraic vector carrier. -/
noncomputable def matContinuousLinearMap {d : ℕ} (A : Mat d) :
    Vec d →L[ℝ] Vec d :=
  ⟨Matrix.toLin' A, (Matrix.toLin' A).continuous_of_finiteDimensional⟩

@[simp] theorem matContinuousLinearMap_apply {d : ℕ} (A : Mat d) (x : Vec d) :
    matContinuousLinearMap A x = matVecMul A x :=
  rfl

namespace HilbertVec

/-- A matrix acts continuously on the Euclidean Hilbert realization of `\R^d`
by conjugating the algebraic action through `HilbertVec d ≃L[ℝ] Vec d`. -/
noncomputable def applyMat {d : ℕ} (A : Mat d) :
    HilbertVec d →L[ℝ] HilbertVec d :=
  ((continuousLinearEquivVec d).symm.toContinuousLinearMap).comp
    ((matContinuousLinearMap A).comp
      (continuousLinearEquivVec d).toContinuousLinearMap)

@[simp] theorem applyMat_apply {d : ℕ} (A : Mat d) (x : HilbertVec d) :
    applyMat A x = ofVec (matVecMul A x.toVec) := by
  simp [applyMat]

@[simp] theorem applyMat_zero {d : ℕ} :
    applyMat (0 : Mat d) = 0 := by
  ext x i
  simp [applyMat_apply, matVecMul]

@[simp] theorem norm_sq_ofVec {d : ℕ} (x : Vec d) :
    ‖ofVec x‖ ^ 2 = vecDot x x := by
  rw [norm_sq_eq_sum_sq]
  simp [vecDot, pow_two]

@[simp] theorem norm_sq_eq_vecDot {d : ℕ} (x : HilbertVec d) :
    ‖x‖ ^ 2 = vecDot x.toVec x.toVec := by
  simpa [ofVec_toVec x] using norm_sq_ofVec x.toVec

@[simp] theorem inner_ofVec_applyMat {d : ℕ} (A : Mat d) (x y : Vec d) :
    inner ℝ (ofVec x) (applyMat A (ofVec y)) =
      vecDot x (matVecMul A y) := by
  simp [applyMat_apply, inner_def]

@[simp] theorem norm_sq_applyMat {d : ℕ} (A : Mat d) (x : HilbertVec d) :
    ‖applyMat A x‖ ^ 2 =
      vecDot (matVecMul A x.toVec) (matVecMul A x.toVec) := by
  rw [applyMat_apply, norm_sq_ofVec]

theorem opNorm_applyMat_le_of_vec_bound {d : ℕ} {A : Mat d} {C : ℝ}
    (hC : 0 ≤ C)
    (hA : ∀ ξ : Vec d,
      vecDot (matVecMul A ξ) (matVecMul A ξ) ≤ C ^ 2 * vecDot ξ ξ) :
    ‖applyMat A‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC ?_
  intro x
  have hsq :
      ‖applyMat A x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    calc
      ‖applyMat A x‖ ^ 2
          = vecDot (matVecMul A x.toVec) (matVecMul A x.toVec) := by
              rw [norm_sq_applyMat]
      _ ≤ C ^ 2 * vecDot x.toVec x.toVec := hA x.toVec
      _ = C ^ 2 * ‖x‖ ^ 2 := by
            rw [norm_sq_eq_vecDot]
      _ = (C * ‖x‖) ^ 2 := by
            ring
  have hCnorm_nonneg : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg x)
  have habs : |‖applyMat A x‖| ≤ |C * ‖x‖| := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCnorm_nonneg] using habs

theorem opNorm_applyMat_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) :
    ‖applyMat A‖ ≤ Lam := by
  refine opNorm_applyMat_le_of_vec_bound (A := A) ?_ ?_
  · exact le_trans (le_of_lt hA.1) hA.2.1
  · intro ξ
    simpa [vecNormSq] using vecNormSq_matVecMul_le_of_isEllipticMatrix hA ξ

end HilbertVec

/--
Measurable uniformly bounded pointwise operator fields on the Hilbert-vector
carrier over `U`.

This is the vector-side analogue of the doubled `MuOperator` infrastructure.
-/
structure PointwiseHilbertVecOperatorField {d : ℕ} (U : Set (Vec d)) where
  /-- The pointwise operator field. -/
  field : Vec d → HilbertVec d →L[ℝ] HilbertVec d
  /-- Measurability of the operator field. -/
  measurable_field : Measurable field
  /-- A uniform operator-norm bound. -/
  opNormBound : ℝ
  /-- Nonnegativity of the bound. -/
  opNormBound_nonneg : 0 ≤ opNormBound
  /-- The pointwise operators are bounded by `opNormBound`. -/
  le_opNormBound : ∀ x : Vec d, ‖field x‖ ≤ opNormBound

namespace PointwiseHilbertVecOperatorField

variable {d : ℕ} {U : Set (Vec d)}

/-- Pointwise action of the operator field on a typed `L²` vector field. -/
def applyFn (M : PointwiseHilbertVecOperatorField U) (F : HilbertVectorL2 U) :
    Vec d → HilbertVec d :=
  fun x => M.field x (F x)

theorem aestronglyMeasurable_applyFn (M : PointwiseHilbertVecOperatorField U)
    (F : HilbertVectorL2 U) :
    MeasureTheory.AEStronglyMeasurable (M.applyFn F) (volumeMeasureOn U) := by
  let evalCLM :
      (HilbertVec d →L[ℝ] HilbertVec d) →L[ℝ]
        HilbertVec d →L[ℝ] HilbertVec d :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ (HilbertVec d))
  have hfield :
      MeasureTheory.AEStronglyMeasurable M.field (volumeMeasureOn U) :=
    M.measurable_field.aestronglyMeasurable (μ := volumeMeasureOn U)
  have hF := MeasureTheory.Lp.aestronglyMeasurable (μ := volumeMeasureOn U) F
  simpa [applyFn, evalCLM] using!
    ContinuousLinearMap.aestronglyMeasurable_comp₂ (L := evalCLM) hfield hF

theorem memHilbertVectorL2_applyFn (M : PointwiseHilbertVecOperatorField U)
    (F : HilbertVectorL2 U) :
    MemHilbertVectorL2 U (M.applyFn F) := by
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U, ‖M.applyFn F x‖ ≤ M.opNormBound * ‖F x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    calc
      ‖M.applyFn F x‖ = ‖M.field x (F x)‖ := rfl
      _ ≤ ‖M.field x‖ * ‖F x‖ := (M.field x).le_opNorm (F x)
      _ ≤ M.opNormBound * ‖F x‖ := by
        exact mul_le_mul_of_nonneg_right (M.le_opNormBound x) (norm_nonneg _)
  exact
    MeasureTheory.MemLp.of_le_mul
      (MeasureTheory.Lp.memLp F)
      (M.aestronglyMeasurable_applyFn F)
      hbound

/-- The typed `L²` field obtained by applying the operator field pointwise. -/
noncomputable def apply (M : PointwiseHilbertVecOperatorField U)
    (F : HilbertVectorL2 U) : HilbertVectorL2 U :=
  toHilbertVectorL2 (M.memHilbertVectorL2_applyFn F)

theorem coeFn_apply (M : PointwiseHilbertVecOperatorField U)
    (F : HilbertVectorL2 U) :
    M.apply F =ᵐ[volumeMeasureOn U] M.applyFn F :=
  coeFn_toHilbertVectorL2 (M.memHilbertVectorL2_applyFn F)

theorem apply_add (M : PointwiseHilbertVecOperatorField U)
    (F G : HilbertVectorL2 U) :
    M.apply (F + G) = M.apply F + M.apply G := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [M.coeFn_apply (F + G), M.coeFn_apply F, M.coeFn_apply G,
       MeasureTheory.Lp.coeFn_add F G, MeasureTheory.Lp.coeFn_add (M.apply F) (M.apply G)]
    with x hFG hF hG hdom hcod
  have hdom' : (F + G) x = F x + G x := by
    simpa using hdom
  have hcod' : (M.apply F + M.apply G) x = M.apply F x + M.apply G x := by
    simpa using hcod
  rw [hFG]
  calc
    M.applyFn (F + G) x = M.field x ((F + G) x) := rfl
    _ = M.field x (F x + G x) := by rw [hdom']
    _ = M.field x (F x) + M.field x (G x) := map_add (M.field x) (F x) (G x)
    _ = M.applyFn F x + M.applyFn G x := rfl
    _ = M.apply F x + M.apply G x := by rw [← hF, ← hG]
    _ = (M.apply F + M.apply G) x := by rw [hcod']

theorem apply_smul (M : PointwiseHilbertVecOperatorField U)
    (c : ℝ) (F : HilbertVectorL2 U) :
    M.apply (c • F) = c • M.apply F := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [M.coeFn_apply (c • F), M.coeFn_apply F,
       MeasureTheory.Lp.coeFn_smul c F, MeasureTheory.Lp.coeFn_smul c (M.apply F)]
    with x hCF hF hdom hcod
  have hdom' : (c • F) x = c • F x := by
    simpa using hdom
  have hcod' : (c • M.apply F) x = c • M.apply F x := by
    simpa using hcod
  rw [hCF]
  calc
    M.applyFn (c • F) x = M.field x ((c • F) x) := rfl
    _ = M.field x (c • F x) := by rw [hdom']
    _ = c • M.field x (F x) := map_smul (M.field x) c (F x)
    _ = c • M.applyFn F x := by rfl
    _ = c • M.apply F x := by rw [← hF]
    _ = (c • M.apply F) x := by rw [hcod']

theorem norm_apply_le (M : PointwiseHilbertVecOperatorField U)
    (F : HilbertVectorL2 U) :
    ‖M.apply F‖ ≤ M.opNormBound * ‖F‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [M.coeFn_apply F] with x hF
  calc
    ‖M.apply F x‖ = ‖M.field x (F x)‖ := by
      rw [hF]
      simp [applyFn]
    _ ≤ ‖M.field x‖ * ‖F x‖ := (M.field x).le_opNorm (F x)
    _ ≤ M.opNormBound * ‖F x‖ := by
      exact mul_le_mul_of_nonneg_right (M.le_opNormBound x) (norm_nonneg _)

/-- The bounded operator on `L²(U; \R^d)` induced by the pointwise operator
field. -/
noncomputable def toContinuousLinearMap (M : PointwiseHilbertVecOperatorField U) :
    HilbertVectorL2 U →L[ℝ] HilbertVectorL2 U := by
  let L : HilbertVectorL2 U →ₗ[ℝ] HilbertVectorL2 U :=
    { toFun := M.apply
      map_add' := M.apply_add
      map_smul' := M.apply_smul }
  exact L.mkContinuous M.opNormBound (M.norm_apply_le)

@[simp] theorem toContinuousLinearMap_apply (M : PointwiseHilbertVecOperatorField U)
    (F : HilbertVectorL2 U) :
    M.toContinuousLinearMap F = M.apply F := by
  simp [toContinuousLinearMap]

theorem coeFn_toContinuousLinearMap (M : PointwiseHilbertVecOperatorField U)
    (F : HilbertVectorL2 U) :
    M.toContinuousLinearMap F =ᵐ[volumeMeasureOn U] M.applyFn F :=
  (M.toContinuousLinearMap_apply F).symm ▸ M.coeFn_apply F

end PointwiseHilbertVecOperatorField

private noncomputable def matToHilbertOperatorLinear (d : ℕ) :
    Mat d →ₗ[ℝ] (HilbertVec d →L[ℝ] HilbertVec d) where
  toFun := HilbertVec.applyMat
  map_add' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    apply HilbertVec.ext
    intro i
    simp [HilbertVec.applyMat_apply, matVecMul, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c A
    apply ContinuousLinearMap.ext
    intro x
    apply HilbertVec.ext
    intro i
    simp [HilbertVec.applyMat_apply, matVecMul, Finset.mul_sum, mul_assoc]

private noncomputable def matToHilbertOperator (d : ℕ) :
    Mat d →L[ℝ] (HilbertVec d →L[ℝ] HilbertVec d) :=
  ⟨matToHilbertOperatorLinear d,
    (matToHilbertOperatorLinear d).continuous_of_finiteDimensional⟩

private theorem measurable_matToHilbertOperator {d : ℕ} {α : Type*}
    [MeasurableSpace α] {A : α → Mat d} (hA : Measurable A) :
    Measurable (fun x => matToHilbertOperator d (A x)) := by
  exact (matToHilbertOperator d).continuous.measurable.comp hA

@[simp] private theorem matToHilbertOperator_apply {d : ℕ} (A : Mat d) :
    matToHilbertOperator d A = HilbertVec.applyMat A := by
  rfl

/-- The pointwise Hilbert-vector operator field induced by an elliptic
coefficient field on `U`. Outside `U` we insert the zero matrix to keep the
field globally measurable. -/
noncomputable def hilbertCoeffOperatorField {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    PointwiseHilbertVecOperatorField U := by
  classical
  have hmeasA :
      Measurable (fun x : Vec d => fun i j => if x ∈ U then a x i j else 0) :=
    hEll.1
  refine
    { field := fun x => matToHilbertOperator d (fun i j => if x ∈ U then a x i j else 0)
      measurable_field :=
        by
          exact
            (measurable_matToHilbertOperator
              (A := fun x : Vec d => (fun i j => if x ∈ U then a x i j else 0 : Mat d))
              hmeasA)
      opNormBound := max Lam 0
      opNormBound_nonneg := le_max_right _ _
      le_opNormBound := ?_ }
  intro x
  by_cases hx : x ∈ U
  · have hAx : (fun i j => if x ∈ U then a x i j else 0 : Mat d) = a x := by
      funext i j
      simp [hx]
    calc
      ‖matToHilbertOperator d (fun i j => if x ∈ U then a x i j else 0)‖
          = ‖HilbertVec.applyMat (a x)‖ := by
              rw [hAx, matToHilbertOperator_apply]
      _ ≤ Lam := HilbertVec.opNorm_applyMat_le_of_isEllipticMatrix (hEll.2 x hx)
      _ ≤ max Lam 0 := le_max_left _ _
  · have hAx : (fun i j => if x ∈ U then a x i j else 0 : Mat d) = 0 := by
      funext i j
      simp [hx]
    calc
      ‖matToHilbertOperator d (fun i j => if x ∈ U then a x i j else 0)‖
          = ‖HilbertVec.applyMat (0 : Mat d)‖ := by
              rw [hAx]; exact congrArg norm (matToHilbertOperator_apply 0)
      _ = 0 := by simp
      _ ≤ max Lam 0 := le_max_right _ _

/-- The bounded operator on `L²(U; \R^d)` induced by an elliptic coefficient
field. -/
noncomputable def hilbertCoeffOperator {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    HilbertVectorL2 U →L[ℝ] HilbertVectorL2 U :=
  (hilbertCoeffOperatorField (U := U) hEll).toContinuousLinearMap

theorem ae_hilbertCoeffOperator_apply {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    (F : HilbertVectorL2 U) :
    hilbertCoeffOperator hEll F =ᵐ[volumeMeasureOn U]
      fun x => HilbertVec.applyMat (a x) (F x) := by
  classical
  have happly := (hilbertCoeffOperatorField (U := U) hEll).coeFn_toContinuousLinearMap F
  have hmem :
      ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  filter_upwards [happly, hmem] with x hx hUx
  have hAx : (fun i j => if x ∈ U then a x i j else 0 : Mat d) = a x := by
    funext i j
    simp [hUx]
  change ((hilbertCoeffOperatorField (U := U) hEll).toContinuousLinearMap F) x =
    HilbertVec.applyMat (a x) (F x)
  rw [hx]
  change (hilbertCoeffOperatorField (U := U) hEll).field x (F x) =
    HilbertVec.applyMat (a x) (F x)
  simp [hilbertCoeffOperatorField, hAx]

theorem hilbertCoeffOperator_toHilbertVectorL2OfVecField {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    hilbertCoeffOperator hEll (toHilbertVectorL2OfVecField hf) =
      toHilbertVectorL2OfVecField
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hf) := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [ae_hilbertCoeffOperator_apply hEll (toHilbertVectorL2OfVecField hf),
       coeFn_toHilbertVectorL2OfVecField (U := U) (f := f) hf,
       coeFn_toHilbertVectorL2OfVecField
         (U := U)
         (f := fun x => matVecMul (a x) (f x))
         (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hf)]
    with x hx hF hAxF
  rw [hx, hF, hAxF]
  simp [HilbertVec.applyMat_apply, hilbertifyVecField]

/-- The pointwise Hilbert-vector operator field induced by the symmetric part
of an elliptic coefficient field. Outside `U` we insert the zero matrix to keep
the field globally measurable. -/
noncomputable def hilbertSymmCoeffOperatorField {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    PointwiseHilbertVecOperatorField U := by
  classical
  let aExt : Vec d → Mat d := fun x => if x ∈ U then a x else 0
  have haExt : Measurable aExt := by
    have hdef :
        aExt = fun x : Vec d => (fun i j => if x ∈ U then a x i j else 0 : Mat d) := by
      funext x i j
      by_cases hx : x ∈ U <;> simp [aExt, hx]
    rw [hdef]
    exact hEll.1
  have hmeasSymm : Measurable (fun x : Vec d => symmPart (aExt x)) := by
    refine measurable_pi_iff.2 fun i => ?_
    refine measurable_pi_iff.2 fun j => ?_
    have hij : Measurable (fun x : Vec d => aExt x i j) :=
      measurable_pi_iff.1 (measurable_pi_iff.1 haExt i) j
    have hji : Measurable (fun x : Vec d => aExt x j i) :=
      measurable_pi_iff.1 (measurable_pi_iff.1 haExt j) i
    simpa [symmPart, div_eq_mul_inv] using (hij.add hji).mul_const ((2 : ℝ)⁻¹)
  refine
    { field := fun x => matToHilbertOperator d (symmPart (aExt x))
      measurable_field :=
        by
          exact
            (measurable_matToHilbertOperator
              (A := fun x : Vec d => symmPart (aExt x))
              hmeasSymm)
      opNormBound := max Lam 0
      opNormBound_nonneg := le_max_right _ _
      le_opNormBound := ?_ }
  intro x
  by_cases hx : x ∈ U
  · have hAx : aExt x = a x := by
      simp [aExt, hx]
    have hLam_nonneg : 0 ≤ Lam := le_trans (le_of_lt (hEll.2 x hx).1) (hEll.2 x hx).2.1
    calc
      ‖matToHilbertOperator d (symmPart (aExt x))‖
          = ‖HilbertVec.applyMat (symmPart (a x))‖ := by
              rw [hAx, matToHilbertOperator_apply]
      _ ≤ Lam := by
              refine HilbertVec.opNorm_applyMat_le_of_vec_bound hLam_nonneg ?_
              intro ξ
              simpa [vecNormSq] using
                vecNormSq_matVecMul_symmPart_le_of_isEllipticMatrix (hEll.2 x hx) ξ
      _ ≤ max Lam 0 := le_max_left _ _
  · have hAx : aExt x = 0 := by
      simp [aExt, hx]
    have hSymmZero : symmPart (0 : Mat d) = 0 := by
      funext i j
      simp [symmPart]
    calc
      ‖matToHilbertOperator d (symmPart (aExt x))‖
          = ‖HilbertVec.applyMat (0 : Mat d)‖ := by
              rw [hAx]
              rw [hSymmZero, matToHilbertOperator_apply]
      _ = 0 := by simp
      _ ≤ max Lam 0 := le_max_right _ _

/-- The bounded operator on `L²(U; \R^d)` induced by the symmetric part of an
elliptic coefficient field. -/
noncomputable def hilbertSymmCoeffOperator {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    HilbertVectorL2 U →L[ℝ] HilbertVectorL2 U :=
  (hilbertSymmCoeffOperatorField (U := U) hEll).toContinuousLinearMap

theorem ae_hilbertSymmCoeffOperator_apply {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    (F : HilbertVectorL2 U) :
    hilbertSymmCoeffOperator hEll F =ᵐ[volumeMeasureOn U]
      fun x => HilbertVec.applyMat (symmPart (a x)) (F x) := by
  classical
  let aExt : Vec d → Mat d := fun x => if x ∈ U then a x else 0
  have happly := (hilbertSymmCoeffOperatorField (U := U) hEll).coeFn_toContinuousLinearMap F
  have hmem :
      ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  filter_upwards [happly, hmem] with x hx hUx
  have hAx : aExt x = a x := by
    simp [aExt, hUx]
  change ((hilbertSymmCoeffOperatorField (U := U) hEll).toContinuousLinearMap F) x =
    HilbertVec.applyMat (symmPart (a x)) (F x)
  rw [hx]
  change (hilbertSymmCoeffOperatorField (U := U) hEll).field x (F x) =
    HilbertVec.applyMat (symmPart (a x)) (F x)
  simp [hilbertSymmCoeffOperatorField, aExt, hAx]

theorem hilbertSymmCoeffOperator_toHilbertVectorL2OfVecField {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    hilbertSymmCoeffOperator hEll (toHilbertVectorL2OfVecField hf) =
      toHilbertVectorL2OfVecField
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hf) := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [ae_hilbertSymmCoeffOperator_apply hEll (toHilbertVectorL2OfVecField hf),
       coeFn_toHilbertVectorL2OfVecField (U := U) (f := f) hf,
       coeFn_toHilbertVectorL2OfVecField
         (U := U)
         (f := fun x => matVecMul (symmPart (a x)) (f x))
         (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hf)]
    with x hx hF hAxF
  rw [hx, hF, hAxF]
  simp [HilbertVec.applyMat_apply, hilbertifyVecField]

end

end Homogenization
