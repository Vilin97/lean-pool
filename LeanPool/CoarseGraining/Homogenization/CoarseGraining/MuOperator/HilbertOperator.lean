/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuQuadratic
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuWellPosedness
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.HilbertMinimizationMeasurability
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Instances.Matrix

/-! # Hilbert Operator -/

namespace Homogenization

noncomputable section

/-!
This file packages the concrete doubled `L²(U; \R^{2d})` operator expected by
the coarse-graining notes.

The key point is fidelity to the text: the Hilbert-space bilinear form used by
the minimization engine should coincide with the averaged pairing

`\fint_U X \cdot \mathbf A(a,x) Y`.

Since the `L²` inner product uses the raw integral, the operator recorded here
already includes the normalization factor `|U|^{-1}`.
-/

/--
Measurable uniformly bounded pointwise operator fields on the Hilbert block
carrier over `U`.

This is the analytic input needed to turn a pointwise doubled operator field
into an actual bounded operator on `L²(U; \R^{2d})`.
-/
structure PointwiseHilbertBlockOperatorField {d : ℕ} (U : Set (Vec d)) where
  /-- The pointwise operator field. -/
  field : Vec d → HilbertBlockVec d →L[ℝ] HilbertBlockVec d
  /-- Measurability of the operator field. -/
  measurable_field : Measurable field
  /-- A uniform operator-norm bound. -/
  opNormBound : ℝ
  /-- Nonnegativity of the bound. -/
  opNormBound_nonneg : 0 ≤ opNormBound
  /-- The pointwise operators are bounded by `opNormBound`. -/
  le_opNormBound : ∀ x : Vec d, ‖field x‖ ≤ opNormBound

namespace PointwiseHilbertBlockOperatorField

variable {d : ℕ} {U : Set (Vec d)}

/-- Pointwise action of the operator field on a typed `L²` block field. -/
def applyFn (M : PointwiseHilbertBlockOperatorField U) (F : HilbertBlockL2 U) :
    Vec d → HilbertBlockVec d :=
  fun x => M.field x (F x)

theorem aestronglyMeasurable_applyFn (M : PointwiseHilbertBlockOperatorField U)
    (F : HilbertBlockL2 U) :
    MeasureTheory.AEStronglyMeasurable (M.applyFn F) (volumeMeasureOn U) := by
  let evalCLM :
      (HilbertBlockVec d →L[ℝ] HilbertBlockVec d) →L[ℝ]
        HilbertBlockVec d →L[ℝ] HilbertBlockVec d :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ (HilbertBlockVec d))
  have hfield := M.measurable_field.aestronglyMeasurable (μ := volumeMeasureOn U)
  have hF := MeasureTheory.Lp.aestronglyMeasurable (μ := volumeMeasureOn U) F
  simpa [applyFn, evalCLM] using!
    ContinuousLinearMap.aestronglyMeasurable_comp₂ (L := evalCLM) hfield hF

theorem memHilbertBlockL2_applyFn (M : PointwiseHilbertBlockOperatorField U)
    (F : HilbertBlockL2 U) :
    MemHilbertBlockL2 U (M.applyFn F) := by
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
noncomputable def apply (M : PointwiseHilbertBlockOperatorField U)
    (F : HilbertBlockL2 U) : HilbertBlockL2 U :=
  toHilbertBlockL2 (M.memHilbertBlockL2_applyFn F)

theorem coeFn_apply (M : PointwiseHilbertBlockOperatorField U)
    (F : HilbertBlockL2 U) :
    M.apply F =ᵐ[volumeMeasureOn U] M.applyFn F :=
  coeFn_toHilbertBlockL2 (M.memHilbertBlockL2_applyFn F)

theorem apply_add (M : PointwiseHilbertBlockOperatorField U)
    (F G : HilbertBlockL2 U) :
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

theorem apply_smul (M : PointwiseHilbertBlockOperatorField U)
    (c : ℝ) (F : HilbertBlockL2 U) :
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
    _ = c • M.applyFn F x := rfl
    _ = c • M.apply F x := by rw [← hF]
    _ = (c • M.apply F) x := by rw [hcod']

theorem norm_apply_le (M : PointwiseHilbertBlockOperatorField U)
    (F : HilbertBlockL2 U) :
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

/-- The bounded operator on `L²(U; \R^{2d})` induced by the pointwise operator
field. -/
noncomputable def toContinuousLinearMap (M : PointwiseHilbertBlockOperatorField U) :
    HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U := by
  let L : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U :=
    { toFun := M.apply
      map_add' := M.apply_add
      map_smul' := M.apply_smul }
  exact L.mkContinuous M.opNormBound (M.norm_apply_le)

@[simp] theorem toContinuousLinearMap_apply (M : PointwiseHilbertBlockOperatorField U)
    (F : HilbertBlockL2 U) :
    M.toContinuousLinearMap F = M.apply F := by
  simp [toContinuousLinearMap]

theorem coeFn_toContinuousLinearMap (M : PointwiseHilbertBlockOperatorField U)
    (F : HilbertBlockL2 U) :
    M.toContinuousLinearMap F =ᵐ[volumeMeasureOn U] M.applyFn F :=
  (M.toContinuousLinearMap_apply F).symm ▸ M.coeFn_apply F

end PointwiseHilbertBlockOperatorField

/-!
The operator-valued measurability step for the doubled coefficient field is
handled through the full `2d × 2d` matrix entries. Since `BlockMat d` does not
carry a measurable/topological structure, we pass through the raw function type
`BlockCoord d → BlockCoord d → ℝ`, which does.
-/

noncomputable def fullEntriesToHilbertOperatorLinear (d : ℕ) :
    (BlockCoord d → BlockCoord d → ℝ) →ₗ[ℝ]
      (HilbertBlockVec d →L[ℝ] HilbertBlockVec d) where
  toFun := fun M => HilbertBlockVec.applyBlockMat (ofFullBlockMat M)
  map_add' := by
    intro M N
    apply ContinuousLinearMap.ext
    intro X
    simp [HilbertBlockVec.applyBlockMat_apply]
    apply HilbertBlockVec.ext
    · apply HilbertVec.ext
      intro i
      simp [ofFullBlockMat, blockMatVecMul, matVecMul, Finset.sum_add_distrib, add_mul,
        add_left_comm, add_assoc]
    · apply HilbertVec.ext
      intro i
      simp [ofFullBlockMat, blockMatVecMul, matVecMul, Finset.sum_add_distrib, add_mul,
        add_left_comm, add_assoc]
  map_smul' := by
    intro c M
    apply ContinuousLinearMap.ext
    intro X
    simp [HilbertBlockVec.applyBlockMat_apply]
    apply HilbertBlockVec.ext
    · apply HilbertVec.ext
      intro i
      simp [ofFullBlockMat, blockMatVecMul, matVecMul, Finset.mul_sum, mul_assoc]
    · apply HilbertVec.ext
      intro i
      simp [ofFullBlockMat, blockMatVecMul, matVecMul, Finset.mul_sum, mul_assoc]

noncomputable def fullEntriesToHilbertOperator (d : ℕ) :
    (BlockCoord d → BlockCoord d → ℝ) →L[ℝ]
      (HilbertBlockVec d →L[ℝ] HilbertBlockVec d) :=
  ⟨fullEntriesToHilbertOperatorLinear d,
    (fullEntriesToHilbertOperatorLinear d).continuous_of_finiteDimensional⟩

theorem measurable_fullEntriesToHilbertOperator {d : ℕ} {α : Type*}
    [MeasurableSpace α] {b : α → BlockCoord d → BlockCoord d → ℝ}
    (hb : Measurable b) :
    Measurable (fun x => fullEntriesToHilbertOperator d (b x)) := by
  exact (fullEntriesToHilbertOperator d).continuous.measurable.comp hb

@[simp] theorem fullEntriesToHilbertOperator_toFullBlockMat {d : ℕ} (B : BlockMat d) :
    fullEntriesToHilbertOperator d (toFullBlockMat B) = HilbertBlockVec.applyBlockMat B := by
  simp [fullEntriesToHilbertOperator, fullEntriesToHilbertOperatorLinear]

@[simp] theorem symmPart_zero {d : ℕ} :
    symmPart (0 : Mat d) = 0 := by
  ext i j
  simp [symmPart]

@[simp] theorem skewPart_zero {d : ℕ} :
    skewPart (0 : Mat d) = 0 := by
  ext i j
  simp [skewPart]

theorem measurable_matrix_transpose_entry {d : ℕ} {α : Type*} [MeasurableSpace α]
    {A : α → Fin d → Fin d → ℝ} (hA : Measurable A) (i j : Fin d) :
    Measurable (fun x => matTranspose (A x) i j) := by
  simpa [matTranspose] using! (measurable_pi_iff.1 (measurable_pi_iff.1 hA j) i)

theorem measurable_symmPart_entry {d : ℕ} {α : Type*} [MeasurableSpace α]
    {A : α → Fin d → Fin d → ℝ} (hA : Measurable A) (i j : Fin d) :
    Measurable (fun x => symmPart (A x) i j) := by
  have hij : Measurable (fun x => A x i j) :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hA i) j
  have hji : Measurable (fun x => A x j i) :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hA j) i
  simpa [symmPart, div_eq_mul_inv] using (hij.add hji).mul_const ((2 : ℝ)⁻¹)

theorem measurable_skewPart_entry {d : ℕ} {α : Type*} [MeasurableSpace α]
    {A : α → Fin d → Fin d → ℝ} (hA : Measurable A) (i j : Fin d) :
    Measurable (fun x => skewPart (A x) i j) := by
  have hij : Measurable (fun x => A x i j) :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hA i) j
  have hji : Measurable (fun x => A x j i) :=
    measurable_pi_iff.1 (measurable_pi_iff.1 hA j) i
  simpa [skewPart, div_eq_mul_inv] using (hij.sub hji).mul_const ((2 : ℝ)⁻¹)

theorem measurable_matrix_mul_entry {d : ℕ} {α : Type*} [MeasurableSpace α]
    {A B : α → Fin d → Fin d → ℝ} (hA : Measurable A) (hB : Measurable B) (i j : Fin d) :
    Measurable (fun x => ∑ k, A x i k * B x k j) := by
  classical
  exact Finset.measurable_sum Finset.univ (fun k _ =>
      (measurable_pi_iff.1 (measurable_pi_iff.1 hA i) k).mul
        (measurable_pi_iff.1 (measurable_pi_iff.1 hB k) j))

theorem measurable_toFullBlockMat_blockCoeffField {d : ℕ} {α : Type*}
    [MeasurableSpace α] {A : α → Fin d → Fin d → ℝ} (hA : Measurable A) :
    Measurable (fun x α β =>
      toFullBlockMat (blockMatrixOfCoeff (A x)) α β) := by
  let s : α → Fin d → Fin d → ℝ := fun x i j => symmPart (A x) i j
  let sInv : α → Fin d → Fin d → ℝ := fun x i j => (((symmPart (A x))⁻¹ : Mat d) i j)
  let k : α → Fin d → Fin d → ℝ := fun x i j => skewPart (A x) i j
  let kT : α → Fin d → Fin d → ℝ := fun x i j => matTranspose (skewPart (A x)) i j
  let kTsInv : α → Fin d → Fin d → ℝ := fun x i j => ∑ l, kT x i l * sInv x l j
  let kTsInvk : α → Fin d → Fin d → ℝ := fun x i j => ∑ l, kTsInv x i l * k x l j
  let sInvk : α → Fin d → Fin d → ℝ := fun x i j => ∑ l, sInv x i l * k x l j
  have hs : Measurable s := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [s] using measurable_symmPart_entry hA i j
  have hk : Measurable k := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [k] using measurable_skewPart_entry hA i j
  have hsInv : Measurable sInv := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [sInv] using measurable_matrix_inv_entry hs i j
  have hkT : Measurable kT := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [kT, matTranspose] using (measurable_pi_iff.1 (measurable_pi_iff.1 hk j) i)
  have hkTsInv : Measurable kTsInv := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [kTsInv] using measurable_matrix_mul_entry hkT hsInv i j
  have hkTsInvk : Measurable kTsInvk := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [kTsInvk] using measurable_matrix_mul_entry hkTsInv hk i j
  have hsInvk : Measurable sInvk := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    simpa [sInvk] using measurable_matrix_mul_entry hsInv hk i j
  refine measurable_pi_iff.2 ?_
  intro α
  refine measurable_pi_iff.2 ?_
  intro β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [blockMatrixOfCoeff, toFullBlockMat, s, k, kT, sInv, kTsInv, kTsInvk,
            Matrix.mul_apply] using
            (measurable_pi_iff.1 (measurable_pi_iff.1 (hs.add hkTsInvk) i) j)
      | inr j =>
          simpa [blockMatrixOfCoeff, toFullBlockMat, kT, sInv, kTsInv, Matrix.mul_apply] using
            (measurable_pi_iff.1 (measurable_pi_iff.1 hkTsInv.neg i) j)
  | inr i =>
      cases β with
      | inl j =>
          simpa [blockMatrixOfCoeff, toFullBlockMat, sInv, k, sInvk, Matrix.mul_apply] using
            (measurable_pi_iff.1 (measurable_pi_iff.1 hsInvk.neg i) j)
      | inr j =>
          simpa [blockMatrixOfCoeff, toFullBlockMat, sInv] using
            (measurable_pi_iff.1 (measurable_pi_iff.1 hsInv i) j)

theorem blockMatrixOfCoeffNormSqBound_nonneg (lam Lam : ℝ) :
    0 ≤ blockMatrixOfCoeffNormSqBound lam Lam := by
  unfold blockMatrixOfCoeffNormSqBound
  have hFirst : 0 ≤ 2 * Lam ^ 2 := by
    nlinarith [sq_nonneg Lam]
  have hFactor : 0 ≤ 2 * Lam ^ 2 + 1 := by
    nlinarith [sq_nonneg Lam]
  have hInvSq : 0 ≤ lam⁻¹ * lam⁻¹ := by
    nlinarith [sq_nonneg (lam⁻¹)]
  have hLast : 0 ≤ Lam ^ 2 + 1 := by
    nlinarith [sq_nonneg Lam]
  have hSecond : 0 ≤ 2 * (2 * Lam ^ 2 + 1) * (lam⁻¹ * lam⁻¹) * (Lam ^ 2 + 1) := by
    refine mul_nonneg ?_ hLast
    refine mul_nonneg ?_ hInvSq
    refine mul_nonneg ?_ hFactor
    positivity
  exact add_nonneg hFirst hSecond

/--
The normalized doubled coefficient operator at a single point `x`.

The operator is built from the coefficient field restricted to `U` and extended
by zero off `U`. This matches the note-faithful situation that all analytic
statements are made on `U`, while keeping a genuinely global measurable field
for the ambient `L²(volume.restrict U)` construction.
-/
noncomputable def normalizedBlockCoeffOperator {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (x : Vec d) : HilbertBlockVec d →L[ℝ] HilbertBlockVec d :=
  (MeasureTheory.volume U).toReal⁻¹ •
    HilbertBlockVec.applyBlockMat (blockCoeffField (restrictCoeffField U a) x)

@[simp] theorem normalizedBlockCoeffOperator_apply {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (x : Vec d) (X : HilbertBlockVec d) :
    normalizedBlockCoeffOperator U a x X =
      (MeasureTheory.volume U).toReal⁻¹ •
        HilbertBlockVec.applyBlockMat (blockCoeffField (restrictCoeffField U a) x) X := by
  simp [normalizedBlockCoeffOperator]

theorem normalizedBlockCoeffOperator_apply_of_mem {d : ℕ} {U : Set (Vec d)}
    (a : CoeffField d) {x : Vec d} (hx : x ∈ U) (X : HilbertBlockVec d) :
    normalizedBlockCoeffOperator U a x X =
      (MeasureTheory.volume U).toReal⁻¹ •
        HilbertBlockVec.applyBlockMat (blockCoeffField a x) X := by
  have hcoeff :
      blockCoeffField (restrictCoeffField U a) x = blockCoeffField a x := by
    simp [blockCoeffField, restrictCoeffField, hx]
  simp [normalizedBlockCoeffOperator, hcoeff]

end

end Homogenization
