/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.Integrand

/-! # Pair Half Scalar -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse perturbation -- pair-half scalar decomposition

Pointwise decomposition of blockResponse_integrand on pair-half states into
the scalarResponse sum, and the resulting blockJValueSet membership lemmas
including the responseJ-adjoint-sum and note-form witness theorems.
-/

private theorem blockResponse_integrand_pair_half_eq_pointwise_scalar_split_of_pointwise_det {d : ℕ}
    (a : CoeffField d) (p pStar q qStar : Vec d) (ξ η : Vec d → Vec d)
    (hdet : ∀ x : Vec d, IsUnit (symmPart (a x)).det) :
    blockResponseIntegrand a (p, q) (qStar, pStar)
        ((1 / 2 : ℝ) •
          { potential := fun x => ξ x + η x
            flux := fun x => matVecMul (a x) (ξ x) - matVecMul (matTranspose (a x)) (η x) }) =
      fun x =>
        (1 / 2 : ℝ) * pointwiseScalarResponseIntegrand (a x) (p - pStar) (qStar - q) (ξ x) +
          (1 / 2 : ℝ) * pointwiseScalarResponseIntegrand (matTranspose (a x))
            (pStar + p) (qStar + q) (η x) := by
  let Y : BlockState d :=
    { potential := fun x => ξ x + η x
      flux := fun x => matVecMul (a x) (ξ x) - matVecMul (matTranspose (a x)) (η x) }
  funext x
  have hsmul :=
    congrFun (blockResponse_integrand_smul a (p, q) (qStar, pStar) (1 / 2 : ℝ) Y) x
  have himage :
      blockMatVecMul (blockCoeffField a x) (Y.eval x) =
        (matVecMul (a x) (ξ x) + matVecMul (matTranspose (a x)) (η x), ξ x - η x) := by
    simpa [Y, BlockState.eval] using
      blockMatVecMul_blockCoeffField_pair_of_isUnit_det_symmPart a x (hdet x) (ξ x) (η x)
  have henergy :
      blockEnergyDensity a Y x =
        vecDot (ξ x) (matVecMul (symmPart (a x)) (ξ x)) +
          vecDot (η x) (matVecMul (symmPart (a x)) (η x)) := by
    unfold blockEnergyDensity
    simpa [Y, BlockState.eval] using!
      pointwiseBlockEnergy_pair_eq_symmPart_sum_of_isUnit_det_symmPart
        (a x) (hdet x) (ξ x) (η x)
  rw [hsmul]
  rw [henergy, himage]
  simp [Y, BlockState.eval, pointwiseScalarResponseIntegrand, symmPart_matTranspose, blockVecDot,
    vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right, sub_eq_add_neg]
  ring_nf

theorem blockResponse_integrand_pair_half_eq_pointwise_split_of_pointwise_det {d : ℕ}
    (a : CoeffField d) (p pStar q qStar : Vec d) (ξ η : Vec d → Vec d)
    (hdet : ∀ x : Vec d, IsUnit (symmPart (a x)).det) :
    blockResponseIntegrand a (p, q) (qStar, pStar)
        ((1 / 2 : ℝ) •
          { potential := fun x => ξ x + η x
            flux := fun x => matVecMul (a x) (ξ x) - matVecMul (matTranspose (a x)) (η x) }) =
      fun x =>
        (1 / 2 : ℝ) *
            (-((1 / 2 : ℝ) * vecDot (ξ x) (matVecMul (symmPart (a x)) (ξ x))) -
              vecDot (p - pStar) (matVecMul (a x) (ξ x)) +
              vecDot (qStar - q) (ξ x)) +
          (1 / 2 : ℝ) *
            (-((1 / 2 : ℝ) * vecDot (η x)
                (matVecMul (symmPart (matTranspose (a x))) (η x))) -
              vecDot (pStar + p) (matVecMul (matTranspose (a x)) (η x)) +
              vecDot (qStar + q) (η x)) := by
  simpa [pointwiseScalarResponseIntegrand] using
    blockResponse_integrand_pair_half_eq_pointwise_scalar_split_of_pointwise_det
      (a := a) (p := p) (pStar := pStar) (q := q) (qStar := qStar)
      (ξ := ξ) (η := η) hdet

theorem blockResponse_integrand_pair_half_eq_scalarResponse_sum_on_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    ∀ x ∈ U,
      blockResponseIntegrand a (p, q) (qStar, pStar)
          ((1 / 2 : ℝ) •
            { potential := fun y => u.toH1.grad y + v.toH1.grad y
              flux := fun y =>
                matVecMul (a y) (u.toH1.grad y) -
                  matVecMul (matTranspose (a y)) (v.toH1.grad y) }) x =
        (1 / 2 : ℝ) *
          scalarResponseIntegrand U a (p - pStar) (qStar - q) u x +
        (1 / 2 : ℝ) *
          scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
            (pStar + p) (qStar + q) v x := by
  intro x hx
  let Y : BlockState d :=
    { potential := fun y => u.toH1.grad y + v.toH1.grad y
      flux := fun y =>
        matVecMul (a y) (u.toH1.grad y) -
          matVecMul (matTranspose (a y)) (v.toH1.grad y) }
  have hsmul :=
    congrFun (blockResponse_integrand_smul a (p, q) (qStar, pStar) (1 / 2 : ℝ) Y) x
  have himage :
      blockMatVecMul (blockCoeffField a x) (Y.eval x) =
        (matVecMul (a x) (u.toH1.grad x) +
            matVecMul (matTranspose (a x)) (v.toH1.grad x),
          u.toH1.grad x - v.toH1.grad x) := by
    simpa [Y, BlockState.eval] using
      blockMatVecMul_blockCoeffField_pair_of_isEllipticFieldOn
        (a := a) hEll hx (u.toH1.grad x) (v.toH1.grad x)
  have henergy :
      blockEnergyDensity a Y x =
        vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) +
          vecDot (v.toH1.grad x) (matVecMul (symmPart (a x)) (v.toH1.grad x)) := by
    unfold blockEnergyDensity
    simpa [Y, BlockState.eval] using!
      pointwiseBlockEnergy_pair_eq_symmPart_sum_of_isUnit_det_symmPart
        (a x) (isUnit_det_symmPart_of_isEllipticMatrix (hEll.2 x hx))
        (u.toH1.grad x) (v.toH1.grad x)
  rw [hsmul, henergy, himage]
  simp [Y, BlockState.eval, scalarResponseIntegrand, Homogenization.adjointCoeffField,
    symmPart_matTranspose,
    blockVecDot, vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right,
    sub_eq_add_neg]
  ring_nf

theorem volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    volumeAverage U
        (blockResponseIntegrand a (p, q) (qStar, pStar)
          ((1 / 2 : ℝ) •
            { potential := fun x => u.toH1.grad x + v.toH1.grad x
              flux := fun x =>
                matVecMul (a x) (u.toH1.grad x) -
                  matVecMul (matTranspose (a x)) (v.toH1.grad x) })) =
        (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v) := by
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  have hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hIntAdj : ResponseLinearIntegrabilityData U (Homogenization.adjointCoeffField a) :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllAdj
  have hu_resp := hInt.response (p - pStar) (qStar - q) u
  have hv_resp := hIntAdj.response (pStar + p) (qStar + q) v
  have hu_half :
      MeasureTheory.IntegrableOn
        (fun x => (1 / 2 : ℝ) * scalarResponseIntegrand U a (p - pStar) (qStar - q) u x) U := by
    simpa [MeasureTheory.IntegrableOn, smul_eq_mul] using!
      hu_resp.integrable.smul (1 / 2 : ℝ)
  have hv_half :
      MeasureTheory.IntegrableOn
        (fun x =>
          (1 / 2 : ℝ) *
            scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v x) U := by
    simpa [MeasureTheory.IntegrableOn, smul_eq_mul] using!
      hv_resp.integrable.smul (1 / 2 : ℝ)
  have hbridge :
      volumeAverage U
          (blockResponseIntegrand a (p, q) (qStar, pStar)
            ((1 / 2 : ℝ) •
              { potential := fun x => u.toH1.grad x + v.toH1.grad x
                flux := fun x =>
                  matVecMul (a x) (u.toH1.grad x) -
                    matVecMul (matTranspose (a x)) (v.toH1.grad x) })) =
        volumeAverage U
          (fun x =>
            (1 / 2 : ℝ) * scalarResponseIntegrand U a (p - pStar) (qStar - q) u x +
              (1 / 2 : ℝ) *
                scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q) v x) := by
    unfold volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    exact blockResponse_integrand_pair_half_eq_scalarResponse_sum_on_of_isEllipticFieldOn
      (a := a) hEll p pStar q qStar u v x hx
  rw [hbridge]
  change volumeAverage U
      ((fun x => (1 / 2 : ℝ) * scalarResponseIntegrand U a (p - pStar) (qStar - q) u x) +
        fun x =>
          (1 / 2 : ℝ) *
            scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v x) =
    (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
      (1 / 2 : ℝ) *
        volumeAverage U
          (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
            (pStar + p) (qStar + q) v)
  rw [volumeAverage_add hu_half hv_half]
  have hu_avg :
      volumeAverage U
          (fun x => (1 / 2 : ℝ) * scalarResponseIntegrand U a (p - pStar) (qStar - q) u x) =
        (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) := by
    simpa [smul_eq_mul] using!
      (volumeAverage_smul U (1 / 2 : ℝ)
        (scalarResponseIntegrand U a (p - pStar) (qStar - q) u))
  have hv_avg :
      volumeAverage U
          (fun x =>
            (1 / 2 : ℝ) *
              scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                (pStar + p) (qStar + q) v x) =
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v) := by
    simpa [smul_eq_mul] using!
      (volumeAverage_smul U (1 / 2 : ℝ)
        (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
          (pStar + p) (qStar + q) v))
  rw [hu_avg, hv_avg]

theorem blockResponse_half_scalarResponse_sum_mem_blockJValueSet_of_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hX :
      BlockResponseSpace a U
        ((1 / 2 : ℝ) •
          { potential := fun x => u.toH1.grad x + v.toH1.grad x
            flux := fun x =>
              matVecMul (a x) (u.toH1.grad x) -
                matVecMul (matTranspose (a x)) (v.toH1.grad x) })) :
    (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v) ∈
      blockJValueSet U (p, q) (qStar, pStar) a := by
  refine ⟨((1 / 2 : ℝ) •
      { potential := fun x => u.toH1.grad x + v.toH1.grad x
        flux := fun x =>
          matVecMul (a x) (u.toH1.grad x) -
            matVecMul (matTranspose (a x)) (v.toH1.grad x) }), hX,
    blockResponseIntegrabilityData_pair_half_of_isEllipticFieldOn hEll u v, ?_⟩
  symm
  exact volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn
    (a := a) hU hEll p pStar q qStar u v

theorem blockResponse_half_scalarResponse_sum_mem_blockJValueSet_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v) ∈
      blockJValueSet U (p, q) (qStar, pStar) a := by
  exact blockResponse_half_scalarResponse_sum_mem_blockJValueSet_of_responseSpace_of_isEllipticFieldOn
    (a := a) hU hEll p pStar q qStar u v
    (blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn (a := a) hEll u v)

theorem blockResponse_half_responseJ_adjoint_sum_mem_blockJValueSet_of_isResponseMaximizer
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hmax : IsResponseMaximizer U (p - pStar) (qStar - q) a u)
    (hmaxAdj :
      IsResponseMaximizer U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) v) :
    (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ∈
      blockJValueSet U (p, q) (qStar, pStar) a := by
  simpa [responseJ_eq_of_isResponseMaximizer U (p - pStar) (qStar - q) a hmax,
    responseJ_eq_of_isResponseMaximizer U (pStar + p) (qStar + q)
      (Homogenization.adjointCoeffField a) hmaxAdj] using
    blockResponse_half_scalarResponse_sum_mem_blockJValueSet_of_isEllipticFieldOn
      (a := a) hU hEll p pStar q qStar u v

theorem blockResponse_half_responseJ_adjoint_sum_note_form_mem_blockJValueSet_of_isResponseMaximizer
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q h : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hmax : IsResponseMaximizer U p (q - h) a u)
    (hmaxAdj :
      IsResponseMaximizer U p (q + h) (Homogenization.adjointCoeffField a) v) :
    (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) ∈
      blockJValueSet U (p, h) (q, 0) a := by
  have hmax' : IsResponseMaximizer U (p - 0) (q - h) a u := by
    simpa using hmax
  have hmaxAdj' :
      IsResponseMaximizer U (0 + p) (q + h) (Homogenization.adjointCoeffField a) v := by
    simpa using hmaxAdj
  simpa using
    blockResponse_half_responseJ_adjoint_sum_mem_blockJValueSet_of_isResponseMaximizer
      (a := a) hU hEll (p := p) (pStar := 0) (q := h) (qStar := q) u v
      hmax' hmaxAdj'

end

end Homogenization
