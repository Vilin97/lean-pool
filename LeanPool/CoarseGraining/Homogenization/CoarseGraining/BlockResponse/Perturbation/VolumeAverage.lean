/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.PairHalfScalar

/-! # Volume Average -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# BlockResponse perturbation -- volume-averaged identities

Volume-average versions of the pair-half scalar decomposition (with and
without the finite-measure assumption), the first-variation pair-half
identity, and the statePairing = quarter scalarVariationEnergy equality.
-/

theorem volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn_of_finiteMeasure
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    volumeAverage U
        (blockResponseIntegrand a (p, q) (qStar, pStar) (blockResponsePairHalfState a u v)) =
      (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v) := by
  simpa [blockResponsePairHalfState] using!
    volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn
      (a := a) hU hEll p pStar q qStar u v

/-- The block first variation around a primal/adjoint half-pair splits into the
corresponding primal and adjoint scalar first variations. -/
theorem blockFirstVariationIntegrand_pair_half_eq_scalarFirstVariation_sum_on_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u w : AHarmonicFunction a U)
    (v z : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    ∀ x ∈ U,
      blockFirstVariationIntegrand a (p, q) (qStar, pStar)
          (blockResponsePairHalfState a u v)
          (blockResponsePairHalfState a w z) x =
        (1 / 2 : ℝ) *
            scalarFirstVariationIntegrand U a (p - pStar) (qStar - q) u w x +
          (1 / 2 : ℝ) *
            scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v z x := by
  intro x hx
  let X : BlockState d := blockResponsePairState a u v
  let Y : BlockState d := blockResponsePairState a w z
  have hXimage :
      blockMatVecMul (blockCoeffField a x) (X.eval x) =
        (matVecMul (a x) (u.toH1.grad x) +
            matVecMul (matTranspose (a x)) (v.toH1.grad x),
          u.toH1.grad x - v.toH1.grad x) := by
    simpa [X, blockResponsePairState, BlockState.eval] using
      blockMatVecMul_blockCoeffField_pair_of_isEllipticFieldOn
        (a := a) hEll hx (u.toH1.grad x) (v.toH1.grad x)
  have hYimage :
      blockMatVecMul (blockCoeffField a x) (Y.eval x) =
        (matVecMul (a x) (w.toH1.grad x) +
            matVecMul (matTranspose (a x)) (z.toH1.grad x),
          w.toH1.grad x - z.toH1.grad x) := by
    simpa [Y, blockResponsePairState, BlockState.eval] using
      blockMatVecMul_blockCoeffField_pair_of_isEllipticFieldOn
        (a := a) hEll hx (w.toH1.grad x) (z.toH1.grad x)
  have hcross_u :
      vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) =
        (1 / 2 : ℝ) *
          (vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1.grad x)) +
            vecDot (matVecMul (a x) (w.toH1.grad x)) (u.toH1.grad x)) := by
    simp [symmPart_eq_smul_add_transpose, smul_matVecMul, add_matVecMul,
      vecDot_add_right, vecDot_smul_right, vecDot_matVecMul_transpose]
    ring_nf
  have hcross_v :
      vecDot (z.toH1.grad x) (matVecMul (symmPart (matTranspose (a x))) (v.toH1.grad x)) =
        (1 / 2 : ℝ) *
          (vecDot (z.toH1.grad x) (matVecMul (matTranspose (a x)) (v.toH1.grad x)) +
            vecDot (matVecMul (matTranspose (a x)) (z.toH1.grad x)) (v.toH1.grad x)) := by
    simp [symmPart_eq_smul_add_transpose, smul_matVecMul, add_matVecMul,
      vecDot_add_right, vecDot_smul_right, matTranspose]
    rw [show
      vecDot (z.toH1.grad x) (matVecMul (a x) (v.toH1.grad x)) =
        vecDot (matVecMul (matTranspose (a x)) (z.toH1.grad x)) (v.toH1.grad x) by
        simpa [matTranspose] using
          (vecDot_matVecMul_transpose (z.toH1.grad x) (v.toH1.grad x)
            (matTranspose (a x)))]
    simp [matTranspose]
    ring_nf
  have hcross_v_symm :
      vecDot (z.toH1.grad x) (matVecMul (symmPart (a x)) (v.toH1.grad x)) =
        (1 / 2 : ℝ) *
          (vecDot (z.toH1.grad x) (matVecMul (matTranspose (a x)) (v.toH1.grad x)) +
            vecDot (matVecMul (matTranspose (a x)) (z.toH1.grad x)) (v.toH1.grad x)) := by
    simpa [symmPart_matTranspose] using hcross_v
  change
    blockFirstVariationIntegrand a (p, q) (qStar, pStar)
        ((1 / 2 : ℝ) • X) ((1 / 2 : ℝ) • Y) x =
      (1 / 2 : ℝ) *
          scalarFirstVariationIntegrand U a (p - pStar) (qStar - q) u w x +
        (1 / 2 : ℝ) *
          scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a)
            (pStar + p) (qStar + q) v z x
  have hXhalf :
      blockMatVecMul (blockCoeffField a x) (((1 / 2 : ℝ) • X).eval x) =
        (1 / 2 : ℝ) •
          (matVecMul (a x) (u.toH1.grad x) +
              matVecMul (matTranspose (a x)) (v.toH1.grad x),
            u.toH1.grad x - v.toH1.grad x) := by
    change
      blockMatVecMul (blockCoeffField a x) ((1 / 2 : ℝ) • X.eval x) =
        (1 / 2 : ℝ) •
          (matVecMul (a x) (u.toH1.grad x) +
              matVecMul (matTranspose (a x)) (v.toH1.grad x),
            u.toH1.grad x - v.toH1.grad x)
    rw [blockMatVecMul_smul, hXimage]
  have hYhalf :
      blockMatVecMul (blockCoeffField a x) (((1 / 2 : ℝ) • Y).eval x) =
        (1 / 2 : ℝ) •
          (matVecMul (a x) (w.toH1.grad x) +
              matVecMul (matTranspose (a x)) (z.toH1.grad x),
            w.toH1.grad x - z.toH1.grad x) := by
    change
      blockMatVecMul (blockCoeffField a x) ((1 / 2 : ℝ) • Y.eval x) =
        (1 / 2 : ℝ) •
          (matVecMul (a x) (w.toH1.grad x) +
              matVecMul (matTranspose (a x)) (z.toH1.grad x),
            w.toH1.grad x - z.toH1.grad x)
    rw [blockMatVecMul_smul, hYimage]
  have hYeval :
      (((1 / 2 : ℝ) • Y).eval x) =
        (1 / 2 : ℝ) •
          (w.toH1.grad x + z.toH1.grad x,
            matVecMul (a x) (w.toH1.grad x) -
              matVecMul (matTranspose (a x)) (z.toH1.grad x)) := by
    change ((1 / 2 : ℝ) • Y.eval x) =
      (1 / 2 : ℝ) •
        (w.toH1.grad x + z.toH1.grad x,
          matVecMul (a x) (w.toH1.grad x) -
            matVecMul (matTranspose (a x)) (z.toH1.grad x))
    rfl
  have hcross_wv :
      vecDot (matVecMul (a x) (w.toH1.grad x)) (v.toH1.grad x) =
        vecDot (w.toH1.grad x) (matVecMul (matTranspose (a x)) (v.toH1.grad x)) := by
    exact (vecDot_matVecMul_transpose (w.toH1.grad x) (v.toH1.grad x) (a x)).symm
  have hcross_zu :
      vecDot (matVecMul (matTranspose (a x)) (z.toH1.grad x)) (u.toH1.grad x) =
        vecDot (z.toH1.grad x) (matVecMul (a x) (u.toH1.grad x)) := by
    simpa [matTranspose] using
      (vecDot_matVecMul_transpose (z.toH1.grad x) (u.toH1.grad x) (matTranspose (a x))).symm
  unfold blockFirstVariationIntegrand scalarFirstVariationIntegrand
  rw [hYhalf, hXhalf, hYeval]
  simp [blockVecDot,
    Homogenization.adjointCoeffField, symmPart_matTranspose, vecDot_add_left, vecDot_add_right,
    vecDot_neg_left, vecDot_neg_right, vecDot_smul_left, vecDot_smul_right,
    sub_eq_add_neg, hcross_u, hcross_v_symm, hcross_wv, hcross_zu]
  ring_nf

/-- Averaged form of
`blockFirstVariationIntegrand_pair_half_eq_scalarFirstVariation_sum_on_of_isEllipticFieldOn`. -/
theorem volumeAverage_blockFirstVariationIntegrand_pair_half_eq_scalarFirstVariation_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u w : AHarmonicFunction a U)
    (v z : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    volumeAverage U
        (blockFirstVariationIntegrand a (p, q) (qStar, pStar)
          (blockResponsePairHalfState a u v)
          (blockResponsePairHalfState a w z)) =
      (1 / 2 : ℝ) *
          volumeAverage U
            (scalarFirstVariationIntegrand U a (p - pStar) (qStar - q) u w) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v z) := by
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  let f : Vec d → ℝ :=
    scalarFirstVariationIntegrand U a (p - pStar) (qStar - q) u w
  let g : Vec d → ℝ :=
    scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a)
      (pStar + p) (qStar + q) v z
  have hAvg :
      volumeAverage U
          (blockFirstVariationIntegrand a (p, q) (qStar, pStar)
            (blockResponsePairHalfState a u v)
            (blockResponsePairHalfState a w z)) =
        volumeAverage U (fun x => (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * g x) := by
    unfold volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    simpa [f, g] using
      blockFirstVariationIntegrand_pair_half_eq_scalarFirstVariation_sum_on_of_isEllipticFieldOn
        (a := a) hEll p pStar q qStar u w v z x hx
  have hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hIntAdj : ResponseLinearIntegrabilityData U (Homogenization.adjointCoeffField a) :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllAdj
  have hf : MeasureTheory.IntegrableOn f U :=
    hInt.firstVariation (p - pStar) (qStar - q) u w
  have hg : MeasureTheory.IntegrableOn g U :=
    hIntAdj.firstVariation (pStar + p) (qStar + q) v z
  have hf_half : MeasureTheory.IntegrableOn (((1 / 2 : ℝ) • f)) U := by
    simpa [MeasureTheory.IntegrableOn] using hf.integrable.smul (1 / 2 : ℝ)
  have hg_half : MeasureTheory.IntegrableOn (((1 / 2 : ℝ) • g)) U := by
    simpa [MeasureTheory.IntegrableOn] using hg.integrable.smul (1 / 2 : ℝ)
  have hfun :
      (fun x => (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * g x) =
        ((1 / 2 : ℝ) • f) + ((1 / 2 : ℝ) • g) := by
    funext x
    simp [smul_eq_mul]
  rw [hAvg, hfun, volumeAverage_add hf_half hg_half, volumeAverage_smul,
    volumeAverage_smul]

/-- The pointwise state pairing of a primal/adjoint half-pair is the
quarter-difference of the primal and adjoint scalar energies. -/
theorem statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    (fun x =>
      vecDot ((blockResponsePairHalfState a u v).potential x)
        ((blockResponsePairHalfState a u v).flux x)) =
      fun x =>
        (1 / 4 : ℝ) * scalarVariationEnergyIntegrand a u x -
          (1 / 4 : ℝ) *
            scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v x := by
  funext x
  have hself_u :
      vecDot (u.toH1.grad x) (matVecMul (a x) (u.toH1.grad x)) =
        vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) :=
    vecDot_matVecMul_self_eq_symmPart (a x) (u.toH1.grad x)
  have hself_v :
      vecDot (v.toH1.grad x) (matVecMul (matTranspose (a x)) (v.toH1.grad x)) =
        vecDot (v.toH1.grad x)
          (matVecMul (symmPart (Homogenization.adjointCoeffField a x)) (v.toH1.grad x)) := by
    simpa [Homogenization.adjointCoeffField] using
      vecDot_matVecMul_self_eq_symmPart (matTranspose (a x)) (v.toH1.grad x)
  have hcross :
      vecDot (u.toH1.grad x) (matVecMul (matTranspose (a x)) (v.toH1.grad x)) =
        vecDot (v.toH1.grad x) (matVecMul (a x) (u.toH1.grad x)) := by
    calc
      vecDot (u.toH1.grad x) (matVecMul (matTranspose (a x)) (v.toH1.grad x))
          = vecDot (matVecMul (a x) (u.toH1.grad x)) (v.toH1.grad x) := by
              rw [vecDot_matVecMul_transpose]
      _ = vecDot (v.toH1.grad x) (matVecMul (a x) (u.toH1.grad x)) := by
              rw [vecDot_comm]
  have hpot :
      (blockResponsePairHalfState a u v).potential x =
        (1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x) := rfl
  have hflux :
      (blockResponsePairHalfState a u v).flux x =
        (1 / 2 : ℝ) •
          (matVecMul (a x) (u.toH1.grad x) -
            matVecMul (matTranspose (a x)) (v.toH1.grad x)) := rfl
  rw [hpot, hflux]
  simp [scalarVariationEnergyIntegrand, Homogenization.adjointCoeffField,
    vecDot_add_left, vecDot_add_right, vecDot_neg_right, vecDot_smul_left,
    vecDot_smul_right, sub_eq_add_neg, hself_u, hself_v, hcross]
  ring_nf

/-- Averaged state-pairing form for a primal/adjoint half-pair. -/
theorem volumeAverage_statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    volumeAverage U
        (fun x =>
          vecDot ((blockResponsePairHalfState a u v).potential x)
            ((blockResponsePairHalfState a u v).flux x)) =
      (1 / 4 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a u) -
        (1 / 4 : ℝ) *
          volumeAverage U
            (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v) := by
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  let f : Vec d → ℝ := scalarVariationEnergyIntegrand a u
  let g : Vec d → ℝ := scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v
  rw [statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub]
  have hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hIntAdj : ResponseLinearIntegrabilityData U (Homogenization.adjointCoeffField a) :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllAdj
  have hf : MeasureTheory.IntegrableOn f U := hInt.energy u
  have hg : MeasureTheory.IntegrableOn g U := hIntAdj.energy v
  have hf_quarter : MeasureTheory.IntegrableOn (((1 / 4 : ℝ) • f)) U := by
    simpa [MeasureTheory.IntegrableOn] using hf.integrable.smul (1 / 4 : ℝ)
  have hg_quarter : MeasureTheory.IntegrableOn (((1 / 4 : ℝ) • g)) U := by
    simpa [MeasureTheory.IntegrableOn] using hg.integrable.smul (1 / 4 : ℝ)
  have hfun :
      (fun x => (1 / 4 : ℝ) * f x - (1 / 4 : ℝ) * g x) =
        ((1 / 4 : ℝ) • f) - ((1 / 4 : ℝ) • g) := by
    funext x
    simp [smul_eq_mul]
  rw [hfun, volumeAverage_sub hf_quarter hg_quarter, volumeAverage_smul,
    volumeAverage_smul]

end

end Homogenization
