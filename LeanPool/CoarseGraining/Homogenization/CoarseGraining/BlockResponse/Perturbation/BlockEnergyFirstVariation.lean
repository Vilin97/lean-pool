/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.VolumeAverage

/-! # Block Energy First Variation -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse perturbation -- blockEnergyAverage and scalarFirstVariation

blockEnergyAverage_blockResponsePairHalfState = quarter scalarVariationEnergySum
under IsEllipticFieldOn, together with the three scalarFirstVariation-zero
theorems (zero_right, neg_left_zero, neg_left_right) for ae-equal pair-half
states under IsBlockMuAdmissible.
-/

/-- The half-pair witness has block energy equal to one quarter of the sum of
the primal and adjoint scalar variation energies. -/
theorem blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    blockEnergyAverage U a (blockResponsePairHalfState a u v) =
      (1 / 4 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a u) +
        (1 / 4 : ℝ) *
          volumeAverage U
            (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v) := by
  have hsplit :=
    volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn_of_finiteMeasure
      (a := a) hU hEll (p := 0) (pStar := 0) (q := 0) (qStar := 0) u v
  have hleft :
      volumeAverage U
          (blockResponseIntegrand a (0, 0) (0, 0) (blockResponsePairHalfState a u v)) =
        -(blockEnergyAverage U a (blockResponsePairHalfState a u v)) := by
    have hfun :
        blockResponseIntegrand a (0, 0) (0, 0) (blockResponsePairHalfState a u v) =
          fun x => -blockEnergyDensity a (blockResponsePairHalfState a u v) x := by
      funext x
      simp [blockResponseIntegrand, blockVecDot, vecDot_zero_left]
    calc
      volumeAverage U
          (blockResponseIntegrand a (0, 0) (0, 0) (blockResponsePairHalfState a u v)) =
        volumeAverage U (fun x => -blockEnergyDensity a (blockResponsePairHalfState a u v) x) := by
          rw [hfun]
      _ = volumeAverage U ((-1 : ℝ) • blockEnergyDensity a (blockResponsePairHalfState a u v)) := by
          congr 1
          funext x
          simp [smul_eq_mul]
      _ = -(blockEnergyAverage U a (blockResponsePairHalfState a u v)) := by
          simpa [blockEnergyAverage, smul_eq_mul] using
            (volumeAverage_smul U (-1 : ℝ)
              (blockEnergyDensity a (blockResponsePairHalfState a u v)))
  have hu :
      volumeAverage U (scalarResponseIntegrand U a 0 0 u) =
        (-(1 / 2 : ℝ)) * volumeAverage U (scalarVariationEnergyIntegrand a u) := by
    have hfun :
        scalarResponseIntegrand U a 0 0 u =
          (-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a u := by
      funext x
      simp [scalarResponseIntegrand, scalarVariationEnergyIntegrand, smul_eq_mul,
        vecDot_zero_left]
    calc
      volumeAverage U (scalarResponseIntegrand U a 0 0 u) =
        volumeAverage U ((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a u) := by
          rw [hfun]
      _ = (-(1 / 2 : ℝ)) * volumeAverage U (scalarVariationEnergyIntegrand a u) := by
          simpa [smul_eq_mul] using
            (volumeAverage_smul U (-(1 / 2 : ℝ)) (scalarVariationEnergyIntegrand a u))
  have hv :
      volumeAverage U
          (scalarResponseIntegrand U (Homogenization.adjointCoeffField a) 0 0 v) =
        (-(1 / 2 : ℝ)) *
          volumeAverage U
            (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v) := by
    have hfun :
        scalarResponseIntegrand U (Homogenization.adjointCoeffField a) 0 0 v =
          (-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v := by
      funext x
      simp [scalarResponseIntegrand, scalarVariationEnergyIntegrand, smul_eq_mul,
        vecDot_zero_left]
    calc
      volumeAverage U
          (scalarResponseIntegrand U (Homogenization.adjointCoeffField a) 0 0 v) =
        volumeAverage U
          ((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v) := by
            rw [hfun]
      _ = (-(1 / 2 : ℝ)) *
            volumeAverage U
              (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v) := by
            simpa [smul_eq_mul] using
              (volumeAverage_smul U (-(1 / 2 : ℝ))
              (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v))
  linarith [hleft, hsplit, hu, hv]

/--
Decoupling lemma for the pure-flux slice.

If a recovered `\mu`-admissible state at coarse data `(0,q)` is a.e. a
primal/adjoint half-pair, then the primal member of the half-pair satisfies the
scalar Euler-Lagrange identity for `ResponseJ U 0 q a`.
-/
theorem scalarFirstVariation_zero_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (X : BlockState d)
    (hEq :
      (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U]
        X.eval)
    (hAdm : IsBlockMuAdmissible U (0, q) X) :
    ∀ w : AHarmonicFunction a U,
      volumeAverage U (scalarFirstVariationIntegrand U a 0 q u w) = 0 := by
  intro w
  let zeroAdj : AHarmonicFunction (Homogenization.adjointCoeffField a) U := 0
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  let T : BlockState d := blockResponsePairHalfState a w zeroAdj
  let Ycorr : BlockState d :=
    { potential := fun x => X.potential x - (0 : Vec d)
      flux := fun x => X.flux x - q }
  have hT : BlockResponseSpace a U T := by
    simpa [T, zeroAdj, blockResponsePairHalfState, blockResponsePairState] using
      (blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn
        (a := a) hEll w zeroAdj)
  have hYtest : IsBlockTestOn U Ycorr := by
    refine ⟨?_, ?_⟩
    · simpa [Ycorr] using! hAdm.isPotentialZeroTrace
    · simpa [Ycorr] using! hAdm.isSolenoidalZeroNormalTrace
  have horth :
      ∫ x in U,
        blockVecDot (Ycorr.eval x)
          (blockMatVecMul (blockCoeffField a x) (T.eval x)) ∂MeasureTheory.volume = 0 :=
    hT.2.2 Ycorr hYtest
  have hLowerT :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x) (T.eval x)).2)
        =ᵐ[volumeMeasureOn U] fun x => T.potential x := by
    have h :=
      blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
        (a := a) hEll w zeroAdj
    filter_upwards [h] with x hx
    simpa [T, zeroAdj, blockResponsePairHalfState, blockResponsePairState] using! hx
  have hBlock :
      volumeAverage U
        (blockFirstVariationIntegrand a (0, (0 : Vec d)) (q, (0 : Vec d)) Xpair T) = 0 := by
    unfold volumeAverage
    have hInt :
        ∫ x in U,
          blockFirstVariationIntegrand a (0, (0 : Vec d)) (q, (0 : Vec d)) Xpair T x
            ∂MeasureTheory.volume =
        ∫ x in U,
          -blockVecDot (Ycorr.eval x)
            (blockMatVecMul (blockCoeffField a x) (T.eval x)) ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hEq, hLowerT] with x hxEq hxLower
      have hcomm :
          blockVecDot (T.eval x)
              (blockMatVecMul (blockCoeffField a x) (Xpair.eval x)) =
            blockVecDot (X.eval x)
              (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
        rw [hxEq]
        simpa [blockCoeffField] using
          blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm (a x) (T.eval x) (X.eval x)
      have hQ :
          blockVecDot (q, (0 : Vec d)) (T.eval x) =
            blockVecDot ((0 : Vec d), q)
              (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
        calc
          blockVecDot (q, (0 : Vec d)) (T.eval x) = vecDot q (T.potential x) := by
            simp [BlockState.eval, blockVecDot, vecDot_zero_left]
          _ =
              vecDot q ((blockMatVecMul (blockCoeffField a x) (T.eval x)).2) := by
                rw [hxLower]
          _ =
              blockVecDot ((0 : Vec d), q)
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
                simp [blockVecDot, vecDot_zero_left]
      calc
        blockFirstVariationIntegrand a (0, (0 : Vec d)) (q, (0 : Vec d)) Xpair T x
            =
              blockVecDot (q, (0 : Vec d)) (T.eval x) -
                blockVecDot (T.eval x)
                  (blockMatVecMul (blockCoeffField a x) (Xpair.eval x)) := by
              simp [blockFirstVariationIntegrand, blockVecDot, vecDot_zero_left]
        _ =
              blockVecDot ((0 : Vec d), q)
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) -
                blockVecDot (X.eval x)
                  (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
              rw [hQ, hcomm]
        _ =
              -blockVecDot (Ycorr.eval x)
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
              simp [Ycorr, BlockState.eval, blockVecDot, sub_eq_add_neg, vecDot_add_left,
                vecDot_neg_left, vecDot_zero_left]
              ring_nf
    rw [hInt, MeasureTheory.integral_neg, horth, neg_zero, mul_zero]
  have hsplit :=
    volumeAverage_blockFirstVariationIntegrand_pair_half_eq_scalarFirstVariation_sum_of_isEllipticFieldOn
      (a := a) hU hEll (0 : Vec d) (0 : Vec d) (0 : Vec d) q u w v zeroAdj
  have hsplit' :
      volumeAverage U
          (blockFirstVariationIntegrand a (0, (0 : Vec d)) (q, (0 : Vec d)) Xpair T) =
        (1 / 2 : ℝ) *
            volumeAverage U (scalarFirstVariationIntegrand U a 0 q u w) +
          (1 / 2 : ℝ) *
            volumeAverage U
              (scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a)
                0 q v zeroAdj) := by
    simpa [Xpair, T] using hsplit
  have hAdjZero :
      volumeAverage U
        (scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a) 0 q v zeroAdj) = 0 := by
    have hfun :
        scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a) 0 q v zeroAdj =
          fun _ => 0 := by
      funext x
      simp [scalarFirstVariationIntegrand, zeroAdj, vecDot_zero_left, vecDot_zero_right]
    rw [hfun]
    simp [volumeAverage]
  linarith [hBlock, hsplit', hAdjZero]

/--
Decoupling lemma for the pure-gradient slice.

The sign is forced by the block convention: a recovered `\mu`-admissible state
at coarse data `(p,0)` yields the primal scalar Euler-Lagrange identity for
`ResponseJ U (-p) 0 a`. The final energy statement removes this sign using the
quadratic homogeneity of `ResponseJ`.
-/
theorem scalarFirstVariation_neg_left_zero_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p : Vec d)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (X : BlockState d)
    (hEq :
      (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U]
        X.eval)
    (hAdm : IsBlockMuAdmissible U (p, 0) X) :
    ∀ w : AHarmonicFunction a U,
      volumeAverage U (scalarFirstVariationIntegrand U a (-p) 0 u w) = 0 := by
  intro w
  let zeroAdj : AHarmonicFunction (Homogenization.adjointCoeffField a) U := 0
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  let T : BlockState d := blockResponsePairHalfState a w zeroAdj
  let Ycorr : BlockState d :=
    { potential := fun x => X.potential x - p
      flux := fun x => X.flux x - (0 : Vec d) }
  have hT : BlockResponseSpace a U T := by
    simpa [T, zeroAdj, blockResponsePairHalfState, blockResponsePairState] using
      (blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn
        (a := a) hEll w zeroAdj)
  have hYtest : IsBlockTestOn U Ycorr := by
    refine ⟨?_, ?_⟩
    · simpa [Ycorr] using! hAdm.isPotentialZeroTrace
    · simpa [Ycorr] using! hAdm.isSolenoidalZeroNormalTrace
  have horth :
      ∫ x in U,
        blockVecDot (Ycorr.eval x)
          (blockMatVecMul (blockCoeffField a x) (T.eval x)) ∂MeasureTheory.volume = 0 :=
    hT.2.2 Ycorr hYtest
  have hUpperT :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x) (T.eval x)).1)
        =ᵐ[volumeMeasureOn U] fun x => T.flux x := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    let Y : BlockState d := blockResponsePairState a w zeroAdj
    have hYimage :
        blockMatVecMul (blockCoeffField a x) (Y.eval x) =
          (matVecMul (a x) (w.toH1.grad x) +
              matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x),
            w.toH1.grad x - zeroAdj.toH1.grad x) := by
      simpa [Y, blockResponsePairState, BlockState.eval] using
        blockMatVecMul_blockCoeffField_pair_of_isEllipticFieldOn
          (a := a) hEll hx (w.toH1.grad x) (zeroAdj.toH1.grad x)
    have hThalf :
        blockMatVecMul (blockCoeffField a x) (T.eval x) =
          (1 / 2 : ℝ) •
            (matVecMul (a x) (w.toH1.grad x) +
                matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x),
              w.toH1.grad x - zeroAdj.toH1.grad x) := by
      change
        blockMatVecMul (blockCoeffField a x) ((1 / 2 : ℝ) • Y.eval x) =
          (1 / 2 : ℝ) •
            (matVecMul (a x) (w.toH1.grad x) +
                matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x),
              w.toH1.grad x - zeroAdj.toH1.grad x)
      rw [blockMatVecMul_smul, hYimage]
    calc
      (blockMatVecMul (blockCoeffField a x) (T.eval x)).1 =
          ((1 / 2 : ℝ) •
            (matVecMul (a x) (w.toH1.grad x) +
                matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x),
              w.toH1.grad x - zeroAdj.toH1.grad x)).1 := by
            rw [hThalf]
      _ = T.flux x := by
            change
              (1 / 2 : ℝ) •
                  (matVecMul (a x) (w.toH1.grad x) +
                    matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x)) =
                (1 / 2 : ℝ) •
                  (matVecMul (a x) (w.toH1.grad x) -
                    matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x))
            simp [zeroAdj, matVecMul_zero]
  have hBlock :
      volumeAverage U
        (blockFirstVariationIntegrand a (0, (0 : Vec d)) (0, p) Xpair T) = 0 := by
    unfold volumeAverage
    have hInt :
        ∫ x in U,
          blockFirstVariationIntegrand a (0, (0 : Vec d)) (0, p) Xpair T x
            ∂MeasureTheory.volume =
        ∫ x in U,
          -blockVecDot (Ycorr.eval x)
            (blockMatVecMul (blockCoeffField a x) (T.eval x)) ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hEq, hUpperT] with x hxEq hxUpper
      have hcomm :
          blockVecDot (T.eval x)
              (blockMatVecMul (blockCoeffField a x) (Xpair.eval x)) =
            blockVecDot (X.eval x)
              (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
        rw [hxEq]
        simpa [blockCoeffField] using
          blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm (a x) (T.eval x) (X.eval x)
      have hP :
          blockVecDot (0, p) (T.eval x) =
            blockVecDot (p, (0 : Vec d))
              (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
        calc
          blockVecDot (0, p) (T.eval x) = vecDot p (T.flux x) := by
            simp [BlockState.eval, blockVecDot, vecDot_zero_left]
          _ =
              vecDot p ((blockMatVecMul (blockCoeffField a x) (T.eval x)).1) := by
                rw [hxUpper]
          _ =
              blockVecDot (p, (0 : Vec d))
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
                simp [blockVecDot, vecDot_zero_left]
      calc
        blockFirstVariationIntegrand a (0, (0 : Vec d)) (0, p) Xpair T x
            =
              blockVecDot (0, p) (T.eval x) -
                blockVecDot (T.eval x)
                  (blockMatVecMul (blockCoeffField a x) (Xpair.eval x)) := by
              simp [blockFirstVariationIntegrand, blockVecDot, vecDot_zero_left]
        _ =
              blockVecDot (p, (0 : Vec d))
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) -
                blockVecDot (X.eval x)
                  (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
              rw [hP, hcomm]
        _ =
              -blockVecDot (Ycorr.eval x)
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
              simp [Ycorr, BlockState.eval, blockVecDot, sub_eq_add_neg, vecDot_add_left,
                vecDot_neg_left, vecDot_zero_left]
              ring_nf
    rw [hInt, MeasureTheory.integral_neg, horth, neg_zero, mul_zero]
  have hsplit :=
    volumeAverage_blockFirstVariationIntegrand_pair_half_eq_scalarFirstVariation_sum_of_isEllipticFieldOn
      (a := a) hU hEll (0 : Vec d) p (0 : Vec d) (0 : Vec d) u w v zeroAdj
  have hsplit' :
      volumeAverage U
          (blockFirstVariationIntegrand a (0, (0 : Vec d)) (0, p) Xpair T) =
        (1 / 2 : ℝ) *
            volumeAverage U (scalarFirstVariationIntegrand U a (-p) 0 u w) +
          (1 / 2 : ℝ) *
            volumeAverage U
              (scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a)
                p 0 v zeroAdj) := by
    simpa [Xpair, T] using hsplit
  have hAdjZero :
      volumeAverage U
        (scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a) p 0 v zeroAdj) = 0 := by
    have hfun :
        scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a) p 0 v zeroAdj =
          fun _ => 0 := by
      funext x
      simp [scalarFirstVariationIntegrand, zeroAdj, vecDot_zero_left, vecDot_zero_right,
        matVecMul_zero]
    rw [hfun]
    simp [volumeAverage]
  linarith [hBlock, hsplit', hAdjZero]

/--
Decoupling lemma for arbitrary block data.

The sign in the primal scalar first variation is dictated by the block
convention: a recovered `\mu`-admissible state at coarse datum `(p,q)` yields
the Euler-Lagrange identity for `ResponseJ U (-p) q a`.
-/
theorem scalarFirstVariation_neg_left_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (X : BlockState d)
    (hEq :
      (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U]
        X.eval)
    (hAdm : IsBlockMuAdmissible U (p, q) X) :
    ∀ w : AHarmonicFunction a U,
      volumeAverage U (scalarFirstVariationIntegrand U a (-p) q u w) = 0 := by
  intro w
  let zeroAdj : AHarmonicFunction (Homogenization.adjointCoeffField a) U := 0
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  let T : BlockState d := blockResponsePairHalfState a w zeroAdj
  let Ycorr : BlockState d :=
    { potential := fun x => X.potential x - p
      flux := fun x => X.flux x - q }
  have hT : BlockResponseSpace a U T := by
    simpa [T, zeroAdj, blockResponsePairHalfState, blockResponsePairState] using
      (blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn
        (a := a) hEll w zeroAdj)
  have hYtest : IsBlockTestOn U Ycorr := by
    refine ⟨?_, ?_⟩
    · simpa [Ycorr] using! hAdm.isPotentialZeroTrace
    · simpa [Ycorr] using! hAdm.isSolenoidalZeroNormalTrace
  have horth :
      ∫ x in U,
        blockVecDot (Ycorr.eval x)
          (blockMatVecMul (blockCoeffField a x) (T.eval x)) ∂MeasureTheory.volume = 0 :=
    hT.2.2 Ycorr hYtest
  have hLowerT :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x) (T.eval x)).2)
        =ᵐ[volumeMeasureOn U] fun x => T.potential x := by
    have h :=
      blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
        (a := a) hEll w zeroAdj
    filter_upwards [h] with x hx
    simpa [T, zeroAdj, blockResponsePairHalfState, blockResponsePairState] using! hx
  have hUpperT :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x) (T.eval x)).1)
        =ᵐ[volumeMeasureOn U] fun x => T.flux x := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    let Y : BlockState d := blockResponsePairState a w zeroAdj
    have hYimage :
        blockMatVecMul (blockCoeffField a x) (Y.eval x) =
          (matVecMul (a x) (w.toH1.grad x) +
              matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x),
            w.toH1.grad x - zeroAdj.toH1.grad x) := by
      simpa [Y, blockResponsePairState, BlockState.eval] using
        blockMatVecMul_blockCoeffField_pair_of_isEllipticFieldOn
          (a := a) hEll hx (w.toH1.grad x) (zeroAdj.toH1.grad x)
    have hThalf :
        blockMatVecMul (blockCoeffField a x) (T.eval x) =
          (1 / 2 : ℝ) •
            (matVecMul (a x) (w.toH1.grad x) +
                matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x),
              w.toH1.grad x - zeroAdj.toH1.grad x) := by
      change
        blockMatVecMul (blockCoeffField a x) ((1 / 2 : ℝ) • Y.eval x) =
          (1 / 2 : ℝ) •
            (matVecMul (a x) (w.toH1.grad x) +
                matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x),
              w.toH1.grad x - zeroAdj.toH1.grad x)
      rw [blockMatVecMul_smul, hYimage]
    calc
      (blockMatVecMul (blockCoeffField a x) (T.eval x)).1 =
          ((1 / 2 : ℝ) •
            (matVecMul (a x) (w.toH1.grad x) +
                matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x),
              w.toH1.grad x - zeroAdj.toH1.grad x)).1 := by
            rw [hThalf]
      _ = T.flux x := by
            change
              (1 / 2 : ℝ) •
                  (matVecMul (a x) (w.toH1.grad x) +
                    matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x)) =
                (1 / 2 : ℝ) •
                  (matVecMul (a x) (w.toH1.grad x) -
                    matVecMul (matTranspose (a x)) (zeroAdj.toH1.grad x))
            simp [zeroAdj, matVecMul_zero]
  have hBlock :
      volumeAverage U
        (blockFirstVariationIntegrand a (0, (0 : Vec d)) (q, p) Xpair T) = 0 := by
    unfold volumeAverage
    have hInt :
        ∫ x in U,
          blockFirstVariationIntegrand a (0, (0 : Vec d)) (q, p) Xpair T x
            ∂MeasureTheory.volume =
        ∫ x in U,
          -blockVecDot (Ycorr.eval x)
            (blockMatVecMul (blockCoeffField a x) (T.eval x)) ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hEq, hLowerT, hUpperT] with x hxEq hxLower hxUpper
      have hcomm :
          blockVecDot (T.eval x)
              (blockMatVecMul (blockCoeffField a x) (Xpair.eval x)) =
            blockVecDot (X.eval x)
              (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
        rw [hxEq]
        simpa [blockCoeffField] using
          blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm (a x) (T.eval x) (X.eval x)
      have hPQ :
          blockVecDot (q, p) (T.eval x) =
            blockVecDot (p, q)
              (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
        calc
          blockVecDot (q, p) (T.eval x) =
              vecDot q (T.potential x) + vecDot p (T.flux x) := by
                simp [BlockState.eval, blockVecDot]
          _ =
              vecDot q ((blockMatVecMul (blockCoeffField a x) (T.eval x)).2) +
                vecDot p ((blockMatVecMul (blockCoeffField a x) (T.eval x)).1) := by
                rw [hxLower, hxUpper]
          _ =
              blockVecDot (p, q)
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
                simp [blockVecDot, add_comm]
      calc
        blockFirstVariationIntegrand a (0, (0 : Vec d)) (q, p) Xpair T x
            =
              blockVecDot (q, p) (T.eval x) -
                blockVecDot (T.eval x)
                  (blockMatVecMul (blockCoeffField a x) (Xpair.eval x)) := by
              simp [blockFirstVariationIntegrand, blockVecDot, vecDot_zero_left]
        _ =
              blockVecDot (p, q)
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) -
                blockVecDot (X.eval x)
                  (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
              rw [hPQ, hcomm]
        _ =
              -blockVecDot (Ycorr.eval x)
                (blockMatVecMul (blockCoeffField a x) (T.eval x)) := by
              simp [Ycorr, BlockState.eval, blockVecDot, sub_eq_add_neg, vecDot_add_left,
                vecDot_neg_left]
              ring_nf
    rw [hInt, MeasureTheory.integral_neg, horth, neg_zero, mul_zero]
  have hsplit :=
    volumeAverage_blockFirstVariationIntegrand_pair_half_eq_scalarFirstVariation_sum_of_isEllipticFieldOn
      (a := a) hU hEll (0 : Vec d) p (0 : Vec d) q u w v zeroAdj
  have hsplit' :
      volumeAverage U
          (blockFirstVariationIntegrand a (0, (0 : Vec d)) (q, p) Xpair T) =
        (1 / 2 : ℝ) *
            volumeAverage U (scalarFirstVariationIntegrand U a (-p) q u w) +
          (1 / 2 : ℝ) *
            volumeAverage U
              (scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a)
                p q v zeroAdj) := by
    simpa [Xpair, T] using hsplit
  have hAdjZero :
      volumeAverage U
        (scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a) p q v zeroAdj) = 0 := by
    have hfun :
        scalarFirstVariationIntegrand U (Homogenization.adjointCoeffField a) p q v zeroAdj =
          fun _ => 0 := by
      funext x
      simp [scalarFirstVariationIntegrand, zeroAdj, vecDot_zero_left, vecDot_zero_right,
        matVecMul_zero]
    rw [hfun]
    simp [volumeAverage]
  linarith [hBlock, hsplit', hAdjZero]


end

end Homogenization
