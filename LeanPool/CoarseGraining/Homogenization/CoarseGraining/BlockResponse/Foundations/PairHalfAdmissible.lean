/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Foundations.PairStates
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.SigmaAdjoint
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence

/-! # Pair Half Admissible -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# BlockResponse Foundations -- pair-half admissibility

blockResponse_pair_half isBlockMuAdmissible and averagePotential /
averageFlux identities: from the basic average-eq hypothesis, under
scalarCanonicalMaximizers data (with or without basis data) and under
the IsOpenBoundedConvexDomain assumption.
-/

/-- The half-pair witness built from a primal maximizer at `(0,q)` and an
adjoint maximizer at `(0,-q)` has zero average potential. -/
theorem blockResponse_pair_half_averagePotential_eq_zero_of_scalarCanonicalMaximizers_zero_right
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} {q : Vec d}
    (u : ScalarCanonicalMaximizer U 0 q a)
    (v : ScalarCanonicalMaximizer U 0 (-q) (Homogenization.adjointCoeffField a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (Homogenization.adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (Homogenization.adjointCoeffField a) sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (hIntAdj : ResponseLinearIntegrabilityData U (Homogenization.adjointCoeffField a))
    (uGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1)
      (Homogenization.adjointCoeffField a)) :
    (fun i =>
      integralAverage U
        (fun x =>
          (blockResponsePairHalfState a
            (u : AHarmonicFunction a U)
            (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).potential x i)) = 0 := by
  ext i
  have hu_int :
      MeasureTheory.IntegrableOn (fun x => (u : AHarmonicFunction a U).toH1.grad x i) U := by
    simpa [MeasureTheory.IntegrableOn] using
      ((u : AHarmonicFunction a U).toH1.grad_memL2 i).integrable
        (by norm_num : (1 : ENNReal) ≤ 2)
  have hv_int :
      MeasureTheory.IntegrableOn
        (fun x => (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad x i) U := by
    simpa [MeasureTheory.IntegrableOn] using
      ((v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad_memL2 i).integrable
        (by norm_num : (1 : ENNReal) ≤ 2)
  have hu_avg :
      volumeAverage U (fun x => (u : AHarmonicFunction a U).toH1.grad x i) =
        (matVecMul (sigmaStarInvCoarse U a) q) i := by
    simpa [matVecMul_zero] using congrFun
      (ScalarCanonicalMaximizer.averageGradientFormulaCanonical
        (v := u) (hS := hS) (hK := hK) (hdet := hdet)
        (hInt := hInt) (vGrad := uGrad)) i
  have hv_avg_adj :
      volumeAverage U
        (fun x => (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad x i) =
          (matVecMul (sigmaStarInvCoarse U (Homogenization.adjointCoeffField a)) (-q)) i := by
    simpa [matVecMul_zero] using congrFun
      (ScalarCanonicalMaximizer.averageGradientFormulaCanonical
        (v := v) (a := Homogenization.adjointCoeffField a)
        (hS := hSAdj) (hK := hKAdj) (hdet := hdet)
        (hInt := hIntAdj) (vGrad := vGrad)) i
  have hv_avg :
      volumeAverage U
        (fun x => (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad x i) =
          -(matVecMul (sigmaStarInvCoarse U a) q) i := by
    rw [sigmaStarInvCoarse_adjointCoeffField_eq hS hSAdj] at hv_avg_adj
    simpa [matVecMul_neg] using hv_avg_adj
  change volumeAverage U
      (fun x =>
        (blockResponsePairHalfState a
          (u : AHarmonicFunction a U)
          (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).potential x i) = 0
  have hsplit :
      (fun x =>
        (blockResponsePairHalfState a
          (u : AHarmonicFunction a U)
          (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).potential x i) =
        (1 / 2 : ℝ) •
          ((fun x => (u : AHarmonicFunction a U).toH1.grad x i) +
            fun x => (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad x i) := by
    funext x
    rfl
  rw [hsplit, volumeAverage_smul U (1 / 2 : ℝ), volumeAverage_add hu_int hv_int, hu_avg, hv_avg]
  ring

/-- Bundled basis-data wrapper for the previous zero-average-potential identity. -/
theorem
    blockResponse_pair_half_averagePotential_eq_zero_of_scalarCanonicalMaximizers_zero_right_of_basisData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} {q : Vec d}
    (u : ScalarCanonicalMaximizer U 0 q a)
    (v : ScalarCanonicalMaximizer U 0 (-q) (Homogenization.adjointCoeffField a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (Homogenization.adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (Homogenization.adjointCoeffField a) sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (hIntAdj : ResponseLinearIntegrabilityData U (Homogenization.adjointCoeffField a))
    (basisGrad : Homogenization.ScalarCanonicalMaximizer.GradientBasisData U a)
    (basisGradAdj :
      Homogenization.ScalarCanonicalMaximizer.GradientBasisData U
        (Homogenization.adjointCoeffField a)) :
    (fun i =>
      integralAverage U
        (fun x =>
          (blockResponsePairHalfState a
            (u : AHarmonicFunction a U)
            (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).potential x i)) = 0 := by
  exact
    blockResponse_pair_half_averagePotential_eq_zero_of_scalarCanonicalMaximizers_zero_right
      (u := u) (v := v) hS hK hSAdj hKAdj hdet hInt hIntAdj basisGrad.grad basisGradAdj.grad

/-- The half-pair witness built from a primal maximizer at `(0,q)` and an
adjoint maximizer at `(0,-q)` has average flux equal to `q`. -/
theorem blockResponse_pair_half_averageFlux_eq_of_scalarCanonicalMaximizers_zero_right
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} {q : Vec d}
    (u : ScalarCanonicalMaximizer U 0 q a)
    (v : ScalarCanonicalMaximizer U 0 (-q) (Homogenization.adjointCoeffField a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (Homogenization.adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (Homogenization.adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (Homogenization.adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (hIntAdj : ResponseLinearIntegrabilityData U (Homogenization.adjointCoeffField a))
    (uFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0
      (Homogenization.adjointCoeffField a)) :
    (fun i =>
      integralAverage U
        (fun x =>
          (blockResponsePairHalfState a
            (u : AHarmonicFunction a U)
            (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).flux x i)) = q := by
  ext i
  have hu_int :
      MeasureTheory.IntegrableOn
        (fun x => matVecMul (a x) ((u : AHarmonicFunction a U).toH1.grad x) i) U := by
    simpa [vecDot_single_left] using
      hInt.flux (Pi.single i 1) (u : AHarmonicFunction a U)
  have hv_int :
      MeasureTheory.IntegrableOn
        (fun x =>
          matVecMul (matTranspose (a x))
            ((v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad x) i) U := by
    simpa [Homogenization.adjointCoeffField, vecDot_single_left] using
      hIntAdj.flux (Pi.single i 1)
        (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
  have hu_avg :
      volumeAverage U
        (fun x => matVecMul (a x) ((u : AHarmonicFunction a U).toH1.grad x) i) =
          (q - matVecMul (matTranspose (kappaCoarse U a))
            (matVecMul (sigmaStarInvCoarse U a) q)) i := by
    simpa [matVecMul_zero] using congrFun
      (ScalarCanonicalMaximizer.averageFluxFormulaCanonical
        (v := u) (hS := hS) (hK := hK) (hSigma := hSigma) (hdet := hdet)
        (hInt := hInt) (vFlux := uFlux)) i
  have hv_avg_adj :
      volumeAverage U
        (fun x =>
          matVecMul (matTranspose (a x))
            ((v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad x) i) =
          ((-q) - matVecMul (matTranspose (kappaCoarse U (Homogenization.adjointCoeffField a)))
            (matVecMul (sigmaStarInvCoarse U (Homogenization.adjointCoeffField a)) (-q))) i := by
    simpa [Homogenization.adjointCoeffField, matVecMul_zero] using congrFun
      (ScalarCanonicalMaximizer.averageFluxFormulaCanonical
        (v := v) (a := Homogenization.adjointCoeffField a)
        (hS := hSAdj) (hK := hKAdj) (hSigma := hSigmaAdj) (hdet := hdet)
        (hInt := hIntAdj) (vFlux := vFlux)) i
  have hv_avg :
      volumeAverage U
        (fun x =>
          matVecMul (matTranspose (a x))
            ((v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad x) i) =
          (-q - matVecMul (matTranspose (kappaCoarse U a))
            (matVecMul (sigmaStarInvCoarse U a) q)) i := by
    rw [sigmaStarInvCoarse_adjointCoeffField_eq hS hSAdj,
      kappaCoarse_adjointCoeffField_eq_neg hS hK hSAdj hKAdj hdet] at hv_avg_adj
    simpa [matVecMul_neg, neg_matVecMul, Matrix.transpose_neg, matTranspose, sub_eq_add_neg] using
      hv_avg_adj
  change volumeAverage U
      (fun x =>
        (blockResponsePairHalfState a
          (u : AHarmonicFunction a U)
          (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).flux x i) = q i
  have hsplit :
      (fun x =>
        (blockResponsePairHalfState a
          (u : AHarmonicFunction a U)
          (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).flux x i) =
        (1 / 2 : ℝ) •
          ((fun x => matVecMul (a x) ((u : AHarmonicFunction a U).toH1.grad x) i) -
            fun x =>
              matVecMul (matTranspose (a x))
                ((v : AHarmonicFunction (Homogenization.adjointCoeffField a) U).toH1.grad x) i) := by
    funext x
    rfl
  rw [hsplit, volumeAverage_smul U (1 / 2 : ℝ), volumeAverage_sub hu_int hv_int, hu_avg, hv_avg]
  simp [Pi.sub_apply, sub_eq_add_neg]
  ring

/-- Bundled basis-data wrapper for the previous average-flux identity. -/
theorem blockResponse_pair_half_averageFlux_eq_of_scalarCanonicalMaximizers_zero_right_of_basisData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} {q : Vec d}
    (u : ScalarCanonicalMaximizer U 0 q a)
    (v : ScalarCanonicalMaximizer U 0 (-q) (Homogenization.adjointCoeffField a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (Homogenization.adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (Homogenization.adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (Homogenization.adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (hIntAdj : ResponseLinearIntegrabilityData U (Homogenization.adjointCoeffField a))
    (basisFlux : Homogenization.ScalarCanonicalMaximizer.FluxBasisData U a)
    (basisFluxAdj :
      Homogenization.ScalarCanonicalMaximizer.FluxBasisData U
        (Homogenization.adjointCoeffField a)) :
    (fun i =>
      integralAverage U
        (fun x =>
          (blockResponsePairHalfState a
            (u : AHarmonicFunction a U)
            (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).flux x i)) = q := by
  exact
    blockResponse_pair_half_averageFlux_eq_of_scalarCanonicalMaximizers_zero_right
      (u := u) (v := v) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet hInt hIntAdj
      basisFlux.flux basisFluxAdj.flux

/-- Convex-domain wrapper for the zero-average-potential identity. The gradient
basis-data packages are produced automatically from the Stage-6 canonical
maximizer existence theorem. -/
theorem blockResponse_pair_half_averagePotential_eq_zero_of_scalarCanonicalMaximizers_zero_right_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam : ℝ} {sigmaStar kappa : Mat d} {q : Vec d}
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (u : ScalarCanonicalMaximizer U 0 q a)
    (v : ScalarCanonicalMaximizer U 0 (-q) (Homogenization.adjointCoeffField a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (Homogenization.adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (Homogenization.adjointCoeffField a) sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (fun i =>
      integralAverage U
        (fun x =>
          (blockResponsePairHalfState a
            (u : AHarmonicFunction a U)
            (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).potential x i)) = 0 := by
  classical
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hne : Set.Nonempty U := by
    by_contra hne
    have hEmpty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact hvol (by simp [hEmpty])
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  let basisGrad : ScalarCanonicalMaximizer.GradientBasisData U a :=
    Classical.choice
      (ScalarCanonicalMaximizer.GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := a) hne hConv hEll)
  let basisGradAdj :
      ScalarCanonicalMaximizer.GradientBasisData U (Homogenization.adjointCoeffField a) :=
    Classical.choice
      (ScalarCanonicalMaximizer.GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := Homogenization.adjointCoeffField a) hne hConv hEllAdj)
  exact
    blockResponse_pair_half_averagePotential_eq_zero_of_scalarCanonicalMaximizers_zero_right_of_basisData
      (u := u) (v := v) hS hK hSAdj hKAdj hdet
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllAdj)
      basisGrad basisGradAdj

/-- Explicitly named existential convex-domain version of the previous
average-potential identity. The scalar canonical maximizers are chosen
internally from the bounded-open-convex existence theorem. -/
theorem
    exists_scalarCanonicalMaximizers_blockResponse_pair_half_averagePotential_eq_zero_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam : ℝ} {sigmaStar kappa : Mat d} {q : Vec d}
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (Homogenization.adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (Homogenization.adjointCoeffField a) sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    ∃ u : ScalarCanonicalMaximizer U 0 q a,
      ∃ v : ScalarCanonicalMaximizer U 0 (-q) (Homogenization.adjointCoeffField a),
        (fun i =>
          integralAverage U
            (fun x =>
              (blockResponsePairHalfState a
                (u : AHarmonicFunction a U)
                (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).potential x i)) = 0 := by
  classical
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hne : Set.Nonempty U := by
    by_contra hne
    have hEmpty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact hvol (by simp [hEmpty])
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := a) hne hConv hEll 0 q with
    ⟨u⟩
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := Homogenization.adjointCoeffField a) hne hConv hEllAdj 0 (-q) with
    ⟨v⟩
  refine ⟨u, v, ?_⟩
  exact
    blockResponse_pair_half_averagePotential_eq_zero_of_scalarCanonicalMaximizers_zero_right_of_isOpenBoundedConvexDomain
      hConv hEll hvol u v hS hK hSAdj hKAdj hdet

/-- Convex-domain wrapper for the average-flux identity. The flux basis-data
packages are produced automatically from the Stage-6 canonical maximizer
existence theorem. -/
theorem blockResponse_pair_half_averageFlux_eq_of_scalarCanonicalMaximizers_zero_right_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam : ℝ} {sigma sigmaStar kappa : Mat d} {q : Vec d}
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (u : ScalarCanonicalMaximizer U 0 q a)
    (v : ScalarCanonicalMaximizer U 0 (-q) (Homogenization.adjointCoeffField a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (Homogenization.adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (Homogenization.adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (Homogenization.adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    (fun i =>
      integralAverage U
        (fun x =>
          (blockResponsePairHalfState a
            (u : AHarmonicFunction a U)
            (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).flux x i)) = q := by
  classical
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hne : Set.Nonempty U := by
    by_contra hne
    have hEmpty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact hvol (by simp [hEmpty])
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  let basisFlux : ScalarCanonicalMaximizer.FluxBasisData U a :=
    Classical.choice
      (ScalarCanonicalMaximizer.FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := a) hne hConv hEll)
  let basisFluxAdj :
      ScalarCanonicalMaximizer.FluxBasisData U (Homogenization.adjointCoeffField a) :=
    Classical.choice
      (ScalarCanonicalMaximizer.FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := Homogenization.adjointCoeffField a) hne hConv hEllAdj)
  exact
    blockResponse_pair_half_averageFlux_eq_of_scalarCanonicalMaximizers_zero_right_of_basisData
      (u := u) (v := v) hS hK hSigma hSAdj hKAdj hSigmaAdj hdet
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllAdj)
      basisFlux basisFluxAdj

/-- Explicitly named existential convex-domain version of the previous
average-flux identity. The scalar canonical maximizers are chosen internally
from bounded-open-convex existence. -/
theorem
    exists_scalarCanonicalMaximizers_blockResponse_pair_half_averageFlux_eq_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam : ℝ} {sigma sigmaStar kappa : Mat d} {q : Vec d}
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hSAdj : IsSigmaStarCoarse U (Homogenization.adjointCoeffField a) sigmaStar)
    (hKAdj : IsKappaCoarse U (Homogenization.adjointCoeffField a) sigmaStar (-kappa))
    (hSigmaAdj : IsSigmaCoarse U (Homogenization.adjointCoeffField a) sigma sigmaStar (-kappa))
    (hdet : IsUnit sigmaStar.det) :
    ∃ u : ScalarCanonicalMaximizer U 0 q a,
      ∃ v : ScalarCanonicalMaximizer U 0 (-q) (Homogenization.adjointCoeffField a),
        (fun i =>
          integralAverage U
            (fun x =>
              (blockResponsePairHalfState a
                (u : AHarmonicFunction a U)
                (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)).flux x i)) = q := by
  classical
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hne : Set.Nonempty U := by
    by_contra hne
    have hEmpty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact hvol (by simp [hEmpty])
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := a) hne hConv hEll 0 q with
    ⟨u⟩
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := Homogenization.adjointCoeffField a) hne hConv hEllAdj 0 (-q) with
    ⟨v⟩
  refine ⟨u, v, ?_⟩
  exact
    blockResponse_pair_half_averageFlux_eq_of_scalarCanonicalMaximizers_zero_right_of_isOpenBoundedConvexDomain
      hConv hEll hvol u v hS hK hSigma hSAdj hKAdj hSigmaAdj hdet

theorem blockResponseIntegrand_integrableOn_pair_half_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (P Q : BlockVec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    MeasureTheory.IntegrableOn
      (blockResponseIntegrand a P Q (blockResponsePairHalfState a u v)) U := by
  exact
    blockResponseIntegrand_integrableOn_of_mem_responseSpace_of_integrabilityData_of_isEllipticFieldOn
      (hX := by
        simpa [blockResponsePairHalfState] using!
          (blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn (a := a) hEll u v))
      (hInt := blockResponseIntegrabilityData_pair_half_of_isEllipticFieldOn hEll u v)
      hEll P Q


end

end Homogenization
