/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantEnvelope
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2Response
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2RHSCoefficientLocalization

/-! # General Coarse Graining L2Two Exponent -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scale-separated general coarse-graining handoff

This file contains the repaired inhomogeneous Ch3.3 general coarse-graining
surface.  The local flux-response exponent and the positive forcing exponent
are separated, so the forcing term carries the visible inverse depth factor
`3^{-r₂(m-n)}`.
-/

noncomputable section

/-- Public general coarse-graining package with a stronger force exponent. -/
structure GeneralCoarseGrainingL2TwoExponentTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {a0 : ConstantCoeffMatrix d}
        {s r r₂ : ℝ} {j : ℕ} {g : Vec d → Vec d}
        (_ha0 : IsPositiveScalarMatrix a0.matrix)
        (w : CoarseGrainingComparisonDatum Q a a0 g),
        0 < s → 0 < r → r < s / 2 → s < 1 → r ≤ r₂ →
          ForceBesovRegularity Q r₂ g →
          homogenizationComparisonNegativeBesovLHS Q a a0 s w.u w.v ≤
            generalCoarseGrainingL2TwoExponentRHS C Q a a0 s r r₂ j g w.u

private theorem generalCoarseGrainingL2TwoExponentFluxDefectRHS_eq_const_mul_one
    {d : ℕ} [NeZero d] (C : ℝ) (Q : TriadicCube d)
    (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d) (r r₂ : ℝ) (j : ℕ)
    (g : Vec d → Vec d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    generalCoarseGrainingL2TwoExponentFluxDefectRHS C Q a a0 r r₂ j g u =
      C * generalCoarseGrainingL2TwoExponentFluxDefectRHS 1 Q a a0 r r₂ j g u := by
  unfold generalCoarseGrainingL2TwoExponentFluxDefectRHS
  ring

private theorem generalCoarseGrainingL2TwoExponentTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss_of_localizedFluxDefectBridge
    {d : ℕ} [NeZero d] {Cproj C : ℝ}
    (hC_pos : 0 < C)
    (hproj : ScalarSolutionComparisonDualityEstimateExponentLoss d Cproj)
    (hlocalized :
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {a0 : ConstantCoeffMatrix d}
        {s r r₂ : ℝ} {j : ℕ} {g : Vec d → Vec d}
        (_ha0 : IsPositiveScalarMatrix a0.matrix)
        (w : CoarseGrainingComparisonDatum Q a a0 g),
        0 < s → 0 < r → r < s / 2 → s < 1 → r ≤ r₂ →
          ForceBesovRegularity Q r₂ g →
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)) *
              (Cproj * s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
                localizedFluxDefectNegativeBesovAverageTwo Q r
                  (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) j) ≤
            generalCoarseGrainingL2TwoExponentRHS C Q a a0 s r r₂ j g w.u) :
    GeneralCoarseGrainingL2TwoExponentTheory d := by
  refine ⟨⟨C, hC_pos, ?_⟩⟩
  intro Q a a0 s r r₂ j g ha0 w hs hr hrs hs_lt hr₂ hg
  let K : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hpublic :
      homogenizationComparisonNegativeBesovLHS Q a a0 s w.u w.v ≤
        K *
          solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
            a0.matrix w.u.grad w.v.grad := by
    simpa [K] using
      homogenizationComparisonNegativeBesovLHS_le_note_constant_mul_solutionComparisonNegativeBesovLhs_publicCoeffField
        Q a a0 s w.u w.v hs
  have hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q)
        (publicCoeffField Q a) a0.matrix w.u.grad w.v.grad := by
    simpa [publicH1ToCubeSet_grad] using
      w.isHomogenizationComparisonPairOn_publicCoeffField_cubeSet
  have hF :
      MemVectorL2 (cubeSet Q)
        (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) :=
    publicH1_fluxDefect_memVectorL2_descendant_cubeSet
      (Q := Q) (R := Q) (a := a) (a0 := a0) (j := 0) w.u (by simp)
  have ha0_saved := ha0
  rcases ha0 with ⟨sigma0, hsigma0, ha0eq⟩
  have hcomparison_scalar :
      IsHomogenizationComparisonPairOn (cubeSet Q)
        (publicCoeffField Q a) (scalarMatrix (d := d) sigma0)
          w.u.grad w.v.grad := by
    simpa [ha0eq] using hcomparison
  have hF_scalar :
      MemVectorL2 (cubeSet Q)
        (fluxDefect (publicCoeffField Q a) (scalarMatrix (d := d) sigma0)
          w.u.grad) := by
    simpa [ha0eq] using hF
  have hinternal :
      solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
          a0.matrix w.u.grad w.v.grad ≤
        Cproj * s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
          localizedFluxDefectNegativeBesovAverageTwo Q r
            (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) j := by
    have hscalar :
        solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
            (scalarMatrix (d := d) sigma0) w.u.grad w.v.grad ≤
          Cproj * s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
            localizedFluxDefectNegativeBesovAverageTwo Q r
              (fluxDefect (publicCoeffField Q a) (scalarMatrix (d := d) sigma0)
                w.u.grad) j :=
      solutionComparisonNegativeBesovLhs_le_of_scalarSolutionComparisonDualityEstimateExponentLoss
        hproj Q (publicCoeffField Q a) sigma0 w.u.grad w.v.grad j
        hsigma0 hs hr hrs hs_lt hF_scalar hcomparison_scalar
    simpa [ha0eq] using hscalar
  calc
    homogenizationComparisonNegativeBesovLHS Q a a0 s w.u w.v
        ≤ K *
          solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
            a0.matrix w.u.grad w.v.grad := hpublic
    _ ≤
        K *
          (Cproj * s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
            localizedFluxDefectNegativeBesovAverageTwo Q r
              (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) j) :=
        mul_le_mul_of_nonneg_left hinternal hK_nonneg
    _ ≤ generalCoarseGrainingL2TwoExponentRHS C Q a a0 s r r₂ j g w.u :=
        hlocalized ha0_saved w hs hr hrs hs_lt hr₂ hg

private theorem generalCoarseGrainingL2TwoExponentTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss_of_const_mul_descendantCoarseFluxResponseRHSBound_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] {Cdual K : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimateExponentLoss d Cdual)
    (hK_nonneg : 0 ≤ K)
    (hData :
      ∀ Q : TriadicCube d, ∀ a : CoeffFamily d,
        _root_.Homogenization.OpenCubeDescendantDeterministicCoarseData Q
          (publicCoeffField Q a))
    (hdescendantRHS :
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {a0 : ConstantCoeffMatrix d}
        {s : ℝ} {j : ℕ} {g : Vec d → Vec d}
        (_ha0 : IsPositiveScalarMatrix a0.matrix)
        (w : CoarseGrainingComparisonDatum Q a a0 g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          ∀ R ∈ descendantsAtDepth Q j,
            cubeBesovNegativeVectorSeminormTwo R s
                (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) ≤
              K * _root_.Homogenization.coarseFluxResponseRHSBound R
                (publicCoeffField Q a) a0.matrix s w.u.grad g) :
    GeneralCoarseGrainingL2TwoExponentTheory d := by
  let Kgeom : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)
  let Cbase : ℝ := max 1 (Kgeom * (Cdual + 1) * K)
  let C : ℝ := (d : ℝ) ^ 2 * Cbase
  have hCbase_pos : 0 < Cbase := by
    dsimp [Cbase]
    exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) (Kgeom * (Cdual + 1) * K))
  have hC_pos : 0 < C := by
    dsimp [C]
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact mul_pos (sq_pos_of_pos hd_pos) hCbase_pos
  refine
    generalCoarseGrainingL2TwoExponentTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss_of_localizedFluxDefectBridge
      (Cproj := Cdual) (C := C) hC_pos hdual ?_
  intro Q a a0 s r r₂ j g ha0 w hs hr hrs hs_lt hr₂ hg₂
  let A : CoeffField d := publicCoeffField Q a
  let B : ℝ :=
    _root_.Homogenization.coarseGrainingL2FluxDefectBoundTwoExponent Q A
      a0.matrix r r₂ j w.u.grad g
  let L : ℝ :=
    _root_.Homogenization.localizedCoarseFluxResponseRHSBound Q A
      a0.matrix r j w.u.grad g
  let Z : ℝ :=
    localizedFluxDefectNegativeBesovAverageTwo Q r
      (fluxDefect A a0.matrix w.u.grad) j
  let Kscale : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)
  have hr_lt : r < 1 := by
    nlinarith
  have hg₁ : ForceBesovRegularity Q r g :=
    hg₂.of_exponent_le hr₂
  have hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R r N
            (fluxDefect A a0.matrix w.u.grad)) := by
    intro R hR
    dsimp [A]
    exact w.fluxDefect_negativeBesovPartialSeminormTwo_bddAbove_descendant hR hr
  have hZ_le_L : Z ≤ K * L := by
    dsimp [Z, L, A]
    exact
      localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_const_mul_localizedCoarseFluxResponseRHSBound_of_descendant_bounds
        Q (publicCoeffField Q a) a0.matrix w.u.grad g j hK_nonneg
        hdefect_bdd (hdescendantRHS ha0 w hr hr_lt hg₁)
  have hEll : IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (cubeSet Q) A := by
    dsimp [A]
    exact publicCoeffField_isEllipticFieldOn_cubeSet Q a
  have henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A w.u.grad)
        (cubeSet Q) MeasureTheory.volume := by
    have hgrad : MemVectorL2 (cubeSet Q) w.u.grad := by
      simpa [publicH1ToCubeSet_grad] using
        (publicH1ToCubeSet w.u).grad_memVectorL2
    exact integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hgrad
  have hr_half_pos : 0 < r / 2 := by
    nlinarith
  have hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (r / 2) 2 n *
          Real.rpow
            (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A)
            (2 / 2)) := by
    have hsum :
        Summable (fun n : ℕ =>
          geometricWeight (r / 2) 2 n *
            maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A) :=
      summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := A) (s := r / 2) hr_half_pos hEll (hData Q a)
    simpa [Real.rpow_one] using hsum
  have hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (r / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A)
            (2 / 2)) := by
    have hsum :
        Summable (fun n : ℕ =>
          geometricWeight (r / 2) 2 n *
            maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A) :=
      summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := A) (s := r / 2) hr_half_pos hEll (hData Q a)
    simpa [Real.rpow_one] using hsum
  have hL_le_B : L ≤ B := by
    dsimp [L, B]
    exact
      _root_.Homogenization.localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBoundTwoExponent_of_bddAbove_of_isEllipticFieldOn_of_summable
        Q A a0.matrix j w.u.grad g hr hr₂ hEll henergy_int
        hg₂.partialSeminorms_bddAbove
        (fun R hR => forceBesovRegularity_descendant_partialSeminorms_bddAbove hg₂ hR)
        hsumB hsumSigma
  have hZ_le_B : Z ≤ K * B :=
    hZ_le_L.trans (mul_le_mul_of_nonneg_left hL_le_B hK_nonneg)
  have hB_nonneg : 0 ≤ B := by
    have hL_nonneg : 0 ≤ L := by
      dsimp [L, _root_.Homogenization.localizedCoarseFluxResponseRHSBound]
      exact Real.sqrt_nonneg _
    exact hL_nonneg.trans hL_le_B
  have hKscale_nonneg : 0 ≤ Kscale := by
    dsimp [Kscale]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hKgeom_nonneg : 0 ≤ Kgeom := by
    dsimp [Kgeom]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hKscale_le : Kscale ≤ Kgeom := by
    dsimp [Kscale, Kgeom]
    have hpow :
        Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith)
    exact mul_le_mul_of_nonneg_left hpow (by exact_mod_cast Nat.zero_le d)
  have hCdual_nonneg : 0 ≤ Cdual := hdual.1
  have hCdual_le : Cdual ≤ Cdual + 1 := by linarith
  have hscaleCoeff_le : Kscale * Cdual * K ≤ Cbase := by
    have hstep₁ : Kscale * Cdual ≤ Kgeom * (Cdual + 1) :=
      mul_le_mul hKscale_le hCdual_le hCdual_nonneg hKgeom_nonneg
    have hstep₂ :
        (Kscale * Cdual) * K ≤ (Kgeom * (Cdual + 1)) * K :=
      mul_le_mul_of_nonneg_right hstep₁ hK_nonneg
    have hmax :
        Kgeom * (Cdual + 1) * K ≤ Cbase := by
      dsimp [Cbase]
      exact le_max_right (1 : ℝ) (Kgeom * (Cdual + 1) * K)
    exact hstep₂.trans (by simpa [mul_assoc] using hmax)
  have hCbase_nonneg : 0 ≤ Cbase := hCbase_pos.le
  have hB_to_public :
      Cbase * B ≤
        C * generalCoarseGrainingL2TwoExponentFluxDefectRHS
          1 Q a a0 r r₂ j g w.u := by
    have hBsemi_nonneg :
        0 ≤ cubeBesovPositiveVectorSeminormTwo Q r₂ g :=
      cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q r₂ g
        hg₂.partialSeminorms_bddAbove
    have herror :
        _root_.Homogenization.coarseGrainingHomogenizationErrorAtDepth
          Q A a0.matrix r j =
        coarseGrainingHomogenizationErrorAtDepth Q a a0 r j := by
      dsimp [A]
      exact coarseGrainingHomogenizationErrorAtDepth_publicCoeffField_eq_public Q a a0 r j
    have hH_nonneg :
        0 ≤ coarseGrainingHomogenizationErrorAtDepth Q a a0 r j := by
      have hOld :
          0 ≤ _root_.Homogenization.coarseGrainingHomogenizationErrorAtDepth
            Q A a0.matrix r j :=
        _root_.Homogenization.coarseGrainingHomogenizationErrorAtDepth_nonneg
          Q A a0.matrix j hr.le
      simpa [herror] using hOld
    calc
      Cbase * B =
          Cbase * _root_.Homogenization.coarseGrainingL2FluxDefectBoundTwoExponent
            Q A a0.matrix r r₂ j w.u.grad g := by
        rfl
      _ ≤ generalCoarseGrainingL2TwoExponentFluxDefectRHS C Q a a0 r r₂ j g w.u := by
        dsimp [C, A]
        exact
          coarseGrainingL2FluxDefectBoundTwoExponent_publicCoeffField_le_dim_sq_mul_public_of_homogenizationErrorAtDepth_eq
            Cbase Q a a0 j w.u hCbase_nonneg hr hBsemi_nonneg hH_nonneg herror
      _ = C * generalCoarseGrainingL2TwoExponentFluxDefectRHS 1 Q a a0 r r₂ j g w.u :=
        generalCoarseGrainingL2TwoExponentFluxDefectRHS_eq_const_mul_one
          C Q a a0 r r₂ j g w.u
  have hinner :
      Kscale * (Cdual * Z) ≤
        C * generalCoarseGrainingL2TwoExponentFluxDefectRHS
          1 Q a a0 r r₂ j g w.u := by
    have hfactor_nonneg : 0 ≤ Kscale * Cdual :=
      mul_nonneg hKscale_nonneg hCdual_nonneg
    calc
      Kscale * (Cdual * Z) = (Kscale * Cdual) * Z := by ring
      _ ≤ (Kscale * Cdual) * (K * B) :=
        mul_le_mul_of_nonneg_left hZ_le_B hfactor_nonneg
      _ = (Kscale * Cdual * K) * B := by ring
      _ ≤ Cbase * B :=
        mul_le_mul_of_nonneg_right hscaleCoeff_le hB_nonneg
      _ ≤ C * generalCoarseGrainingL2TwoExponentFluxDefectRHS
          1 Q a a0 r r₂ j g w.u :=
        hB_to_public
  have hfactor_nonneg :
      0 ≤ s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ := by
    have hr_lt_half : r < 1 / 2 := by nlinarith
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr hs.le)
        (pow_nonneg (inv_nonneg.mpr hr.le) _))
      (inv_nonneg.mpr (by linarith : 0 ≤ (1 / 2 : ℝ) - r))
  calc
    ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)) *
        (Cdual * s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
          localizedFluxDefectNegativeBesovAverageTwo Q r
            (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) j)
        =
      s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
        (Kscale * (Cdual * Z)) := by
        simp [Kscale, Z, A]
        ring
    _ ≤
      s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
        (C * generalCoarseGrainingL2TwoExponentFluxDefectRHS
          1 Q a a0 r r₂ j g w.u) :=
      mul_le_mul_of_nonneg_left hinner hfactor_nonneg
    _ = generalCoarseGrainingL2TwoExponentRHS C Q a a0 s r r₂ j g w.u := by
      unfold generalCoarseGrainingL2TwoExponentRHS
      rw [generalCoarseGrainingL2TwoExponentFluxDefectRHS_eq_const_mul_one
        C Q a a0 r r₂ j g w.u]

private theorem generalCoarseGrainingL2TwoExponentTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss_of_const_mul_descendantCoarseFluxResponseRHSBound
    {d : ℕ} [NeZero d] {Cdual K : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimateExponentLoss d Cdual)
    (hK_nonneg : 0 ≤ K)
    (hdescendantRHS :
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {a0 : ConstantCoeffMatrix d}
        {s : ℝ} {j : ℕ} {g : Vec d → Vec d}
        (_ha0 : IsPositiveScalarMatrix a0.matrix)
        (w : CoarseGrainingComparisonDatum Q a a0 g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          ∀ R ∈ descendantsAtDepth Q j,
            cubeBesovNegativeVectorSeminormTwo R s
                (fluxDefect (publicCoeffField Q a) a0.matrix w.u.grad) ≤
              K * _root_.Homogenization.coarseFluxResponseRHSBound R
                (publicCoeffField Q a) a0.matrix s w.u.grad g) :
    GeneralCoarseGrainingL2TwoExponentTheory d :=
  generalCoarseGrainingL2TwoExponentTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss_of_const_mul_descendantCoarseFluxResponseRHSBound_of_openCubeDescendantDeterministicCoarseData
    hdual hK_nonneg
    (fun Q a => publicCoeffField_openCubeDescendantDeterministicCoarseData Q a)
    hdescendantRHS

private theorem generalCoarseGrainingL2TwoExponentTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimateExponentLoss d Cdual) :
    GeneralCoarseGrainingL2TwoExponentTheory d := by
  let K : ℝ :=
    2 *
      ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
      (ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant_nonneg
        d 1)
  refine
    generalCoarseGrainingL2TwoExponentTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss_of_const_mul_descendantCoarseFluxResponseRHSBound
      (Cdual := Cdual) (K := K) hdual hK_nonneg ?_
  intro Q a a0 s j g _ha0 w hs hs_lt hg R hR
  simpa [K] using
    w.cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_const_mul_coarseFluxResponseRHSBound_descendant
      (Q := Q) (R := R) (a := a) (a0 := a0) (g := g) (j := j)
      hs hs_lt hg hR

private theorem generalCoarseGrainingL2TwoExponentTheory_of_coordinateBridge
    {d : ℕ} [NeZero d] {Cbridge : ℝ}
    (hbridge : UnitFullDualCoordinateOverlappingBridgeSharpLoss d Cbridge) :
    GeneralCoarseGrainingL2TwoExponentTheory d := by
  rcases Homogenization.exists_discreteConstantCoefficientDirichletBesovFunctionSpacesUniform d with
    ⟨Cdir, hdir⟩
  let Cpair : ℝ :=
    (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
      Real.sqrt (3 ^ d : ℝ)
  let CdualGenuine : ℝ :=
    2 * (Fintype.card (Fin d) : ℝ) *
      (Cpair * (Cdir + 1) * Cbridge)
  let Cdual : ℝ := 110 * sharpBoundaryKernelNoteConstant d * CdualGenuine
  have hdual : ScalarSolutionComparisonDualityEstimateExponentLoss d Cdual := by
    dsimp [Cdual, CdualGenuine, Cpair]
    exact
      (Homogenization.scalarSolutionComparisonGenuineDualityEstimateSharpLoss_of_dirichletBesov_of_coordinateBridgeSharpLoss_of_localizedPairing
        (d := d) (Cdir := Cdir) (Cbridge := Cbridge)
        hdir hbridge
        (localizedFluxDefectPositivePairingEstimate_standardOverlap d)).to_exponentLoss
  exact
    generalCoarseGrainingL2TwoExponentTheory_of_scalarSolutionComparisonDualityEstimateExponentLoss
      (Cdual := Cdual) hdual

/-- Public Ch3.3 scale-separated general coarse-graining package with all
currently formalized analytic inputs discharged. -/
theorem generalCoarseGrainingL2TwoExponentTheory
    (d : ℕ) [NeZero d] :
    GeneralCoarseGrainingL2TwoExponentTheory d :=
  generalCoarseGrainingL2TwoExponentTheory_of_coordinateBridge
    (unitFullDualCoordinateOverlappingBridgeSharpLoss d)

end

end Ch03
end Book
end Homogenization
