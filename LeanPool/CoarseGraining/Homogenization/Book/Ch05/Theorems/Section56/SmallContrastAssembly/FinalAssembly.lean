/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.WeightedGeometricSummation
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.TraceAverageEstimate
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.FluctuationSumEstimate
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastJBound

/-! # Final Assembly -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAssembly

open Section53.JUpperBoundCoarseFluctuations
open Section54.VarianceBoundGoodScale

/-!
# Final constant selection for Lemma `l.small.contrast.assembly`

This file owns the final real-algebra assembly of the Section 5.6
small-contrast iteration.  The analytic fluctuation-sum estimate is kept as a
separate input to the pure algebra lemma so the final theorem can quantify the
constant before the law.
-/

/-- The right side in Lemma `l.small.contrast.assembly`. -/
noncomputable def smallContrastAssemblyRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C : ℝ) (ell k m : ℕ) (e : Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  C * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e +
    C * Real.rpow (3 : ℝ) (-β * (m : ℝ)) +
      C * Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) +
        C * (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ)

/-- Pure real algebra for the last assembly step. -/
theorem smallContrastAssembly_real_bound
    {J F tau tail geom thetaM thetaEll CJ C Ktau Kgeom Ktheta : ℝ}
    (hJ :
      J ≤ CJ * F + CJ * tau + CJ * tail + CJ * thetaM)
    (hF :
      F ≤ Ktau * tau + Kgeom * geom + Ktheta * thetaEll)
    (hCJ_nonneg : 0 ≤ CJ)
    (htau_nonneg : 0 ≤ tau) (htail_nonneg : 0 ≤ tail)
    (hgeom_nonneg : 0 ≤ geom) (hthetaEll_nonneg : 0 ≤ thetaEll)
    (hthetaM_le : thetaM ≤ thetaEll)
    (hC_tau : CJ * Ktau + CJ ≤ C)
    (hC_tail : CJ ≤ C)
    (hC_geom : CJ * Kgeom ≤ C)
    (hC_theta : CJ * Ktheta + CJ ≤ C) :
    J ≤ C * tau + C * tail + C * geom + C * thetaEll := by
  have hF_term :
      CJ * F ≤ CJ * (Ktau * tau + Kgeom * geom + Ktheta * thetaEll) :=
    mul_le_mul_of_nonneg_left hF hCJ_nonneg
  have htau_term : (CJ * Ktau + CJ) * tau ≤ C * tau :=
    mul_le_mul_of_nonneg_right hC_tau htau_nonneg
  have htail_term : CJ * tail ≤ C * tail :=
    mul_le_mul_of_nonneg_right hC_tail htail_nonneg
  have hgeom_term : (CJ * Kgeom) * geom ≤ C * geom :=
    mul_le_mul_of_nonneg_right hC_geom hgeom_nonneg
  have htheta_term : (CJ * Ktheta + CJ) * thetaEll ≤ C * thetaEll :=
    mul_le_mul_of_nonneg_right hC_theta hthetaEll_nonneg
  nlinarith

theorem thetaAtScale_sub_one_sq_mono_of_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {ell m : ℕ} (hellm : ell ≤ m) :
    (thetaAtScale hP hStruct (m : ℤ) - 1) ^ (2 : ℕ) ≤
      (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
  have hmono :
      thetaAtScale hP hStruct (m : ℤ) ≤
        thetaAtScale hP hStruct (ell : ℤ) := by
    simpa using
      Section54.GoodScale.thetaAtScale_mono_of_P4
        hP hStruct hP4 (n := ell) (m := m) hellm
  have hm_one :
      1 ≤ thetaAtScale hP hStruct (m : ℤ) :=
    one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hell_one :
      1 ≤ thetaAtScale hP hStruct (ell : ℤ) :=
    one_le_thetaAtScale_of_P4 hP hStruct hP4 ell
  have hsub_nonneg : 0 ≤ thetaAtScale hP hStruct (m : ℤ) - 1 := by linarith
  have hsub_le :
      thetaAtScale hP hStruct (m : ℤ) - 1 ≤
        thetaAtScale hP hStruct (ell : ℤ) - 1 := by
    linarith
  exact pow_le_pow_left₀ hsub_nonneg hsub_le 2

/-- Nonnegativity of the special-direction additivity defect. -/
theorem tauAtScale_special_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Vec d) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    0 ≤ tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := by
  dsimp only
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
  have hBlockM :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hBlockK :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (k : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 k
  have hDescBlock :
      ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) (k : ℤ) →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hk_nonneg hkm_int hR hBlockK
  simpa [p_e, q_e] using
    Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
      hP hstat hk_nonneg hkm_int p_e q_e hBlockM hDescBlock

/-- Final constant selection, assuming a parameter-uniform estimate on the
coarse fluctuation sum.  The produced constant is chosen before the law. -/
theorem smallContrastAssembly_homogenizationScale_of_fluctuation_bound
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (Ktau Kgeom Ktheta : ℝ)
    (hFluct :
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ell k m : ℕ}, ell < k → k < m →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
          Ktau * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e +
            Kgeom *
              Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) +
              Ktheta * (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ell k m : ℕ}, ell < k → k < m → C ≤ ((m - k : ℕ) : ℝ) →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
          smallContrastAssemblyRHSAtScale hP hStruct hP4 C ell k m e := by
  rcases smallContrastJBound_homogenizationScale params with
    ⟨CJ, hCJ_pos, hJbound⟩
  let C : ℝ :=
    max 1
      (max CJ
        (max (CJ * Ktau + CJ)
          (max (CJ * Kgeom) (CJ * Ktheta + CJ))))
  have hC_ge_one : 1 ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge_one
  have hCJ_nonneg : 0 ≤ CJ := hCJ_pos.le
  have hC_ge_CJ : CJ ≤ C := by
    dsimp [C]
    exact
      (le_max_left CJ
        (max (CJ * Ktau + CJ)
          (max (CJ * Kgeom) (CJ * Ktheta + CJ)))).trans
        (le_max_right 1
          (max CJ
            (max (CJ * Ktau + CJ)
              (max (CJ * Kgeom) (CJ * Ktheta + CJ)))))
  have hC_tau : CJ * Ktau + CJ ≤ C := by
    dsimp [C]
    exact
      (le_max_left (CJ * Ktau + CJ)
        (max (CJ * Kgeom) (CJ * Ktheta + CJ))).trans
        ((le_max_right CJ
          (max (CJ * Ktau + CJ)
            (max (CJ * Kgeom) (CJ * Ktheta + CJ)))).trans
          (le_max_right 1
            (max CJ
              (max (CJ * Ktau + CJ)
                (max (CJ * Kgeom) (CJ * Ktheta + CJ))))))
  have hC_geom : CJ * Kgeom ≤ C := by
    dsimp [C]
    exact
      (le_max_left (CJ * Kgeom) (CJ * Ktheta + CJ)).trans
        ((le_max_right (CJ * Ktau + CJ)
          (max (CJ * Kgeom) (CJ * Ktheta + CJ))).trans
          ((le_max_right CJ
            (max (CJ * Ktau + CJ)
              (max (CJ * Kgeom) (CJ * Ktheta + CJ)))).trans
            (le_max_right 1
              (max CJ
                (max (CJ * Ktau + CJ)
                  (max (CJ * Kgeom) (CJ * Ktheta + CJ)))))))
  have hC_theta : CJ * Ktheta + CJ ≤ C := by
    dsimp [C]
    exact
      (le_max_right (CJ * Kgeom) (CJ * Ktheta + CJ)).trans
        ((le_max_right (CJ * Ktau + CJ)
          (max (CJ * Kgeom) (CJ * Ktheta + CJ))).trans
          ((le_max_right CJ
            (max (CJ * Ktau + CJ)
              (max (CJ * Kgeom) (CJ * Ktheta + CJ)))).trans
            (le_max_right 1
              (max CJ
                (max (CJ * Ktau + CJ)
                  (max (CJ * Kgeom) (CJ * Ktheta + CJ)))))))
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hstat hStruct hP4 hparams hsmall e he ell k m hellk hkm hgap
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let J := Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e
  let F := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let tau := tauAtScale P (m : ℤ) (k : ℤ) p_e q_e
  let tail := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let geom := Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ))
  let thetaM := (thetaAtScale hP hStruct (m : ℤ) - 1) ^ (2 : ℕ)
  let thetaEll := (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ)
  have hCJ_gap : CJ ≤ ((m - k : ℕ) : ℝ) := hC_ge_CJ.trans hgap
  have hJraw :
      J ≤ CJ * F + CJ * tau + CJ * tail + CJ * thetaM := by
    have h := hJbound hP hstat hStruct hP4 hparams hsmall e he
      (k := k) (m := m) hCJ_gap
    simpa [J, F, tau, tail, thetaM, p_e, q_e, β,
      smallContrastFinalRHSAtScale] using h
  have hFraw :
      F ≤ Ktau * tau + Kgeom * geom + Ktheta * thetaEll := by
    have h := hFluct hP hstat hStruct hP4 hparams hsmall e he hellk hkm
    simpa [F, tau, geom, thetaEll, p_e, q_e] using h
  have hkm_le : k ≤ m := hkm.le
  have hellm : ell ≤ m := by omega
  have htau_nonneg : 0 ≤ tau := by
    simpa [tau, p_e, q_e] using
      tauAtScale_special_nonneg hP hstat hStruct hP4 hkm_le e
  have htail_nonneg : 0 ≤ tail := by
    dsimp [tail]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hgeom_nonneg : 0 ≤ geom := by
    dsimp [geom]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hthetaEll_nonneg : 0 ≤ thetaEll := by
    dsimp [thetaEll]
    exact sq_nonneg _
  have hthetaM_le : thetaM ≤ thetaEll := by
    simpa [thetaM, thetaEll] using
      thetaAtScale_sub_one_sq_mono_of_le hP hStruct hP4 hellm
  have hreal :=
    smallContrastAssembly_real_bound hJraw hFraw hCJ_nonneg
      htau_nonneg htail_nonneg hgeom_nonneg hthetaEll_nonneg
      hthetaM_le hC_tau hC_ge_CJ hC_geom hC_theta
  simpa [smallContrastAssemblyRHSAtScale, J, tau, tail, geom, thetaEll, p_e, q_e, β]
    using hreal

/-- Lemma `l.small.contrast.assembly`, with the constant chosen before the
law. -/
theorem smallContrastAssembly_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ell k m : ℕ}, ell < k → k < m → C ≤ ((m - k : ℕ) : ℝ) →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
          smallContrastAssemblyRHSAtScale hP hStruct hP4 C ell k m e := by
  rcases coarseFluctuationFullBlockSumAtScale_le_assembly_fluctuation_bound
      params with
    ⟨Ktau, Kgeom, Ktheta, hFluct⟩
  rcases smallContrastAssembly_homogenizationScale_of_fluctuation_bound
      params Ktau Kgeom Ktheta hFluct with
    ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams hsmall e he ell k m hellk hkm hgap
  exact
    hC hP hStruct.stationary hStruct hP4 hparams hsmall e he hellk hkm hgap

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
