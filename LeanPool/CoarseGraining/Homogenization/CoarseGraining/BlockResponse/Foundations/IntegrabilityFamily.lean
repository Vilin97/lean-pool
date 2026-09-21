/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Foundations.BasicIdentities
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator

/-! # Integrability Family -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse Foundations -- integrability data family

BlockJIntegrabilityData and BlockResponseLowerImageMemVectorL2Data structures,
blockResponseIntegrabilityData smul / zero, the flux_memL2 / lowerImage
variants from IsEllipticFieldOn, the blockResponseIntegrand_integrableOn
theorems, and the BlockJIntegrabilityData.of_lowerImageMemVectorL2Data bridge.
-/

theorem blockEnergyDensity_smul_state {d : ℕ} (a : CoeffField d) (c : ℝ)
    (X : BlockState d) :
    blockEnergyDensity a (c • X) = fun x => c ^ 2 * blockEnergyDensity a X x := by
  funext x
  simp [blockEnergyDensity, pow_two, blockMatVecMul_smul, blockVecDot_smul_left,
    blockVecDot_smul_right]
  ring

theorem BlockResponseIntegrabilityData.smul {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    (hInt : BlockResponseIntegrabilityData U a X) (c : ℝ) :
    BlockResponseIntegrabilityData U a (c • X) := by
  refine ⟨?_, ?_⟩
  · simpa [Pi.smul_apply] using! hInt.flux_memL2.const_smul c
  · rw [blockEnergyDensity_smul_state]
    simpa [MeasureTheory.IntegrableOn, smul_eq_mul] using!
      hInt.energyIntegrable.integrable.smul (c ^ 2)

theorem blockResponseIntegrabilityData_zero {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) :
    BlockResponseIntegrabilityData U a ({ potential := 0, flux := 0 } : BlockState d) := by
  refine ⟨?_, ?_⟩
  · change MemVectorL2 U (0 : Vec d → Vec d)
    exact MeasureTheory.MemLp.zero
  · rw [show blockEnergyDensity a ({ potential := 0, flux := 0 } : BlockState d) = 0 by
        funext x
        simp [blockEnergyDensity, BlockState.eval, blockMatVecMul, blockVecDot,
          matVecMul_zero, vecDot_zero_right]]
    exact MeasureTheory.integrableOn_zero

theorem blockResponseIntegrabilityData_of_flux_memL2_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    (hFlux : MemVectorL2 U X.flux) (hEll : IsEllipticFieldOn lam Lam U a) :
    BlockResponseIntegrabilityData U a X := by
  have hBlock : MemBlockL2 U X.eval := by
    simpa [BlockState.eval, blockField] using!
      memBlockL2_blockField
        (blockResponse_potential_memL2_of_mem_responseSpace hX)
        hFlux
  refine ⟨hFlux, ?_⟩
  exact
    blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (U := U) (a := a) hBlock hEll

theorem blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    (hFlux : MemVectorL2 U X.flux) (hEll : IsEllipticFieldOn lam Lam U a) :
    MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
  have hPot : MemVectorL2 U X.potential :=
    blockResponse_potential_memL2_of_mem_responseSpace hX
  have hSkewPot :
      MemVectorL2 U (fun x => matVecMul (skewPart (a x)) (X.potential x)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hPot
  have hShift :
      MemVectorL2 U
        (fun x => X.flux x - matVecMul (skewPart (a x)) (X.potential x)) := by
    simpa [sub_eq_add_neg] using! hFlux.sub hSkewPot
  have hInv :
      MemVectorL2 U
        (fun x =>
          matVecMul ((symmPart (a x))⁻¹)
            (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hShift
  have hEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) =
        (fun x =>
          matVecMul ((symmPart (a x))⁻¹)
            (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) := by
    funext x
    simpa [BlockState.eval, blockCoeffField] using
      (blockMatVecMul_blockMatrixOfCoeff_snd (A := a x) (p := X.potential x) (q := X.flux x))
  simpa [hEq] using hInv

theorem blockResponse_flux_memL2_of_lowerImage_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    (hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    (hEll : IsEllipticFieldOn lam Lam U a) :
    MemVectorL2 U X.flux := by
  have hPot : MemVectorL2 U X.potential :=
    blockResponse_potential_memL2_of_mem_responseSpace hX
  have hSymmLower :
      MemVectorL2 U
        (fun x =>
          matVecMul (symmPart (a x))
            ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hLowerL2
  have hSkewPot :
      MemVectorL2 U (fun x => matVecMul (skewPart (a x)) (X.potential x)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hPot
  have hrepr :
      (fun x => X.flux x) =ᵐ[volumeMeasureOn U]
        (fun x =>
          matVecMul (symmPart (a x))
            ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2) +
              matVecMul (skewPart (a x)) (X.potential x)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)] with
      x hx
    simpa [BlockState.eval, blockCoeffField] using
      blockMatVecMul_blockMatrixOfCoeff_snd_recover_flux_of_isEllipticMatrix
        (A := a x) (hEll.2 x hx) (X.potential x) (X.flux x)
  have hFlux' :
      MemVectorL2 U
        (fun x =>
          matVecMul (symmPart (a x))
            ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2) +
              matVecMul (skewPart (a x)) (X.potential x)) := by
    simpa [Pi.add_apply] using! hSymmLower.add hSkewPot
  have hFluxMeas :
      MeasureTheory.AEStronglyMeasurable (fun x => X.flux x) (volumeMeasureOn U) :=
    hFlux'.1.congr hrepr.symm
  refine hFlux'.congr_norm hFluxMeas ?_
  filter_upwards [hrepr] with x hx
  simpa using congrArg norm hx.symm

theorem blockResponse_flux_memL2_of_lowerImage_ae_eq_potential_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    {f : Vec d → Vec d}
    (hLowerPot : IsPotentialOn U f)
    (hLowerEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) =ᵐ[volumeMeasureOn U] f)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    MemVectorL2 U X.flux := by
  have hLowerPotL2 : MemVectorL2 U f := by
    rcases hLowerPot with ⟨u, hu⟩
    simpa [hu] using u.grad_memVectorL2
  have hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
    have hLowerMeas :
        MeasureTheory.AEStronglyMeasurable
          (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2)
          (volumeMeasureOn U) :=
      hLowerPotL2.1.congr hLowerEq.symm
    refine hLowerPotL2.congr_norm hLowerMeas ?_
    filter_upwards [hLowerEq] with x hx
    simpa using congrArg norm hx.symm
  exact
    blockResponse_flux_memL2_of_lowerImage_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
      hX hLowerL2 hEll

theorem blockResponse_flux_memL2_of_lowerImage_isPotential_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    (hLower :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    (hEll : IsEllipticFieldOn lam Lam U a) :
    MemVectorL2 U X.flux := by
  exact
    blockResponse_flux_memL2_of_lowerImage_ae_eq_potential_of_mem_responseSpace_of_isEllipticFieldOn
      hX hLower Filter.EventuallyEq.rfl hEll

theorem blockResponseIntegrabilityData_of_lowerImage_ae_eq_potential_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    {f : Vec d → Vec d}
    (hLowerPot : IsPotentialOn U f)
    (hLowerEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) =ᵐ[volumeMeasureOn U] f)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    BlockResponseIntegrabilityData U a X := by
  exact
    blockResponseIntegrabilityData_of_flux_memL2_of_mem_responseSpace_of_isEllipticFieldOn
      hX
      (blockResponse_flux_memL2_of_lowerImage_ae_eq_potential_of_mem_responseSpace_of_isEllipticFieldOn
        hX hLowerPot hLowerEq hEll)
      hEll

theorem blockResponseIntegrabilityData_of_lowerImage_isPotential_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    (hLower :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    (hEll : IsEllipticFieldOn lam Lam U a) :
    BlockResponseIntegrabilityData U a X := by
  exact
    blockResponseIntegrabilityData_of_lowerImage_ae_eq_potential_of_mem_responseSpace_of_isEllipticFieldOn
      hX hLower Filter.EventuallyEq.rfl hEll

theorem blockResponseIntegrabilityData_of_lowerImage_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    (hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    (hEll : IsEllipticFieldOn lam Lam U a) :
    BlockResponseIntegrabilityData U a X := by
  exact
    blockResponseIntegrabilityData_of_flux_memL2_of_mem_responseSpace_of_isEllipticFieldOn
      hX
      (blockResponse_flux_memL2_of_lowerImage_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
        hX hLowerL2 hEll)
      hEll

theorem blockResponseIntegrand_integrableOn_of_mem_responseSpace_of_integrabilityData_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    (hInt : BlockResponseIntegrabilityData U a X)
    (hEll : IsEllipticFieldOn lam Lam U a) (P Q : BlockVec d) :
    MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U := by
  have hBlock : MemBlockL2 U X.eval :=
    blockResponse_memBlockL2_of_mem_responseSpace_of_integrabilityData hX hInt
  let YP : BlockState d := { potential := fun _ => P.1, flux := fun _ => P.2 }
  have hYPL2 : MemBlockL2 U YP.eval := by
    simpa [YP, BlockState.eval, blockField] using!
      memBlockL2_blockField
        (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := P.1))
        (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := P.2))
  have hPInt :
      MeasureTheory.IntegrableOn
        (fun x => blockVecDot P (blockMatVecMul (blockCoeffField a x) (X.eval x))) U := by
    simpa [YP, blockPairingIntegrand, BlockState.eval] using!
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (U := U) (a := a) (X := YP) (Y := X) hYPL2 hBlock hEll
  have hQPotInt :
      MeasureTheory.IntegrableOn (fun x => vecDot Q.1 (X.potential x)) U :=
    CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2
      (U := U) Q.1 (blockResponse_potential_memL2_of_mem_responseSpace hX)
  have hQFluxInt :
      MeasureTheory.IntegrableOn (fun x => vecDot Q.2 (X.flux x)) U :=
    CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2
      (U := U) Q.2 hInt.flux_memL2
  have hQInt :
      MeasureTheory.IntegrableOn (fun x => blockVecDot Q (X.eval x)) U := by
    simpa [MeasureTheory.IntegrableOn, BlockState.eval, blockVecDot] using!
      hQPotInt.integrable.add hQFluxInt.integrable
  have hsum12 :
      MeasureTheory.IntegrableOn
        (fun x =>
          -blockEnergyDensity a X x -
            blockVecDot P (blockMatVecMul (blockCoeffField a x) (X.eval x))) U := by
    simpa [sub_eq_add_neg, MeasureTheory.IntegrableOn] using!
      hInt.energyIntegrable.integrable.neg.add hPInt.integrable.neg
  have hsum123 :
      MeasureTheory.IntegrableOn
        (fun x =>
          (-blockEnergyDensity a X x -
            blockVecDot P (blockMatVecMul (blockCoeffField a x) (X.eval x))) +
              blockVecDot Q (X.eval x)) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum12.integrable.add hQInt.integrable
  have hrewrite :
      (fun x =>
        (-blockEnergyDensity a X x -
          blockVecDot P (blockMatVecMul (blockCoeffField a x) (X.eval x))) +
            blockVecDot Q (X.eval x)) =
        blockResponseIntegrand a P Q X := by
    funext x
    simp [blockResponseIntegrand]
  rw [hrewrite] at hsum123
  exact hsum123

theorem blockResponseIntegrand_integrableOn_of_lowerImage_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hX : BlockResponseSpace a U X)
    (hLowerL2 :
      MemVectorL2 U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2))
    (hEll : IsEllipticFieldOn lam Lam U a) (P Q : BlockVec d) :
    MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U := by
  exact
    blockResponseIntegrand_integrableOn_of_mem_responseSpace_of_integrabilityData_of_isEllipticFieldOn
      hX
      (blockResponseIntegrabilityData_of_lowerImage_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
        hX hLowerL2 hEll)
      hEll P Q

theorem BlockJIntegrabilityData.of_lowerImageMemVectorL2Data_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hLower : BlockResponseLowerImageMemVectorL2Data U a)
    (hEll : IsEllipticFieldOn lam Lam U a) (P Q : BlockVec d) :
    BlockJIntegrabilityData U a P Q := by
  refine ⟨?_⟩
  intro X hX
  exact
    blockResponseIntegrand_integrableOn_of_lowerImage_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
      hX (hLower.lowerImage_memVectorL2 X hX) hEll P Q

end

end Homogenization
