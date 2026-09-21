/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.SymmetricDirichletNeumann.Common

/-! # Neumann -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Neumann Side

This file is split mechanically out of `Internal.Ch02.SymmetricDirichletNeumann`.
-/

/-- Construct the old constant-flux Neumann solution predicate from the
mean-zero Neumann RHS solver on a bounded open convex domain. -/
theorem exists_isConstantFluxNeumannSolution_of_isEllipticFieldOn
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (q : Vec d) :
    ∃ u : H1MeanZeroFunction (U : Set (Vec d)),
      IsConstantFluxNeumannSolution a.toCoeffField (U : Set (Vec d)) q u := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let g : Vec d → Vec d := fun _ => q
  have hg : MemVectorL2 Uset g := by
    simpa [Uset, g] using memVectorL2_const_vec (U := Uset) q
  let hC : H1CoerciveEstimate Uset :=
    h1CoerciveEstimate_of_isOpenBoundedConvexDomain (U := Uset) U.isDomain
  let u : H1MeanZeroFunction Uset :=
    H1MeanZeroFunction.coeffGradientProblemSolution
      (U := Uset) (a := a.toCoeffField) (lam := a.lam) (Lam := a.Lam)
      hg hC (by simpa [Uset] using U.nonempty) hEll
  have huWeak : IsMeanZeroNeumannRhsWeakSolution a.toCoeffField Uset u g :=
    isMeanZeroNeumannRhsWeakSolution_coeffGradientProblemSolution_of_h1CoerciveEstimate
      (U := Uset) (a := a.toCoeffField) (lam := a.lam) (Lam := a.Lam)
      hg hC (by simpa [Uset] using U.nonempty) hEll
  refine ⟨u, ?_⟩
  constructor
  · constructor
    · exact u.toH1Function.isPotentialOn
    · intro φ
      have hweak :
          ∫ x in Uset,
              vecDot
                (matVecMul (a.toCoeffField x) (u.toH1Function.grad x))
                (φ.toH1Function.grad x) ∂MeasureTheory.volume =
            ∫ x in Uset, vecDot (g x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume :=
        H1Function.coeffGradientProblemSolution_firstVariation_eq_integral
          (U := Uset) (a := a.toCoeffField) (lam := a.lam) (Lam := a.Lam)
          hg hC (by simpa [Uset] using U.nonempty) hEll φ.toH1Function
      rw [hweak]
      simpa [g] using integral_vecDot_const_zeroTraceGrad_eq_zero φ q
  · simpa [g] using
      huWeak.residual_zeroNormalTrace (hEll := hEll) (hg := hg)

theorem symmetricNeumannEnergyValue_eq_of_isConstantFluxNeumannSolution
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {q : Vec d}
    {u : H1MeanZeroFunction (U : Set (Vec d))}
    (hu : IsConstantFluxNeumannSolution a.toCoeffField (U : Set (Vec d)) q u)
    (ha : IsSymmetricCoeffField a.toCoeffField)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (w : H1Function (U : Set (Vec d))) :
    symmetricNeumannEnergyValue U a q w =
      symmetricNeumannEnergyValue U a q u.toH1Function -
        (1 / 2 : ℝ) *
          volumeAverage (U : Set (Vec d))
            (fun x =>
              vecDot ((w - u.toH1Function).grad x)
                (matVecMul (a.toCoeffField x) ((w - u.toH1Function).grad x))) := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let z : H1Function Uset := w - u.toH1Function
  let fU : Vec d → ℝ :=
    fun x =>
      vecDot q (u.toH1Function.grad x) -
        (1 / 2 : ℝ) *
          vecDot (u.toH1Function.grad x)
            (matVecMul (a.toCoeffField x) (u.toH1Function.grad x))
  let fW : Vec d → ℝ :=
    fun x =>
      vecDot q (w.grad x) -
        (1 / 2 : ℝ) *
          vecDot (w.grad x) (matVecMul (a.toCoeffField x) (w.grad x))
  let fRes : Vec d → ℝ :=
    fun x =>
      vecDot
        (matVecMul (a.toCoeffField x) (u.toH1Function.grad x) - q)
        (z.grad x)
  let fZ : Vec d → ℝ :=
    fun x =>
      vecDot (z.grad x) (matVecMul (a.toCoeffField x) (z.grad x))
  have hfU : MeasureTheory.IntegrableOn fU Uset := by
    simpa [fU, Uset] using
      integrableOn_symmetricNeumannIntegrand_of_isEllipticFieldOn
        (U := Uset) hEll q u.toH1Function
  have hfW : MeasureTheory.IntegrableOn fW Uset := by
    simpa [fW, Uset] using
      integrableOn_symmetricNeumannIntegrand_of_isEllipticFieldOn
        (U := Uset) hEll q w
  have hfluxMem :
      MemVectorL2 Uset
        (fun x => matVecMul (a.toCoeffField x) (u.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      u.toH1Function.grad_memVectorL2
  have hresMem :
      MemVectorL2 Uset
        (fun x => matVecMul (a.toCoeffField x) (u.toH1Function.grad x) - q) :=
    hfluxMem.sub (memVectorL2_const_vec (U := Uset) q)
  have hfRes : MeasureTheory.IntegrableOn fRes Uset := by
    simpa [fRes, Uset] using
      integrableOn_vecDot_of_memVectorL2 hresMem z.grad_memVectorL2
  have hfZ : MeasureTheory.IntegrableOn fZ Uset := by
    simpa [fZ, Uset] using
      integrableOn_h1_coefficientEnergyDensity hEll z
  have hresZero :
      volumeAverage Uset fRes = 0 := by
    apply volumeAverage_eq_zero_of_integral_eq_zero
    simpa [fRes, z, Uset] using
      hu.isSolenoidalZeroNormalTraceOn_flux_sub_const z
  have hpoint :
      fW =
        fun x => fU x - fRes x - (1 / 2 : ℝ) * fZ x := by
    funext x
    have hgradW : w.grad x = u.toH1Function.grad x + z.grad x := by
      have hz :
          z.grad x = w.grad x - u.toH1Function.grad x := by
        simp [z]
      rw [hz]
      simp [sub_eq_add_neg]
    have hsymm :
        vecDot (u.toH1Function.grad x)
            (matVecMul (a.toCoeffField x) (z.grad x)) =
          vecDot (matVecMul (a.toCoeffField x) (u.toH1Function.grad x))
            (z.grad x) := by
      calc
        vecDot (u.toH1Function.grad x)
            (matVecMul (a.toCoeffField x) (z.grad x))
            =
          vecDot (z.grad x)
            (matVecMul (a.toCoeffField x) (u.toH1Function.grad x)) :=
              vecDot_matVecMul_comm_of_isSymm (ha x)
                (u.toH1Function.grad x) (z.grad x)
        _ =
          vecDot (matVecMul (a.toCoeffField x) (u.toH1Function.grad x))
            (z.grad x) := by
              rw [vecDot_comm]
    have hcommZu :
        vecDot (z.grad x)
            (matVecMul (a.toCoeffField x) (u.toH1Function.grad x)) =
          vecDot (matVecMul (a.toCoeffField x) (u.toH1Function.grad x))
            (z.grad x) := by
      rw [vecDot_comm]
    simp [fU, fW, fRes, fZ, hgradW, matVecMul_add, vecDot_add_left,
      vecDot_add_right, hsymm, hcommZu, sub_eq_add_neg, vecDot_neg_left]
    ring_nf
  have hvalue :
      symmetricNeumannEnergyValue U a q w =
        symmetricNeumannEnergyValue U a q u.toH1Function -
          (1 / 2 : ℝ) * volumeAverage Uset fZ := by
    calc
      symmetricNeumannEnergyValue U a q w =
          volumeAverage Uset fW := rfl
      _ =
          volumeAverage Uset
            (fun x => fU x - fRes x - (1 / 2 : ℝ) * fZ x) := by
            rw [hpoint]
      _ =
          volumeAverage Uset fU -
            volumeAverage Uset fRes -
              volumeAverage Uset ((1 / 2 : ℝ) • fZ) := by
            have hfU_sub_res : MeasureTheory.IntegrableOn (fU - fRes) Uset :=
              hfU.sub hfRes
            have hfZ_smul :
                MeasureTheory.IntegrableOn ((1 / 2 : ℝ) • fZ) Uset := by
              simpa [Pi.smul_apply, smul_eq_mul] using!
                (hfZ.const_mul (1 / 2 : ℝ))
            change
              volumeAverage Uset ((fU - fRes) - ((1 / 2 : ℝ) • fZ)) =
                volumeAverage Uset fU -
                  volumeAverage Uset fRes -
                    volumeAverage Uset ((1 / 2 : ℝ) • fZ)
            rw [volumeAverage_sub hfU_sub_res hfZ_smul]
            rw [volumeAverage_sub hfU hfRes]
      _ =
          symmetricNeumannEnergyValue U a q u.toH1Function -
            (1 / 2 : ℝ) * volumeAverage Uset fZ := by
            rw [hresZero, volumeAverage_smul]
            change
              volumeAverage Uset fU - 0 - (1 / 2 : ℝ) * volumeAverage Uset fZ =
                volumeAverage Uset fU - (1 / 2 : ℝ) * volumeAverage Uset fZ
            ring
  simpa [fZ, z, Uset] using hvalue

theorem symmetricNeumannEnergyValue_eq_half_variationEnergy_of_isConstantFluxNeumannSolution
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {q : Vec d}
    {u : H1MeanZeroFunction (U : Set (Vec d))}
    (hu : IsConstantFluxNeumannSolution a.toCoeffField (U : Set (Vec d)) q u)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    symmetricNeumannEnergyValue U a q u.toH1Function =
      (1 / 2 : ℝ) *
        volumeAverage (U : Set (Vec d))
          (scalarVariationEnergyIntegrand a.toCoeffField hu.toAHarmonicFunction) := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let fQ : Vec d → ℝ := fun x => vecDot q (u.toH1Function.grad x)
  let fE : Vec d → ℝ :=
    fun x =>
      vecDot (u.toH1Function.grad x)
        (matVecMul (a.toCoeffField x) (u.toH1Function.grad x))
  let fRes : Vec d → ℝ :=
    fun x =>
      vecDot
        (matVecMul (a.toCoeffField x) (u.toH1Function.grad x) - q)
        (u.toH1Function.grad x)
  have hfQ : MeasureTheory.IntegrableOn fQ Uset := by
    simpa [fQ, Uset] using
      integrableOn_vecDot_const_h1Grad (U := Uset) q u.toH1Function
  have hfE : MeasureTheory.IntegrableOn fE Uset := by
    simpa [fE, Uset] using
      integrableOn_h1_coefficientEnergyDensity hEll u.toH1Function
  have hresZero : volumeAverage Uset fRes = 0 := by
    apply volumeAverage_eq_zero_of_integral_eq_zero
    simpa [fRes, Uset] using
      hu.isSolenoidalZeroNormalTraceOn_flux_sub_const u.toH1Function
  have hresFun : fRes = fE - fQ := by
    funext x
    simp [fRes, fE, fQ, sub_eq_add_neg, vecDot_add_right, vecDot_neg_right,
      vecDot_comm]
  have hQE : volumeAverage Uset fQ = volumeAverage Uset fE := by
    have hsub :
        volumeAverage Uset (fE - fQ) =
          volumeAverage Uset fE - volumeAverage Uset fQ :=
      volumeAverage_sub hfE hfQ
    rw [← hresFun, hresZero] at hsub
    linarith
  have hscalar :
      volumeAverage Uset
          (scalarVariationEnergyIntegrand a.toCoeffField hu.toAHarmonicFunction) =
        volumeAverage Uset fE := by
    congr 1
    funext x
    simp [fE, scalarVariationEnergyIntegrand, vecDot_matVecMul_symmPart]
  calc
    symmetricNeumannEnergyValue U a q u.toH1Function =
        volumeAverage Uset (fun x => fQ x - (1 / 2 : ℝ) * fE x) := rfl
    _ =
        volumeAverage Uset fQ - volumeAverage Uset ((1 / 2 : ℝ) • fE) := by
          have hfE_smul :
              MeasureTheory.IntegrableOn ((1 / 2 : ℝ) • fE) Uset := by
            simpa [Pi.smul_apply, smul_eq_mul] using!
              (hfE.const_mul (1 / 2 : ℝ))
          change
            volumeAverage Uset (fQ - ((1 / 2 : ℝ) • fE)) =
              volumeAverage Uset fQ - volumeAverage Uset ((1 / 2 : ℝ) • fE)
          rw [volumeAverage_sub hfQ hfE_smul]
    _ =
        (1 / 2 : ℝ) * volumeAverage Uset fE := by
          rw [volumeAverage_smul, hQE]
          ring
    _ =
        (1 / 2 : ℝ) *
          volumeAverage Uset
            (scalarVariationEnergyIntegrand a.toCoeffField hu.toAHarmonicFunction) := by
          rw [hscalar]

theorem isSymmetricNeumannMaximizer_of_isConstantFluxNeumannSolution
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {q : Vec d}
    {u : H1MeanZeroFunction (U : Set (Vec d))}
    (hu : IsConstantFluxNeumannSolution a.toCoeffField (U : Set (Vec d)) q u)
    (ha : IsSymmetricCoeffField a.toCoeffField)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    IsSymmetricNeumannMaximizer U a q u.toH1Function := by
  intro w
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let z : H1Function Uset := w - u.toH1Function
  let fZ : Vec d → ℝ :=
    fun x =>
      vecDot (z.grad x) (matVecMul (a.toCoeffField x) (z.grad x))
  have hvalue :=
    symmetricNeumannEnergyValue_eq_of_isConstantFluxNeumannSolution
      U a hu ha hEll w
  have hvalue' :
      symmetricNeumannEnergyValue U a q w =
        symmetricNeumannEnergyValue U a q u.toH1Function -
          (1 / 2 : ℝ) * volumeAverage Uset fZ := by
    simpa [fZ, z, Uset] using hvalue
  have hZNonneg : 0 ≤ volumeAverage Uset fZ := by
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    have hnonneg :=
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll z.grad x hx
    simpa [fZ, coefficientEnergyDensity_eq_unsymmetrized] using hnonneg
  nlinarith [hvalue', hZNonneg]

theorem sameGradientAE_of_isSymmetricNeumannMaximizer_of_isConstantFluxNeumannSolution
    {d : ℕ} (U : Domain d) (a : CoeffOn U) {q : Vec d}
    {u : H1MeanZeroFunction (U : Set (Vec d))}
    (hu : IsConstantFluxNeumannSolution a.toCoeffField (U : Set (Vec d)) q u)
    (ha : IsSymmetricCoeffField a.toCoeffField)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    {w : H1Function (U : Set (Vec d))}
    (hw : IsSymmetricNeumannMaximizer U a q w) :
    w.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] u.toH1Function.grad := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let z : H1Function Uset := w - u.toH1Function
  let fZ : Vec d → ℝ :=
    fun x =>
      vecDot (z.grad x) (matVecMul (a.toCoeffField x) (z.grad x))
  have hvalue :=
    symmetricNeumannEnergyValue_eq_of_isConstantFluxNeumannSolution
      U a hu ha hEll w
  have hvalue' :
      symmetricNeumannEnergyValue U a q w =
        symmetricNeumannEnergyValue U a q u.toH1Function -
          (1 / 2 : ℝ) * volumeAverage Uset fZ := by
    simpa [fZ, z, Uset] using hvalue
  have hZNonneg : 0 ≤ volumeAverage Uset fZ := by
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    have hnonneg :=
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll z.grad x hx
    simpa [fZ, coefficientEnergyDensity_eq_unsymmetrized] using hnonneg
  have hZLeZero : volumeAverage Uset fZ ≤ 0 := by
    have hmax := hw u.toH1Function
    nlinarith [hvalue']
  have hZZero : volumeAverage Uset fZ = 0 :=
    le_antisymm hZLeZero hZNonneg
  have hfZ : MeasureTheory.IntegrableOn fZ Uset := by
    simpa [fZ, z, Uset] using
      integrableOn_h1_coefficientEnergyDensity hEll z
  have hzZero : z.grad =ᵐ[volumeMeasureOn Uset] 0 := by
    simpa [fZ, Uset] using
      h1_grad_eq_zero_ae_of_volumeAverage_energy_eq_zero U a hEll z hfZ hZZero
  filter_upwards [hzZero] with x hx
  have hz :
      z.grad x = w.grad x - u.toH1Function.grad x := by
    simp [z]
  rw [hz] at hx
  exact sub_eq_zero.mp hx

end BookCh02

end

end Ch02
end Internal
end Homogenization
