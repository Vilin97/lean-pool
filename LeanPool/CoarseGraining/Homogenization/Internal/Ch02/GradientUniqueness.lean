/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.GradientUniquenessDefinitions
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Foundations.Ellipticity
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Existence
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Gradient Uniqueness -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem grad_eq_zero_ae_of_volumeAverage_energy_eq_zero {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a)
    (hEnergyInt :
      MeasureTheory.IntegrableOn
        (scalarVariationEnergyIntegrand a.toCoeffField u) (U : Set (Vec d)))
    (hEnergyAvg :
      volumeAverage (U : Set (Vec d))
        (scalarVariationEnergyIntegrand a.toCoeffField u) = 0) :
    u.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] 0 := by
  have hvolPos : 0 < MeasureTheory.volume (U : Set (Vec d)) :=
    U.isOpen.measure_pos MeasureTheory.volume U.nonempty
  have hvolNeZero : MeasureTheory.volume (U : Set (Vec d)) ≠ 0 :=
    ne_of_gt hvolPos
  have hvolNeTop : MeasureTheory.volume (U : Set (Vec d)) ≠ ⊤ := by
    have htop :
        volumeMeasureOn (U : Set (Vec d)) Set.univ ≠ ⊤ :=
      MeasureTheory.measure_ne_top (μ := volumeMeasureOn (U : Set (Vec d))) Set.univ
    simpa [volumeMeasureOn] using htop
  have hvolRealPos : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    ENNReal.toReal_pos hvolNeZero hvolNeTop
  have hvolRealNe : (MeasureTheory.volume (U : Set (Vec d))).toReal ≠ 0 :=
    ne_of_gt hvolRealPos
  have hIntegral :
      ∫ x in (U : Set (Vec d)),
          scalarVariationEnergyIntegrand a.toCoeffField u x ∂MeasureTheory.volume = 0 := by
    unfold volumeAverage at hEnergyAvg
    exact (mul_eq_zero.mp hEnergyAvg).resolve_left (inv_ne_zero hvolRealNe)
  have hNonnegAE :
      ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
        0 ≤ scalarVariationEnergyIntegrand a.toCoeffField u x := by
    filter_upwards
        [MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)] with x hxU
    exact
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (U : Set (Vec d)) a.toCoeffField hEll u x hxU
  have hEnergyAE :
      scalarVariationEnergyIntegrand a.toCoeffField u
        =ᵐ[volumeMeasureOn (U : Set (Vec d))] 0 := by
    exact
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        hNonnegAE hEnergyInt.integrable).1 (by
          simpa [volumeMeasureOn] using hIntegral)
  filter_upwards
      [hEnergyAE,
        MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)] with
    x hEnergyZero hxU
  have hA := hEll.2 x hxU
  have hlower :=
    lowerBound_symmPart_of_isEllipticMatrix hA (u.toH1.grad x)
  have hEnergyPoint :
      vecDot (u.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (u.toH1.grad x)) = 0 := by
    simpa [scalarVariationEnergyIntegrand] using hEnergyZero
  have hnormNonneg : 0 ≤ vecNormSq (u.toH1.grad x) :=
    vecNormSq_nonneg (u.toH1.grad x)
  have hnormZero : vecNormSq (u.toH1.grad x) = 0 := by
    nlinarith [hA.1, hlower, hEnergyPoint, hnormNonneg]
  exact vecNormSq_eq_zero hnormZero

private theorem volumeAverage_energy_eq_zero_of_sub_maximizer_zero {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a)
    (hu : Homogenization.IsResponseMaximizer
      (U : Set (Vec d)) 0 0 a.toCoeffField u) :
    volumeAverage (U : Set (Vec d))
      (scalarVariationEnergyIntegrand a.toCoeffField u) = 0 := by
  have hrespNonneg :
      0 ≤ volumeAverage (U : Set (Vec d))
        (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField 0 0 u) := by
    simpa using hu (0 : AHarmonicFunction a.toCoeffField (U : Set (Vec d)))
  have hrespEq :
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField 0 0 u) =
        (-(1 / 2 : ℝ)) *
          volumeAverage (U : Set (Vec d))
            (scalarVariationEnergyIntegrand a.toCoeffField u) := by
    have hfun :
        scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField 0 0 u =
          (-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a.toCoeffField u := by
      funext x
      simp [scalarResponseIntegrand, scalarVariationEnergyIntegrand, smul_eq_mul,
        vecDot_zero_left]
    calc
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField 0 0 u)
          = volumeAverage (U : Set (Vec d))
              ((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a.toCoeffField u) := by
              rw [hfun]
      _ = (-(1 / 2 : ℝ)) *
            volumeAverage (U : Set (Vec d))
              (scalarVariationEnergyIntegrand a.toCoeffField u) := by
              exact volumeAverage_smul (U : Set (Vec d)) (-(1 / 2 : ℝ))
                (scalarVariationEnergyIntegrand a.toCoeffField u)
  have hEnergyNonneg :
      0 ≤ volumeAverage (U : Set (Vec d))
        (scalarVariationEnergyIntegrand a.toCoeffField u) :=
    volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      (U : Set (Vec d)) a.toCoeffField hEll u
  have hEnergyLeZero :
      volumeAverage (U : Set (Vec d))
        (scalarVariationEnergyIntegrand a.toCoeffField u) ≤ 0 := by
    nlinarith [hrespNonneg, hrespEq]
  exact le_antisymm hEnergyLeZero hEnergyNonneg

/-- Internal pointwise-coefficient gradient uniqueness theorem. -/
theorem responseGradientUniquenessTheory_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseGradientUniquenessTheory U a where
  unique_gradient := by
    intro p q v w hv hw
    let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    let diff : Solution U a :=
      AHarmonicFunction.subOfIntegrable v w (hInt.weakFlux v) (hInt.weakFlux w)
    have hdiffMax :
        Homogenization.IsResponseMaximizer
          (U : Set (Vec d)) (p - p) (q - q) a.toCoeffField diff :=
      basic_cg_identities_sub_isResponseMaximizer_of_isResponseMaximizer
        (U : Set (Vec d)) a.toCoeffField p q p q hInt v w hv hw
    have hdiffMaxZero :
        Homogenization.IsResponseMaximizer
          (U : Set (Vec d)) 0 0 a.toCoeffField diff := by
      simpa using hdiffMax
    have hEnergyAvg :
        volumeAverage (U : Set (Vec d))
          (scalarVariationEnergyIntegrand a.toCoeffField diff) = 0 :=
      volumeAverage_energy_eq_zero_of_sub_maximizer_zero U a hEll diff hdiffMaxZero
    have hdiffGradZero :
        diff.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] 0 :=
      grad_eq_zero_ae_of_volumeAverage_energy_eq_zero U a hEll diff
        (hInt.energy diff) hEnergyAvg
    have hsubGradZero :
        (fun x => v.toH1.grad x - w.toH1.grad x)
          =ᵐ[volumeMeasureOn (U : Set (Vec d))] 0 := by
      simpa [diff, AHarmonicFunction.grad_subOfIntegrable] using hdiffGradZero
    filter_upwards [hsubGradZero] with x hx
    exact sub_eq_zero.mp hx

/-- Note-facing Chapter 2 gradient uniqueness from the public a.e. coefficient
interface. -/
theorem responseGradientUniquenessTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseGradientUniquenessTheory U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hEll :
      IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
  have hb : ResponseGradientUniquenessTheory U b :=
    responseGradientUniquenessTheory_of_isEllipticFieldOn U b hEll
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact ResponseGradientUniquenessTheory.ofAEEq hba hb

end BookCh02

end

end Ch02
end Internal
end Homogenization
