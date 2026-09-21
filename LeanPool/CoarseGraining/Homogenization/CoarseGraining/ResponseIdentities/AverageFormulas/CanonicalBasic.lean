/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.CoarseFormulas

/-! # Canonical Basic -/

namespace Homogenization

noncomputable section

open Pointwise

/-!
# Average formulas (part 3) -- ScalarCanonicalMaximizer basic API

ScalarCanonicalMaximizer namespace: responseJ_eq, first/second variation,
energy, linear response, polarization, averagePairing, together with the
GradientBasisData and FluxBasisData structures and their nonempty
constructors.
-/

namespace ScalarCanonicalMaximizer

theorem responseJ_eq {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) :
    ResponseJ U p q a = volumeAverage U (scalarResponseIntegrand U a p q (v : AHarmonicFunction a U)) := by
  exact responseJ_eq_of_isResponseMaximizer U p q a v.isResponseMaximizer

theorem firstVariation {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) (w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a (v : AHarmonicFunction a U))
    (hw_int : weakFluxIntegrable U a w)
    (hresp_v : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand U a p q (v : AHarmonicFunction a U)) U)
    (hlin : MeasureTheory.IntegrableOn
      (scalarFirstVariationIntegrand U a p q (v : AHarmonicFunction a U) w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U (scalarFirstVariationIntegrand U a p q (v : AHarmonicFunction a U) w) = 0 := by
  exact responseJ_first_variation_of_isResponseMaximizer
    U a p q (v : AHarmonicFunction a U) v.isResponseMaximizer w
    hu_int hw_int hresp_v hlin henergy

theorem secondVariationLine {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) (w : AHarmonicFunction a U) (t : ℝ)
    (hu_int : weakFluxIntegrable U a (v : AHarmonicFunction a U))
    (hw_int : weakFluxIntegrable U a w)
    (hresp_v : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand U a p q (v : AHarmonicFunction a U)) U)
    (hlin : MeasureTheory.IntegrableOn
      (scalarFirstVariationIntegrand U a p q (v : AHarmonicFunction a U) w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U
        (scalarResponseIntegrand U a p q
          (scalarPerturbation (v : AHarmonicFunction a U) w t hu_int hw_int)) =
      ResponseJ U p q a - ((t ^ 2) / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  exact responseJ_second_variation_line_of_isResponseMaximizer
    U a p q (v : AHarmonicFunction a U) v.isResponseMaximizer w t
    hu_int hw_int hresp_v hlin henergy

theorem secondVariation {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) (w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a (v : AHarmonicFunction a U))
    (hw_int : weakFluxIntegrable U a w)
    (hresp_v : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand U a p q (v : AHarmonicFunction a U)) U)
    (hlin : MeasureTheory.IntegrableOn
      (scalarFirstVariationIntegrand U a p q (v : AHarmonicFunction a U) w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U
        (scalarResponseIntegrand U a p q
          (scalarPerturbation (v : AHarmonicFunction a U) w 1 hu_int hw_int)) =
      ResponseJ U p q a - (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  exact responseJ_second_variation_of_isResponseMaximizer
    U a p q (v : AHarmonicFunction a U) v.isResponseMaximizer w
    hu_int hw_int hresp_v hlin henergy

theorem energy {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a)
    (hu_int : ∀ φ : H10Function U,
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x))
          (φ.toH1Function.grad x)) U)
    (hresp_v : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand U a p q (v : AHarmonicFunction a U)) U)
    (hlin_self : MeasureTheory.IntegrableOn
      (scalarFirstVariationIntegrand U a p q
        (v : AHarmonicFunction a U) (v : AHarmonicFunction a U)) U)
    (henergy : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand a (v : AHarmonicFunction a U)) U) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a (v : AHarmonicFunction a U)) := by
  exact responseJ_energy_of_isResponseMaximizer
    U a p q (v : AHarmonicFunction a U) v.isResponseMaximizer
    hu_int hresp_v hlin_self henergy

theorem linearResponseSq {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {lam Lam : ℝ} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a) (hInt : ResponseLinearIntegrabilityData U a)
    (w : AHarmonicFunction a U) :
    (volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))) ^ 2 ≤
      volumeAverage U (scalarVariationEnergyIntegrand a w) * (2 * ResponseJ U p q a) := by
  exact basic_cg_identities_linear_response_sq_of_isResponseMaximizer
    U a hEll p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer w

theorem linearResponseSqOfIsEllipticFieldOn {d : ℕ} {U : Set (Vec d)}
    {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (v : ScalarCanonicalMaximizer U p q a) (hEll : IsEllipticFieldOn lam Lam U a)
    (w : AHarmonicFunction a U) :
    (volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))) ^ 2 ≤
      volumeAverage U (scalarVariationEnergyIntegrand a w) * (2 * ResponseJ U p q a) :=
  linearResponseSq v hEll (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w

theorem linearResponse {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {lam Lam : ℝ} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a) (hInt : ResponseLinearIntegrabilityData U a)
    (w : AHarmonicFunction a U) :
    |volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * ResponseJ U p q a) := by
  exact basic_cg_identities_linear_response_of_isResponseMaximizer
    U a hEll p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer w

theorem linearResponseOfIsEllipticFieldOn {d : ℕ} {U : Set (Vec d)}
    {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (v : ScalarCanonicalMaximizer U p q a) (hEll : IsEllipticFieldOn lam Lam U a)
    (w : AHarmonicFunction a U) :
    |volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))| ≤
      Real.sqrt (volumeAverage U (scalarVariationEnergyIntegrand a w)) *
        Real.sqrt (2 * ResponseJ U p q a) :=
  linearResponse v hEll (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w

theorem polarization {d : ℕ} {U : Set (Vec d)} {p q p' q' : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a)
    (v' : ScalarCanonicalMaximizer U p' q' a)
    (hInt : ResponseLinearIntegrabilityData U a) :
    volumeAverage U
        (fun x => vecDot ((v' : AHarmonicFunction a U).toH1.grad x)
          (matVecMul (symmPart (a x)) ((v : AHarmonicFunction a U).toH1.grad x))) =
      ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a := by
  exact basic_cg_identities_polarization_of_isResponseMaximizer
    U a p q p' q' hInt
    (v : AHarmonicFunction a U) (v' : AHarmonicFunction a U)
    v.isResponseMaximizer v'.isResponseMaximizer

theorem polarizationOfIsEllipticFieldOn {d : ℕ} {U : Set (Vec d)}
    {p q p' q' : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (v : ScalarCanonicalMaximizer U p q a)
    (v' : ScalarCanonicalMaximizer U p' q' a)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    volumeAverage U
        (fun x => vecDot ((v' : AHarmonicFunction a U).toH1.grad x)
          (matVecMul (symmPart (a x)) ((v : AHarmonicFunction a U).toH1.grad x))) =
      ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a :=
  polarization v v' (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)

theorem averagePairing {d : ℕ} {U : Set (Vec d)} {p q p' q' : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a)
    (v' : ScalarCanonicalMaximizer U p' q' a)
    (hInt : ResponseLinearIntegrabilityData U a) :
    volumeAverage U (fun x => vecDot q' ((v : AHarmonicFunction a U).toH1.grad x)) -
        volumeAverage U
          (fun x => vecDot p' (matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x))) =
      ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a := by
  exact basic_cg_identities_average_pairing_of_isResponseMaximizer
    U a p q p' q' hInt
    (v : AHarmonicFunction a U) (v' : AHarmonicFunction a U)
    v.isResponseMaximizer v'.isResponseMaximizer

theorem averagePairingOfIsEllipticFieldOn {d : ℕ} {U : Set (Vec d)}
    {p q p' q' : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (v : ScalarCanonicalMaximizer U p q a)
    (v' : ScalarCanonicalMaximizer U p' q' a)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    volumeAverage U (fun x => vecDot q' ((v : AHarmonicFunction a U).toH1.grad x)) -
        volumeAverage U
          (fun x => vecDot p' (matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x))) =
      ResponseJ U p q a + ResponseJ U p' q' a - ResponseJ U (p - p') (q - q') a :=
  averagePairing v v' (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll)

structure GradientBasisData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  grad :
    ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a

structure FluxBasisData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  flux :
    ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a

namespace GradientBasisData

noncomputable def ofNonempty {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (h : ∀ i : Fin d, Nonempty (ScalarCanonicalMaximizer U 0 (Pi.single i 1) a)) :
    GradientBasisData U a where
  grad i := Classical.choice (h i)

theorem nonempty_of_forall_nonempty {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (h : ∀ i : Fin d, Nonempty (ScalarCanonicalMaximizer U 0 (Pi.single i 1) a)) :
    Nonempty (GradientBasisData U a) :=
  ⟨ofNonempty h⟩

theorem nonempty_of_forall_exists_firstVariation_eq_zero_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hex :
      ∀ i : Fin d,
        ∃ u : AHarmonicFunction a U,
          ∀ w : AHarmonicFunction a U,
            volumeAverage U
              (scalarFirstVariationIntegrand U a 0 (Pi.single i 1) u w) = 0) :
    Nonempty (GradientBasisData U a) :=
  nonempty_of_forall_nonempty fun i =>
    ScalarCanonicalMaximizer.nonempty_of_exists_firstVariation_eq_zero_of_isEllipticFieldOn
      hEll 0 (Pi.single i 1) (hex i)

theorem nonempty_of_forall_exists_firstVariation_integral_eq_zero_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hex :
      ∀ i : Fin d,
        ∃ u : AHarmonicFunction a U,
          ∀ w : AHarmonicFunction a U,
            ∫ x in U, scalarFirstVariationIntegrand U a 0 (Pi.single i 1) u w x
              ∂MeasureTheory.volume = 0) :
    Nonempty (GradientBasisData U a) :=
  nonempty_of_forall_nonempty fun i =>
    ScalarCanonicalMaximizer.nonempty_of_exists_firstVariation_integral_eq_zero_of_isEllipticFieldOn
      hEll 0 (Pi.single i 1) (hex i)

end GradientBasisData

namespace FluxBasisData

noncomputable def ofNonempty {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (h : ∀ i : Fin d, Nonempty (ScalarCanonicalMaximizer U (Pi.single i 1) 0 a)) :
    FluxBasisData U a where
  flux i := Classical.choice (h i)

theorem nonempty_of_forall_nonempty {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (h : ∀ i : Fin d, Nonempty (ScalarCanonicalMaximizer U (Pi.single i 1) 0 a)) :
    Nonempty (FluxBasisData U a) :=
  ⟨ofNonempty h⟩

theorem nonempty_of_forall_exists_firstVariation_eq_zero_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hex :
      ∀ i : Fin d,
        ∃ u : AHarmonicFunction a U,
          ∀ w : AHarmonicFunction a U,
            volumeAverage U
              (scalarFirstVariationIntegrand U a (Pi.single i 1) 0 u w) = 0) :
    Nonempty (FluxBasisData U a) :=
  nonempty_of_forall_nonempty fun i =>
    ScalarCanonicalMaximizer.nonempty_of_exists_firstVariation_eq_zero_of_isEllipticFieldOn
      hEll (Pi.single i 1) 0 (hex i)

theorem nonempty_of_forall_exists_firstVariation_integral_eq_zero_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hex :
      ∀ i : Fin d,
        ∃ u : AHarmonicFunction a U,
          ∀ w : AHarmonicFunction a U,
            ∫ x in U, scalarFirstVariationIntegrand U a (Pi.single i 1) 0 u w x
              ∂MeasureTheory.volume = 0) :
    Nonempty (FluxBasisData U a) :=
  nonempty_of_forall_nonempty fun i =>
    ScalarCanonicalMaximizer.nonempty_of_exists_firstVariation_integral_eq_zero_of_isEllipticFieldOn
      hEll (Pi.single i 1) 0 (hex i)

end FluxBasisData

end ScalarCanonicalMaximizer

end

end Homogenization
