/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra

/-! # Maximizer -/

namespace Homogenization

noncomputable section

open Pointwise

/-!
# Response maximizer identities

`ResponseLinearIntegrabilityData`, `IsResponseMaximizer`,
`ScalarCanonicalMaximizer`, and the basic coarse-graining identities
(`basic_cg_identities_first_variation_*`, `basic_cg_identities_sub_*`).
-/

structure ResponseLinearIntegrabilityData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : Prop where
  weakFlux : ∀ u : AHarmonicFunction a U, weakFluxIntegrable U a u
  grad :
    ∀ (q : Vec d) (u : AHarmonicFunction a U),
      MeasureTheory.IntegrableOn (fun x => vecDot q (u.toH1.grad x)) U
  flux :
    ∀ (p : Vec d) (u : AHarmonicFunction a U),
      MeasureTheory.IntegrableOn (fun x => vecDot p (matVecMul (a x) (u.toH1.grad x))) U
  cross :
    ∀ (u w : AHarmonicFunction a U),
      MeasureTheory.IntegrableOn
        (fun x => vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) U

namespace ResponseLinearIntegrabilityData

theorem of_isEllipticFieldOn {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam : ℝ} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) :
    ResponseLinearIntegrabilityData U a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u φ
    have hflux :
        MemVectorL2 U (fun x => matVecMul (a x) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    exact CorrectionFieldData.integrableOn_vecDot_of_memVectorL2 hflux
      φ.toH1Function.grad_memVectorL2
  · intro q u
    exact CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 q
      u.toH1.grad_memVectorL2
  · intro p u
    have hflux :
        MemVectorL2 U (fun x => matVecMul (a x) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    exact CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 p hflux
  · intro u w
    have huFlux :
        MemVectorL2 U (fun x => matVecMul (a x) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    have hwFlux :
        MemVectorL2 U (fun x => matVecMul (a x) (w.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2
    have hterm1 :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1.grad x))) U :=
      CorrectionFieldData.integrableOn_vecDot_of_memVectorL2 w.toH1.grad_memVectorL2 huFlux
    have hterm2 :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (u.toH1.grad x) (matVecMul (a x) (w.toH1.grad x))) U :=
      CorrectionFieldData.integrableOn_vecDot_of_memVectorL2 u.toH1.grad_memVectorL2 hwFlux
    have hsum :
        MeasureTheory.IntegrableOn
          ((fun x => vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1.grad x))) +
            fun x => vecDot (u.toH1.grad x) (matVecMul (a x) (w.toH1.grad x))) U := by
      simpa [MeasureTheory.IntegrableOn] using hterm1.integrable.add hterm2.integrable
    have hhalf :
        MeasureTheory.IntegrableOn
          ((1 / 2 : ℝ) •
            ((fun x => vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1.grad x))) +
              fun x => vecDot (u.toH1.grad x) (matVecMul (a x) (w.toH1.grad x)))) U := by
      simpa [MeasureTheory.IntegrableOn] using hsum.integrable.smul (1 / 2 : ℝ)
    have hdecomp :
        (fun x => vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) =
          ((1 / 2 : ℝ) •
            ((fun x => vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1.grad x))) +
              fun x => vecDot (u.toH1.grad x) (matVecMul (a x) (w.toH1.grad x)))) := by
      funext x
      calc
        vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) =
            (1 / 2 : ℝ) *
              (vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1.grad x)) +
                vecDot (w.toH1.grad x) (matVecMul (matTranspose (a x)) (u.toH1.grad x))) := by
                  rw [symmPart_eq_smul_add_transpose, smul_matVecMul, add_matVecMul,
                    vecDot_smul_right, vecDot_add_right]
        _ = (1 / 2 : ℝ) *
              (vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1.grad x)) +
                vecDot (u.toH1.grad x) (matVecMul (a x) (w.toH1.grad x))) := by
                  have htranspose :
                      vecDot (w.toH1.grad x) (matVecMul (matTranspose (a x)) (u.toH1.grad x)) =
                        vecDot (u.toH1.grad x) (matVecMul (a x) (w.toH1.grad x)) := by
                    calc
                      vecDot (w.toH1.grad x) (matVecMul (matTranspose (a x)) (u.toH1.grad x)) =
                          vecDot (matVecMul (a x) (w.toH1.grad x)) (u.toH1.grad x) := by
                            rw [vecDot_matVecMul_transpose]
                      _ = vecDot (u.toH1.grad x) (matVecMul (a x) (w.toH1.grad x)) := by
                            rw [vecDot_comm]
                  rw [htranspose]
        _ = ((1 / 2 : ℝ) •
              ((fun x => vecDot (w.toH1.grad x) (matVecMul (a x) (u.toH1.grad x))) +
                fun x => vecDot (u.toH1.grad x) (matVecMul (a x) (w.toH1.grad x)))) x := by
                  rfl
    rw [hdecomp]
    exact hhalf

theorem energy {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hInt : ResponseLinearIntegrabilityData U a) (w : AHarmonicFunction a U) :
    MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U := by
  simpa [scalarVariationEnergyIntegrand] using! hInt.cross w w

theorem firstVariation {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hInt : ResponseLinearIntegrabilityData U a) (p q : Vec d)
    (u w : AHarmonicFunction a U) :
    MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u w) U := by
  have hgrad := hInt.grad q w
  have hflux := hInt.flux p w
  have hcross := hInt.cross u w
  have hsub :
      MeasureTheory.IntegrableOn
        (fun x => vecDot q (w.toH1.grad x) - vecDot p (matVecMul (a x) (w.toH1.grad x))) U := by
    simpa [sub_eq_add_neg, MeasureTheory.IntegrableOn] using!
      hgrad.integrable.sub hflux.integrable
  simpa [scalarFirstVariationIntegrand, sub_eq_add_neg, MeasureTheory.IntegrableOn] using!
    hsub.integrable.sub hcross.integrable

theorem response {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hInt : ResponseLinearIntegrabilityData U a) (p q : Vec d) (u : AHarmonicFunction a U) :
    MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U := by
  have henergy := hInt.energy u
  have hflux := hInt.flux p u
  have hgrad := hInt.grad q u
  have hhalf_energy :
      MeasureTheory.IntegrableOn (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a u)) U := by
    simpa [MeasureTheory.IntegrableOn] using henergy.integrable.smul (-(1 / 2 : ℝ))
  have hsub :
      MeasureTheory.IntegrableOn
        (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a u) -
          fun x => vecDot p (matVecMul (a x) (u.toH1.grad x))) U := by
    simpa [MeasureTheory.IntegrableOn] using hhalf_energy.integrable.sub hflux.integrable
  have hdecomp :
      scalarResponseIntegrand U a p q u =
        (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a u) -
            fun x => vecDot p (matVecMul (a x) (u.toH1.grad x))) +
          fun x => vecDot q (u.toH1.grad x) := by
    funext x
    simp [scalarResponseIntegrand, scalarVariationEnergyIntegrand, sub_eq_add_neg, smul_eq_mul]
  rw [hdecomp]
  simpa [MeasureTheory.IntegrableOn] using
    hsub.integrable.add hgrad.integrable

end ResponseLinearIntegrabilityData

def IsResponseMaximizer {d : ℕ} (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d)
    (u : AHarmonicFunction a U) : Prop :=
  ∀ w : AHarmonicFunction a U,
    volumeAverage U (scalarResponseIntegrand U a p q w) ≤
      volumeAverage U (scalarResponseIntegrand U a p q u)

namespace IsResponseMaximizer

theorem addConst {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : AHarmonicFunction a U} (hmax : IsResponseMaximizer U p q a u) (c : ℝ) :
    IsResponseMaximizer U p q a (u.addConst c) := by
  intro w
  simpa using hmax w

theorem normalizeMeanZero {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : AHarmonicFunction a U} (hmax : IsResponseMaximizer U p q a u) :
    IsResponseMaximizer U p q a u.normalizeMeanZero := by
  intro w
  simpa using hmax w

end IsResponseMaximizer

structure ScalarCanonicalMaximizer {d : ℕ} (U : Set (Vec d)) (p q : Vec d)
    (a : CoeffField d) where
  toAHarmonicFunctionMeanZero : AHarmonicFunctionMeanZero a U
  isMaximizer : IsResponseMaximizer U p q a toAHarmonicFunctionMeanZero

namespace ScalarCanonicalMaximizer

instance {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} :
    CoeOut (ScalarCanonicalMaximizer U p q a) (AHarmonicFunctionMeanZero a U) where
  coe v := v.toAHarmonicFunctionMeanZero

instance {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} :
    CoeOut (ScalarCanonicalMaximizer U p q a) (AHarmonicFunction a U) where
  coe v := v.toAHarmonicFunctionMeanZero.toAHarmonicFunction

theorem meanZero {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) :
    MeanZeroOn U v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.toFun :=
  v.toAHarmonicFunctionMeanZero.meanZero

theorem isResponseMaximizer {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) :
    IsResponseMaximizer U p q a (v : AHarmonicFunction a U) :=
  v.isMaximizer

noncomputable def ofIsResponseMaximizer {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u) :
    ScalarCanonicalMaximizer U p q a where
  toAHarmonicFunctionMeanZero := u.toMeanZero
  isMaximizer := hmax.normalizeMeanZero

@[simp] theorem coe_ofIsResponseMaximizer {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u) :
    ((ofIsResponseMaximizer u hmax : ScalarCanonicalMaximizer U p q a) : AHarmonicFunction a U) =
      u.normalizeMeanZero :=
  rfl

end ScalarCanonicalMaximizer

noncomputable def scalarPerturbation {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u w : AHarmonicFunction a U) (t : ℝ)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w) :
    AHarmonicFunction a U :=
  AHarmonicFunction.addSMulOfIntegrable u w hu_int hw_int t

@[simp] theorem scalarPerturbation_grad {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u w : AHarmonicFunction a U) (t : ℝ)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w) :
    (scalarPerturbation u w t hu_int hw_int).toH1.grad = u.toH1.grad + t • w.toH1.grad := by
  simpa [scalarPerturbation] using AHarmonicFunction.grad_addSMulOfIntegrable u w hu_int hw_int t

theorem scalarResponseIntegrand_scalarPerturbation {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p q : Vec d) (u w : AHarmonicFunction a U) (t : ℝ)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w) :
    scalarResponseIntegrand U a p q (scalarPerturbation u w t hu_int hw_int) =
      scalarResponseIntegrand U a p q u
        + t • scalarFirstVariationIntegrand U a p q u w
        - (((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w) := by
  funext x
  have hsymm :
      vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (w.toH1.grad x)) =
        vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) := by
    calc
      vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (w.toH1.grad x))
        = vecDot (u.toH1.grad x) (matVecMul (matTranspose (symmPart (a x))) (w.toH1.grad x)) := by
            simp
      _ = vecDot (matVecMul (symmPart (a x)) (u.toH1.grad x)) (w.toH1.grad x) := by
            rw [vecDot_matVecMul_transpose]
      _ = vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) := by
            rw [vecDot_comm]
  simp [scalarResponseIntegrand, scalarFirstVariationIntegrand, scalarVariationEnergyIntegrand,
    scalarPerturbation_grad, matVecMul_add, matVecMul_smul, vecDot_add_left, vecDot_add_right,
    vecDot_smul_left, vecDot_smul_right, hsymm, smul_eq_mul, sub_eq_add_neg]
  ring

theorem volumeAverage_scalarResponseIntegrand_scalarPerturbation {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (p q : Vec d) (u w : AHarmonicFunction a U) (t : ℝ)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U (scalarResponseIntegrand U a p q (scalarPerturbation u w t hu_int hw_int)) =
      volumeAverage U (scalarResponseIntegrand U a p q u)
        + t * volumeAverage U (scalarFirstVariationIntegrand U a p q u w)
        - ((t ^ 2) / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  unfold volumeAverage
  rw [scalarResponseIntegrand_scalarPerturbation]
  have hlin_t :
      MeasureTheory.IntegrableOn (t • scalarFirstVariationIntegrand U a p q u w) U :=
    by
      simpa [MeasureTheory.IntegrableOn] using (hlin.integrable.smul t)
  have henergy_t :
      MeasureTheory.IntegrableOn ((((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w)) U :=
    by
      simpa [MeasureTheory.IntegrableOn] using (henergy.integrable.smul ((t ^ 2) / 2 : ℝ))
  have hsub :
      MeasureTheory.IntegrableOn
        (t • scalarFirstVariationIntegrand U a p q u w -
          (((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w)) U :=
    by
      simpa [MeasureTheory.IntegrableOn] using (hlin_t.integrable.sub henergy_t.integrable)
  have hsplit_add :
      (fun x =>
        (scalarResponseIntegrand U a p q u + t • scalarFirstVariationIntegrand U a p q u w -
            (((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w)) x) =
        fun x =>
          scalarResponseIntegrand U a p q u x +
            (t • scalarFirstVariationIntegrand U a p q u w -
              (((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w)) x := by
    funext x
    simp [sub_eq_add_neg, add_assoc]
  rw [hsplit_add]
  rw [MeasureTheory.integral_add hresp_u hsub]
  have hsplit_sub :
      (fun x =>
        (t • scalarFirstVariationIntegrand U a p q u w -
            (((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w)) x) =
        fun x =>
          (t • scalarFirstVariationIntegrand U a p q u w) x -
            ((((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w) x) := by
    funext x
    simp
  rw [hsplit_sub]
  rw [MeasureTheory.integral_sub hlin_t henergy_t]
  rw [show (fun x => (t • scalarFirstVariationIntegrand U a p q u w) x) =
      fun x => t • scalarFirstVariationIntegrand U a p q u w x by
        funext x
        simp]
  rw [show (fun x => ((((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w)) x) =
      fun x => (((t ^ 2) / 2 : ℝ) • scalarVariationEnergyIntegrand a w x) by
        funext x
        simp]
  rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul]
  simp [smul_eq_mul]
  ring_nf

theorem scalarFirstVariationIntegrand_split {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p q p' q' : Vec d) (u w : AHarmonicFunction a U) :
    scalarFirstVariationIntegrand U a p q u w =
      scalarFirstVariationIntegrand U a p' q' u w
        + scalarResponseIntegrand U a (p - p') (q - q') w
        + ((1 / 2 : ℝ) • scalarVariationEnergyIntegrand a w) := by
  funext x
  have hq :
      vecDot q (w.toH1.grad x) =
        vecDot q' (w.toH1.grad x) + vecDot (q - q') (w.toH1.grad x) := by
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    ring
  have hp :
      vecDot p (matVecMul (a x) (w.toH1.grad x)) =
        vecDot p' (matVecMul (a x) (w.toH1.grad x)) +
          vecDot (p - p') (matVecMul (a x) (w.toH1.grad x)) := by
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    ring
  unfold scalarFirstVariationIntegrand scalarResponseIntegrand scalarVariationEnergyIntegrand
  rw [hq, hp]
  simp [sub_eq_add_neg, smul_eq_mul]
  ring

theorem scalarResponseIntegrand_scalarPerturbation_one_split {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (p q p' q' : Vec d) (u w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w) :
    scalarResponseIntegrand U a p q (scalarPerturbation u w 1 hu_int hw_int) =
      scalarResponseIntegrand U a p q u
        + scalarResponseIntegrand U a (p - p') (q - q') w
        + scalarFirstVariationIntegrand U a p' q' u w := by
  rw [scalarResponseIntegrand_scalarPerturbation U a p q u w 1 hu_int hw_int]
  rw [scalarFirstVariationIntegrand_split U a p q p' q' u w]
  funext x
  simp [sub_eq_add_neg, smul_eq_mul]
  ring

theorem linearCoeff_eq_zero_of_quadratic_nonpos (L Q : ℝ)
    (h : ∀ t : ℝ, t * L - ((t ^ 2) / 2 : ℝ) * Q ≤ 0) : L = 0 := by
  by_contra hL
  have hLsq : 0 < L ^ 2 := by
    exact sq_pos_of_ne_zero hL
  by_cases hQ : 0 < Q
  · have htest := h (L / Q)
    have hpos : 0 < (L / Q) * L - (((L / Q) ^ 2) / 2 : ℝ) * Q := by
      field_simp [hQ.ne']
      nlinarith
    linarith
  · have hQ_nonpos : Q ≤ 0 := le_of_not_gt hQ
    have htest := h L
    have hpos : 0 < L * L - ((L ^ 2) / 2 : ℝ) * Q := by
      nlinarith
    linarith

theorem basic_cg_identities_first_variation_of_isResponseMaximizer {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u) (w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0 := by
  let L := volumeAverage U (scalarFirstVariationIntegrand U a p q u w)
  let Q := volumeAverage U (scalarVariationEnergyIntegrand a w)
  have hquad : ∀ t : ℝ, t * L - ((t ^ 2) / 2 : ℝ) * Q ≤ 0 := by
    intro t
    have hopt := hmax (scalarPerturbation u w t hu_int hw_int)
    rw [volumeAverage_scalarResponseIntegrand_scalarPerturbation U a p q u w t
      hu_int hw_int hresp_u hlin henergy] at hopt
    simpa [L, Q] using hopt
  exact linearCoeff_eq_zero_of_quadratic_nonpos L Q hquad

theorem basic_cg_identities_first_variation_eq_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u) (w : AHarmonicFunction a U) :
    volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
        volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) =
      volumeAverage U
        (fun x => vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
  have hfirst :=
    basic_cg_identities_first_variation_of_isResponseMaximizer
      U a p q u hmax w (hInt.weakFlux u) (hInt.weakFlux w)
      (hInt.response p q u) (hInt.firstVariation p q u w) (hInt.energy w)
  have hsub_qp :
      MeasureTheory.IntegrableOn
        (fun x => vecDot q (w.toH1.grad x) - vecDot p (matVecMul (a x) (w.toH1.grad x))) U := by
    simpa [MeasureTheory.IntegrableOn] using!
      (hInt.grad q w).integrable.sub (hInt.flux p w).integrable
  have havg :
      volumeAverage U (scalarFirstVariationIntegrand U a p q u w) =
        (volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
          volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x)))) -
            volumeAverage U
              (fun x => vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
    unfold scalarFirstVariationIntegrand
    have hrewrite :
        volumeAverage U
            (fun x =>
              vecDot q (w.toH1.grad x) - vecDot p (matVecMul (a x) (w.toH1.grad x)) -
                vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) =
          volumeAverage U
            ((fun x => vecDot q (w.toH1.grad x) - vecDot p (matVecMul (a x) (w.toH1.grad x))) -
              fun x => vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
      rfl
    have hrewrite_qp :
        volumeAverage U (fun x => vecDot q (w.toH1.grad x) - vecDot p (matVecMul (a x) (w.toH1.grad x))) =
          volumeAverage U (fun x => vecDot q (w.toH1.grad x)) -
            volumeAverage U (fun x => vecDot p (matVecMul (a x) (w.toH1.grad x))) :=
      volumeAverage_sub (hInt.grad q w) (hInt.flux p w)
    rw [hrewrite]
    rw [volumeAverage_sub hsub_qp (hInt.cross u w)]
    rw [hrewrite_qp]
  rw [havg] at hfirst
  linarith

theorem isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d) (u : AHarmonicFunction a U)
    (hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0) :
    IsResponseMaximizer U p q a u := by
  let hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  intro w
  let wdiff :=
    AHarmonicFunction.subOfIntegrable w u (hInt.weakFlux w) (hInt.weakFlux u)
  have hgrad_w :
      (scalarPerturbation u wdiff 1 (hInt.weakFlux u) (hInt.weakFlux wdiff)).toH1.grad =
        w.toH1.grad := by
    dsimp [wdiff]
    rw [scalarPerturbation_grad, AHarmonicFunction.grad_subOfIntegrable]
    funext x
    simp [sub_eq_add_neg]
  have hresp_w :
      volumeAverage U
          (scalarResponseIntegrand U a p q
            (scalarPerturbation u wdiff 1 (hInt.weakFlux u) (hInt.weakFlux wdiff))) =
        volumeAverage U (scalarResponseIntegrand U a p q w) := by
    exact congrArg (volumeAverage U) (scalarResponseIntegrand_eq_of_grad_eq hgrad_w)
  have hsplit :=
    volumeAverage_scalarResponseIntegrand_scalarPerturbation U a p q u wdiff 1
      (hInt.weakFlux u) (hInt.weakFlux wdiff)
      (hInt.response p q u) (hInt.firstVariation p q u wdiff) (hInt.energy wdiff)
  rw [hresp_w] at hsplit
  have hfirst_zero :
      volumeAverage U (scalarFirstVariationIntegrand U a p q u wdiff) = 0 :=
    hfirst wdiff
  have henergy_nonneg :
      0 ≤ volumeAverage U (scalarVariationEnergyIntegrand a wdiff) :=
    by
      have hpointwise :
          ∀ x ∈ U, 0 ≤ scalarVariationEnergyIntegrand a wdiff x := by
        intro x hx
        unfold scalarVariationEnergyIntegrand
        rcases hEll with ⟨_, hEllPt⟩
        have hlower :=
          lowerBound_symmPart_of_isEllipticMatrix (hEllPt x hx) (wdiff.toH1.grad x)
        have hnorm_nonneg : 0 ≤ vecNormSq (wdiff.toH1.grad x) :=
          vecNormSq_nonneg (wdiff.toH1.grad x)
        have hlam_nonneg : 0 ≤ lam := le_of_lt (hEllPt x hx).1
        nlinarith
      apply volumeAverage_nonneg_of_nonneg_on
        (measurableSet_of_isEllipticFieldOn hEll)
      exact hpointwise
  rw [hfirst_zero] at hsplit
  have hrewrite :
      volumeAverage U (scalarResponseIntegrand U a p q w) =
        volumeAverage U (scalarResponseIntegrand U a p q u) -
          ((1 ^ 2) / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a wdiff) := by
    simpa using hsplit
  linarith

namespace ScalarCanonicalMaximizer

theorem firstVariation_eq_zero_of_integral_eq_zero {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {p q : Vec d}
    {u : AHarmonicFunction a U}
    (hfirst :
      ∀ w : AHarmonicFunction a U,
        ∫ x in U, scalarFirstVariationIntegrand U a p q u w x ∂MeasureTheory.volume = 0) :
    ∀ w : AHarmonicFunction a U,
      volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0 := by
  intro w
  exact volumeAverage_eq_zero_of_integral_eq_zero (hfirst w)

noncomputable def ofFirstVariationEqZeroOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d)
    (u : AHarmonicFunction a U)
    (hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0) :
    ScalarCanonicalMaximizer U p q a :=
  ofIsResponseMaximizer u
    (isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
      U a hEll p q u hfirst)

@[simp] theorem coe_ofFirstVariationEqZeroOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d)
    (u : AHarmonicFunction a U)
    (hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0) :
    ((ofFirstVariationEqZeroOfIsEllipticFieldOn hEll p q u hfirst :
        ScalarCanonicalMaximizer U p q a) : AHarmonicFunction a U) =
      u.normalizeMeanZero :=
  rfl

theorem nonempty_of_exists_firstVariation_eq_zero_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d)
    (hex :
      ∃ u : AHarmonicFunction a U,
        ∀ w : AHarmonicFunction a U,
          volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0) :
    Nonempty (ScalarCanonicalMaximizer U p q a) := by
  rcases hex with ⟨u, hfirst⟩
  exact ⟨ofFirstVariationEqZeroOfIsEllipticFieldOn hEll p q u hfirst⟩

theorem nonempty_of_exists_firstVariation_integral_eq_zero_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d)
    (hex :
      ∃ u : AHarmonicFunction a U,
        ∀ w : AHarmonicFunction a U,
          ∫ x in U, scalarFirstVariationIntegrand U a p q u w x ∂MeasureTheory.volume = 0) :
    Nonempty (ScalarCanonicalMaximizer U p q a) := by
  rcases hex with ⟨u, hfirst⟩
  exact nonempty_of_exists_firstVariation_eq_zero_of_isEllipticFieldOn hEll p q
    ⟨u, firstVariation_eq_zero_of_integral_eq_zero hfirst⟩

end ScalarCanonicalMaximizer

theorem volumeAverage_scalarResponseIntegrand_scalarPerturbation_one_split_of_isResponseMaximizer
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) (p q p' q' : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p' q' a u) (w : AHarmonicFunction a U) :
    volumeAverage U
        (scalarResponseIntegrand U a p q
          (scalarPerturbation u w 1 (hInt.weakFlux u) (hInt.weakFlux w))) =
      volumeAverage U (scalarResponseIntegrand U a p q u)
        + volumeAverage U (scalarResponseIntegrand U a (p - p') (q - q') w) := by
  have hfirst :=
    basic_cg_identities_first_variation_of_isResponseMaximizer
      U a p' q' u hmax w (hInt.weakFlux u) (hInt.weakFlux w)
      (hInt.response p' q' u) (hInt.firstVariation p' q' u w) (hInt.energy w)
  rw [scalarResponseIntegrand_scalarPerturbation_one_split U a p q p' q' u w
    (hInt.weakFlux u) (hInt.weakFlux w)]
  have hresp_sum :
      MeasureTheory.IntegrableOn
        (scalarResponseIntegrand U a p q u +
          scalarResponseIntegrand U a (p - p') (q - q') w) U := by
    simpa [MeasureTheory.IntegrableOn] using
      (hInt.response p q u).integrable.add (hInt.response (p - p') (q - q') w).integrable
  rw [volumeAverage_add hresp_sum (hInt.firstVariation p' q' u w)]
  rw [volumeAverage_add (hInt.response p q u) (hInt.response (p - p') (q - q') w)]
  rw [hfirst]
  ring

theorem basic_cg_identities_sub_isResponseMaximizer_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q p' q' : Vec d)
    (hInt : ResponseLinearIntegrabilityData U a)
    (u u' : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (hmax' : IsResponseMaximizer U p' q' a u') :
    IsResponseMaximizer U (p - p') (q - q') a
      (AHarmonicFunction.subOfIntegrable u u' (hInt.weakFlux u) (hInt.weakFlux u')) := by
  intro w
  let udiff := AHarmonicFunction.subOfIntegrable u u' (hInt.weakFlux u) (hInt.weakFlux u')
  have hopt := hmax (scalarPerturbation u' w 1 (hInt.weakFlux u') (hInt.weakFlux w))
  have hsplit_w :=
    volumeAverage_scalarResponseIntegrand_scalarPerturbation_one_split_of_isResponseMaximizer
      U a p q p' q' hInt u' hmax' w
  have hsplit_u :=
    volumeAverage_scalarResponseIntegrand_scalarPerturbation_one_split_of_isResponseMaximizer
      U a p q p' q' hInt u' hmax' udiff
  have hgrad_u :
      (scalarPerturbation u' udiff 1 (hInt.weakFlux u') (hInt.weakFlux udiff)).toH1.grad =
        u.toH1.grad := by
    dsimp [udiff]
    rw [scalarPerturbation_grad, AHarmonicFunction.grad_subOfIntegrable]
    funext x
    simp [sub_eq_add_neg]
  have hresp_u :
      volumeAverage U
          (scalarResponseIntegrand U a p q
            (scalarPerturbation u' udiff 1 (hInt.weakFlux u') (hInt.weakFlux udiff))) =
        volumeAverage U (scalarResponseIntegrand U a p q u) := by
    exact congrArg (volumeAverage U) (scalarResponseIntegrand_eq_of_grad_eq hgrad_u)
  rw [hresp_u] at hsplit_u
  rw [hsplit_w, hsplit_u] at hopt
  linarith

end

end Homogenization
