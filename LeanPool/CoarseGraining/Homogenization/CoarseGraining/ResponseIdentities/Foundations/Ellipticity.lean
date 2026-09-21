/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Foundations.Maximizer

/-! # Ellipticity -/

namespace Homogenization

noncomputable section

open Pointwise

/-!
# Ellipticity-driven response bounds

Variation-energy arithmetic on `subOfIntegrable`,
`scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn` (the main
Young-inequality estimate), and the `responseJ` supremum structure under
ellipticity assumptions.
-/

/-- Young's inequality in the form `u^2 ≤ A*B ⇒ |u| ≤ A/2 + B/2` for non-negative
`A, B`. Used twice inside the plain upper-bound proof to avoid repeating the
same nlinarith chain. -/
private theorem young_abs_of_sq_le {u A B : ℝ}
    (hu_sq : u ^ 2 ≤ A * B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |u| ≤ A / 2 + B / 2 := by
  have habsSq : |u| ^ 2 ≤ A * B := by simpa [sq_abs] using hu_sq
  have hsumSq : (2 * |u|) ^ 2 ≤ (A + B) ^ 2 := by
    have h0 : 0 ≤ (A - B) ^ 2 := sq_nonneg _
    nlinarith [habsSq, h0]
  have hsum_nonneg : 0 ≤ A + B := add_nonneg hA hB
  have habs2u : 2 * |u| ≤ A + B := le_of_sq_le_sq hsumSq hsum_nonneg
  linarith

theorem scalarVariationEnergyIntegrand_subOfIntegrable {d : ℕ} (a : CoeffField d)
    {U : Set (Vec d)} (u u' : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hu'_int : weakFluxIntegrable U a u') :
    scalarVariationEnergyIntegrand a (AHarmonicFunction.subOfIntegrable u u' hu_int hu'_int) =
      scalarVariationEnergyIntegrand a u + scalarVariationEnergyIntegrand a u'
        - (2 : ℝ) •
            (fun x => vecDot (u'.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
  funext x
  have hsymm :
      vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (u'.toH1.grad x)) =
        vecDot (u'.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) := by
    simpa using vecDot_matVecMul_symmPart_comm (a x) (u.toH1.grad x) (u'.toH1.grad x)
  unfold scalarVariationEnergyIntegrand
  rw [AHarmonicFunction.grad_subOfIntegrable]
  simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left, vecDot_add_right,
    vecDot_neg_left, vecDot_neg_right, smul_eq_mul, hsymm]
  ring

theorem volumeAverage_scalarVariationEnergyIntegrand_subOfIntegrable {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (hInt : ResponseLinearIntegrabilityData U a)
    (u u' : AHarmonicFunction a U) :
    volumeAverage U (scalarVariationEnergyIntegrand a
        (AHarmonicFunction.subOfIntegrable u u' (hInt.weakFlux u) (hInt.weakFlux u'))) =
      volumeAverage U (scalarVariationEnergyIntegrand a u) +
        volumeAverage U (scalarVariationEnergyIntegrand a u') -
          2 * volumeAverage U
            (fun x => vecDot (u'.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
  rw [scalarVariationEnergyIntegrand_subOfIntegrable a u u' (hInt.weakFlux u) (hInt.weakFlux u')]
  have hsum :
      MeasureTheory.IntegrableOn
        (scalarVariationEnergyIntegrand a u + scalarVariationEnergyIntegrand a u') U := by
    simpa [MeasureTheory.IntegrableOn] using
      (hInt.energy u).integrable.add (hInt.energy u').integrable
  rw [volumeAverage_sub hsum]
  · rw [volumeAverage_add (hInt.energy u) (hInt.energy u')]
    rw [volumeAverage_smul]
  · simpa [MeasureTheory.IntegrableOn] using (hInt.cross u u').integrable.smul (2 : ℝ)

theorem basic_cg_identities_second_variation_line_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u) (w : AHarmonicFunction a U) (t : ℝ)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U (scalarResponseIntegrand U a p q (scalarPerturbation u w t hu_int hw_int)) =
      volumeAverage U (scalarResponseIntegrand U a p q u)
        - ((t ^ 2) / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  rw [volumeAverage_scalarResponseIntegrand_scalarPerturbation U a p q u w t
    hu_int hw_int hresp_u hlin henergy]
  rw [basic_cg_identities_first_variation_of_isResponseMaximizer U a p q u hmax w
    hu_int hw_int hresp_u hlin henergy]
  ring

theorem basic_cg_identities_second_variation_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u) (w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U (scalarResponseIntegrand U a p q (scalarPerturbation u w 1 hu_int hw_int)) =
      volumeAverage U (scalarResponseIntegrand U a p q u)
        - (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  simpa using basic_cg_identities_second_variation_line_of_isResponseMaximizer
    U a p q u hmax w 1 hu_int hw_int hresp_u hlin henergy

theorem scalarResponseIntegrand_eq_firstVariation_self_add_half_energy {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U) :
    scalarResponseIntegrand U a p q u =
      scalarFirstVariationIntegrand U a p q u u
        + ((1 / 2 : ℝ) • scalarVariationEnergyIntegrand a u) := by
  funext x
  simp [scalarResponseIntegrand, scalarFirstVariationIntegrand, scalarVariationEnergyIntegrand,
    smul_eq_mul]
  ring

theorem volumeAverage_scalarResponseIntegrand_eq_firstVariation_self_add_half_energy {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U)
    (hlin_self : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u u) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) U) :
    volumeAverage U (scalarResponseIntegrand U a p q u) =
      volumeAverage U (scalarFirstVariationIntegrand U a p q u u)
        + (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a u) := by
  unfold volumeAverage
  rw [scalarResponseIntegrand_eq_firstVariation_self_add_half_energy]
  have hhalf_energy :
      MeasureTheory.IntegrableOn (((1 / 2 : ℝ) • scalarVariationEnergyIntegrand a u)) U := by
    simpa [MeasureTheory.IntegrableOn] using (henergy.integrable.smul (1 / 2 : ℝ))
  rw [show
      (fun x =>
        (scalarFirstVariationIntegrand U a p q u u + ((1 / 2 : ℝ) • scalarVariationEnergyIntegrand a u))
          x) =
        fun x =>
          scalarFirstVariationIntegrand U a p q u u x +
            (((1 / 2 : ℝ) • scalarVariationEnergyIntegrand a u) x) by
        funext x
        simp]
  rw [MeasureTheory.integral_add hlin_self hhalf_energy]
  rw [show
      (fun x => (((1 / 2 : ℝ) • scalarVariationEnergyIntegrand a u) x)) =
        fun x => (1 / 2 : ℝ) • scalarVariationEnergyIntegrand a u x by
        funext x
        simp]
  rw [MeasureTheory.integral_smul]
  simp [smul_eq_mul]
  ring

theorem basic_cg_identities_energy_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u)
    (hu_int : weakFluxIntegrable U a u)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin_self : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u u) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) U) :
    volumeAverage U (scalarResponseIntegrand U a p q u) =
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a u) := by
  have hfirst :=
    basic_cg_identities_first_variation_of_isResponseMaximizer
      U a p q u hmax u hu_int hu_int hresp_u hlin_self henergy
  rw [volumeAverage_scalarResponseIntegrand_eq_firstVariation_self_add_half_energy
    U a p q u hlin_self henergy]
  rw [hfirst]
  ring

theorem responseJValueSet_mem {d : ℕ} (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d)
    (u : AHarmonicFunction a U) :
    volumeAverage U (scalarResponseIntegrand U a p q u) ∈ responseJValueSet U p q a :=
  ⟨u, rfl⟩

theorem responseJValueSet_zero_mem {d : ℕ} (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d) :
    0 ∈ responseJValueSet U p q a := by
  refine ⟨0, ?_⟩
  simp

theorem responseJValueSet_nonempty {d : ℕ} (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d) :
    (responseJValueSet U p q a).Nonempty :=
  ⟨0, responseJValueSet_zero_mem U p q a⟩

def responseJValueSetMeanZero {d : ℕ} (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d) :
    Set ℝ :=
  {m | ∃ u : AHarmonicFunctionMeanZero a U,
      volumeAverage U (scalarResponseIntegrand U a p q (u : AHarmonicFunction a U)) = m}

theorem responseJValueSetMeanZero_mem {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} (u : AHarmonicFunctionMeanZero a U) :
    volumeAverage U (scalarResponseIntegrand U a p q (u : AHarmonicFunction a U)) ∈
      responseJValueSetMeanZero U p q a :=
  ⟨u, rfl⟩

theorem responseJValueSet_eq_responseJValueSetMeanZero {d : ℕ} {U : Set (Vec d)}
    {p q : Vec d} {a : CoeffField d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    responseJValueSet U p q a = responseJValueSetMeanZero U p q a := by
  ext m
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u.toMeanZero, ?_⟩
    simp
  · rintro ⟨u, rfl⟩
    exact responseJValueSet_mem U p q a (u : AHarmonicFunction a U)

theorem responseJ_eq_sSup_responseJValueSetMeanZero {d : ℕ} {U : Set (Vec d)}
    {p q : Vec d} {a : CoeffField d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    ResponseJ U p q a = sSup (responseJValueSetMeanZero U p q a) := by
  rw [ResponseJ, responseJValueSet_eq_responseJValueSetMeanZero]

theorem responseJ_nonneg {d : ℕ} (U : Set (Vec d)) (p q : Vec d) (a : CoeffField d) :
    0 ≤ ResponseJ U p q a := by
  unfold ResponseJ
  exact Real.sSup_nonneg' ⟨0, responseJValueSet_zero_mem U p q a, le_rfl⟩

theorem responseJValueSet_smul_mem {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} {m : ℝ} (hm : m ∈ responseJValueSet U p q a) (c : ℝ) :
    c ^ 2 * m ∈ responseJValueSet U (c • p) (c • q) a := by
  rcases hm with ⟨u, rfl⟩
  refine ⟨c • u, ?_⟩
  exact (volumeAverage_scalarResponseIntegrand_smul U a c p q u).symm

theorem responseJValueSet_homogeneous {d : ℕ} (U : Set (Vec d)) (p q : Vec d)
    (a : CoeffField d) {c : ℝ} (hc : c ≠ 0) :
    responseJValueSet U (c • p) (c • q) a = (c ^ 2 : ℝ) • responseJValueSet U p q a := by
  ext m
  constructor
  · intro hm
    change ∃ y, y ∈ responseJValueSet U p q a ∧ (c ^ 2 : ℝ) * y = m
    have hm' :
        (c⁻¹ : ℝ) ^ 2 * m ∈ responseJValueSet U p q a := by
      simpa [smul_smul, hc, pow_two] using
        (responseJValueSet_smul_mem (p := c • p) (q := c • q) hm c⁻¹)
    refine ⟨(c⁻¹ : ℝ) ^ 2 * m, hm', ?_⟩
    field_simp [hc]
  · rintro ⟨m', hm', rfl⟩
    simpa [smul_eq_mul] using responseJValueSet_smul_mem hm' c

theorem responseJ_homogeneous {d : ℕ} (U : Set (Vec d)) (p q : Vec d)
    (a : CoeffField d) {c : ℝ} (hc : c ≠ 0) :
    ResponseJ U (c • p) (c • q) a = c ^ 2 * ResponseJ U p q a := by
  rw [ResponseJ, responseJValueSet_homogeneous U p q a hc]
  simpa [smul_eq_mul] using!
    (Real.sSup_smul_of_nonneg (show 0 ≤ (c ^ 2 : ℝ) by positivity) (responseJValueSet U p q a))

theorem responseJ_homogeneous_zero_left {d : ℕ} (U : Set (Vec d)) (q : Vec d)
    (a : CoeffField d) {c : ℝ} (hc : c ≠ 0) :
    ResponseJ U 0 (c • q) a = c ^ 2 * ResponseJ U 0 q a := by
  simpa using responseJ_homogeneous U 0 q a hc

theorem responseJ_homogeneous_zero_right {d : ℕ} (U : Set (Vec d)) (p : Vec d)
    (a : CoeffField d) {c : ℝ} (hc : c ≠ 0) :
    ResponseJ U (c • p) 0 a = c ^ 2 * ResponseJ U p 0 a := by
  simpa using responseJ_homogeneous U p 0 a hc

theorem scalarResponseIntegrand_rescaleCoeff_sq {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p q : Vec d) (c : ℝ) (hc : c ≠ 0) (u : AHarmonicFunction a U) :
    scalarResponseIntegrand U ((c ^ 2) • a) p q
        (((c⁻¹) • u).rescaleCoeff (c ^ 2)) =
      scalarResponseIntegrand U a (c • p) (c⁻¹ • q) u := by
  funext x
  change
    -((1 / 2 : ℝ) * vecDot ((c⁻¹) • u.toH1.grad x)
        (matVecMul (symmPart (((c ^ 2) • a) x)) ((c⁻¹) • u.toH1.grad x))) -
        vecDot p (matVecMul (((c ^ 2) • a) x) ((c⁻¹) • u.toH1.grad x)) +
      vecDot q ((c⁻¹) • u.toH1.grad x) =
    -((1 / 2 : ℝ) * vecDot (u.toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x))) -
        vecDot (c • p) (matVecMul (a x) (u.toH1.grad x)) +
      vecDot (c⁻¹ • q) (u.toH1.grad x)
  simp [Pi.smul_apply, symmPart_smul, smul_matVecMul, matVecMul_smul, vecDot_smul_left,
    vecDot_smul_right]
  field_simp [hc]

theorem scalarResponseIntegrand_unscaleCoeff_sq {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p q : Vec d) (c : ℝ) (hc : c ≠ 0) (u : AHarmonicFunction ((c ^ 2) • a) U) :
    scalarResponseIntegrand U ((c ^ 2) • a) p q u =
      scalarResponseIntegrand U a (c • p) (c⁻¹ • q)
        (c • (u.unscaleCoeff (c ^ 2) (pow_ne_zero 2 hc))) := by
  funext x
  change
    -((1 / 2 : ℝ) * vecDot (u.toH1.grad x)
        (matVecMul (symmPart (((c ^ 2) • a) x)) (u.toH1.grad x))) -
        vecDot p (matVecMul (((c ^ 2) • a) x) (u.toH1.grad x)) +
      vecDot q (u.toH1.grad x) =
    -((1 / 2 : ℝ) * vecDot (c • u.toH1.grad x)
        (matVecMul (symmPart (a x)) (c • u.toH1.grad x))) -
        vecDot (c • p) (matVecMul (a x) (c • u.toH1.grad x)) +
      vecDot (c⁻¹ • q) (c • u.toH1.grad x)
  simp [Pi.smul_apply, symmPart_smul, smul_matVecMul, matVecMul_smul, vecDot_smul_left,
    vecDot_smul_right, hc]
  ring_nf

theorem responseJValueSet_rescaleCoeff_sq_eq {d : ℕ} (U : Set (Vec d)) (p q : Vec d)
    (a : CoeffField d) (c : ℝ) (hc : c ≠ 0) :
    responseJValueSet U p q ((c ^ 2) • a) =
      responseJValueSet U (c • p) (c⁻¹ • q) a := by
  ext m
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨c • (u.unscaleCoeff (c ^ 2) (pow_ne_zero 2 hc)), ?_⟩
    exact congrArg (volumeAverage U) (scalarResponseIntegrand_unscaleCoeff_sq U a p q c hc u)
  · rintro ⟨u, rfl⟩
    refine ⟨((c⁻¹) • u).rescaleCoeff (c ^ 2), ?_⟩
    exact (congrArg (volumeAverage U) (scalarResponseIntegrand_rescaleCoeff_sq U a p q c hc u)).symm

theorem responseJ_homogeneous_coeffField_sq {d : ℕ} (U : Set (Vec d)) (p q : Vec d)
    (a : CoeffField d) (c : ℝ) (hc : c ≠ 0) :
    ResponseJ U p q ((c ^ 2) • a) = ResponseJ U (c • p) (c⁻¹ • q) a := by
  simp [ResponseJ, responseJValueSet_rescaleCoeff_sq_eq U p q a c hc]

theorem responseJ_homogeneous_coeffField {d : ℕ} (U : Set (Vec d)) (p q : Vec d)
    (a : CoeffField d) {lam : ℝ} (hlam : 0 < lam) :
    ResponseJ U p q (lam • a) = ResponseJ U (Real.sqrt lam • p) ((Real.sqrt lam)⁻¹ • q) a := by
  have hsqrt : Real.sqrt lam ≠ 0 := Real.sqrt_ne_zero'.mpr hlam
  simpa [Real.sq_sqrt (le_of_lt hlam)] using
    responseJ_homogeneous_coeffField_sq U p q a (Real.sqrt lam) hsqrt

theorem scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d) (u : AHarmonicFunction a U) :
    MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U :=
  (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).response p q u

theorem scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (p q : Vec d) (u : AHarmonicFunction a U) :
    ∀ x ∈ U,
      scalarResponseIntegrand U a p q u x ≤
        lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q) := by
  intro x hx
  let ξ : Vec d := u.toH1.grad x
  have hgrad_nonneg : 0 ≤ vecNormSq ξ := vecNormSq_nonneg ξ
  have hlam_pos : 0 < lam := (hEll.2 x hx).1
  have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
  have hlamInv_nonneg : 0 ≤ lam⁻¹ := by positivity
  have henergy :
      lam * vecNormSq ξ ≤ vecDot ξ (matVecMul (symmPart (a x)) ξ) :=
    lowerBound_symmPart_of_isEllipticMatrix (hEll.2 x hx) ξ
  have hpSq :
      vecDot p (matVecMul (a x) ξ) ^ 2 ≤ Lam ^ 2 * vecNormSq p * vecNormSq ξ := by
    have hcs :
        vecDot p (matVecMul (a x) ξ) ^ 2 ≤
          vecNormSq p * vecNormSq (matVecMul (a x) ξ) :=
      sq_vecDot_le_vecNormSq_mul_vecNormSq p (matVecMul (a x) ξ)
    have hnorm :
        vecNormSq (matVecMul (a x) ξ) ≤ Lam ^ 2 * vecNormSq ξ :=
      vecNormSq_matVecMul_le_of_isEllipticMatrix (hEll.2 x hx) ξ
    have hmul :
        vecNormSq p * vecNormSq (matVecMul (a x) ξ) ≤
          vecNormSq p * (Lam ^ 2 * vecNormSq ξ) := by
      exact mul_le_mul_of_nonneg_left hnorm (vecNormSq_nonneg p)
    exact le_trans hcs (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  have hpYoung :
      |vecDot p (matVecMul (a x) ξ)| ≤
        lam⁻¹ * Lam ^ 2 * vecNormSq p + (lam / 4 : ℝ) * vecNormSq ξ := by
    let A : ℝ := 2 * lam⁻¹ * Lam ^ 2 * vecNormSq p
    let B : ℝ := (lam / 2 : ℝ) * vecNormSq ξ
    have hAB_rhs : A / 2 + B / 2 =
        lam⁻¹ * Lam ^ 2 * vecNormSq p + (lam / 4 : ℝ) * vecNormSq ξ := by
      show (2 * lam⁻¹ * Lam ^ 2 * vecNormSq p) / 2 +
          ((lam / 2 : ℝ) * vecNormSq ξ) / 2 = _
      ring
    have hAB_eq : A * B = Lam ^ 2 * vecNormSq p * vecNormSq ξ := by
      show (2 * lam⁻¹ * Lam ^ 2 * vecNormSq p) * ((lam / 2 : ℝ) * vecNormSq ξ) =
        Lam ^ 2 * vecNormSq p * vecNormSq ξ
      field_simp [hlam_pos.ne']
    have hsq : vecDot p (matVecMul (a x) ξ) ^ 2 ≤ A * B := hpSq.trans_eq hAB_eq.symm
    have hA_nonneg : 0 ≤ A :=
      mul_nonneg (by positivity) (vecNormSq_nonneg p)
    have hB_nonneg : 0 ≤ B :=
      mul_nonneg (by positivity) hgrad_nonneg
    exact (young_abs_of_sq_le hsq hA_nonneg hB_nonneg).trans_eq hAB_rhs
  have hqSq :
      vecDot q ξ ^ 2 ≤ vecNormSq q * vecNormSq ξ :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq q ξ
  have hqYoung :
      |vecDot q ξ| ≤
        lam⁻¹ * vecNormSq q + (lam / 4 : ℝ) * vecNormSq ξ := by
    let A : ℝ := 2 * lam⁻¹ * vecNormSq q
    let B : ℝ := (lam / 2 : ℝ) * vecNormSq ξ
    have hAB_rhs : A / 2 + B / 2 =
        lam⁻¹ * vecNormSq q + (lam / 4 : ℝ) * vecNormSq ξ := by
      show (2 * lam⁻¹ * vecNormSq q) / 2 +
          ((lam / 2 : ℝ) * vecNormSq ξ) / 2 = _
      ring
    have hAB_eq : A * B = vecNormSq q * vecNormSq ξ := by
      show (2 * lam⁻¹ * vecNormSq q) * ((lam / 2 : ℝ) * vecNormSq ξ) =
        vecNormSq q * vecNormSq ξ
      field_simp [hlam_pos.ne']
    have hsq : vecDot q ξ ^ 2 ≤ A * B := hqSq.trans_eq hAB_eq.symm
    have hA_nonneg : 0 ≤ A :=
      mul_nonneg (by positivity) (vecNormSq_nonneg q)
    have hB_nonneg : 0 ≤ B :=
      mul_nonneg (by positivity) hgrad_nonneg
    exact (young_abs_of_sq_le hsq hA_nonneg hB_nonneg).trans_eq hAB_rhs
  have hpAbs :
      -vecDot p (matVecMul (a x) ξ) ≤
        lam⁻¹ * Lam ^ 2 * vecNormSq p + (lam / 4 : ℝ) * vecNormSq ξ := by
    calc
      -vecDot p (matVecMul (a x) ξ) ≤ |vecDot p (matVecMul (a x) ξ)| := by
        exact neg_le_abs _
      _ ≤ lam⁻¹ * Lam ^ 2 * vecNormSq p + (lam / 4 : ℝ) * vecNormSq ξ := hpYoung
  have hqAbs :
      vecDot q ξ ≤ lam⁻¹ * vecNormSq q + (lam / 4 : ℝ) * vecNormSq ξ := by
    calc
      vecDot q ξ ≤ |vecDot q ξ| := le_abs_self _
      _ ≤ lam⁻¹ * vecNormSq q + (lam / 4 : ℝ) * vecNormSq ξ := hqYoung
  unfold scalarResponseIntegrand
  nlinarith

theorem responseJValueSet_bddAbove_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q : Vec d) :
    BddAbove (responseJValueSet U p q a) := by
  refine ⟨lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q), ?_⟩
  rintro m ⟨u, rfl⟩
  refine volumeAverage_le_of_le_on (measurableSet_of_isEllipticFieldOn hEll)
    (scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u) hvol ?_
  exact scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn hEll p q u

theorem le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q : Vec d) {m : ℝ} (hm : m ∈ responseJValueSet U p q a) :
    m ≤ ResponseJ U p q a := by
  unfold ResponseJ
  exact le_csSup (responseJValueSet_bddAbove_of_isEllipticFieldOn hEll hvol p q) hm

theorem responseJValueSet_bddAbove_of_isResponseMaximizer {d : ℕ} (U : Set (Vec d))
    (p q : Vec d) (a : CoeffField d) {u : AHarmonicFunction a U}
    (hmax : IsResponseMaximizer U p q a u) :
    BddAbove (responseJValueSet U p q a) := by
  refine ⟨volumeAverage U (scalarResponseIntegrand U a p q u), ?_⟩
  rintro m ⟨w, rfl⟩
  exact hmax w

theorem responseJValueSet_isGreatest_of_isResponseMaximizer {d : ℕ} (U : Set (Vec d))
    (p q : Vec d) (a : CoeffField d) {u : AHarmonicFunction a U}
    (hmax : IsResponseMaximizer U p q a u) :
    IsGreatest (responseJValueSet U p q a)
      (volumeAverage U (scalarResponseIntegrand U a p q u)) := by
  refine ⟨responseJValueSet_mem U p q a u, ?_⟩
  intro m hm
  rcases hm with ⟨w, rfl⟩
  exact hmax w

theorem responseJ_eq_of_isResponseMaximizer {d : ℕ} (U : Set (Vec d)) (p q : Vec d)
    (a : CoeffField d) {u : AHarmonicFunction a U} (hmax : IsResponseMaximizer U p q a u) :
    ResponseJ U p q a = volumeAverage U (scalarResponseIntegrand U a p q u) := by
  simpa [ResponseJ] using
    (responseJValueSet_isGreatest_of_isResponseMaximizer U p q a hmax).csSup_eq

theorem responseJ_first_variation_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u) (w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0 := by
  exact basic_cg_identities_first_variation_of_isResponseMaximizer
    U a p q u hmax w hu_int hw_int hresp_u hlin henergy

theorem responseJ_second_variation_line_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u) (w : AHarmonicFunction a U) (t : ℝ)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U (scalarResponseIntegrand U a p q (scalarPerturbation u w t hu_int hw_int)) =
      ResponseJ U p q a - ((t ^ 2) / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  rw [responseJ_eq_of_isResponseMaximizer U p q a hmax]
  exact basic_cg_identities_second_variation_line_of_isResponseMaximizer
    U a p q u hmax w t hu_int hw_int hresp_u hlin henergy

theorem responseJ_second_variation_of_isResponseMaximizer {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (p q : Vec d) (u : AHarmonicFunction a U)
    (hmax : IsResponseMaximizer U p q a u) (w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u w) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) U) :
    volumeAverage U (scalarResponseIntegrand U a p q (scalarPerturbation u w 1 hu_int hw_int)) =
      ResponseJ U p q a - (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  rw [responseJ_eq_of_isResponseMaximizer U p q a hmax]
  exact basic_cg_identities_second_variation_of_isResponseMaximizer
    U a p q u hmax w hu_int hw_int hresp_u hlin henergy

theorem responseJ_energy_of_isResponseMaximizer {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p q : Vec d) (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p q a u)
    (hu_int : weakFluxIntegrable U a u)
    (hresp_u : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hlin_self : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand U a p q u u) U)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) U) :
    ResponseJ U p q a = (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a u) := by
  rw [responseJ_eq_of_isResponseMaximizer U p q a hmax]
  exact basic_cg_identities_energy_of_isResponseMaximizer
    U a p q u hmax hu_int hresp_u hlin_self henergy

theorem scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (w : AHarmonicFunction a U) :
    ∀ x ∈ U, 0 ≤ scalarVariationEnergyIntegrand a w x := by
  intro x hx
  unfold scalarVariationEnergyIntegrand
  rcases hEll with ⟨_, hEllPt⟩
  have hlower := lowerBound_symmPart_of_isEllipticMatrix (hEllPt x hx) (w.toH1.grad x)
  have hnorm_nonneg : 0 ≤ vecNormSq (w.toH1.grad x) := vecNormSq_nonneg (w.toH1.grad x)
  have hlam_nonneg : 0 ≤ lam := le_of_lt (hEllPt x hx).1
  nlinarith

theorem volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (w : AHarmonicFunction a U) :
    0 ≤ volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  apply volumeAverage_nonneg_of_nonneg_on
    (measurableSet_of_isEllipticFieldOn hEll)
  exact scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U a hEll w



end

end Homogenization
