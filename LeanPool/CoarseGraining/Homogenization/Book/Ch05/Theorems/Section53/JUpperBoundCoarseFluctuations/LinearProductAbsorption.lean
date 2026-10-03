/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Assembly
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.WeakNormInput

/-! # Linear Product Absorption -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# Linear/product absorption for the coarse-fluctuation RHS

This proof-internal file absorbs the first-lemma linear weak-norm terms and
cutoff-product Cauchy term into the special-vector centering term plus paired
weak-norm square expectations.
-/

noncomputable section

private theorem barSigmaStarAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaStarAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hInv : 0 < hP.barSigmaStarInvAtScale hStruct (m : ℤ) := by
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale] using
      Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
        hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct (m : ℤ))
        hBlock
  rw [hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (m : ℤ)]
  exact inv_pos.mpr hInv

private theorem barSigmaAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have htheta :=
    Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct (m : ℤ) hBlock
  have hstar_pos := barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hprod_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by
    exact lt_of_lt_of_le zero_lt_one (by
      simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale] using htheta)
  exact pos_of_mul_pos_left hprod_pos (inv_pos.mpr hstar_pos).le

private theorem sigmaHatAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ) :
    0 ≤ sigmaHatAtScale hP hStruct m := by
  exact Real.sqrt_nonneg _

private theorem sigmaHatAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < sigmaHatAtScale hP hStruct (m : ℤ) := by
  dsimp [sigmaHatAtScale]
  exact Real.sqrt_pos_of_pos
    (mul_pos (barSigmaAtScale_pos_of_P4 hP hStruct hP4 m)
      (barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m))

private theorem young_mul_le_eps_sq_add_inv_eps_sq
    {ε x y : ℝ} (hε : 0 < ε) :
    x * y ≤ ε * x ^ 2 / 2 + ε⁻¹ * y ^ 2 / 2 := by
  have hε_nonneg : 0 ≤ ε := hε.le
  have hε_inv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε_nonneg
  have htwo :=
    two_mul_le_add_sq (Real.sqrt ε * x) (Real.sqrt ε⁻¹ * y)
  have hsqrtε : (Real.sqrt ε) ^ 2 = ε := by
    simpa [pow_two] using Real.sq_sqrt hε_nonneg
  have hsqrti : (Real.sqrt ε⁻¹) ^ 2 = ε⁻¹ := by
    simpa [pow_two] using Real.sq_sqrt hε_inv_nonneg
  have hsqrt_mul : Real.sqrt ε * Real.sqrt ε⁻¹ = 1 := by
    rw [← Real.sqrt_mul hε_nonneg (ε⁻¹)]
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    field_simp [hε_ne]
    norm_num
  have hmain : 2 * x * y ≤ ε * x ^ 2 + ε⁻¹ * y ^ 2 := by
    calc
      2 * x * y =
          2 * (Real.sqrt ε * x) * (Real.sqrt ε⁻¹ * y) := by
            nlinarith [hsqrt_mul]
      _ ≤
          (Real.sqrt ε * x) ^ 2 + (Real.sqrt ε⁻¹ * y) ^ 2 := htwo
      _ =
          ε * x ^ 2 + ε⁻¹ * y ^ 2 := by
            nlinarith [hsqrtε, hsqrti]
  nlinarith

private theorem integral_le_sqrt_integral_sq_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {X : α → ℝ}
    (hX_sq : Integrable (fun x => (X x) ^ 2) μ)
    (hX_nonneg : 0 ≤ᵐ[μ] X) :
    ∫ x, X x ∂μ ≤ Real.sqrt (∫ x, (X x) ^ 2 ∂μ) := by
  have hY_sq : Integrable (fun _x : α => ((1 : ℝ) : ℝ) ^ 2) μ := by
    simp
  have hY_nonneg : 0 ≤ᵐ[μ] fun _x : α => (1 : ℝ) := by
    filter_upwards with _x
    norm_num
  have h :=
    JUpperBoundWeakNorms.integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      (μ := μ) (X := X) (Y := fun _x : α => (1 : ℝ))
      hX_sq hY_sq hX_nonneg hY_nonneg
  have hOne : Real.sqrt (∫ _x : α, ((1 : ℝ) : ℝ) ^ 2 ∂μ) = 1 := by
    simp
  calc
    ∫ x, X x ∂μ = ∫ x, X x * (1 : ℝ) ∂μ := by simp
    _ ≤ Real.sqrt (∫ x, (X x) ^ 2 ∂μ) *
        Real.sqrt (∫ _x : α, ((1 : ℝ) : ℝ) ^ 2 ∂μ) := h
    _ = Real.sqrt (∫ x, (X x) ^ 2 ∂μ) := by rw [hOne, mul_one]

private theorem norm_sq_le_vecNormSq {d : ℕ} (v : Vec d) :
    ‖v‖ ^ 2 ≤ vecNormSq v := by
  have hnorm_le : ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
    intro i
    have hi : ‖v i‖ ^ 2 ≤ vecNormSq v := by
      calc
        ‖v i‖ ^ 2 = v i ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        _ ≤ ∑ j, v j ^ 2 := by
          exact Finset.single_le_sum (fun j _hj => sq_nonneg (v j)) (Finset.mem_univ i)
        _ = vecNormSq v := by
          simp [vecNormSq, vecDot, pow_two]
    exact Real.le_sqrt_of_sq_le hi
  have hsqrt_sq : (Real.sqrt (vecNormSq v)) ^ 2 = vecNormSq v := by
    simpa [pow_two] using Real.sq_sqrt (vecNormSq_nonneg v)
  calc
    ‖v‖ ^ 2 ≤ (Real.sqrt (vecNormSq v)) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm_le
    _ = vecNormSq v := hsqrt_sq

private theorem sigmaHatAtScale_mul_norm_specialPCentering_sq_le_of_vecNormSq_eq_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    sigmaHatAtScale hP hStruct (m : ℤ) * ‖p0_e‖ ^ 2 ≤
      (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ 2 := by
  dsimp only
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  have hσ_nonneg : 0 ≤ σ := by
    exact sigmaHatAtScale_nonneg hP hStruct (m : ℤ)
  have hnorm := norm_sq_le_vecNormSq p0_e
  have hvec :=
    sigmaHatAtScale_mul_vecNormSq_specialPCentering_eq hP hStruct hP4 m e
  calc
    σ * ‖p0_e‖ ^ 2 ≤ σ * vecNormSq p0_e :=
      mul_le_mul_of_nonneg_left hnorm hσ_nonneg
    _ = (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ 2 := by
      simpa [p_e, q_e, p0_e, σ, he] using hvec

private theorem inv_sigmaHatAtScale_mul_norm_specialQCentering_sq_le_of_vecNormSq_eq_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ * ‖q0_e‖ ^ 2 ≤
      (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ 2 := by
  dsimp only
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  have hσ_nonneg : 0 ≤ σ := by
    exact sigmaHatAtScale_nonneg hP hStruct (m : ℤ)
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hnorm := norm_sq_le_vecNormSq q0_e
  have hvec :=
    inv_sigmaHatAtScale_mul_vecNormSq_specialQCentering_eq hP hStruct hP4 m e
  calc
    σ⁻¹ * ‖q0_e‖ ^ 2 ≤ σ⁻¹ * vecNormSq q0_e :=
      mul_le_mul_of_nonneg_left hnorm hσ_inv_nonneg
    _ = (Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1) ^ 2 := by
      simpa [p_e, q_e, q0_e, σ, he] using hvec

private theorem weighted_young_left_le
    {ε σ K u v G : ℝ} (hε : 0 < ε) (hσ : 0 < σ)
    (hv_sq : v ^ 2 ≤ G) :
    K * u * v ≤
      ε * (σ⁻¹ * u ^ 2) / 2 + ε⁻¹ * (K ^ 2 * σ * G) / 2 := by
  have hσ_nonneg : 0 ≤ σ := hσ.le
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hsqrt_inv_sq : (Real.sqrt (σ⁻¹)) ^ 2 = σ⁻¹ := by
    simpa [pow_two] using Real.sq_sqrt hσ_inv_nonneg
  have hsqrt_sq : (Real.sqrt σ) ^ 2 = σ := by
    simpa [pow_two] using Real.sq_sqrt hσ_nonneg
  have hsqrt_mul : Real.sqrt (σ⁻¹) * Real.sqrt σ = 1 := by
    rw [← Real.sqrt_mul hσ_inv_nonneg σ]
    have hσ_ne : σ ≠ 0 := ne_of_gt hσ
    field_simp [hσ_ne]
    norm_num
  have hy := young_mul_le_eps_sq_add_inv_eps_sq (ε := ε)
      (x := Real.sqrt (σ⁻¹) * u) (y := K * Real.sqrt σ * v) hε
  have hleft_eq :
      (Real.sqrt (σ⁻¹) * u) * (K * Real.sqrt σ * v) = K * u * v := by
    calc
      (Real.sqrt (σ⁻¹) * u) * (K * Real.sqrt σ * v)
          = (Real.sqrt (σ⁻¹) * Real.sqrt σ) * (K * u * v) := by ring
      _ = K * u * v := by rw [hsqrt_mul]; ring
  have hy2_le : (K * Real.sqrt σ * v) ^ 2 ≤ K ^ 2 * σ * G := by
    have hfactor_nonneg : 0 ≤ K ^ 2 * σ := mul_nonneg (sq_nonneg K) hσ_nonneg
    calc
      (K * Real.sqrt σ * v) ^ 2 = K ^ 2 * σ * v ^ 2 := by
        rw [mul_pow, mul_pow, hsqrt_sq]
      _ ≤ K ^ 2 * σ * G := by
        exact mul_le_mul_of_nonneg_left hv_sq hfactor_nonneg
  have hright_le :
      ε * (Real.sqrt (σ⁻¹) * u) ^ 2 / 2 +
          ε⁻¹ * (K * Real.sqrt σ * v) ^ 2 / 2 ≤
        ε * (σ⁻¹ * u ^ 2) / 2 + ε⁻¹ * (K ^ 2 * σ * G) / 2 := by
    have hfirst : (Real.sqrt (σ⁻¹) * u) ^ 2 = σ⁻¹ * u ^ 2 := by
      rw [mul_pow, hsqrt_inv_sq]
    rw [hfirst]
    gcongr
  calc
    K * u * v = (Real.sqrt (σ⁻¹) * u) * (K * Real.sqrt σ * v) := hleft_eq.symm
    _ ≤
        ε * (Real.sqrt (σ⁻¹) * u) ^ 2 / 2 +
          ε⁻¹ * (K * Real.sqrt σ * v) ^ 2 / 2 := hy
    _ ≤
        ε * (σ⁻¹ * u ^ 2) / 2 +
          ε⁻¹ * (K ^ 2 * σ * G) / 2 := hright_le

private theorem weighted_young_right_le
    {ε σ K u v F : ℝ} (hε : 0 < ε) (hσ : 0 < σ)
    (hv_sq : v ^ 2 ≤ F) :
    K * u * v ≤
      ε * (σ * u ^ 2) / 2 + ε⁻¹ * (K ^ 2 * σ⁻¹ * F) / 2 := by
  have hσ_inv_pos : 0 < σ⁻¹ := inv_pos.mpr hσ
  have h :=
    weighted_young_left_le (ε := ε) (σ := σ⁻¹) (K := K) (u := u)
      (v := v) (G := F) hε hσ_inv_pos hv_sq
  simpa [inv_inv] using h

private theorem product_sqrt_le_paired_squares
    {ε σ K G F : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1)
    (hσ : 0 < σ) (hK : 0 ≤ K) (hG : 0 ≤ G) (hF : 0 ≤ F) :
    K * (Real.sqrt G * Real.sqrt F) ≤
      ε⁻¹ * (K * (σ * G + σ⁻¹ * F) / 2) := by
  have hσ_nonneg : 0 ≤ σ := hσ.le
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hsqrtσ_sq : (Real.sqrt σ) ^ 2 = σ := by
    simpa [pow_two] using Real.sq_sqrt hσ_nonneg
  have hsqrti_sq : (Real.sqrt (σ⁻¹)) ^ 2 = σ⁻¹ := by
    simpa [pow_two] using Real.sq_sqrt hσ_inv_nonneg
  have hsqrt_mul : Real.sqrt σ * Real.sqrt (σ⁻¹) = 1 := by
    rw [← Real.sqrt_mul hσ_nonneg (σ⁻¹)]
    have hσ_ne : σ ≠ 0 := ne_of_gt hσ
    field_simp [hσ_ne]
    norm_num
  have hy := young_mul_le_eps_sq_add_inv_eps_sq (ε := (1 : ℝ))
      (x := Real.sqrt σ * Real.sqrt G)
      (y := Real.sqrt (σ⁻¹) * Real.sqrt F) (by norm_num)
  have hleft_eq :
      (Real.sqrt σ * Real.sqrt G) *
          (Real.sqrt (σ⁻¹) * Real.sqrt F) =
        Real.sqrt G * Real.sqrt F := by
    calc
      (Real.sqrt σ * Real.sqrt G) *
          (Real.sqrt (σ⁻¹) * Real.sqrt F)
          = (Real.sqrt σ * Real.sqrt (σ⁻¹)) *
              (Real.sqrt G * Real.sqrt F) := by ring
      _ = Real.sqrt G * Real.sqrt F := by rw [hsqrt_mul]; ring
  have hright_eq :
      (1 : ℝ) * (Real.sqrt σ * Real.sqrt G) ^ 2 / 2 +
          (1 : ℝ)⁻¹ * (Real.sqrt (σ⁻¹) * Real.sqrt F) ^ 2 / 2 =
        (σ * G + σ⁻¹ * F) / 2 := by
    rw [mul_pow, mul_pow, hsqrtσ_sq, hsqrti_sq, Real.sq_sqrt hG,
      Real.sq_sqrt hF]
    ring
  have hbase :
      Real.sqrt G * Real.sqrt F ≤ (σ * G + σ⁻¹ * F) / 2 := by
    rw [hleft_eq, hright_eq] at hy
    exact hy
  have hmul :
      K * (Real.sqrt G * Real.sqrt F) ≤
        K * ((σ * G + σ⁻¹ * F) / 2) :=
    mul_le_mul_of_nonneg_left hbase hK
  have htail_nonneg : 0 ≤ K * ((σ * G + σ⁻¹ * F) / 2) := by
    exact mul_nonneg hK
      (div_nonneg
        (add_nonneg (mul_nonneg hσ_nonneg hG)
          (mul_nonneg hσ_inv_nonneg hF))
        (by norm_num))
  have hε_inv_ge_one : 1 ≤ ε⁻¹ := by
    exact (one_le_inv₀ hε).2 hε_le
  calc
    K * (Real.sqrt G * Real.sqrt F) ≤
        K * ((σ * G + σ⁻¹ * F) / 2) := hmul
    _ = 1 * (K * (σ * G + σ⁻¹ * F) / 2) := by ring
    _ ≤ ε⁻¹ * (K * (σ * G + σ⁻¹ * F) / 2) :=
        mul_le_mul_of_nonneg_right hε_inv_ge_one
          (by simpa [div_eq_mul_inv, mul_assoc] using htail_nonneg)

private theorem linear_product_absorb_into_centering_and_pairedSquares
    {ε σ center G F Kg Kf Kp u v : ℝ}
    (hε : 0 < ε) (hε_le : ε ≤ 1) (hσ : 0 < σ)
    (hcenter : 0 ≤ center) (hG : 0 ≤ G) (hF : 0 ≤ F)
    (_hKg : 0 ≤ Kg) (_hKf : 0 ≤ Kf) (hKp : 0 ≤ Kp)
    (hu_center : σ * u ^ 2 ≤ center)
    (hv_center : σ⁻¹ * v ^ 2 ≤ center) :
    let C : ℝ := Kg ^ 2 + Kf ^ 2 + Kp + 2
    0 ≤ C ∧
      Kg * v * Real.sqrt G + Kf * u * Real.sqrt F +
          Kp * (Real.sqrt G * Real.sqrt F) ≤
        C * ε * center +
          C * ε⁻¹ * (σ * G + σ⁻¹ * F) := by
  let C : ℝ := Kg ^ 2 + Kf ^ 2 + Kp + 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    linarith [sq_nonneg Kg, sq_nonneg Kf, hKp]
  have hpaired_nonneg : 0 ≤ σ * G + σ⁻¹ * F := by
    exact add_nonneg (mul_nonneg hσ.le hG)
      (mul_nonneg (inv_nonneg.mpr hσ.le) hF)
  have hgrad :=
    weighted_young_left_le (ε := ε) (σ := σ) (K := Kg) (u := v)
      (v := Real.sqrt G) (G := G) hε hσ (by
        simpa [pow_two] using (Real.sq_sqrt hG).le)
  have hgrad' :
      Kg * v * Real.sqrt G ≤
        ε * center / 2 + ε⁻¹ * (Kg ^ 2 * (σ * G + σ⁻¹ * F)) / 2 := by
    have hfirst :
        ε * (σ⁻¹ * v ^ 2) / 2 ≤ ε * center / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv_center hε.le) (by norm_num)
    have hsecond :
        ε⁻¹ * (Kg ^ 2 * σ * G) / 2 ≤
          ε⁻¹ * (Kg ^ 2 * (σ * G + σ⁻¹ * F)) / 2 := by
      have hKG_nonneg : 0 ≤ Kg ^ 2 := sq_nonneg Kg
      have htail : Kg ^ 2 * σ * G ≤ Kg ^ 2 * (σ * G + σ⁻¹ * F) := by
        calc
          Kg ^ 2 * σ * G = Kg ^ 2 * (σ * G) := by ring
          _ ≤ Kg ^ 2 * (σ * G + σ⁻¹ * F) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hσ.le) hF))
              hKG_nonneg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hε.le)) (by norm_num)
    exact hgrad.trans (add_le_add hfirst hsecond)
  have hflux :=
    weighted_young_right_le (ε := ε) (σ := σ) (K := Kf) (u := u)
      (v := Real.sqrt F) (F := F) hε hσ (by
        simpa [pow_two] using (Real.sq_sqrt hF).le)
  have hflux' :
      Kf * u * Real.sqrt F ≤
        ε * center / 2 + ε⁻¹ * (Kf ^ 2 * (σ * G + σ⁻¹ * F)) / 2 := by
    have hfirst :
        ε * (σ * u ^ 2) / 2 ≤ ε * center / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu_center hε.le) (by norm_num)
    have hsecond :
        ε⁻¹ * (Kf ^ 2 * σ⁻¹ * F) / 2 ≤
          ε⁻¹ * (Kf ^ 2 * (σ * G + σ⁻¹ * F)) / 2 := by
      have hKF_nonneg : 0 ≤ Kf ^ 2 := sq_nonneg Kf
      have htail : Kf ^ 2 * σ⁻¹ * F ≤ Kf ^ 2 * (σ * G + σ⁻¹ * F) := by
        calc
          Kf ^ 2 * σ⁻¹ * F = Kf ^ 2 * (σ⁻¹ * F) := by ring
          _ ≤ Kf ^ 2 * (σ * G + σ⁻¹ * F) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left (mul_nonneg hσ.le hG))
              hKF_nonneg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hε.le)) (by norm_num)
    exact hflux.trans (add_le_add hfirst hsecond)
  have hproduct :
      Kp * (Real.sqrt G * Real.sqrt F) ≤
        ε⁻¹ * (Kp * (σ * G + σ⁻¹ * F) / 2) :=
    product_sqrt_le_paired_squares hε hε_le hσ hKp hG hF
  have hC_ge_grad : Kg ^ 2 / 2 ≤ C := by
    dsimp [C]
    linarith [sq_nonneg Kg, sq_nonneg Kf, hKp]
  have hC_ge_flux : Kf ^ 2 / 2 ≤ C := by
    dsimp [C]
    linarith [sq_nonneg Kg, sq_nonneg Kf, hKp]
  have hC_ge_prod : Kp / 2 ≤ C := by
    dsimp [C]
    linarith [sq_nonneg Kg, sq_nonneg Kf, hKp]
  refine ⟨hC_nonneg, ?_⟩
  calc
    Kg * v * Real.sqrt G + Kf * u * Real.sqrt F +
        Kp * (Real.sqrt G * Real.sqrt F)
        ≤
      (ε * center / 2 + ε⁻¹ * (Kg ^ 2 * (σ * G + σ⁻¹ * F)) / 2) +
        (ε * center / 2 + ε⁻¹ * (Kf ^ 2 * (σ * G + σ⁻¹ * F)) / 2) +
          ε⁻¹ * (Kp * (σ * G + σ⁻¹ * F) / 2) := by
        nlinarith [hgrad', hflux', hproduct]
    _ =
      ε * center +
        ε⁻¹ * ((Kg ^ 2 / 2 + Kf ^ 2 / 2 + Kp / 2) *
          (σ * G + σ⁻¹ * F)) := by ring
    _ ≤
      C * ε * center + C * ε⁻¹ * (σ * G + σ⁻¹ * F) := by
        have hεcenter_nonneg : 0 ≤ ε * center := mul_nonneg hε.le hcenter
        have hcoef_le : Kg ^ 2 / 2 + Kf ^ 2 / 2 + Kp / 2 ≤ C := by
          linarith [hC_ge_grad, hC_ge_flux, hC_ge_prod]
        have hleft1 : ε * center ≤ C * ε * center := by
          have hC_ge_one : 1 ≤ C := by
            dsimp [C]
            linarith [sq_nonneg Kg, sq_nonneg Kf, hKp]
          calc
            ε * center = 1 * (ε * center) := by ring
            _ ≤ C * (ε * center) :=
              mul_le_mul_of_nonneg_right hC_ge_one hεcenter_nonneg
            _ = C * ε * center := by ring
        have hleft2 :
            ε⁻¹ * ((Kg ^ 2 / 2 + Kf ^ 2 / 2 + Kp / 2) *
              (σ * G + σ⁻¹ * F)) ≤
              C * ε⁻¹ * (σ * G + σ⁻¹ * F) := by
          have hε_inv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
          calc
            ε⁻¹ * ((Kg ^ 2 / 2 + Kf ^ 2 / 2 + Kp / 2) *
                (σ * G + σ⁻¹ * F))
                =
              ((Kg ^ 2 / 2 + Kf ^ 2 / 2 + Kp / 2) *
                (ε⁻¹ * (σ * G + σ⁻¹ * F))) := by ring
            _ ≤ C * (ε⁻¹ * (σ * G + σ⁻¹ * F)) :=
              mul_le_mul_of_nonneg_right hcoef_le
                (mul_nonneg hε_inv_nonneg hpaired_nonneg)
            _ = C * ε⁻¹ * (σ * G + σ⁻¹ * F) := by ring
        exact add_le_add hleft1 hleft2

private theorem linear_integral_product_absorb
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gradWeak fluxWeak : Ω → ℝ}
    {gradCoeff fluxCoeff productCoeff Kgrad Kflux Kprod ε σ center u v : ℝ}
    (hε : 0 < ε) (hε_le : ε ≤ 1) (hσ_pos : 0 < σ) (hcenter_nonneg : 0 ≤ center)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hgrad_nonneg_ae : 0 ≤ᵐ[P] gradWeak) (hflux_nonneg_ae : 0 ≤ᵐ[P] fluxWeak)
    (hGradSq' : Integrable (fun a => (gradWeak a) ^ 2) P)
    (hFluxSq' : Integrable (fun a => (fluxWeak a) ^ 2) P)
    (hGradCoeff_nonneg : 0 ≤ gradCoeff) (hFluxCoeff_nonneg : 0 ≤ fluxCoeff)
    (hGradCoeff_le : gradCoeff ≤ 2 * Kgrad) (hFluxCoeff_le : fluxCoeff ≤ 2 * Kflux)
    (hProductCoeff_le : productCoeff ≤ Kprod)
    (hKgrad_nonneg : 0 ≤ Kgrad) (hKflux_nonneg : 0 ≤ Kflux) (hKprod_nonneg : 0 ≤ Kprod)
    (hp_center : σ * u ^ 2 ≤ center) (hq_center : σ⁻¹ * v ^ 2 ≤ center) :
    (1 / 2 : ℝ) * v * (gradCoeff * ∫ a, gradWeak a ∂P) +
      (1 / 2 : ℝ) * u * (fluxCoeff * ∫ a, fluxWeak a ∂P) +
      productCoeff * (Real.sqrt (∫ a, (gradWeak a) ^ 2 ∂P) *
        Real.sqrt (∫ a, (fluxWeak a) ^ 2 ∂P)) ≤
      (Kgrad ^ 2 + Kflux ^ 2 + Kprod + 2) * ε * center +
        (Kgrad ^ 2 + Kflux ^ 2 + Kprod + 2) * ε⁻¹ *
          (σ * (∫ a, (gradWeak a) ^ 2 ∂P) + σ⁻¹ * (∫ a, (fluxWeak a) ^ 2 ∂P)) := by
  let G := ∫ a, (gradWeak a) ^ 2 ∂P
  let F := ∫ a, (fluxWeak a) ^ 2 ∂P
  let C : ℝ := Kgrad ^ 2 + Kflux ^ 2 + Kprod + 2
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact integral_nonneg fun a => sq_nonneg _
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    exact integral_nonneg fun a => sq_nonneg _
  have hIntGrad_le : ∫ a, gradWeak a ∂P ≤ Real.sqrt G := by
    simpa [G] using
      integral_le_sqrt_integral_sq_of_ae_nonneg
        (μ := P) (X := gradWeak) hGradSq' hgrad_nonneg_ae
  have hIntFlux_le : ∫ a, fluxWeak a ∂P ≤ Real.sqrt F := by
    simpa [F] using
      integral_le_sqrt_integral_sq_of_ae_nonneg
        (μ := P) (X := fluxWeak) hFluxSq' hflux_nonneg_ae
  have hAbsorb_pair := linear_product_absorb_into_centering_and_pairedSquares
      (ε := ε) (σ := σ) (center := center)
      (G := G) (F := F) (Kg := Kgrad) (Kf := Kflux) (Kp := Kprod)
      (u := u) (v := v)
      hε hε_le hσ_pos hcenter_nonneg hG_nonneg hF_nonneg
      hKgrad_nonneg hKflux_nonneg hKprod_nonneg hp_center hq_center
  have hAbsorb := hAbsorb_pair.2
  have hGradTerm_le :
      (1 / 2 : ℝ) * v * (gradCoeff * ∫ a, gradWeak a ∂P) ≤
        Kgrad * v * Real.sqrt G := by
    have hint_nonneg : 0 ≤ ∫ a, gradWeak a ∂P :=
      integral_nonneg_of_ae hgrad_nonneg_ae
    have hsqrt_nonneg : 0 ≤ Real.sqrt G := Real.sqrt_nonneg _
    calc
      (1 / 2 : ℝ) * v * (gradCoeff * ∫ a, gradWeak a ∂P)
          = (gradCoeff / 2) * v * (∫ a, gradWeak a ∂P) := by ring
      _ ≤ (gradCoeff / 2) * v * Real.sqrt G := by
        gcongr
      _ ≤ Kgrad * v * Real.sqrt G := by
        have hhalf : gradCoeff / 2 ≤ Kgrad := by linarith [hGradCoeff_le]
        gcongr
  have hFluxTerm_le :
      (1 / 2 : ℝ) * u * (fluxCoeff * ∫ a, fluxWeak a ∂P) ≤
        Kflux * u * Real.sqrt F := by
    have hint_nonneg : 0 ≤ ∫ a, fluxWeak a ∂P :=
      integral_nonneg_of_ae hflux_nonneg_ae
    have hsqrt_nonneg : 0 ≤ Real.sqrt F := Real.sqrt_nonneg _
    calc
      (1 / 2 : ℝ) * u * (fluxCoeff * ∫ a, fluxWeak a ∂P)
          = (fluxCoeff / 2) * u * (∫ a, fluxWeak a ∂P) := by ring
      _ ≤ (fluxCoeff / 2) * u * Real.sqrt F := by
        gcongr
      _ ≤ Kflux * u * Real.sqrt F := by
        have hhalf : fluxCoeff / 2 ≤ Kflux := by linarith [hFluxCoeff_le]
        gcongr
  have hProductTerm_le :
      productCoeff * (Real.sqrt G * Real.sqrt F) ≤
        Kprod * (Real.sqrt G * Real.sqrt F) := by
    exact mul_le_mul_of_nonneg_right hProductCoeff_le
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    (1 / 2 : ℝ) * v * (gradCoeff * ∫ a, gradWeak a ∂P) +
        (1 / 2 : ℝ) * u * (fluxCoeff * ∫ a, fluxWeak a ∂P) +
          productCoeff * (Real.sqrt G * Real.sqrt F)
        ≤
      Kgrad * v * Real.sqrt G +
        Kflux * u * Real.sqrt F +
          Kprod * (Real.sqrt G * Real.sqrt F) :=
        add_le_add (add_le_add hGradTerm_le hFluxTerm_le) hProductTerm_le
    _ ≤
      C * ε * center +
        C * ε⁻¹ * (σ * G + σ⁻¹ * F) := hAbsorb

/-- The linear weak-norm terms and the cutoff-product Cauchy term in the first
Section 5.3 expected RHS are absorbed by the special-vector centering term and
the paired weak-norm square expectations. -/
theorem linearProductTerms_special_le_centering_add_pairedWeakNormSquares
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      ∀ {k m : ℕ}, k < m → ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      (let β := section53CoarseFluctuationBeta hP4
       let s := hP4.sLower + 2 * β
       let p_e := specialPAtScale hP hStruct (m : ℤ) e
       let q_e := specialQAtScale hP hStruct (m : ℤ) e
       let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
       Integrable
         (fun a : RegCoeffField d =>
           (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
               (originCube d (m : ℤ)) s p_e q_e p0_e a.toFun) ^ 2) P) →
      (let β := section53CoarseFluctuationBeta hP4
       let t := hP4.sUpper + 2 * β
       let p_e := specialPAtScale hP hStruct (m : ℤ) e
       let q_e := specialQAtScale hP hStruct (m : ℤ) e
       let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
       Integrable
         (fun a : RegCoeffField d =>
           (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
               (originCube d (m : ℤ)) t p_e q_e q0_e a.toFun) ^ 2) P) →
        let β := section53CoarseFluctuationBeta hP4
        let s := hP4.sLower + 2 * β
        let t := hP4.sUpper + 2 * β
        let Q : TriadicCube d := originCube d (m : ℤ)
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
        let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
        let σ := sigmaHatAtScale hP hStruct (m : ℤ)
        let θ := thetaAtScale hP hStruct (m : ℤ)
        let gradWeak : RegCoeffField d → ℝ := fun a =>
          Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e a.toFun
        let fluxWeak : RegCoeffField d → ℝ := fun a =>
          Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e a.toFun
        let gradCoeff :=
          (Fintype.card (Fin d) : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + s) *
              cubeBesovScaleWeight (-s) Q *
                JUpperBoundWeakNorms.section53CutoffDualBound Q s)
        let fluxCoeff :=
          (Fintype.card (Fin d) : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + t) *
              cubeBesovScaleWeight (-t) Q *
                JUpperBoundWeakNorms.section53CutoffDualBound Q t)
        let productCoeff :=
          JUpperBoundWeakNorms.section53CutoffProductCoeff Q s t
        let G := ∫ a, (gradWeak a) ^ 2 ∂P
        let F := ∫ a, (fluxWeak a) ^ 2 ∂P
        (1 / 2 : ℝ) * ‖q0_e‖ * (gradCoeff * ∫ a, gradWeak a ∂P) +
            (1 / 2 : ℝ) * ‖p0_e‖ * (fluxCoeff * ∫ a, fluxWeak a ∂P) +
              productCoeff * (Real.sqrt G * Real.sqrt F)
          ≤
            C * ε * (Real.sqrt θ - 1) ^ 2 +
              C * ε⁻¹ * (σ * G + σ⁻¹ * F) := by
  classical
  dsimp only
  let Kgrad : ℝ :=
    (d : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + 1) *
        ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) / 2
  let Kflux : ℝ :=
    (d : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + 1) *
        ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) / 2
  let KprodDim : ℝ :=
    (((128 * quantitativeCubeCutoffHessianConst d +
            24 * quantitativeCubeCutoffGradientConst d) * (2 : ℝ) ^ d) *
      (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
        ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1)))
  let Kprod : ℝ := max KprodDim 0
  let C : ℝ := Kgrad ^ 2 + Kflux ^ 2 + Kprod + 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, Kprod]
    linarith [sq_nonneg Kgrad, sq_nonneg Kflux, le_max_right KprodDim (0 : ℝ)]
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hStruct hP4 k m _hkm e he ε hε hε_le hGradSq hFluxSq
  let : IsProbabilityMeasure P := hP.isProbability
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let gradWeak : RegCoeffField d → ℝ := fun a =>
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e a.toFun
  let fluxWeak : RegCoeffField d → ℝ := fun a =>
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e a.toFun
  let gradCoeff :=
    (Fintype.card (Fin d) : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + s) *
        cubeBesovScaleWeight (-s) Q *
          JUpperBoundWeakNorms.section53CutoffDualBound Q s)
  let fluxCoeff :=
    (Fintype.card (Fin d) : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + t) *
        cubeBesovScaleWeight (-t) Q *
          JUpperBoundWeakNorms.section53CutoffDualBound Q t)
  let productCoeff :=
    JUpperBoundWeakNorms.section53CutoffProductCoeff Q s t
  let G := ∫ a, (gradWeak a) ^ 2 ∂P
  let F := ∫ a, (fluxWeak a) ^ 2 ∂P
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs_pos : 0 < s := by
    dsimp [s, β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht_pos : 0 < t := by
    dsimp [t, β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hs_nonneg : 0 ≤ s := hs_pos.le
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have hs_le : s ≤ 1 := by
    simpa [s, β] using sLower_add_two_beta_le_one hP4
  have ht_le : t ≤ 1 := by
    simpa [t, β] using sUpper_add_two_beta_le_one hP4
  have hst_nonneg : 0 ≤ s + t := add_nonneg hs_nonneg ht_nonneg
  have hσ_pos : 0 < σ := by
    simpa [σ] using sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hcenter_nonneg : 0 ≤ (Real.sqrt θ - 1) ^ 2 := sq_nonneg _
  have hgrad_nonneg_ae : 0 ≤ᵐ[P] gradWeak := by
    simpa [gradWeak, Q, s, p_e, q_e, p0_e] using
      JUpperBoundWeakNorms.canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae
        hP Q hs_pos p_e q_e p0_e
  have hflux_nonneg_ae : 0 ≤ᵐ[P] fluxWeak := by
    simpa [fluxWeak, Q, t, p_e, q_e, q0_e] using
      JUpperBoundWeakNorms.canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae
        hP Q ht_pos p_e q_e q0_e
  have hGradSq' : Integrable (fun a : RegCoeffField d => (gradWeak a) ^ 2) P := by
    simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using hGradSq
  have hFluxSq' : Integrable (fun a : RegCoeffField d => (fluxWeak a) ^ 2) P := by
    simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using hFluxSq
  have hGradCoeff_nonneg : 0 ≤ gradCoeff := by
    dsimp [gradCoeff]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
          (cubeBesovScaleWeight_nonneg (-s) Q))
        (JUpperBoundWeakNorms.section53CutoffDualBound_nonneg Q s))
  have hFluxCoeff_nonneg : 0 ≤ fluxCoeff := by
    dsimp [fluxCoeff]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
          (cubeBesovScaleWeight_nonneg (-t) Q))
        (JUpperBoundWeakNorms.section53CutoffDualBound_nonneg Q t))
  have hProductCoeff_nonneg : 0 ≤ productCoeff := by
    simpa [productCoeff, Q] using
      JUpperBoundWeakNorms.section53CutoffProductCoeff_nonneg Q s t
  have hGradCoeff_le : gradCoeff ≤ 2 * Kgrad := by
    have h :=
      JUpperBoundWeakNorms.section53_linearCutoffCoeff_le_dimensional
        Q hs_nonneg hs_le
    calc
      gradCoeff ≤
          (d : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + 1) *
              ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) := by
            simpa [gradCoeff, Q, s, mul_assoc] using h
      _ = 2 * Kgrad := by ring
  have hFluxCoeff_le : fluxCoeff ≤ 2 * Kflux := by
    have h :=
      JUpperBoundWeakNorms.section53_linearCutoffCoeff_le_dimensional
        Q ht_nonneg ht_le
    calc
      fluxCoeff ≤
          (d : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + 1) *
              ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) := by
            simpa [fluxCoeff, Q, t, mul_assoc] using h
      _ = 2 * Kflux := by ring
  have hKgrad_nonneg : 0 ≤ Kgrad := by
    linarith [hGradCoeff_le, hGradCoeff_nonneg]
  have hKflux_nonneg : 0 ≤ Kflux := by
    linarith [hFluxCoeff_le, hFluxCoeff_nonneg]
  have hProductCoeff_le_dim : productCoeff ≤ KprodDim := by
    simpa [productCoeff, KprodDim, Q, s, t] using
      JUpperBoundWeakNorms.section53CutoffProductCoeff_origin_le_dimensional
        (d := d) m hs_nonneg hst_nonneg
  have hProductCoeff_le : productCoeff ≤ Kprod :=
    hProductCoeff_le_dim.trans (le_max_left KprodDim (0 : ℝ))
  have hKprod_nonneg : 0 ≤ Kprod := le_max_right KprodDim (0 : ℝ)
  have hq_center :
      σ⁻¹ * ‖q0_e‖ ^ 2 ≤ (Real.sqrt θ - 1) ^ 2 := by
    simpa [σ, θ, p_e, q_e, q0_e] using
      inv_sigmaHatAtScale_mul_norm_specialQCentering_sq_le_of_vecNormSq_eq_one
        hP hStruct hP4 m e he
  have hp_center :
      σ * ‖p0_e‖ ^ 2 ≤ (Real.sqrt θ - 1) ^ 2 := by
    simpa [σ, θ, p_e, q_e, p0_e] using
      sigmaHatAtScale_mul_norm_specialPCentering_sq_le_of_vecNormSq_eq_one
        hP hStruct hP4 m e he
  exact linear_integral_product_absorb hε hε_le hσ_pos hcenter_nonneg
    (norm_nonneg _) (norm_nonneg _) hgrad_nonneg_ae hflux_nonneg_ae hGradSq' hFluxSq'
    hGradCoeff_nonneg hFluxCoeff_nonneg hGradCoeff_le hFluxCoeff_le hProductCoeff_le
    hKgrad_nonneg hKflux_nonneg hKprod_nonneg hp_center hq_center

/-- Almost-sure paired square version of the beta-shifted weak-norm maximizer
input.  This is kept pointwise so subsequent expectation estimates can expand
the RHS into separately integrable manuscript pieces. -/
theorem ae_paired_weakNormSquares_special_le_four_rhsSquares
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) :
    ∀ᵐ a ∂P,
      let β := section53CoarseFluctuationBeta hP4
      let s := hP4.sLower + 2 * β
      let s' := hP4.sLower + β
      let t := hP4.sUpper + 2 * β
      let t' := hP4.sUpper + β
      let Q : TriadicCube d := originCube d (m : ℤ)
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
      let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
      let σ := sigmaHatAtScale hP hStruct (m : ℤ)
      let gradWeak :=
        Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e a.toFun
      let fluxWeak :=
        Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e a.toFun
      let gradRHS :=
        WeakNormsMaximizer.gradientRHSAtScale
          (WeakNormsMaximizer.section53WeakNormMaximizerConst d)
          (m : ℤ) (k : ℤ) s s' p_e q_e p0_e a
      let fluxRHS :=
        WeakNormsMaximizer.fluxRHSAtScale
          (WeakNormsMaximizer.section53WeakNormMaximizerConst d)
          (m : ℤ) (k : ℤ) t t' p_e q_e q0_e a
      σ * gradWeak ^ 2 + σ⁻¹ * fluxWeak ^ 2 ≤
        4 * (σ * gradRHS ^ 2 + σ⁻¹ * fluxRHS ^ 2) := by
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  have hs_pos : 0 < s := by
    dsimp [s, β]
    linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4]
  have ht_pos : 0 < t := by
    dsimp [t, β]
    linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4]
  have hσ_nonneg : 0 ≤ σ := by
    exact sigmaHatAtScale_nonneg hP hStruct (m : ℤ)
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  filter_upwards
    [ae_specialWeakNormsMaximizer_homogenizationScale hP hStruct hP4 hkm e,
      JUpperBoundWeakNorms.canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae
        hP Q hs_pos p_e q_e p0_e,
      JUpperBoundWeakNorms.canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae
        hP Q ht_pos p_e q_e q0_e] with a hWeak hGradNonneg hFluxNonneg
  dsimp only at hWeak ⊢
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e a.toFun
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e a.toFun
  let gradRHS :=
    WeakNormsMaximizer.gradientRHSAtScale
      (WeakNormsMaximizer.section53WeakNormMaximizerConst d)
      (m : ℤ) (k : ℤ) s s' p_e q_e p0_e a
  let fluxRHS :=
    WeakNormsMaximizer.fluxRHSAtScale
      (WeakNormsMaximizer.section53WeakNormMaximizerConst d)
      (m : ℤ) (k : ℤ) t t' p_e q_e q0_e a
  have hGrad_le : gradWeak ≤ 2 * gradRHS := by
    simpa [gradWeak, gradRHS, Q, s, s', t, t', p_e, q_e, p0_e, q0_e, β] using
      hWeak.1
  have hFlux_le : fluxWeak ≤ 2 * fluxRHS := by
    simpa [fluxWeak, fluxRHS, Q, s, s', t, t', p_e, q_e, p0_e, q0_e, β] using
      hWeak.2
  have hGradRHS_nonneg : 0 ≤ 2 * gradRHS := hGradNonneg.trans hGrad_le
  have hFluxRHS_nonneg : 0 ≤ 2 * fluxRHS := hFluxNonneg.trans hFlux_le
  have hGradSq_le : gradWeak ^ 2 ≤ 4 * gradRHS ^ 2 := by
    have hsq := (sq_le_sq₀ hGradNonneg hGradRHS_nonneg).2 hGrad_le
    calc
      gradWeak ^ 2 ≤ (2 * gradRHS) ^ 2 := hsq
      _ = 4 * gradRHS ^ 2 := by ring
  have hFluxSq_le : fluxWeak ^ 2 ≤ 4 * fluxRHS ^ 2 := by
    have hsq := (sq_le_sq₀ hFluxNonneg hFluxRHS_nonneg).2 hFlux_le
    calc
      fluxWeak ^ 2 ≤ (2 * fluxRHS) ^ 2 := hsq
      _ = 4 * fluxRHS ^ 2 := by ring
  calc
    σ * gradWeak ^ 2 + σ⁻¹ * fluxWeak ^ 2
        ≤ σ * (4 * gradRHS ^ 2) + σ⁻¹ * (4 * fluxRHS ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hGradSq_le hσ_nonneg)
          (mul_le_mul_of_nonneg_left hFluxSq_le hσ_inv_nonneg)
    _ = 4 * (σ * gradRHS ^ 2 + σ⁻¹ * fluxRHS ^ 2) := by ring

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
