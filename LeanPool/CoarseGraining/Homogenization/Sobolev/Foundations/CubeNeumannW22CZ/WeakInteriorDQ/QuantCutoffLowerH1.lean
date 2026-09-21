/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotientH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Order.Filter.Finite

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.EnergyHalf

/-! # Quant Cutoff Lower H1 -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}

private theorem norm_basisVec {d : ℕ} (i : Fin d) :
    ‖basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases hji : j = i
    · subst hji
      simp [basisVec]
    · simp [basisVec, hji]
  · have hi : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

/-- Absorbed direct squared-cutoff Caccioppoli estimate for the forward
difference quotient.  This is the closed direct-test form: the only right-hand
side terms are the forcing and the usual cutoff-gradient error. -/
theorem directDifferenceQuotient_sqCutoff_energy_quarter_le_two_forcing_sq_add_three_error
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V)
    (hη_abs_le_one : ∀ x, |η x| ≤ 1) :
    (1 / 4 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (3 : ℝ) *
          ∫ x in V,
            (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let M : ℝ :=
    ∫ x in V,
      η x ^ 2 *
        vecNormSq
          ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
      ∂MeasureTheory.volume
  let Fsq : ℝ := ∫ x in U, f x ^ 2 ∂MeasureTheory.volume
  let Gsq : ℝ :=
    ∫ x in U,
      ((localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x i) ^ 2
      ∂MeasureTheory.volume
  let E : Vec d → ℝ :=
    fun x =>
      (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
        vecNormSq (euclideanGradient η x)
  let Eint : ℝ := ∫ x in V, E x ∂MeasureTheory.volume
  let E2int : ℝ :=
    ∫ x in V,
      2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
        vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume
  have hbase :=
    h.directDifferenceQuotient_sqCutoff_energy_half_le_two_forcing_sq_add_eighth_localizedSqCutoffForwardGradient_sq_add_error
      hU hf hV hVU hstep i hVshift hη hη_compact hη_sub
  have habsorb :=
    eighth_integral_sq_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_coord_le_quarter_energy_add_error
      (U := U) (V := V) u hV hVU step i hVshift
      hη hη_compact hη_sub hη_abs_le_one
  have hbase' :
      (1 / 2 : ℝ) * M ≤ (2 : ℝ) * Fsq + (1 / 8 : ℝ) * Gsq + E2int := by
    change
      (1 / 2 : ℝ) *
          ∫ x in V,
            η x ^ 2 *
              vecNormSq
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤
        (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
          (1 / 8 : ℝ) *
            ∫ x in U,
              ((localizedSqCutoffForwardDifferenceQuotientToAmbient
                (U := U) (V := V) u hV hVU step i hVshift
                hη hη_compact hη_sub).grad x i) ^ 2
              ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume
    exact hbase
  have habsorb' :
      (1 / 8 : ℝ) * Gsq ≤ (1 / 4 : ℝ) * M + Eint := by
    change
      (1 / 8 : ℝ) *
          ∫ x in U,
            ((localizedSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x i) ^ 2
            ∂MeasureTheory.volume ≤
        (1 / 4 : ℝ) *
          ∫ x in V,
            η x ^ 2 *
              vecNormSq
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume +
          ∫ x in V,
            (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume
    exact habsorb
  have hquarter :
      (1 / 4 : ℝ) * M ≤ (2 : ℝ) * Fsq + Eint + E2int := by
    linarith
  have hE2_eq : E2int = (2 : ℝ) * Eint := by
    calc
      E2int =
          ∫ x in V, (2 : ℝ) * E x ∂MeasureTheory.volume := by
            change
              (∫ x in V,
                2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
                  vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume) =
                ∫ x in V, (2 : ℝ) * E x ∂MeasureTheory.volume
            congr with x
            simp [E]
            ring
      _ = (2 : ℝ) * ∫ x in V, E x ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      _ = (2 : ℝ) * Eint := rfl
  have hE_sum : Eint + E2int = (3 : ℝ) * Eint := by
    rw [hE2_eq]
    ring
  have htarget : (1 / 4 : ℝ) * M ≤ (2 : ℝ) * Fsq + (3 : ℝ) * Eint := by
    linarith
  change (1 / 4 : ℝ) * M ≤ (2 : ℝ) * Fsq + (3 : ℝ) * Eint
  exact htarget

/-- Quantitative cube cutoffs are bounded by one in absolute value. -/
theorem quantitativeCubeCutoff_abs_le_one {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) (x : Vec d) :
    |η x| ≤ 1 :=
  abs_le.mpr ⟨by linarith [η.nonneg x], η.le_one x⟩

/-- The squared Euclidean-gradient vector is controlled by the operator norm
of the Fréchet derivative, with the explicit finite-dimensional coordinate
factor. -/
theorem vecNormSq_euclideanGradient_le_card_mul_fderiv_norm_sq
    (η : Vec d → ℝ) (x : Vec d) :
    vecNormSq (euclideanGradient η x) ≤ (d : ℝ) * ‖fderiv ℝ η x‖ ^ 2 := by
  have hcoord :
      ∀ i : Fin d, (euclideanGradient η x i) ^ 2 ≤ ‖fderiv ℝ η x‖ ^ 2 := by
    intro i
    have habs :
        |euclideanGradient η x i| ≤ ‖fderiv ℝ η x‖ := by
      calc
        |euclideanGradient η x i| =
            ‖(fderiv ℝ η x) (basisVec i)‖ := by
              simp [euclideanGradient, euclideanCoordDeriv, Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ η x‖ * ‖basisVec i‖ := by
              simpa using (fderiv ℝ η x).le_opNorm (basisVec i)
        _ = ‖fderiv ℝ η x‖ := by
              rw [norm_basisVec, mul_one]
    have habs_nonneg : 0 ≤ |euclideanGradient η x i| := abs_nonneg _
    have hnorm_nonneg : 0 ≤ ‖fderiv ℝ η x‖ := norm_nonneg _
    have habs_sq : |euclideanGradient η x i| ^ 2 =
        (euclideanGradient η x i) ^ 2 := sq_abs _
    exact (habs_sq ▸ (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 habs)
  calc
    vecNormSq (euclideanGradient η x) =
        ∑ i : Fin d, (euclideanGradient η x i) ^ 2 := by
          simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ _i : Fin d, ‖fderiv ℝ η x‖ ^ 2 := by
          exact Finset.sum_le_sum fun i _hi => hcoord i
    _ = (d : ℝ) * ‖fderiv ℝ η x‖ ^ 2 := by
          simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Pointwise gradient-error bound for a quantitative cube cutoff. -/
theorem vecNormSq_euclideanGradient_quantitativeCubeCutoff_le
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) (x : Vec d) :
    vecNormSq (euclideanGradient (η : Vec d → ℝ) x) ≤
      (d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2 := by
  let K : ℝ :=
    quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q)
  have hbase :=
    vecNormSq_euclideanGradient_le_card_mul_fderiv_norm_sq
      (η := (η : Vec d → ℝ)) x
  have hgrad : ‖fderiv ℝ (η : Vec d → ℝ) x‖ ≤ K := by
    simpa [K] using η.gradient_bound x
  have hK_nonneg : 0 ≤ K := le_trans (norm_nonneg _) hgrad
  have hgrad_sq : ‖fderiv ℝ (η : Vec d → ℝ) x‖ ^ 2 ≤ K ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hK_nonneg).2 hgrad
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  calc
    vecNormSq (euclideanGradient (η : Vec d → ℝ) x)
        ≤ (d : ℝ) * ‖fderiv ℝ (η : Vec d → ℝ) x‖ ^ 2 := hbase
    _ ≤ (d : ℝ) * K ^ 2 := by
          exact mul_le_mul_of_nonneg_left hgrad_sq hd_nonneg
    _ =
        (d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2 := rfl

/-- Integral form of the quantitative cube cutoff gradient-error bound. -/
theorem integral_sq_mul_vecNormSq_euclideanGradient_quantitativeCubeCutoff_le
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {V : Set (Vec d)} {w : Vec d → ℝ} (hw : MemScalarL2 V w) :
    ∫ x in V, w x ^ 2 * vecNormSq (euclideanGradient (η : Vec d → ℝ) x)
        ∂MeasureTheory.volume ≤
      ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2) *
        ∫ x in V, w x ^ 2 ∂MeasureTheory.volume := by
  let K : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2
  have hleft_int :
      MeasureTheory.IntegrableOn
        (fun x => w x ^ 2 * vecNormSq (euclideanGradient (η : Vec d → ℝ) x)) V := by
    have htwo :=
      integrableOn_two_mul_sq_mul_vecNormSq_euclideanGradient_of_memScalarL2
        (V := V) (w := w) (η := (η : Vec d → ℝ))
        hw η.smooth η.hasCompactSupport
    have hhalf := htwo.const_mul (1 / 2 : ℝ)
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hhalf
  have hsq_int : MeasureTheory.IntegrableOn (fun x => w x ^ 2) V := by
    simpa [volumeMeasureOn] using! hw.integrable_sq
  have hright_int :
      MeasureTheory.IntegrableOn (fun x => K * w x ^ 2) V :=
    hsq_int.const_mul K
  have hpoint :
      (fun x => w x ^ 2 * vecNormSq (euclideanGradient (η : Vec d → ℝ) x))
        ≤ᵐ[MeasureTheory.volume.restrict V]
      fun x => K * w x ^ 2 := by
    filter_upwards with x
    have hgrad := vecNormSq_euclideanGradient_quantitativeCubeCutoff_le η x
    have hw_nonneg : 0 ≤ w x ^ 2 := sq_nonneg _
    calc
      w x ^ 2 * vecNormSq (euclideanGradient (η : Vec d → ℝ) x)
          ≤ w x ^ 2 * K := by
            exact mul_le_mul_of_nonneg_left hgrad hw_nonneg
      _ = K * w x ^ 2 := by ring
  have hmono :=
    MeasureTheory.integral_mono_ae hleft_int hright_int hpoint
  have hright_eq :
      ∫ x in V, K * w x ^ 2 ∂MeasureTheory.volume =
        K * ∫ x in V, w x ^ 2 ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  rw [hright_eq] at hmono
  simpa [K] using hmono

/-- Direct Caccioppoli estimate specialized to a quantitative cube cutoff:
the cutoff-gradient error is bounded by the explicit inverse-gap squared
constant times the unweighted forward quotient square. -/
theorem directDifferenceQuotient_quantitativeCubeCutoff_energy_quarter_le_forcing_sq_add_quotient_sq
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V) :
    (1 / 4 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2) *
          ∫ x in V,
            (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
            ∂MeasureTheory.volume := by
  let w : Vec d → ℝ := euclideanForwardDifferenceQuotient step i u.toFun
  let K : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2
  have hbase :=
    h.directDifferenceQuotient_sqCutoff_energy_quarter_le_two_forcing_sq_add_three_error
      hU hf hV hVU hstep i hVshift
      (η := (η : Vec d → ℝ)) η.smooth η.hasCompactSupport hη_sub
      (quantitativeCubeCutoff_abs_le_one η)
  have hw : MemScalarL2 V w := by
    refine MeasureTheory.MemLp.ae_eq ?_
      (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).memL2
    filter_upwards with x
    simp [w]
  have herr :=
    integral_sq_mul_vecNormSq_euclideanGradient_quantitativeCubeCutoff_le
      (η := η) (V := V) (w := w) hw
  have herr3 : (3 : ℝ) *
      ∫ x in V, w x ^ 2 * vecNormSq (euclideanGradient (η : Vec d → ℝ) x)
          ∂MeasureTheory.volume ≤
        (3 : ℝ) * (K * ∫ x in V, w x ^ 2 ∂MeasureTheory.volume) := by
    exact mul_le_mul_of_nonneg_left (by simpa [K] using herr) (by norm_num)
  have htarget :
      (1 / 4 : ℝ) *
          ∫ x in V,
            η x ^ 2 *
              vecNormSq
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤
        (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
          (3 : ℝ) * (K * ∫ x in V, w x ^ 2 ∂MeasureTheory.volume) := by
    exact hbase.trans
      (add_le_add_right herr3
        ((2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume))
  simpa [w, K, mul_assoc] using htarget

/-- If a cutoff is identically one on an inner measurable set, then its
weighted energy over the ambient set controls the unweighted energy on the
inner set. -/
theorem integral_vecNormSq_le_integral_sqCutoff_vecNormSq_of_subset_eq_one
    {S V : Set (Vec d)} {G : Vec d → Vec d} {η : Vec d → ℝ}
    (hS_meas : MeasurableSet S) (hSV : S ⊆ V)
    (hη_one : ∀ x ∈ S, η x = 1) (hG : MemVectorL2 V G)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η) :
    ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume ≤
      ∫ x in V, η x ^ 2 * vecNormSq (G x) ∂MeasureTheory.volume := by
  have hleft_eq :
      ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume =
        ∫ x in S, η x ^ 2 * vecNormSq (G x) ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hS_meas] with x hx
    rw [hη_one x hx]
    ring
  have hright_int :
      MeasureTheory.IntegrableOn
        (fun x => η x ^ 2 * vecNormSq (G x)) V :=
    integrableOn_sq_cutoff_vecNormSq_of_memVectorL2
      (V := V) (G := G) (η := η) hG hη hη_compact
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict V]
        fun x => η x ^ 2 * vecNormSq (G x) := by
    filter_upwards with x
    exact mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
  have hsubset_ae :
      S ≤ᵐ[MeasureTheory.volume] V :=
    Filter.Eventually.of_forall fun _ hx => hSV hx
  have hmono :=
    MeasureTheory.setIntegral_mono_set hright_int hnonneg hsubset_ae
  rw [hleft_eq]
  exact hmono

/-- Quantitative-cube Caccioppoli estimate with the left side localized to
any measurable inner set on which the cutoff is identically one. -/
theorem directDifferenceQuotient_quantitativeCubeCutoff_inner_energy_quarter_le_forcing_sq_add_quotient_sq
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    {S : Set (Vec d)} (hS_meas : MeasurableSet S) (hSV : S ⊆ V)
    (hη_one : ∀ x ∈ S, (η : Vec d → ℝ) x = 1) :
    (1 / 4 : ℝ) *
        ∫ x in S,
          vecNormSq
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2) *
          ∫ x in V,
            (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
            ∂MeasureTheory.volume := by
  let G : Vec d → Vec d :=
    fun x => (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x
  have hinner_le :
      ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume ≤
        ∫ x in V, η x ^ 2 * vecNormSq (G x) ∂MeasureTheory.volume :=
    integral_vecNormSq_le_integral_sqCutoff_vecNormSq_of_subset_eq_one
      (S := S) (V := V) (G := G) (η := (η : Vec d → ℝ))
      hS_meas hSV hη_one
      (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2
      η.smooth η.hasCompactSupport
  have hweighted :=
    h.directDifferenceQuotient_quantitativeCubeCutoff_energy_quarter_le_forcing_sq_add_quotient_sq
      hU hf hV hVU hstep i hVshift η hη_sub
  have hinner_quarter :
      (1 / 4 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume ≤
        (1 / 4 : ℝ) *
          ∫ x in V, η x ^ 2 * vecNormSq (G x) ∂MeasureTheory.volume := by
    exact mul_le_mul_of_nonneg_left hinner_le (by norm_num)
  have htarget :
      (1 / 4 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2) *
          ∫ x in V,
            (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
            ∂MeasureTheory.volume := by
    exact hinner_quarter.trans (by
      change
        (1 / 4 : ℝ) *
            ∫ x in V, η x ^ 2 * vecNormSq (G x) ∂MeasureTheory.volume ≤
          (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (3 : ℝ) *
              ((d : ℝ) *
                (quantitativeCubeCutoffGradientConst d /
                  ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2) *
              ∫ x in V,
                (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
                ∂MeasureTheory.volume
      exact hweighted)
  change
    (1 / 4 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2) *
          ∫ x in V,
            (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
            ∂MeasureTheory.volume
  exact htarget

/-- Nested-cube version of the quantitative direct Caccioppoli estimate:
the inner energy is taken over `scaledClosedCubeSet Q ρ₁`, where the
quantitative cutoff is exactly one. -/
theorem directDifferenceQuotient_quantitativeCubeCutoff_innerCube_energy_quarter_le_forcing_sq_add_quotient_sq
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V) :
    (1 / 4 : ℝ) *
        ∫ x in scaledClosedCubeSet Q ρ₁,
          vecNormSq
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2) *
          ∫ x in V,
            (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
            ∂MeasureTheory.volume := by
  exact
    h.directDifferenceQuotient_quantitativeCubeCutoff_inner_energy_quarter_le_forcing_sq_add_quotient_sq
      hU hf hV hVU hstep i hVshift η hη_sub
      (isClosed_scaledClosedCubeSet Q ρ₁).measurableSet hinnerV
      (by
        intro x hx
        exact η.eq_one_on_inner x hx)

/-- Test a restricted weak Poisson equation against a smooth cutoff times a
forward coordinate difference quotient of the solution. -/
theorem restrict_test_cutoffForwardDifferenceQuotientToH10
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        vecDot ((u.restrict hV.isOpen hVU).grad x)
          ((u.cutoffForwardDifferenceQuotientToH10 step i hV hVU hVshift
            hφ hφ_compact hφ_sub).toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in V,
        f x * (φ x * euclideanForwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  have htest :=
    (h.restrict hV.isOpen hVU).h10 hV.isOpen hfV
      (u.cutoffForwardDifferenceQuotientToH10 step i hV hVU hVshift
        hφ hφ_compact hφ_sub)
  simpa using htest

/-- Test a restricted weak Poisson equation against a smooth cutoff times a
backward coordinate difference quotient of the solution. -/
theorem restrict_test_cutoffBackwardDifferenceQuotientToH10
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        vecDot ((u.restrict hV.isOpen hVU).grad x)
          ((u.cutoffBackwardDifferenceQuotientToH10 step i hV hVU hVshift
            hφ hφ_compact hφ_sub).toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in V,
        f x * (φ x * euclideanBackwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  have htest :=
    (h.restrict hV.isOpen hVU).h10 hV.isOpen hfV
      (u.cutoffBackwardDifferenceQuotientToH10 step i hV hVU hVshift
        hφ hφ_compact hφ_sub)
  simpa using htest

/-- Test a weak Poisson equation against a smooth cutoff times the solution. -/
theorem test_mulContDiffHasCompactSupportToH10
    (h : WeakPoissonEquationOn U u f)
    (hU : IsOpenBoundedConvexDomain U) (hf : MemScalarL2 U f)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    ∫ x in U,
        vecDot (u.grad x)
          ((u.mulContDiffHasCompactSupportToH10 hU
            hφ hφ_compact hφ_sub).toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, f x * (φ x * u.toFun x) ∂MeasureTheory.volume := by
  have htest :=
    h.h10 hU.isOpen hf
      (u.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub)
  simpa using htest

/-- Coordinatewise gradient identification for the chosen `H¹₀` representative
of a smooth cutoff times an `H¹` function. -/
theorem mulContDiffHasCompactSupportToH10_grad_coord_ae
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U)
    (j : Fin d) :
    (fun x =>
        (u.mulContDiffHasCompactSupportToH10 hU
          hφ hφ_compact hφ_sub).toH1Function.grad x j) =ᵐ[
          MeasureTheory.volume.restrict U]
      fun x => φ x * u.grad x j + u x * (fderiv ℝ φ x) (basisVec j) := by
  let ψ : H10Function U :=
    u.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub
  let uφ : H1Function U := u.mulContDiffHasCompactSupport hφ hφ_compact
  have hψ_fun : ψ.toH1Function.toFun = uφ.toFun := by
    funext x
    simp [ψ, uφ]
  have hψ_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => ψ.toH1Function.grad x j) U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((ψ.toH1Function.gradMemL2 j).locallyIntegrable (by norm_num))
  have huφ_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => uφ.grad x j) U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((uφ.gradMemL2 j).locallyIntegrable (by norm_num))
  have hψ_weak :
      HasWeakPartialDerivOn U j ψ.toH1Function.toFun
        (fun x => ψ.toH1Function.grad x j) :=
    ψ.toH1Function.hasWeakPartialDerivOn j
  have huφ_weak :
      HasWeakPartialDerivOn U j ψ.toH1Function.toFun
        (fun x => uφ.grad x j) := by
    rw [hψ_fun]
    exact uφ.hasWeakPartialDerivOn j
  have hae :=
    HasWeakPartialDerivOn.ae_eq hU.isOpen hψ_loc huφ_loc hψ_weak huφ_weak
  simpa [ψ, uφ, H1Function.mulContDiffHasCompactSupport_grad] using hae

/-- Vector-valued a.e. gradient identification for a smooth cutoff times an
`H¹` function, packaged as the chosen `H¹₀` representative. -/
theorem mulContDiffHasCompactSupportToH10_grad_ae
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    (fun x =>
        (u.mulContDiffHasCompactSupportToH10 hU
          hφ hφ_compact hφ_sub).toH1Function.grad x) =ᵐ[
          MeasureTheory.volume.restrict U]
      fun x j => φ x * u.grad x j + u x * (fderiv ℝ φ x) (basisVec j) := by
  have hcoord :
      ∀ j : Fin d,
        (fun x =>
            (u.mulContDiffHasCompactSupportToH10 hU
              hφ hφ_compact hφ_sub).toH1Function.grad x j) =ᵐ[
              MeasureTheory.volume.restrict U]
          fun x => φ x * u.grad x j + u x * (fderiv ℝ φ x) (basisVec j) := by
    intro j
    exact mulContDiffHasCompactSupportToH10_grad_coord_ae
      u hU hφ hφ_compact hφ_sub j
  filter_upwards [(Filter.eventually_all (l := MeasureTheory.ae (MeasureTheory.volume.restrict U))).2 hcoord] with x hx
  ext j
  exact hx j

/-- Coordinate energy of the chosen H10 product representative, rewritten by
the explicit product-rule gradient. -/
theorem integral_localized_h10_grad_sq_eq_integral_product_rule_grad_sq
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U)
    (i : Fin d) :
    ∫ x in U,
        ((u.mulContDiffHasCompactSupportToH10 hU
          hφ hφ_compact hφ_sub).toH1Function.grad x i) ^ 2
        ∂MeasureTheory.volume =
      ∫ x in U,
        (φ x * u.grad x i + u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2
        ∂MeasureTheory.volume := by
  have hgrad_ae :=
    mulContDiffHasCompactSupportToH10_grad_coord_ae
      u hU hφ hφ_compact hφ_sub i
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hgrad_ae] with x hx
  rw [hx]

/-- Fully expanded lower-order quotient control for a cutoff-localized H¹
function. -/
theorem integral_set_forwardDifferenceQuotient_sq_le_integral_localized_product_rule_grad_sq
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U)
    {S : Set (Vec d)} (hS_meas : MeasurableSet S)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hφ_one : ∀ x ∈ S, φ x = 1)
    (hφ_shift_one : ∀ x ∈ S, φ (euclideanCoordShift step i x) = 1) :
    ∫ x in S, (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
        ∂MeasureTheory.volume ≤
      ∫ x in U,
        (φ x * u.grad x i + u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2
        ∂MeasureTheory.volume := by
  have hbase :=
    integral_set_forwardDifferenceQuotient_sq_le_integral_localized_h10_grad_sq
      (U := U) u hU hφ hφ_compact hφ_sub hS_meas hstep i
      hφ_one hφ_shift_one
  rwa [integral_localized_h10_grad_sq_eq_integral_product_rule_grad_sq
    (U := U) u hU hφ hφ_compact hφ_sub i] at hbase

/-- The product-rule square is controlled by the two usual square terms. -/
theorem integral_product_rule_grad_sq_le_two_integral_cutoff_grad_sq_add_two_integral_value_fderiv_sq
    (u : H1Function U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (i : Fin d) :
    ∫ x in U,
        (φ x * u.grad x i + u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2
        ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, (φ x * u.grad x i) ^ 2 ∂MeasureTheory.volume +
        (2 : ℝ) *
          ∫ x in U, (u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2
            ∂MeasureTheory.volume := by
  have hφ_top : MeasureTheory.MemLp φ ⊤ (volumeMeasureOn U) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hφ_compact (volumeMeasureOn U)
  have hφgrad : MeasureTheory.MemLp (fun x => φ x * u.grad x i) 2
      (volumeMeasureOn U) := by
    simpa [MemScalarL2, volumeMeasureOn, mul_comm] using
      (u.gradMemL2 i).mul' hφ_top
  have hdφ_top : MeasureTheory.MemLp
      (fun x => (fderiv ℝ φ x) (basisVec i)) ⊤ (volumeMeasureOn U) := by
    simpa [euclideanCoordDeriv, volumeMeasureOn] using!
      (contDiff_euclideanCoordDeriv hφ i).continuous.memLp_top_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordDeriv hφ_compact i) (volumeMeasureOn U)
  have hudφ : MeasureTheory.MemLp
      (fun x => u.toFun x * (fderiv ℝ φ x) (basisVec i)) 2
      (volumeMeasureOn U) := by
    simpa [MemScalarL2, volumeMeasureOn, mul_comm, mul_left_comm] using
      u.memL2.mul' hdφ_top
  have hleft_int : MeasureTheory.IntegrableOn
      (fun x =>
        (φ x * u.grad x i + u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2) U := by
    have hsum : MeasureTheory.MemLp
        (fun x => φ x * u.grad x i + u.toFun x * (fderiv ℝ φ x) (basisVec i))
        2 (volumeMeasureOn U) :=
      hφgrad.add hudφ
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using hsum.integrable_sq
  have hterm1_int : MeasureTheory.IntegrableOn
      (fun x => 2 * (φ x * u.grad x i) ^ 2) U := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      hφgrad.integrable_sq.const_mul (2 : ℝ)
  have hterm2_int : MeasureTheory.IntegrableOn
      (fun x => 2 * (u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2) U := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      hudφ.integrable_sq.const_mul (2 : ℝ)
  have hright_int : MeasureTheory.IntegrableOn
      (fun x => 2 * (φ x * u.grad x i) ^ 2 +
        2 * (u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2) U :=
    hterm1_int.add hterm2_int
  have hpoint :
      (fun x =>
        (φ x * u.grad x i + u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict U]
      fun x => 2 * (φ x * u.grad x i) ^ 2 +
        2 * (u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2 := by
    filter_upwards with x
    nlinarith [sq_nonneg
      (φ x * u.grad x i - u.toFun x * (fderiv ℝ φ x) (basisVec i))]
  have hmono := MeasureTheory.integral_mono_ae hleft_int hright_int hpoint
  have hright_eq :
      ∫ x in U, 2 * (φ x * u.grad x i) ^ 2 +
          2 * (u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2
          ∂MeasureTheory.volume =
        (2 : ℝ) * ∫ x in U, (φ x * u.grad x i) ^ 2 ∂MeasureTheory.volume +
          (2 : ℝ) *
            ∫ x in U, (u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2
              ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add hterm1_int hterm2_int]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rwa [hright_eq] at hmono

/-- Lower-order quotient control by the two standard localized H¹ terms. -/
theorem integral_set_forwardDifferenceQuotient_sq_le_two_integral_cutoff_grad_sq_add_two_integral_value_fderiv_sq
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U)
    {S : Set (Vec d)} (hS_meas : MeasurableSet S)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hφ_one : ∀ x ∈ S, φ x = 1)
    (hφ_shift_one : ∀ x ∈ S, φ (euclideanCoordShift step i x) = 1) :
    ∫ x in S, (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
        ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, (φ x * u.grad x i) ^ 2 ∂MeasureTheory.volume +
        (2 : ℝ) *
          ∫ x in U, (u.toFun x * (fderiv ℝ φ x) (basisVec i)) ^ 2
            ∂MeasureTheory.volume := by
  exact
    (integral_set_forwardDifferenceQuotient_sq_le_integral_localized_product_rule_grad_sq
      (U := U) u hU hφ hφ_compact hφ_sub hS_meas hstep i
      hφ_one hφ_shift_one).trans
      (integral_product_rule_grad_sq_le_two_integral_cutoff_grad_sq_add_two_integral_value_fderiv_sq
        (U := U) u hφ hφ_compact i)

/-- Nested quantitative Caccioppoli with the lower-order quotient term replaced
by the two standard localized H¹ terms. -/
theorem directDifferenceQuotient_quantitativeCubeCutoff_inner_energy_quarter_le_forcing_sq_add_lower_h1_terms
    (h : WeakPoissonEquationOn U u f) (hU : IsOpenBoundedConvexDomain U)
    (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    {S : Set (Vec d)} (hS_meas : MeasurableSet S) (hSV : S ⊆ V)
    (hη_one : ∀ x ∈ S, (η : Vec d → ℝ) x = 1)
    {θ : Vec d → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθ_compact : HasCompactSupport θ) (hθ_sub : tsupport θ ⊆ U)
    (hθ_one : ∀ x ∈ V, θ x = 1)
    (hθ_shift_one : ∀ x ∈ V, θ (euclideanCoordShift step i x) = 1) :
    (1 / 4 : ℝ) *
        ∫ x in S,
          vecNormSq
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        ((3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
          ((2 : ℝ) * ∫ x in U, (θ x * u.grad x i) ^ 2 ∂MeasureTheory.volume +
            (2 : ℝ) *
              ∫ x in U, (u.toFun x * (fderiv ℝ θ x) (basisVec i)) ^ 2
                ∂MeasureTheory.volume) := by
  let K : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)
  have hbase :=
    h.directDifferenceQuotient_quantitativeCubeCutoff_inner_energy_quarter_le_forcing_sq_add_quotient_sq
      hU.isOpen hf hV hVU hstep i hVshift η hη_sub hS_meas hSV hη_one
  have hlower :=
    integral_set_forwardDifferenceQuotient_sq_le_two_integral_cutoff_grad_sq_add_two_integral_value_fderiv_sq
      (U := U) u hU hθ hθ_compact hθ_sub hV.isOpen.measurableSet hstep i
      hθ_one hθ_shift_one
  have hK_nonneg : 0 ≤ K := by
    unfold K
    positivity
  have hlowerK :
      K * ∫ x in V,
            (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2
            ∂MeasureTheory.volume ≤
        K *
          ((2 : ℝ) * ∫ x in U, (θ x * u.grad x i) ^ 2 ∂MeasureTheory.volume +
            (2 : ℝ) *
              ∫ x in U, (u.toFun x * (fderiv ℝ θ x) (basisVec i)) ^ 2
                ∂MeasureTheory.volume) :=
    mul_le_mul_of_nonneg_left hlower hK_nonneg
  have htarget := hbase.trans (add_le_add_right hlowerK _)
  simpa [K, mul_assoc] using htarget

/-- Nested quantitative Caccioppoli with both the inner and outer cutoffs
chosen from the quantitative cube-cutoff package. The outer cutoff is assumed
to be identically one on the intermediate domain and on its forward-shifted
points. -/
theorem directDifferenceQuotient_quantitativeCubeCutoff_inner_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms
    (h : WeakPoissonEquationOn U u f) (hU : IsOpenBoundedConvexDomain U)
    (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {Q : TriadicCube d} {ρ₁ ρ₂ σ₁ σ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    {S : Set (Vec d)} (hS_meas : MeasurableSet S) (hSV : S ⊆ V)
    (hη_one : ∀ x ∈ S, (η : Vec d → ℝ) x = 1)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hθ_sub : tsupport (θ : Vec d → ℝ) ⊆ U)
    (hVθ : V ⊆ scaledClosedCubeSet Q σ₁)
    (hVshiftθ : ∀ x ∈ V, euclideanCoordShift step i x ∈ scaledClosedCubeSet Q σ₁) :
    (1 / 4 : ℝ) *
        ∫ x in S,
          vecNormSq
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        ((3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
          ((2 : ℝ) * ∫ x in U, ((θ : Vec d → ℝ) x * u.grad x i) ^ 2
              ∂MeasureTheory.volume +
            (2 : ℝ) *
              ∫ x in U,
                (u.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
                ∂MeasureTheory.volume) := by
  exact
    h.directDifferenceQuotient_quantitativeCubeCutoff_inner_energy_quarter_le_forcing_sq_add_lower_h1_terms
      hU hf hV hVU hstep i hVshift η hη_sub hS_meas hSV hη_one
      θ.smooth θ.hasCompactSupport hθ_sub
      (by
        intro x hx
        exact θ.eq_one_on_inner x (hVθ hx))
      (by
        intro x hx
        exact θ.eq_one_on_inner (euclideanCoordShift step i x) (hVshiftθ x hx))

/-- Inner-cube version of the nested quantitative Caccioppoli estimate with a
quantitative outer lower-order cutoff. -/
theorem directDifferenceQuotient_quantitativeCubeCutoff_innerCube_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms
    (h : WeakPoissonEquationOn U u f) (hU : IsOpenBoundedConvexDomain U)
    (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {Q : TriadicCube d} {ρ₁ ρ₂ σ₁ σ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hθ_sub : tsupport (θ : Vec d → ℝ) ⊆ U)
    (hVθ : V ⊆ scaledClosedCubeSet Q σ₁)
    (hVshiftθ : ∀ x ∈ V, euclideanCoordShift step i x ∈ scaledClosedCubeSet Q σ₁) :
    (1 / 4 : ℝ) *
        ∫ x in scaledClosedCubeSet Q ρ₁,
          vecNormSq
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        ((3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
          ((2 : ℝ) * ∫ x in U, ((θ : Vec d → ℝ) x * u.grad x i) ^ 2
              ∂MeasureTheory.volume +
            (2 : ℝ) *
              ∫ x in U,
                (u.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
                ∂MeasureTheory.volume) := by
  exact
    h.directDifferenceQuotient_quantitativeCubeCutoff_inner_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms
      hU hf hV hVU hstep i hVshift η hη_sub
      (isClosed_scaledClosedCubeSet Q ρ₁).measurableSet hinnerV
      (by
        intro x hx
        exact η.eq_one_on_inner x hx)
      θ hθ_sub hVθ hVshiftθ

/-- Inner-cube nested quantitative Caccioppoli with the outer shifted-containment
hypothesis discharged by a one-coordinate step-size restriction. -/
theorem directDifferenceQuotient_quantitativeCubeCutoff_innerCube_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms_of_step_abs_le
    (h : WeakPoissonEquationOn U u f) (hU : IsOpenBoundedConvexDomain U)
    (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {Q : TriadicCube d} {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hθ_sub : tsupport (θ : Vec d → ℝ) ⊆ U)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hνσ : ν ≤ σ₁)
    (hstep_abs : |step| ≤ (σ₁ - ν) * cubeRadius Q) :
    (1 / 4 : ℝ) *
        ∫ x in scaledClosedCubeSet Q ρ₁,
          vecNormSq
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        ((3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
          ((2 : ℝ) * ∫ x in U, ((θ : Vec d → ℝ) x * u.grad x i) ^ 2
              ∂MeasureTheory.volume +
            (2 : ℝ) *
              ∫ x in U,
                (u.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
                ∂MeasureTheory.volume) := by
  exact
    h.directDifferenceQuotient_quantitativeCubeCutoff_innerCube_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms
      hU hf hV hVU hstep i hVshift η hη_sub hinnerV θ hθ_sub
      (by
        intro x hx
        exact scaledClosedCubeSet_mono Q hνσ (hVν hx))
      (by
        intro x hx
        exact
          euclideanCoordShift_mem_scaledClosedCubeSet_of_mem_scaledClosedCubeSet
            Q hνσ hstep_abs i (hVν hx))

/-- Open-cube ambient version of the nested quantitative Caccioppoli estimate:
the ambient-domain containment, shifted containment, and outer cutoff support
are all discharged by strict subcube radii and the step-size bound. -/
theorem directDifferenceQuotient_quantitativeCubeCutoff_openCube_innerCube_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms_of_step_abs_le
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : |step| ≤ (σ₁ - ν) * cubeRadius Q) :
    (1 / 4 : ℝ) *
        ∫ x in scaledClosedCubeSet Q ρ₁,
          vecNormSq
            ((uQ.forwardDifferenceQuotientOn step i hV.isOpen
                (by
                  intro x hx
                  exact
                    scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q hν_nonneg
                      (lt_of_le_of_lt hνσ hσ₁_lt_one) (hVν hx))
                (by
                  intro x hx
                  rw [mem_translateSet_iff_sub_mem]
                  have hσ₁_nonneg : 0 ≤ σ₁ := hν_nonneg.trans hνσ
                  have hxshift :
                      euclideanCoordShift step i x ∈ scaledClosedCubeSet Q σ₁ :=
                    euclideanCoordShift_mem_scaledClosedCubeSet_of_mem_scaledClosedCubeSet
                      Q hνσ hstep_abs i (hVν hx)
                  have hxopen :
                      euclideanCoordShift step i x ∈ openCubeSet Q :=
                    scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
                      Q hσ₁_nonneg hσ₁_lt_one hxshift
                  simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hxopen)).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
        ((3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
          ((2 : ℝ) * ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
              ∂MeasureTheory.volume +
            (2 : ℝ) *
              ∫ x in openCubeSet Q,
                (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
                ∂MeasureTheory.volume) := by
  have hVU : V ⊆ openCubeSet Q := by
    intro x hx
    exact
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q hν_nonneg
        (lt_of_le_of_lt hνσ hσ₁_lt_one) (hVν hx)
  have hVshift : V ⊆ translateSet ((-step) • basisVec i) (openCubeSet Q) := by
    intro x hx
    rw [mem_translateSet_iff_sub_mem]
    have hσ₁_nonneg : 0 ≤ σ₁ := hν_nonneg.trans hνσ
    have hxshift :
        euclideanCoordShift step i x ∈ scaledClosedCubeSet Q σ₁ :=
      euclideanCoordShift_mem_scaledClosedCubeSet_of_mem_scaledClosedCubeSet
        Q hνσ hstep_abs i (hVν hx)
    have hxopen : euclideanCoordShift step i x ∈ openCubeSet Q :=
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
        Q hσ₁_nonneg hσ₁_lt_one hxshift
    simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hxopen
  exact
    h.directDifferenceQuotient_quantitativeCubeCutoff_innerCube_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms_of_step_abs_le
      (isOpenBoundedConvexDomain_openCubeSet Q) hf hV hVU hstep i hVshift
      η hη_sub hinnerV θ
      (θ.tsupport_subset_openCubeSet_of_nonneg_of_lt_one hσ₂_nonneg hσ₂_lt_one)
      hVν hνσ hstep_abs

end WeakPoissonEquationOn

end

end Homogenization
