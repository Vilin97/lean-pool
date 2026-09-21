/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ProbeMax
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.QuenchedGammaEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedUnitEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-! # Uniform Ellipticity Endpoint -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped Matrix.Norms.Elementwise

/-!
# The uniform ellipticity endpoint in Section 5.7

This file records the `σ = ∞` endpoint of the quenched coarse-grained
ellipticity assumption.  The endpoint is deliberately kept as a separate API:
it gives an a.s. unit-scale bound, and from that bound we may recover every
finite `Γσ` input needed by the existing concentration arguments.
-/

noncomputable section

/-- The `σ = ∞` endpoint of the quenched coarse-grained ellipticity
assumption.

The field `bound` is the Lean version of the uniform estimate
`Γ_∞`: the unit-cube ellipticity observable is bounded by `thetaHat`
almost surely. -/
structure GammaInfinityCoarseGrainedEllipticity
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : Type where
  params : QuantitativeCoarseGrainedEllipticityParams d
  thetaHat : ℝ
  thetaHat_pos : 0 < thetaHat
  bound :
    gammaSigmaUnitEllipticityObservable hP hStruct
      params.sUpper params.sLower ≤ᵐ[P] fun _ => thetaHat

/-- Manuscript-facing `σ = ∞` endpoint of `(P5)`, with no exposed moment
exponent `xi`. -/
structure GammaInfinityCoarseGrainedEllipticityNoXi
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : Type where
  params : GammaCoarseGrainedEllipticityParams d
  thetaHat : ℝ
  thetaHat_pos : 0 < thetaHat
  bound :
    gammaSigmaUnitEllipticityObservable hP hStruct
      params.sUpper params.sLower ≤ᵐ[P] fun _ => thetaHat

namespace GammaInfinityCoarseGrainedEllipticityNoXi

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

/-- Add the internal finite moment exponent used by the existing endpoint
proof infrastructure. -/
noncomputable def withInternalXi
    (hInf : GammaInfinityCoarseGrainedEllipticityNoXi P hP hStruct) :
    GammaInfinityCoarseGrainedEllipticity P hP hStruct where
  params := hInf.params.toQuantitativeParams
  thetaHat := hInf.thetaHat
  thetaHat_pos := hInf.thetaHat_pos
  bound := by
    simpa using hInf.bound

@[simp]
theorem withInternalXi_thetaHat
    (hInf : GammaInfinityCoarseGrainedEllipticityNoXi P hP hStruct) :
    hInf.withInternalXi.thetaHat = hInf.thetaHat := rfl

end GammaInfinityCoarseGrainedEllipticityNoXi

/-- Transfer an a.s. upper bound across equality in law. -/
theorem ae_le_of_map_eq_map_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} {A : ℝ}
    (hYm : AEMeasurable Y μ) (hXm : AEMeasurable X μ)
    (hmap : Measure.map Y μ = Measure.map X μ)
    (hX : X ≤ᵐ[μ] fun _ => A) :
    Y ≤ᵐ[μ] fun _ => A := by
  have hXmap : ∀ᵐ y ∂Measure.map X μ, y ≤ A :=
    (MeasureTheory.ae_map_iff hXm measurableSet_Iic).2 hX
  have hYmap : ∀ᵐ y ∂Measure.map Y μ, y ≤ A := by
    simpa [hmap] using hXmap
  exact (MeasureTheory.ae_map_iff hYm measurableSet_Iic).1 hYmap

/-- A deterministic counterpart of the finite-`Γσ` scale-zero propagation:
an a.s. bound at the unit origin cube propagates to every larger origin cube. -/
theorem blockJObservableCubeSetBlockVec_originCube_le_of_scaleZero_ae
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hPμ : Ch04.RestrictionLawCarrier Pμ) (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {θ : ℝ} (Pvec Qvec : BlockVec d)
    (h0 :
      Ch04.blockJObservableCubeSetBlockVec (originCube d 0) Pvec Qvec
        ≤ᵐ[Pμ] fun _ => θ)
    {n : ℤ} (hn : 0 ≤ n) :
    Ch04.blockJObservableCubeSetBlockVec (originCube d n) Pvec Qvec
      ≤ᵐ[Pμ] fun _ => θ := by
  classical
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => Ch04.blockJSetObservableBlockVec Pvec Qvec U a.toFun
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d n) 0
  let Avg : RegCoeffField d → ℝ :=
    fun a => ((D.card : ℝ)⁻¹) *
      D.sum (fun R => Ch04.blockJObservableCubeSetBlockVec R Pvec Qvec a)
  have hn0 : (0 : ℤ) ≤ (originCube d n).scale := by
    simpa [originCube] using hn
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtScale_nonempty (originCube d n) hn0
  have hX_cov : Ch04.IsRestrictionTranslationCovariant X :=
    Ch04.blockJSetObservableBlockVec_restrictionTranslationCovariant Pvec Qvec
  have hX0_aemeas :
      AEMeasurable (X (cubeSet (originCube d 0))) Pμ := by
    simpa [X] using
      Ch04.aemeasurable_blockJSetObservableBlockVec_cubeSet hPμ
        (originCube d 0) Pvec Qvec
  have hDesc_aemeas :
      ∀ R, AEMeasurable (Ch04.blockJObservableCubeSetBlockVec R Pvec Qvec) Pμ := by
    intro R
    simpa [X] using
      Ch04.aemeasurable_blockJSetObservableBlockVec_cubeSet hPμ R Pvec Qvec
  have hDesc_le :
      ∀ R ∈ D,
        Ch04.blockJObservableCubeSetBlockVec R Pvec Qvec
          ≤ᵐ[Pμ] fun _ => θ := by
    intro R hR
    have hshift :
        cubeSet R =
          translateSet (intVecToRealVec (Ch04.scaleTranslationShift 0 R))
            (cubeSet (originCube d 0)) := by
      exact Ch04.cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) (n := 0) (m := n) (R := R)
        (by norm_num) hn (by simpa [D] using hR)
    have hXR_aemeas : AEMeasurable (X (cubeSet R)) Pμ := by
      simpa [X] using hDesc_aemeas R
    have hmap :
        Measure.map (X (cubeSet R)) Pμ =
          Measure.map (X (cubeSet (originCube d 0))) Pμ := by
      calc
        Measure.map (X (cubeSet R)) Pμ =
            Measure.map
              (X
                (translateSet (intVecToRealVec (Ch04.scaleTranslationShift 0 R))
                  (cubeSet (originCube d 0)))) Pμ := by
              rw [hshift]
        _ = Measure.map (X (cubeSet (originCube d 0))) Pμ := by
              exact Ch04.map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
                (P := Pμ) hstat (U := cubeSet (originCube d 0))
                hX0_aemeas hX_cov (Ch04.scaleTranslationShift 0 R)
    have h0X : X (cubeSet (originCube d 0)) ≤ᵐ[Pμ] fun _ => θ := by
      simpa [X] using h0
    simpa [X] using
      ae_le_of_map_eq_map_aemeasurable hXR_aemeas hX0_aemeas hmap h0X
  have hAvg_le : Avg ≤ᵐ[Pμ] fun _ => θ := by
    have hAll : ∀ᵐ a ∂Pμ,
        ∀ R ∈ D, Ch04.blockJObservableCubeSetBlockVec R Pvec Qvec a ≤ θ := by
      rw [Filter.eventually_all_finset]
      intro R hR
      exact hDesc_le R hR
    filter_upwards [hAll] with a ha
    have hD_card_ne : (D.card : ℝ) ≠ 0 := by
      exact_mod_cast hD_nonempty.card_ne_zero
    have hsum_le :
        D.sum (fun R => Ch04.blockJObservableCubeSetBlockVec R Pvec Qvec a) ≤
          D.sum (fun _R => θ) :=
      Finset.sum_le_sum fun R hR => ha R hR
    calc
      Avg a =
          ((D.card : ℝ)⁻¹) *
            D.sum (fun R => Ch04.blockJObservableCubeSetBlockVec R Pvec Qvec a) := by
            rfl
      _ ≤ ((D.card : ℝ)⁻¹) * D.sum (fun _R => θ) := by
            exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = θ := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp [hD_card_ne]
  have hsub_ae :
      ∀ᵐ a ∂Pμ,
        Ch04.blockJObservableCubeSetBlockVec (originCube d n) Pvec Qvec a ≤ Avg a := by
    filter_upwards [hPμ.ae_locallyUniformlyEllipticField] with a ha
    have hsub :=
      Ch04.blockJObservableCubeSetBlockVec_le_descendantsAverage_cubeSet_of_aelocallyUniformlyEllipticField
        (a := a) ha (originCube d n) (k := 0) hn0 Pvec Qvec
    simpa [Avg, D, descendantsAverage,
      descendantsAtScale_eq_descendantsAtDepth (originCube d n) hn0] using hsub
  filter_upwards [hsub_ae, hAvg_le] with a hsub hAvg
  exact hsub.trans hAvg

/-- Transfer an a.s. bound from the origin cube at scale `n` to a descendant
cube at the same scale, using stationarity. -/
theorem limitNormalizedBlockJObservable_of_mem_descendantsAtScale_le_ae
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hPμ : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {θ : ℝ} {m n : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) n)
    (e : FullBlockVec d)
    (hOrigin :
      limitNormalizedBlockJObservable hPμ hStruct (originCube d n) e
        ≤ᵐ[Pμ] fun _ => θ) :
    limitNormalizedBlockJObservable hPμ hStruct R e
      ≤ᵐ[Pμ] fun _ => θ := by
  have hmap :=
    map_limitNormalizedBlockJObservable_eq_origin_of_mem_descendantsAtScale
      hPμ hStruct hstat hn hnm hR e
  have hXR_aemeas :
      AEMeasurable (limitNormalizedBlockJObservable hPμ hStruct R e) Pμ :=
    aemeasurable_limitNormalizedBlockJObservable hPμ hStruct R e
  have hX0_aemeas :
      AEMeasurable
        (limitNormalizedBlockJObservable hPμ hStruct (originCube d n) e) Pμ :=
    aemeasurable_limitNormalizedBlockJObservable hPμ hStruct (originCube d n) e
  exact
    ae_le_of_map_eq_map_aemeasurable hXR_aemeas hX0_aemeas hmap hOrigin

/-- An a.s. origin-cube bound controls the localized maximum over descendants. -/
theorem localizedLimitNormalizedJMax_le_of_originCube_ae
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hPμ : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {θ : ℝ} {m n : ℕ} (hnm : n ≤ m) (e : FullBlockVec d)
    (hOrigin :
      limitNormalizedBlockJObservable hPμ hStruct
          (originCube d ((n : ℕ) : ℤ)) e
        ≤ᵐ[Pμ] fun _ => θ) :
    localizedLimitNormalizedJMax hPμ hStruct m n e
      ≤ᵐ[Pμ] fun _ => θ := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n) hnm
  have hn_nonneg : 0 ≤ ((n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hnm_int : ((n : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by
    exact_mod_cast hnm
  have hEach :
      ∀ R ∈ D,
        limitNormalizedBlockJObservable hPμ hStruct R e
          ≤ᵐ[Pμ] fun _ => θ := by
    intro R hR
    exact
      limitNormalizedBlockJObservable_of_mem_descendantsAtScale_le_ae
        hPμ hStruct hstat hn_nonneg hnm_int
        (R := R) (by simpa [D] using hR) e hOrigin
  have hAll : ∀ᵐ a ∂Pμ,
      ∀ R ∈ D, limitNormalizedBlockJObservable hPμ hStruct R e a ≤ θ := by
    rw [Filter.eventually_all_finset]
    intro R hR
    exact hEach R hR
  filter_upwards [hAll] with a ha
  dsimp [localizedLimitNormalizedJMax]
  simp only [D, hD, dite_true]
  exact Finset.sup'_le hD _ (fun R hR => ha R hR)

namespace GammaInfinityCoarseGrainedEllipticity

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

theorem sUpper_pos
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct) :
    0 < hInf.params.sUpper :=
  hInf.params.sUpper_pos

theorem sLower_pos
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct) :
    0 < hInf.params.sLower :=
  hInf.params.sLower_pos

/-- The guarded unit-cube observable is nonnegative even before proving that
the normalizing scalar `barσ_0` is positive. -/
theorem unitEllipticityObservable_nonneg
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct)
    (a : RegCoeffField d) :
    0 ≤ gammaSigmaUnitEllipticityObservable hP hStruct
      hInf.params.sUpper hInf.params.sLower a := by
  by_cases hbar : 0 < hP.barSigmaAtScale hStruct (0 : ℤ)
  · have hbar_nonneg : 0 ≤ hP.barSigmaAtScale hStruct (0 : ℤ) := hbar.le
    have hbar_inv_nonneg :
        0 ≤ (hP.barSigmaAtScale hStruct (0 : ℤ))⁻¹ :=
      (inv_pos.mpr hbar).le
    simpa [gammaSigmaUnitEllipticityObservable, hbar] using add_nonneg
      (mul_nonneg hbar_inv_nonneg
        (Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
          hInf.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)))
      (mul_nonneg hbar_nonneg
        (inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
            hInf.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))))
  · simpa [gammaSigmaUnitEllipticityObservable, hbar] using add_nonneg
      (Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hInf.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1))
      (inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
          hInf.sLower_pos (by norm_num : (1 : ℝ) ≤ 1)))

theorem abs_unitEllipticityObservable_le_thetaHat_ae
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct) :
    (fun a : RegCoeffField d =>
      |gammaSigmaUnitEllipticityObservable hP hStruct
        hInf.params.sUpper hInf.params.sLower a|)
      ≤ᵐ[P] fun _ => hInf.thetaHat := by
  filter_upwards [hInf.bound] with a ha
  rwa [abs_of_nonneg (hInf.unitEllipticityObservable_nonneg a)]

/-- A uniform unit-scale bound is, in particular, a finite `Γσ` tail for every
positive finite exponent `σ`. -/
theorem unitEllipticityObservable_isBigO
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct)
    {σ : ℝ} (_hσ : 0 < σ) :
    IsBigO P (gammaSigma σ)
      (gammaSigmaUnitEllipticityObservable hP hStruct
        hInf.params.sUpper hInf.params.sLower)
      hInf.thetaHat := by
  let : IsProbabilityMeasure P := hP.isProbability
  change IsBigOWith P (gammaSigma σ)
    (fun a : RegCoeffField d =>
      |gammaSigmaUnitEllipticityObservable hP hStruct
        hInf.params.sUpper hInf.params.sLower a|)
    hInf.thetaHat
  have hconst :
      IsBigOWith P (gammaSigma σ)
        (fun _ : RegCoeffField d => hInf.thetaHat) hInf.thetaHat := by
    have hconstAbs :
        IsBigO P (gammaSigma σ)
          (fun _ : RegCoeffField d => hInf.thetaHat) hInf.thetaHat :=
      Ch04.isBigO_gammaSigma_const_of_abs_le (μ := P) (σ := σ)
        (A := hInf.thetaHat) (c := hInf.thetaHat)
        hInf.thetaHat_pos.le
        (by rw [abs_of_pos hInf.thetaHat_pos])
    change IsBigOWith P (gammaSigma σ)
      (fun _ : RegCoeffField d => |hInf.thetaHat|) hInf.thetaHat at hconstAbs
    simpa [abs_of_pos hInf.thetaHat_pos] using hconstAbs
  exact
    Ch04.isBigOWith_of_ae_le (μ := P) (Ψ := gammaSigma σ)
      hconst hInf.abs_unitEllipticityObservable_le_thetaHat_ae

/-- Forget the endpoint input to any finite positive `Γσ` input. -/
def toGammaSigma
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct)
    (σ : ℝ) (hσ : 0 < σ) :
    GammaSigmaCoarseGrainedEllipticity P hP hStruct where
  sigma := σ
  sigma_pos := hσ
  params := hInf.params
  thetaHat := hInf.thetaHat
  thetaHat_pos := hInf.thetaHat_pos
  tail := hInf.unitEllipticityObservable_isBigO hσ

/-- The endpoint implies the Chapter 5 quantitative coarse-grained
ellipticity package, via any finite exponent. -/
def toQuantitativeCoarseGrainedEllipticity
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct) :
    QuantitativeCoarseGrainedEllipticity P :=
  (hInf.toGammaSigma 1 zero_lt_one).toQuantitativeCoarseGrainedEllipticity

theorem barSigmaAtScale_zero_pos
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct) :
    0 < hP.barSigmaAtScale hStruct (0 : ℤ) :=
  (hInf.toGammaSigma 1 zero_lt_one).barSigmaAtScale_zero_pos

/-- The deterministic unit-scale constant for the endpoint normalized
`J` bound. -/
noncomputable def unitJConst (d : ℕ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
    (Ch04.gammaMomentConst 1 * (params.xi : ℝ))

theorem unitJConst_pos
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < unitJConst d params := by
  unfold unitJConst
  have hcard_pos : 0 < (Fintype.card (BlockCoord d) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (BlockCoord d)))
  have hxi_pos : 0 < (params.xi : ℝ) := by
    exact_mod_cast params.xi_pos
  have hgamma_pos : 0 < Ch04.gammaMomentConst (1 : ℝ) := by
    exact IndependentSums.gammaMomentConst_pos zero_lt_one
  positivity

/-- Under the endpoint assumption, the limiting-normalized unit-cube `J`
observable is almost surely bounded by a deterministic multiple of
`thetaHat^2`. -/
theorem limitNormalizedBlockJObservable_unit_le_thetaHat_sq_ae
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct)
    (e : FullBlockVec d) (he : ∀ α : BlockCoord d, |e α| ≤ 1) :
    limitNormalizedBlockJObservable hP hStruct (originCube d 0) e
      ≤ᵐ[P] fun _ =>
        unitJConst d hInf.params * hInf.thetaHat ^ (2 : ℕ) := by
  let hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct :=
    hInf.toGammaSigma 1 zero_lt_one
  let Cdim : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let G : ℝ := Ch04.gammaMomentConst (1 : ℝ) * (hInf.params.xi : ℝ)
  let X : RegCoeffField d → ℝ :=
    gammaSigmaUnitEllipticityObservable hP hStruct
      hInf.params.sUpper hInf.params.sLower
  let Y : RegCoeffField d → ℝ :=
    limitWeightedUnitEllipticityObservable hP hStruct
      hInf.params.sUpper hInf.params.sLower
  have hJ_ae := hΓ.limitNormalizedBlockJObservable_le_card_sq_mul_weighted_ae e he
  have htheta_le :
      thetaAtScale hP hStruct (0 : ℤ) ≤ G * hInf.thetaHat := by
    have h := hΓ.thetaAtScale_zero_le_gammaMomentScale
    simpa [hΓ, G, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using h
  have htheta_nonneg : 0 ≤ thetaAtScale hP hStruct (0 : ℤ) := by
    exact le_trans zero_le_one
      (by
        simpa using
          Section54.GoodScale.one_le_thetaAtScale_of_P4
            hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0)
  have hthetaHat_nonneg : 0 ≤ hInf.thetaHat := hInf.thetaHat_pos.le
  filter_upwards [hJ_ae, hInf.bound] with a hJ hX_le
  have hY_le : Y a ≤ thetaAtScale hP hStruct (0 : ℤ) * X a := by
    simpa [Y, X, hΓ, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using
      hΓ.limitWeightedUnitEllipticityObservable_le_thetaAtScale_zero_mul_unit a
  have hX_nonneg : 0 ≤ X a := by
    simpa [X] using hInf.unitEllipticityObservable_nonneg a
  have hY_scale :
      Y a ≤ G * hInf.thetaHat ^ (2 : ℕ) := by
    calc
      Y a ≤ thetaAtScale hP hStruct (0 : ℤ) * X a := hY_le
      _ ≤ thetaAtScale hP hStruct (0 : ℤ) * hInf.thetaHat :=
            mul_le_mul_of_nonneg_left hX_le htheta_nonneg
      _ ≤ (G * hInf.thetaHat) * hInf.thetaHat :=
            mul_le_mul_of_nonneg_right htheta_le hthetaHat_nonneg
      _ = G * hInf.thetaHat ^ (2 : ℕ) := by ring
  calc
    limitNormalizedBlockJObservable hP hStruct (originCube d 0) e a
        ≤ Cdim * Y a := by
          simpa [Cdim, Y, hΓ,
            GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using hJ
    _ ≤ Cdim * (G * hInf.thetaHat ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hY_scale (by dsimp [Cdim]; positivity)
    _ = unitJConst d hInf.params * hInf.thetaHat ^ (2 : ℕ) := by
          simp [unitJConst, Cdim, G]
          ring

/-- The endpoint unit `J` bound propagates to every origin scale. -/
theorem limitNormalizedBlockJObservable_originCube_le_thetaHat_sq_ae
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct)
    (e : FullBlockVec d) (he : ∀ α : BlockCoord d, |e α| ≤ 1)
    {n : ℕ} :
    limitNormalizedBlockJObservable hP hStruct
        (originCube d ((n : ℕ) : ℤ)) e
      ≤ᵐ[P] fun _ =>
        unitJConst d hInf.params * hInf.thetaHat ^ (2 : ℕ) := by
  let Pvec : BlockVec d := scalarLimitInvSqrtBlockVec hP hStruct e
  let Qvec : BlockVec d := scalarLimitSqrtBlockVec hP hStruct e
  have h0 :=
    hInf.limitNormalizedBlockJObservable_unit_le_thetaHat_sq_ae e he
  have h0_raw :
      Ch04.blockJObservableCubeSetBlockVec (originCube d 0) Pvec Qvec
        ≤ᵐ[P] fun _ =>
          unitJConst d hInf.params * hInf.thetaHat ^ (2 : ℕ) := by
    simpa [limitNormalizedBlockJObservable, Pvec, Qvec] using h0
  have hn_nonneg : 0 ≤ ((n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hraw :=
    blockJObservableCubeSetBlockVec_originCube_le_of_scaleZero_ae
      hP hStruct.stationary Pvec Qvec h0_raw hn_nonneg
  simpa [limitNormalizedBlockJObservable, Pvec, Qvec] using hraw

/-- The endpoint controls every localized normalized finite-probe maximum by a
deterministic multiple of `thetaHat^2`. -/
theorem localizedNormalizedProbeJMax_le_thetaHat_sq_ae
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct)
    {m n : ℕ} (hnm : n ≤ m) :
    localizedNormalizedProbeJMax hP hStruct m n
      ≤ᵐ[P] fun _ =>
        unitJConst d hInf.params * hInf.thetaHat ^ (2 : ℕ) := by
  classical
  let A : ℝ := unitJConst d hInf.params * hInf.thetaHat ^ (2 : ℕ)
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  have hS : S.Nonempty := by
    let α : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α, α, NormalizedProbeKind.coord), by simp [S]⟩
  have hEach :
      ∀ i ∈ S,
        localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i)
          ≤ᵐ[P] fun _ => A := by
    intro i _hi
    have hOrigin :=
      hInf.limitNormalizedBlockJObservable_originCube_le_thetaHat_sq_ae
        (normalizedProbeVec i) (normalizedProbeVec_abs_apply_le_one i) (n := n)
    exact
      localizedLimitNormalizedJMax_le_of_originCube_ae
        hP hStruct hStruct.stationary hnm (normalizedProbeVec i)
        (by simpa [A] using hOrigin)
  have hAll : ∀ᵐ a ∂P,
      ∀ i ∈ S,
        localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a ≤ A := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact hEach i hi
  filter_upwards [hAll] with a ha
  dsimp [localizedNormalizedProbeJMax]
  exact Finset.sup'_le hS _ (fun i hi => ha i (by simp [S] at hi ⊢))

/-- The endpoint controls the localized scale-zero unit-ellipticity supremum
by a deterministic multiple of `thetaHat^2`. -/
theorem localizedLimitWeightedUnitEllipticitySup_le_thetaHat_sq_ae
    (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct)
    {m : ℕ} :
    localizedLimitWeightedUnitEllipticitySup hP hStruct hInf.params m
      ≤ᵐ[P] fun _ =>
        (Ch04.gammaMomentConst (1 : ℝ) * (hInf.params.xi : ℝ)) *
          hInf.thetaHat ^ (2 : ℕ) := by
  classical
  let hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct :=
    hInf.toGammaSigma 1 zero_lt_one
  let G : ℝ := Ch04.gammaMomentConst (1 : ℝ) * (hInf.params.xi : ℝ)
  let A : ℝ := G * hInf.thetaHat ^ (2 : ℕ)
  have htheta_le :
      thetaAtScale hP hStruct (0 : ℤ) ≤ G * hInf.thetaHat := by
    have h := hΓ.thetaAtScale_zero_le_gammaMomentScale
    simpa [hΓ, G, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using h
  have htheta_nonneg : 0 ≤ thetaAtScale hP hStruct (0 : ℤ) := by
    exact le_trans zero_le_one
      (by
        simpa using
          Section54.GoodScale.one_le_thetaAtScale_of_P4
            hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0)
  have hthetaHat_nonneg : 0 ≤ hInf.thetaHat := hInf.thetaHat_pos.le
  have hOrigin :
      limitWeightedUnitEllipticityObservable hP hStruct
          hInf.params.sUpper hInf.params.sLower
        ≤ᵐ[P] fun _ => A := by
    filter_upwards [hInf.bound] with a hunit
    have hlim :=
      hΓ.limitWeightedUnitEllipticityObservable_le_thetaAtScale_zero_mul_unit a
    calc
      limitWeightedUnitEllipticityObservable hP hStruct
          hInf.params.sUpper hInf.params.sLower a
          ≤ thetaAtScale hP hStruct (0 : ℤ) *
              gammaSigmaUnitEllipticityObservable hP hStruct
                hInf.params.sUpper hInf.params.sLower a := by
            simpa [hΓ, GammaInfinityCoarseGrainedEllipticity.toGammaSigma]
              using hlim
      _ ≤ thetaAtScale hP hStruct (0 : ℤ) * hInf.thetaHat :=
            mul_le_mul_of_nonneg_left hunit htheta_nonneg
      _ ≤ (G * hInf.thetaHat) * hInf.thetaHat :=
            mul_le_mul_of_nonneg_right htheta_le hthetaHat_nonneg
      _ = A := by
            simp [A]
            ring
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let hD : D.Nonempty := descendantsAtScale_nonempty Q (by simp [Q, originCube])
  have hEach :
      ∀ U ∈ D,
        (fun a : RegCoeffField d =>
          limitWeightedUnitEllipticityObservableOnCube hP hStruct U
            hInf.params.sUpper hInf.params.sLower a)
          ≤ᵐ[P] fun _ => A := by
    intro U hU
    have hUscale : U.scale = 0 :=
      descendant_scale_eq_of_mem_descendantsAtScale (by simpa [D] using hU)
    have hmap :=
      map_limitWeightedUnitEllipticityObservableOnCube_eq_origin_of_scale_zero
        hP hStruct hUscale hInf.sUpper_pos hInf.sLower_pos
    have hU_aem :
        AEMeasurable
          (limitWeightedUnitEllipticityObservableOnCube hP hStruct U
            hInf.params.sUpper hInf.params.sLower) P :=
      aemeasurable_limitWeightedUnitEllipticityObservableOnCube
        hP hStruct U hInf.sUpper_pos hInf.sLower_pos
    have h0_aem :
        AEMeasurable
          (limitWeightedUnitEllipticityObservable hP hStruct
            hInf.params.sUpper hInf.params.sLower) P := by
      simpa using
        aemeasurable_limitWeightedUnitEllipticityObservableOnCube
          hP hStruct (originCube d 0) hInf.sUpper_pos hInf.sLower_pos
    exact ae_le_of_map_eq_map_aemeasurable hU_aem h0_aem hmap hOrigin
  have hAll : ∀ᵐ a ∂P,
      ∀ U ∈ D,
        limitWeightedUnitEllipticityObservableOnCube hP hStruct U
          hInf.params.sUpper hInf.params.sLower a ≤ A := by
    rw [Filter.eventually_all_finset]
    intro U hU
    exact hEach U hU
  filter_upwards [hAll] with a ha
  dsimp [localizedLimitWeightedUnitEllipticitySup, Q, D]
  exact Finset.sup'_le hD _ (fun U hU => ha U hU)

end GammaInfinityCoarseGrainedEllipticity

namespace GammaInfinityCoarseGrainedEllipticityNoXi

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

/-- Forget the endpoint input to any finite positive `Γσ` input, in the
manuscript-facing parameter package with no exposed moment exponent. -/
noncomputable def toGammaSigmaNoXi
    (hInf : GammaInfinityCoarseGrainedEllipticityNoXi P hP hStruct)
    (σ : ℝ) (hσ : 0 < σ) :
    GammaSigmaCoarseGrainedEllipticityNoXi P hP hStruct where
  sigma := σ
  sigma_pos := hσ
  params := hInf.params
  thetaHat := hInf.thetaHat
  thetaHat_pos := hInf.thetaHat_pos
  tail := by
    simpa [GammaInfinityCoarseGrainedEllipticityNoXi.withInternalXi] using
      hInf.withInternalXi.unitEllipticityObservable_isBigO hσ

end GammaInfinityCoarseGrainedEllipticityNoXi

/-- Endpoint (`σ = ∞`) version of Corollary `c.first.quenched.estimate`.

In Lean the endpoint assumption is a separate structure.  The conclusion is
obtained by applying the finite-`σ` corollary at `σ = 2`, which is exactly the
`Γ_{σ ∧ 2}` exponent when `σ = ∞`. -/
theorem firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent_noXi_infinity
    {d : ℕ} [NeZero d]
    (params : GammaCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∃ Cfluct : ℝ, 0 < Cfluct ∧
        ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
          (hPμ : Ch04.RestrictionLawCarrier Pμ)
          (hStruct : Ch04.RestrictionStructuralLaw Pμ)
          (hInf : GammaInfinityCoarseGrainedEllipticityNoXi Pμ hPμ hStruct),
          hInf.params = params →
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
        ∀ {n m : ℕ}, n < m →
          let hΓ2 : GammaSigmaCoarseGrainedEllipticityNoXi Pμ hPμ hStruct :=
            hInf.toGammaSigmaNoXi 2 (by norm_num : (0 : ℝ) < 2)
          let N0 : ℕ :=
            annealedAlgebraicEntryScale Pμ
              hΓ2.withInternalXi.toQuantitativeCoarseGrainedEllipticity Centry
          IsBigOWith Pμ (gammaSigma 2)
            (fun aω =>
              limitNormalizedBlockJObservable hPμ hStruct
                  (originCube d ((N0 + m : ℕ) : ℤ)) e aω -
                Real.rpow (3 : ℝ) (-a * (n : ℝ)))
            (Cfluct *
              (3 : ℝ) ^
                (-(d : ℝ) / 2 *
                  (Int.toNat
                    (((N0 + m : ℕ) : ℤ) -
                      ((N0 + n : ℕ) : ℤ)) : ℝ)) *
              hInf.thetaHat ^ (2 : ℕ)) := by
  obtain ⟨Centry, a, hCentry, ha, hfinite⟩ :=
    firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent_noXi
      (d := d) params
  obtain ⟨Cfluct, hCfluct, hfluct⟩ :=
    hfinite (σ := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
  refine ⟨Centry, a, hCentry, ha, Cfluct, hCfluct, ?_⟩
  intro Pμ hPμ hStruct hInf hparams e he_norm n m hnm
  let hΓ2 : GammaSigmaCoarseGrainedEllipticityNoXi Pμ hPμ hStruct :=
    hInf.toGammaSigmaNoXi 2 (by norm_num : (0 : ℝ) < 2)
  have hσ2 : hΓ2.sigma = (2 : ℝ) := rfl
  have hparams2 : hΓ2.params = params := by
    simpa [hΓ2, GammaInfinityCoarseGrainedEllipticityNoXi.toGammaSigmaNoXi]
      using hparams
  have h :=
    hfluct hPμ hStruct hΓ2 hσ2 hparams2 e he_norm hnm
  simpa [hΓ2, GammaInfinityCoarseGrainedEllipticityNoXi.toGammaSigmaNoXi]
    using h

end

end Section57
end Ch05
end Book
end Homogenization
