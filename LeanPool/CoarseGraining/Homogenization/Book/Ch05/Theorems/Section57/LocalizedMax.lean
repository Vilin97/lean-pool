/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FirstQuenchedEstimate

/-! # Localized Max -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums

/-!
# Localized block-response maxima

This file packages the finite maximum over subcubes appearing in
Theorem `t.homogenization.quenched`.  The maximum is first defined for a fixed
full-block vector `e`; the finite-basis reduction for the maximum over unit
vectors is kept as a later deterministic step.
-/

noncomputable section

/-- The finite maximum of the limiting-normalized block response over all
scale-`n` descendants of the scale-`m` origin cube. -/
noncomputable def localizedLimitNormalizedJMax
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ)
    (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (m n : ℕ) (e : FullBlockVec d) : RegCoeffField d → ℝ :=
  fun a =>
    let D : Finset (TriadicCube d) :=
      descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
    if hD : D.Nonempty then
      D.sup' hD (fun R => limitNormalizedBlockJObservable hP hStruct R e a)
    else
      0

theorem descendantsAtScale_originCube_nat_nonempty
    {d : ℕ} [NeZero d] {m n : ℕ} (hnm : n ≤ m) :
    (descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)).Nonempty := by
  have hnm_int : ((n : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by
    exact_mod_cast hnm
  simpa using
    descendantsAtScale_nonempty (originCube d ((m : ℕ) : ℤ)) hnm_int

theorem limitNormalizedBlockJObservable_le_localizedLimitNormalizedJMax
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    {m n : ℕ} (e : FullBlockVec d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ))
    (a : RegCoeffField d) :
    limitNormalizedBlockJObservable hP hStruct R e a ≤
      localizedLimitNormalizedJMax hP hStruct m n e a := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty := ⟨R, by simpa [D] using hR⟩
  dsimp [localizedLimitNormalizedJMax]
  simp only [D, hD, dite_true]
  exact Finset.le_sup' (s := D)
    (f := fun S => limitNormalizedBlockJObservable hP hStruct S e a)
    (b := R) (by simpa [D] using hR)

/-- Discounted localized response, the left side of the bad-event predicate. -/
noncomputable def discountedLocalizedLimitNormalizedJMax
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ)
    (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (t : ℝ) (m n : ℕ) (e : FullBlockVec d) : RegCoeffField d → ℝ :=
  fun a =>
      (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
      localizedLimitNormalizedJMax hP hStruct m n e a

theorem aemeasurable_limitNormalizedBlockJObservable
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (Q : TriadicCube d) (e : FullBlockVec d) :
    AEMeasurable (limitNormalizedBlockJObservable hP hStruct Q e) Pμ := by
  simpa [limitNormalizedBlockJObservable] using
    Ch04.aemeasurable_blockJSetObservableBlockVec_cubeSet hP Q
      (scalarLimitInvSqrtBlockVec hP hStruct e)
      (scalarLimitSqrtBlockVec hP hStruct e)

theorem map_limitNormalizedBlockJObservable_eq_origin_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {m n : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) n)
    (e : FullBlockVec d) :
    Measure.map (limitNormalizedBlockJObservable hP hStruct R e) Pμ =
      Measure.map (limitNormalizedBlockJObservable hP hStruct (originCube d n) e) Pμ := by
  let Pvec : BlockVec d := scalarLimitInvSqrtBlockVec hP hStruct e
  let Qvec : BlockVec d := scalarLimitSqrtBlockVec hP hStruct e
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => Ch04.blockJSetObservableBlockVec Pvec Qvec U a.toFun
  have hshift :
      cubeSet R =
        translateSet (intVecToRealVec (Ch04.scaleTranslationShift n R))
          (cubeSet (originCube d n)) := by
    exact Ch04.cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
      (d := d) (n := n) (m := m) (R := R) hn hnm hR
  have hX_cov : Ch04.IsRestrictionTranslationCovariant X :=
    Ch04.blockJSetObservableBlockVec_restrictionTranslationCovariant Pvec Qvec
  have hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) Pμ := by
    simpa [X] using
      Ch04.aemeasurable_blockJSetObservableBlockVec_cubeSet hP
        (originCube d n) Pvec Qvec
  calc
    Measure.map (limitNormalizedBlockJObservable hP hStruct R e) Pμ =
        Measure.map (X (cubeSet R)) Pμ := by
          rfl
    _ =
        Measure.map
          (X
            (translateSet (intVecToRealVec (Ch04.scaleTranslationShift n R))
              (cubeSet (originCube d n)))) Pμ := by
          rw [hshift]
    _ = Measure.map (X (cubeSet (originCube d n))) Pμ := by
          exact Ch04.map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
            (P := Pμ) hstat (U := cubeSet (originCube d n))
            hX0_aemeas hX_cov (Ch04.scaleTranslationShift n R)
    _ = Measure.map
        (limitNormalizedBlockJObservable hP hStruct (originCube d n) e) Pμ := by
          rfl

theorem isBigOWith_limitNormalizedBlockJObservable_sub_const_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {σ A c : ℝ}
    {m n : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) n)
    (e : FullBlockVec d)
    (hOrigin :
      IsBigOWith Pμ (gammaSigma σ)
        (fun a => limitNormalizedBlockJObservable hP hStruct (originCube d n) e a - c) A) :
    IsBigOWith Pμ (gammaSigma σ)
      (fun a => limitNormalizedBlockJObservable hP hStruct R e a - c) A := by
  let Pvec : BlockVec d := scalarLimitInvSqrtBlockVec hP hStruct e
  let Qvec : BlockVec d := scalarLimitSqrtBlockVec hP hStruct e
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => Ch04.blockJSetObservableBlockVec Pvec Qvec U a.toFun - c
  let : IsProbabilityMeasure Pμ := hP.isProbability
  have hshift :
      cubeSet R =
        translateSet (intVecToRealVec (Ch04.scaleTranslationShift n R))
          (cubeSet (originCube d n)) := by
    exact Ch04.cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
      (d := d) (n := n) (m := m) (R := R) hn hnm hR
  have hX_cov : Ch04.IsRestrictionTranslationCovariant X := by
    intro U z a
    simp [X, Ch04.blockJSetObservableBlockVec_restrictionTranslationCovariant Pvec Qvec U z a]
  have hXR_aemeas : AEMeasurable (X (cubeSet R)) Pμ := by
    exact (Ch04.aemeasurable_blockJSetObservableBlockVec_cubeSet hP R Pvec Qvec).sub
      aemeasurable_const
  have hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) Pμ := by
    exact
      (Ch04.aemeasurable_blockJSetObservableBlockVec_cubeSet hP
        (originCube d n) Pvec Qvec).sub aemeasurable_const
  have hmap :
      Measure.map (X (cubeSet R)) Pμ =
        Measure.map (X (cubeSet (originCube d n))) Pμ := by
    calc
      Measure.map (X (cubeSet R)) Pμ =
          Measure.map
            (X
              (translateSet (intVecToRealVec (Ch04.scaleTranslationShift n R))
                (cubeSet (originCube d n)))) Pμ := by
            rw [hshift]
      _ = Measure.map (X (cubeSet (originCube d n))) Pμ := by
            exact Ch04.map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
              (P := Pμ) hstat (U := cubeSet (originCube d n))
              hX0_aemeas hX_cov (Ch04.scaleTranslationShift n R)
  have htransfer :=
    Ch04.isBigOWith_gammaSigma_iff_of_map_eq_map_aemeasurable
      (μ := Pμ) (σ := σ) (A := A)
      hXR_aemeas hX0_aemeas hmap
  exact htransfer.2 (by simpa [X, limitNormalizedBlockJObservable, Pvec, Qvec] using hOrigin)

theorem isBigO_limitNormalizedBlockJObservable_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {σ A : ℝ}
    {m n : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) n)
    (e : FullBlockVec d)
    (hOrigin :
      IsBigO Pμ (gammaSigma σ)
        (limitNormalizedBlockJObservable hP hStruct (originCube d n) e) A) :
    IsBigO Pμ (gammaSigma σ)
      (limitNormalizedBlockJObservable hP hStruct R e) A := by
  let : IsProbabilityMeasure Pμ := hP.isProbability
  have hmap :=
    map_limitNormalizedBlockJObservable_eq_origin_of_mem_descendantsAtScale
      hP hStruct hstat hn hnm hR e
  have hXR_aemeas :
      AEMeasurable (limitNormalizedBlockJObservable hP hStruct R e) Pμ :=
    aemeasurable_limitNormalizedBlockJObservable hP hStruct R e
  have hX0_aemeas :
      AEMeasurable
        (limitNormalizedBlockJObservable hP hStruct (originCube d n) e) Pμ :=
    aemeasurable_limitNormalizedBlockJObservable hP hStruct (originCube d n) e
  exact
    (Ch04.isBigO_gammaSigma_iff_of_map_eq_map_aemeasurable
      (μ := Pμ) (σ := σ) (A := A)
      hXR_aemeas hX0_aemeas hmap).2 hOrigin

theorem isBigO_limitNormalizedBlockJObservable_originCube_of_scaleZero
    {d : ℕ} [NeZero d] {σ : ℝ}
    (_hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
        (hPμ : Ch04.RestrictionLawCarrier Pμ)
        (hStruct : Ch04.RestrictionStructuralLaw Pμ)
        (hΓ : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ (e : FullBlockVec d),
        (∀ α : BlockCoord d, |e α| ≤ 1) →
      ∀ {n : ℕ},
        IsBigO Pμ (gammaSigma σ)
          (limitNormalizedBlockJObservable hPμ hStruct
            (originCube d ((n : ℕ) : ℤ)) e)
          (C * hΓ.thetaHat ^ (2 : ℕ)) := by
  let Cdim : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let G : ℝ :=
    Ch04.gammaTriangleConst σ * Cdim *
      (Ch04.gammaMomentConst σ * (params.xi : ℝ) ^ σ⁻¹)
  let C : ℝ := max 1 G
  have hC_pos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 G)
  refine ⟨C, hC_pos, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq hparams e he n
  let : IsProbabilityMeasure Pμ := hPμ.isProbability
  let Pvec : BlockVec d := scalarLimitInvSqrtBlockVec hPμ hStruct e
  let Qvec : BlockVec d := scalarLimitSqrtBlockVec hPμ hStruct e
  let θ : ℝ :=
    Cdim * (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat)
  have hCdim_nonneg : 0 ≤ Cdim := by
    dsimp [Cdim]
    positivity
  have hCdim_pos : 0 < Cdim := by
    dsimp [Cdim]
    positivity
  have hθ0_one : 1 ≤ thetaAtScale hPμ hStruct (0 : ℤ) := by
    simpa using
      Section54.GoodScale.one_le_thetaAtScale_of_P4
        hPμ hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0
  have hθ0_pos : 0 < thetaAtScale hPμ hStruct (0 : ℤ) :=
    lt_of_lt_of_le zero_lt_one hθ0_one
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact mul_pos hCdim_pos (mul_pos hθ0_pos hΓ.thetaHat_pos)
  have hunit :
      IsBigO Pμ (gammaSigma hΓ.sigma)
        (Ch04.blockJObservableCubeSetBlockVec (originCube d 0) Pvec Qvec)
        θ := by
    have htail0 := hΓ.limitNormalizedBlockJObservable_unit_isBigO e he
    simpa [limitNormalizedBlockJObservable, Pvec, Qvec, θ, Cdim] using htail0
  have hn_nonneg : 0 ≤ ((n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hraw :
      IsBigO Pμ (gammaSigma hΓ.sigma)
        (Ch04.blockJObservableCubeSetBlockVec
          (originCube d ((n : ℕ) : ℤ)) Pvec Qvec)
        (Ch04.gammaTriangleConst hΓ.sigma * θ) :=
    Ch04.isBigO_gammaSigma_blockJObservableCubeSetBlockVec_originCube_of_scaleZero
      hPμ hStruct.stationary hΓ.sigma_pos hθ_pos Pvec Qvec hunit hn_nonneg
  have hscale :
      Ch04.gammaTriangleConst hΓ.sigma * θ ≤
        C * hΓ.thetaHat ^ (2 : ℕ) := by
    have htheta_le :
        thetaAtScale hPμ hStruct (0 : ℤ) ≤
          Ch04.gammaMomentConst hΓ.sigma *
            (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat :=
      hΓ.thetaAtScale_zero_le_gammaMomentScale
    have htri_nonneg : 0 ≤ Ch04.gammaTriangleConst hΓ.sigma :=
      (IndependentSums.gammaTriangleConst_pos (σ := hΓ.sigma)).le
    have hthetaHat_nonneg : 0 ≤ hΓ.thetaHat := hΓ.thetaHat_pos.le
    have hleft_le :
        Ch04.gammaTriangleConst hΓ.sigma * θ ≤
          (Ch04.gammaTriangleConst hΓ.sigma * Cdim *
            (Ch04.gammaMomentConst hΓ.sigma *
              (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹)) *
            hΓ.thetaHat ^ (2 : ℕ) := by
      dsimp [θ]
      calc
        Ch04.gammaTriangleConst hΓ.sigma *
            (Cdim * (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat))
            =
          (Ch04.gammaTriangleConst hΓ.sigma * Cdim) *
            (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat) := by
            ring
        _ ≤
          (Ch04.gammaTriangleConst hΓ.sigma * Cdim) *
            ((Ch04.gammaMomentConst hΓ.sigma *
              (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat) *
                hΓ.thetaHat) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right htheta_le hthetaHat_nonneg)
              (mul_nonneg htri_nonneg hCdim_nonneg)
        _ =
          (Ch04.gammaTriangleConst hΓ.sigma * Cdim *
            (Ch04.gammaMomentConst hΓ.sigma *
              (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹)) *
            hΓ.thetaHat ^ (2 : ℕ) := by
            ring
    have hG_le_C :
        Ch04.gammaTriangleConst hΓ.sigma * Cdim *
            (Ch04.gammaMomentConst hΓ.sigma *
              (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹) ≤ C := by
      have hG_eq :
          Ch04.gammaTriangleConst hΓ.sigma * Cdim *
              (Ch04.gammaMomentConst hΓ.sigma *
                (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹) = G := by
        simp [G, hσ_eq, hparams]
      rw [hG_eq]
      exact le_max_right 1 G
    exact hleft_le.trans
      (mul_le_mul_of_nonneg_right hG_le_C (sq_nonneg hΓ.thetaHat))
  have hmono := hraw.mono_scale hscale
  simpa [limitNormalizedBlockJObservable, Pvec, Qvec, hσ_eq] using hmono

theorem localizedLimitNormalizedJMax_sub_const_le_sup_sub
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    {m n : ℕ} (e : FullBlockVec d) (c : ℝ)
    (a : RegCoeffField d) :
    let D : Finset (TriadicCube d) :=
      descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
    ∀ hD : D.Nonempty,
      localizedLimitNormalizedJMax hP hStruct m n e a - c ≤
        D.sup' hD (fun R =>
          limitNormalizedBlockJObservable hP hStruct R e a - c) := by
  intro D hD
  dsimp [localizedLimitNormalizedJMax]
  simp only [D, hD, dite_true]
  have hle :
      D.sup' hD (fun R => limitNormalizedBlockJObservable hP hStruct R e a) ≤
        c + D.sup' hD (fun R =>
          limitNormalizedBlockJObservable hP hStruct R e a - c) := by
    refine Finset.sup'_le hD _ ?_
    intro R hR
    have hR_le :
        limitNormalizedBlockJObservable hP hStruct R e a - c ≤
          D.sup' hD (fun S =>
            limitNormalizedBlockJObservable hP hStruct S e a - c) :=
      Finset.le_sup' (s := D)
        (f := fun S => limitNormalizedBlockJObservable hP hStruct S e a - c)
        hR
    linarith
  linarith

theorem descendantsAtScale_originCube_nat_card_two_le
    {d : ℕ} [NeZero d] {m n : ℕ} (hnm : n < m) :
    2 ≤
      (descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)).card := by
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  let j : ℕ := Int.toNat (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ))
  have hnm_le_int : ((n : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by
    exact_mod_cast (le_of_lt hnm)
  have hcard : D.card = (3 ^ d) ^ j := by
    dsimp [D, j]
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d ((m : ℕ) : ℤ)) hnm_le_int]
    exact descendantsAtDepth_card (originCube d ((m : ℕ) : ℤ))
      (Int.toNat (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)))
  have hj_pos : 0 < j := by
    dsimp [j]
    have hdiff_pos : 0 < (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) :=
      sub_pos.mpr (by exact_mod_cast hnm)
    have hdiff_nonneg : 0 ≤ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) :=
      le_of_lt hdiff_pos
    have hj_cast :
        (Int.toNat (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) : ℤ) =
          (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) :=
      Int.toNat_of_nonneg hdiff_nonneg
    have hj_int_pos :
        (0 : ℤ) <
          (Int.toNat (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) : ℤ) := by
      simpa [hj_cast] using hdiff_pos
    exact_mod_cast hj_int_pos
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hbase_ge_two : 2 ≤ 3 ^ d := by
    have hpow : 3 ^ (1 : ℕ) ≤ 3 ^ d :=
      Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) (by omega : 1 ≤ d)
    norm_num at hpow ⊢
    omega
  have hpow_ge_base : 3 ^ d ≤ (3 ^ d) ^ j := by
    simpa using
      Nat.pow_le_pow_right (by omega : 1 ≤ 3 ^ d) (by omega : 1 ≤ j)
  rw [hcard]
  exact hbase_ge_two.trans hpow_ge_base

theorem isBigO_localizedLimitNormalizedJMax
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
        (hPμ : Ch04.RestrictionLawCarrier Pμ)
        (hStruct : Ch04.RestrictionStructuralLaw Pμ)
        (hΓ : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
      ∀ {m n : ℕ}, n < m →
        let D : Finset (TriadicCube d) :=
          descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        IsBigO Pμ (gammaSigma σ)
          (localizedLimitNormalizedJMax hPμ hStruct m n e)
          (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
            (C * hΓ.thetaHat ^ (2 : ℕ))) := by
  obtain ⟨C, hC_pos, hOrigin⟩ :=
    isBigO_limitNormalizedBlockJObservable_originCube_of_scaleZero
      (d := d) hσ_pos params
  refine ⟨C, hC_pos, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq hparams e he_norm m n hnm
  classical
  let : IsProbabilityMeasure Pμ := hPμ.isProbability
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n)
      (le_of_lt hnm)
  have hcard : 2 ≤ D.card := by
    simpa [D] using descendantsAtScale_originCube_nat_card_two_le
      (d := d) (m := m) (n := n) hnm
  have hn_nonneg : 0 ≤ ((n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hnm_int : ((n : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by
    exact_mod_cast le_of_lt hnm
  have he_coord : ∀ β : BlockCoord d, |e β| ≤ 1 :=
    abs_fullBlockVec_coord_le_one_of_dotProduct_le_one e he_norm
  have hOriginTail :
      IsBigO Pμ (gammaSigma σ)
        (limitNormalizedBlockJObservable hPμ hStruct
          (originCube d ((n : ℕ) : ℤ)) e)
        (C * hΓ.thetaHat ^ (2 : ℕ)) :=
    hOrigin hPμ hStruct hΓ hσ_eq hparams e he_coord
  have htailR :
      ∀ R ∈ D,
        IsBigO Pμ (gammaSigma σ)
          (limitNormalizedBlockJObservable hPμ hStruct R e)
          (C * hΓ.thetaHat ^ (2 : ℕ)) := by
    intro R hR
    exact
      isBigO_limitNormalizedBlockJObservable_of_mem_descendantsAtScale
        hPμ hStruct hStruct.stationary hn_nonneg hnm_int
        (R := R) (by simpa [D] using hR) e hOriginTail
  have hsup :
      IsBigO Pμ (gammaSigma σ)
        (fun a =>
          D.sup' hD (fun R =>
            limitNormalizedBlockJObservable hPμ hStruct R e a))
        (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
          D.sup' hD (fun _R => C * hΓ.thetaHat ^ (2 : ℕ))) := by
    exact Ch04.isBigO_gammaSigma_finset_sup'_of_scales
      (μ := Pμ) (s := D) (hs := hD)
      (X := fun R a => limitNormalizedBlockJObservable hPμ hStruct R e a)
      (a := fun _R => C * hΓ.thetaHat ^ (2 : ℕ))
      (σ := σ) hσ_pos hcard htailR
  have hsup' :
      IsBigO Pμ (gammaSigma σ)
        (fun a =>
          D.sup' hD (fun R =>
            limitNormalizedBlockJObservable hPμ hStruct R e a))
        (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
          (C * hΓ.thetaHat ^ (2 : ℕ))) := by
    simpa using hsup
  refine hsup'.of_abs_le ?_
  intro a
  have heq :
      localizedLimitNormalizedJMax hPμ hStruct m n e a =
        D.sup' hD (fun R =>
          limitNormalizedBlockJObservable hPμ hStruct R e a) := by
    dsimp [localizedLimitNormalizedJMax]
    simp [D, hD]
  rw [heq]

theorem isBigOWith_localizedLimitNormalizedJMax_sub_const
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {σ A c : ℝ} (hσ : 0 < σ)
    {m n : ℕ} (hnm : n < m)
    (e : FullBlockVec d)
    (hOrigin :
      IsBigOWith Pμ (gammaSigma σ)
        (fun a =>
          limitNormalizedBlockJObservable hP hStruct
            (originCube d ((n : ℕ) : ℤ)) e a - c) A) :
    IsBigOWith Pμ (gammaSigma σ)
      (fun a => localizedLimitNormalizedJMax hP hStruct m n e a - c)
      (((3 * Real.log
        ((descendantsAtScale
          (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)).card : ℝ)) ^ σ⁻¹) * A) := by
  classical
  let : IsProbabilityMeasure Pμ := hP.isProbability
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n)
      (le_of_lt hnm)
  have hcard : 2 ≤ D.card := by
    simpa [D] using descendantsAtScale_originCube_nat_card_two_le
      (d := d) (m := m) (n := n) hnm
  have hn_nonneg : 0 ≤ ((n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hnm_int : ((n : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by
    exact_mod_cast le_of_lt hnm
  have htailR :
      ∀ R ∈ D,
        IsBigOWith Pμ (gammaSigma σ)
          (fun a => limitNormalizedBlockJObservable hP hStruct R e a - c) A := by
    intro R hR
    exact
      isBigOWith_limitNormalizedBlockJObservable_sub_const_of_mem_descendantsAtScale
        hP hStruct hstat hn_nonneg hnm_int
        (R := R) (by simpa [D] using hR) e hOrigin
  have hsup :
      IsBigOWith Pμ (gammaSigma σ)
        (fun a =>
          D.sup' hD (fun R =>
            limitNormalizedBlockJObservable hP hStruct R e a - c))
        (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) * A) := by
    exact Ch04.isBigOWith_gammaSigma_finset_sup'
      (μ := Pμ) (s := D) (hs := hD)
      (X := fun R a => limitNormalizedBlockJObservable hP hStruct R e a - c)
      (A := A) (σ := σ) hσ hcard htailR
  refine hsup.of_le ?_
  intro a
  exact localizedLimitNormalizedJMax_sub_const_le_sup_sub
    hP hStruct (m := m) (n := n) e c a hD

/-- Localized version of Corollary `c.first.quenched.estimate` for a fixed
unit vector.  The finite maximum over descendants costs only the standard
`(log #D)^{1/(σ∧2)}` factor. -/
theorem localizedFirstQuenchedEstimate_limitNormalized
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry α : ℝ, 0 < Cfluct ∧ 0 < Centry ∧ 0 < α ∧
      ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
        (hPμ : Ch04.RestrictionLawCarrier Pμ)
        (hStruct : Ch04.RestrictionStructuralLaw Pμ)
        (hΓ : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
      ∀ {ℓ n m : ℕ}, ℓ < n → n < m →
        let N0 : ℕ :=
          annealedAlgebraicEntryScale Pμ
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        IsBigOWith Pμ (gammaSigma (min σ 2))
          (fun a =>
            localizedLimitNormalizedJMax hPμ hStruct (N0 + m) (N0 + n) e a -
              Real.rpow (3 : ℝ) (-α * (ℓ : ℝ)))
          (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
            (Cfluct *
              (3 : ℝ) ^
                (-(d : ℝ) / 2 *
                  (Int.toNat
                    ((((N0 + n : ℕ) : ℤ) -
                      ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
              hΓ.thetaHat ^ (2 : ℕ))) := by
  obtain ⟨Cfluct, Centry, α, hCfluct, hCentry, hα, hfirst⟩ :=
    firstQuenchedEstimate_limitNormalized (d := d) hσ_pos params
  refine ⟨Cfluct, Centry, α, hCfluct, hCentry, hα, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq hparams e he_norm ℓ n m hℓn hnm
  let : IsProbabilityMeasure Pμ := hPμ.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale Pμ
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  have hσconc_pos : 0 < min σ 2 :=
    lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hOrigin :
      IsBigOWith Pμ (gammaSigma (min σ 2))
        (fun a =>
          limitNormalizedBlockJObservable hPμ hStruct
              (originCube d ((N0 + n : ℕ) : ℤ)) e a -
            Real.rpow (3 : ℝ) (-α * (ℓ : ℝ)))
        (Cfluct *
          (3 : ℝ) ^
            (-(d : ℝ) / 2 *
              (Int.toNat
                ((((N0 + n : ℕ) : ℤ) -
                  ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)) := by
    simpa [N0] using
      hfirst hPμ hStruct hΓ hσ_eq hparams e he_norm hℓn
  have hnm_abs : N0 + n < N0 + m := Nat.add_lt_add_left hnm N0
  simpa [N0, D] using
    isBigOWith_localizedLimitNormalizedJMax_sub_const
      hPμ hStruct hStruct.stationary hσconc_pos hnm_abs e hOrigin

/-- Uniform-in-`σ` version of
`localizedFirstQuenchedEstimate_limitNormalized`.

The entry constant and annealed algebraic exponent are fixed before the finite
moment exponent; the localized fluctuation constant remains allowed to depend
on `σ`. -/
theorem localizedFirstQuenchedEstimate_limitNormalized_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct : ℝ, 0 < Cfluct ∧
          ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
            (hPμ : Ch04.RestrictionLawCarrier Pμ)
            (hStruct : Ch04.RestrictionStructuralLaw Pμ)
            (hΓ : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ {ℓ n m : ℕ}, ℓ < n → n < m →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale Pμ
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let D : Finset (TriadicCube d) :=
              descendantsAtScale
                (originCube d (((N0 + m : ℕ) : ℤ)))
                (((N0 + n : ℕ) : ℤ))
            IsBigOWith Pμ (gammaSigma (min σ 2))
              (fun aω =>
                localizedLimitNormalizedJMax hPμ hStruct
                    (N0 + m) (N0 + n) e aω -
                  Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)))
              (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
                (Cfluct *
                  (3 : ℝ) ^
                    (-(d : ℝ) / 2 *
                      (Int.toNat
                        ((((N0 + n : ℕ) : ℤ) -
                          ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
                  hΓ.thetaHat ^ (2 : ℕ))) := by
  obtain ⟨Centry, a, hCentry, ha, hfirstBase⟩ :=
    firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, hCfluct, hfirst⟩ := hfirstBase hσ_pos
  refine ⟨Cfluct, hCfluct, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq hparams e he_norm ℓ n m hℓn hnm
  let : IsProbabilityMeasure Pμ := hPμ.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale Pμ
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  have hσconc_pos : 0 < min σ 2 :=
    lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hOrigin :
      IsBigOWith Pμ (gammaSigma (min σ 2))
        (fun aω =>
          limitNormalizedBlockJObservable hPμ hStruct
              (originCube d ((N0 + n : ℕ) : ℤ)) e aω -
            Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)))
        (Cfluct *
          (3 : ℝ) ^
            (-(d : ℝ) / 2 *
              (Int.toNat
                ((((N0 + n : ℕ) : ℤ) -
                  ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)) := by
    simpa [N0] using
      hfirst hPμ hStruct hΓ hσ_eq hparams e he_norm hℓn
  have hnm_abs : N0 + n < N0 + m := Nat.add_lt_add_left hnm N0
  simpa [N0, D] using
    isBigOWith_localizedLimitNormalizedJMax_sub_const
      hPμ hStruct hStruct.stationary hσconc_pos hnm_abs e hOrigin

end

end Section57
end Ch05
end Book
end Homogenization
