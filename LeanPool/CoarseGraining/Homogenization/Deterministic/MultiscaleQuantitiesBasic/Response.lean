/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.HodgeCubeBridge

/-! # Response -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped Matrix.Norms.Frobenius
open scoped MatrixOrder

/-!
# Response and scale-response infrastructure
-/

theorem normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    normalizedBlockResponseMax R a a0 ≤ maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSsup
  have hBdd :
      BddAbove
        ((fun S => normalizedBlockResponseMax S a a0) '' (↑(descendantsAtScale Q k) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun S => normalizedBlockResponseMax S a a0)).bddAbove
  exact le_csSup hBdd ⟨R, hR, rfl⟩

theorem normalizedBlockResponseValueSet_nonempty {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) :
    (normalizedBlockResponseValueSet Q a a0).Nonempty := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let i0 : BlockCoord d := Sum.inl ⟨0, hd⟩
  let e : FullBlockVec d := Pi.single i0 1
  refine ⟨BlockJ (cubeSet Q)
    (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
    (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
    a, ?_⟩
  refine ⟨e, ?_, rfl⟩
  unfold fullBlockVecNormSq e
  rw [Fintype.sum_eq_single i0]
  · simp
  · intro b hb
    simp [hb]

theorem normalizedBlockResponseValueSet_bddAbove_of_isEllipticFieldOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    BddAbove (normalizedBlockResponseValueSet Q a a0) := by
  let MInv := constantFullBlockMatrixInvSqrt a0
  let MSqrt := constantFullBlockMatrixSqrt a0
  let B : ℝ :=
    (lam / (1 + 2 * Lam ^ 2))⁻¹ * fullBlockMatRowAbsSqBound MSqrt +
      (lam / (1 + 2 * Lam ^ 2))⁻¹ *
        blockMatrixOfCoeffNormSqBound lam Lam * fullBlockMatRowAbsSqBound MInv
  refine ⟨B, ?_⟩
  rintro m ⟨e, he, rfl⟩
  let xQ : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hxQ : xQ ∈ cubeSet Q := by
    intro i
    constructor <;> dsimp [xQ]
    · have hscale : 0 < cubeScaleFactor Q := by
        simpa [cubeScaleFactor] using zpow_pos (by norm_num : 0 < (3 : ℝ)) Q.scale
      nlinarith
    · have hscale : 0 < cubeScaleFactor Q := by
        simpa [cubeScaleFactor] using zpow_pos (by norm_num : 0 < (3 : ℝ)) Q.scale
      nlinarith
  rcases hEll.2 xQ hxQ with ⟨hlam_pos, hlamLam, -, -⟩
  have hvolQ : (MeasureTheory.volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hcoeff_nonneg : 0 ≤ (lam / (1 + 2 * Lam ^ 2))⁻¹ := by
    have hden_pos : 0 < 1 + 2 * Lam ^ 2 := by positivity
    have hfrac_pos : 0 < lam / (1 + 2 * Lam ^ 2) := by
      exact div_pos hlam_pos hden_pos
    positivity
  have hbound_nonneg : 0 ≤ blockMatrixOfCoeffNormSqBound lam Lam := by
    unfold blockMatrixOfCoeffNormSqBound
    positivity
  let P := ofFullBlockVec (Matrix.mulVec MInv e)
  let Q' := ofFullBlockVec (Matrix.mulVec MSqrt e)
  have hP :
      blockVecDot P P ≤ fullBlockMatRowAbsSqBound MInv := by
    dsimp [P, MInv]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  have hQ :
      blockVecDot Q' Q' ≤ fullBlockMatRowAbsSqBound MSqrt := by
    dsimp [Q', MSqrt]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  calc
    BlockJ (cubeSet Q) P Q' a ≤ blockResponsePlainUpperBound lam Lam P Q' := by
      exact blockJ_le_plainUpperBound_of_isEllipticFieldOn
        (a := a) (U := cubeSet Q) (measurableSet_cubeSet Q) hEll hvolQ P Q'
    _ ≤ B := by
      let c : ℝ := (lam / (1 + 2 * Lam ^ 2))⁻¹
      have htermQ :
          c * blockVecDot Q' Q' ≤ c * fullBlockMatRowAbsSqBound MSqrt := by
        exact mul_le_mul_of_nonneg_left hQ hcoeff_nonneg
      have htermP :
          c * blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot P P ≤
            c * blockMatrixOfCoeffNormSqBound lam Lam * fullBlockMatRowAbsSqBound MInv := by
        exact mul_le_mul_of_nonneg_left hP (mul_nonneg hcoeff_nonneg hbound_nonneg)
      dsimp [B]
      unfold blockResponsePlainUpperBound
      dsimp [c] at htermQ htermP
      linarith

theorem ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube_reproved {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (p q : Vec d) (a : CoeffField d) :
    ResponseJ (cubeSet Q) p q a = ResponseJ (openCubeSet Q) p q a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hcube :
      cubeSet Q = translateSet z (cubeSet (originCube d Q.scale)) := by
    simpa [z] using! cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hopen :
      openCubeSet Q = translateSet z (openCubeSet (originCube d Q.scale)) := by
    simpa [z] using! openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  calc
    ResponseJ (cubeSet Q) p q a
        = ResponseJ (translateSet z (cubeSet (originCube d Q.scale))) p q a := by
            rw [hcube]
    _ = ResponseJ (cubeSet (originCube d Q.scale)) p q (translateCoeffField z a) := by
          exact ResponseJ_translateSet_eq_translateCoeffField z
            (cubeSet (originCube d Q.scale)) p q a
    _ = ResponseJ (openCubeSet (originCube d Q.scale)) p q (translateCoeffField z a) := by
          exact ResponseJ_cubeSet_originCube_eq_openCubeSet
            (d := d) (n := Q.scale) p q (translateCoeffField z a)
    _ = ResponseJ (translateSet z (openCubeSet (originCube d Q.scale))) p q a := by
          symm
          exact ResponseJ_translateSet_eq_translateCoeffField z
            (openCubeSet (originCube d Q.scale)) p q a
    _ = ResponseJ (openCubeSet Q) p q a := by
          rw [hopen]

theorem normalizedBlockResponseValueSet_eq_half_responseJ_adjoint_sum_set_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))]
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    normalizedBlockResponseValueSet Q a a0 =
      { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
          let P :=
            ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
          let Q' :=
            ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
          m =
            (1 / 2 : ℝ) * ResponseJ (cubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a +
              (1 / 2 : ℝ) *
                ResponseJ (cubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2)
                  (Homogenization.adjointCoeffField a) } := by
  ext m
  constructor
  · rintro ⟨e, he, rfl⟩
    let P := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
    let Q' := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
    have hvol : (MeasureTheory.volume (cubeSet Q)).toReal ≠ 0 := by
      rw [volume_cubeSet_toReal]
      exact (cubeVolume_pos Q).ne'
    refine ⟨e, he, ?_⟩
    dsimp [P, Q']
    simpa using
      (blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
        (a := a) (U := cubeSet Q) (measurableSet_cubeSet Q) hEll hvol
        (p := P.1) (pStar := Q'.2) (q := P.2) (qStar := Q'.1))
  · rintro ⟨e, he, hm⟩
    refine ⟨e, he, ?_⟩
    let P := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
    let Q' := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
    have hvol : (MeasureTheory.volume (cubeSet Q)).toReal ≠ 0 := by
      rw [volume_cubeSet_toReal]
      exact (cubeVolume_pos Q).ne'
    dsimp [P, Q'] at hm ⊢
    rw [blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
      (a := a) (U := cubeSet Q) (measurableSet_cubeSet Q) hEll hvol
      (p := P.1) (pStar := Q'.2) (q := P.2) (qStar := Q'.1)]
    exact hm

theorem normalizedBlockResponseMax_eq_sSup_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))]
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    normalizedBlockResponseMax Q a a0 =
      sSup
        { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
            let P :=
              ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
            let Q' :=
              ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
            m =
              (1 / 2 : ℝ) * ResponseJ (cubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a +
                (1 / 2 : ℝ) *
                  ResponseJ (cubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2)
                    (Homogenization.adjointCoeffField a) } := by
  unfold normalizedBlockResponseMax
  rw [normalizedBlockResponseValueSet_eq_half_responseJ_adjoint_sum_set_of_isEllipticFieldOn
    Q a a0 hEll]

theorem scaleResponseAtScale_infinity_self_eq_rpow_half_sSup_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q))]
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    scaleResponseAtScale Q Q.scale .infinity a a0 =
      Real.rpow
        (sSup
          { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
              let P :=
                ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
              let Q' :=
                ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
              m =
                (1 / 2 : ℝ) * ResponseJ (cubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a +
                  (1 / 2 : ℝ) *
                    ResponseJ (cubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2)
                      (Homogenization.adjointCoeffField a) }) (1 / 2 : ℝ) := by
  rw [scaleResponseAtScale_infinity_self_eq,
    normalizedBlockResponseMax_eq_sSup_half_responseJ_adjoint_sum_of_isEllipticFieldOn
      Q a a0 hEll]

theorem normalizedBlockResponseMax_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) :
    0 ≤ normalizedBlockResponseMax Q a a0 := by
  unfold normalizedBlockResponseMax
  refine Real.sSup_nonneg ?_
  rintro x ⟨e, -, rfl⟩
  exact blockJ_nonneg
    (cubeSet Q)
    (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
    (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
    a

theorem maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k l : ℤ} (a : CoeffField d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    maxDescendantNormalizedBlockResponseAtScale R l a a0 ≤
      maxDescendantNormalizedBlockResponseAtScale Q l a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSsup
  have hne :
      ((fun S => normalizedBlockResponseMax S a a0) ''
        (↑(descendantsAtScale R l) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty R hl with ⟨S, hS⟩
    exact ⟨normalizedBlockResponseMax S a a0, ⟨S, hS, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨S, hS, rfl⟩
  have hBdd :
      BddAbove
        ((fun T => normalizedBlockResponseMax T a a0) ''
          (↑(descendantsAtScale Q l) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun T => normalizedBlockResponseMax T a a0)).bddAbove
  exact le_csSup hBdd ⟨S, mem_descendantsAtScale_trans hR hS, rfl⟩

theorem normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    normalizedBlockResponseMax Q a a0 ≤
      maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  classical
  let := isFiniteMeasureVolumeMeasureOnCubeSet Q
  let j : ℕ := Int.toNat (Q.scale - k)
  have hj : (j : ℤ) = Q.scale - k := by
    dsimp [j]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hEllOpen :
      IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet Q)
      (openCubeSet_subset_cubeSet Q)
  have hEllOpenAdj :
      IsEllipticFieldOn lam Lam (openCubeSet Q) (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEllOpen
  have hvolQ : (MeasureTheory.volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  unfold normalizedBlockResponseMax
  refine csSup_le (normalizedBlockResponseValueSet_nonempty Q a a0) ?_
  rintro x ⟨e, he, rfl⟩
  let P := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
  let Q' := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
  let F : TriadicCube d → ℝ := fun R =>
    ResponseJ (openCubeSet R) (P.1 - Q'.2) (Q'.1 - P.2) a
  let G : TriadicCube d → ℝ := fun R =>
    ResponseJ (openCubeSet R) (Q'.2 + P.1) (Q'.1 + P.2) (Homogenization.adjointCoeffField a)
  have hresp :
      BlockJ (cubeSet Q) P Q' a ≤
        descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
    have hrespF :
        ResponseJ (cubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a ≤
          descendantsAverage Q j F := by
      calc
        ResponseJ (cubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a
            = ResponseJ (openCubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a := by
                exact ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube Q
                  (P.1 - Q'.2) (Q'.1 - P.2) a
        _ ≤ descendantsAverage Q j F := by
              exact responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
                j Q a hEllOpen (P.1 - Q'.2) (Q'.1 - P.2)
    have hrespG :
        ResponseJ (cubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2) (Homogenization.adjointCoeffField a) ≤
          descendantsAverage Q j G := by
      calc
        ResponseJ (cubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2) (Homogenization.adjointCoeffField a)
            =
              ResponseJ (openCubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2)
                (Homogenization.adjointCoeffField a) := by
                  exact ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube Q
                    (Q'.2 + P.1) (Q'.1 + P.2) (Homogenization.adjointCoeffField a)
        _ ≤ descendantsAverage Q j G := by
              exact responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
                j Q (Homogenization.adjointCoeffField a) hEllOpenAdj
                (Q'.2 + P.1) (Q'.1 + P.2)
    have hcombine :
        (1 / 2 : ℝ) * descendantsAverage Q j F + (1 / 2 : ℝ) * descendantsAverage Q j G =
          descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
      calc
        (1 / 2 : ℝ) * descendantsAverage Q j F + (1 / 2 : ℝ) * descendantsAverage Q j G
            = descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R) +
                descendantsAverage Q j (fun R => (1 / 2 : ℝ) * G R) := by
                  rw [descendantsAverage_smul, descendantsAverage_smul]
        _ = descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
              symm
              exact descendantsAverage_add Q j
                (fun R => (1 / 2 : ℝ) * F R) (fun R => (1 / 2 : ℝ) * G R)
    calc
      BlockJ (cubeSet Q) P Q' a
        ≤ (1 / 2 : ℝ) * ResponseJ (cubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a +
            (1 / 2 : ℝ) *
              ResponseJ (cubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2)
                (Homogenization.adjointCoeffField a) := by
            exact blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
              (a := a) (U := cubeSet Q) (measurableSet_cubeSet Q) hEll hvolQ
              (p := P.1) (pStar := Q'.2) (q := P.2) (qStar := Q'.1) |>.le
      _ ≤ (1 / 2 : ℝ) * descendantsAverage Q j F + (1 / 2 : ℝ) * descendantsAverage Q j G := by
            linarith
      _ = descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := hcombine
  have hpointwise :
      ∀ R ∈ descendantsAtDepth Q j,
        (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R ≤ normalizedBlockResponseMax R a a0 := by
    intro R hR
    have hRk : R ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa [j] using hR
    let := isFiniteMeasureVolumeMeasureOnCubeSet R
    have hEllR :
        IsEllipticFieldOn lam Lam (cubeSet R) a :=
      IsEllipticFieldOn.mono hEll (measurableSet_cubeSet R)
        (cubeSet_subset_of_mem_descendantsAtScale hk hRk)
    have hvolR : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
      rw [volume_cubeSet_toReal]
      exact (cubeVolume_pos R).ne'
    have hblock :
        (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R ≤ BlockJ (cubeSet R) P Q' a := by
      calc
        (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R
            =
              (1 / 2 : ℝ) * ResponseJ (cubeSet R) (P.1 - Q'.2) (Q'.1 - P.2) a +
                (1 / 2 : ℝ) *
                  ResponseJ (cubeSet R) (Q'.2 + P.1) (Q'.1 + P.2)
                    (Homogenization.adjointCoeffField a) := by
                      rw [ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube R
                        (P.1 - Q'.2) (Q'.1 - P.2) a,
                        ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube R
                        (Q'.2 + P.1) (Q'.1 + P.2) (Homogenization.adjointCoeffField a)]
        _ ≤ BlockJ (cubeSet R) P Q' a := by
              exact half_responseJ_adjoint_sum_le_blockJ_of_isEllipticFieldOn
                (a := a) (U := cubeSet R) (measurableSet_cubeSet R) hEllR hvolR
                (p := P.1) (pStar := Q'.2) (q := P.2) (qStar := Q'.1)
    have hmem : BlockJ (cubeSet R) P Q' a ∈ normalizedBlockResponseValueSet R a a0 := by
      refine ⟨e, he, ?_⟩
      dsimp [P, Q']
    exact le_trans hblock (by
      unfold normalizedBlockResponseMax
      exact le_csSup
        (normalizedBlockResponseValueSet_bddAbove_of_isEllipticFieldOn
          R a a0 hEllR) hmem)
  have havg :
      descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) ≤
        descendantsAverage Q j (fun R => normalizedBlockResponseMax R a a0) := by
    unfold descendantsAverage
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · refine Finset.sum_le_sum ?_
      intro R hR
      exact hpointwise R hR
    · positivity
  have hmax :
      descendantsAverage Q j (fun R => normalizedBlockResponseMax R a a0) ≤
        maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
    unfold maxDescendantNormalizedBlockResponseAtScale
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
    simpa [j] using
      (descendantsAverage_le_finsetSsup Q j (fun R => normalizedBlockResponseMax R a a0))
  exact le_trans hresp (le_trans havg hmax)

theorem maxDescendantNormalizedBlockResponseAtScale_le_of_le_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k l : ℤ}
    (hkl : k ≤ l) (hlQ : l ≤ Q.scale) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    maxDescendantNormalizedBlockResponseAtScale Q l a a0 ≤
      maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSsup
  have hne :
      ((fun R => normalizedBlockResponseMax R a a0) ''
        (↑(descendantsAtScale Q l) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hlQ with ⟨R, hR⟩
    exact ⟨normalizedBlockResponseMax R a a0, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hRscale : R.scale = l := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hkR : k ≤ R.scale := by
    simpa [hRscale] using hkl
  have hEllR :
      IsEllipticFieldOn lam Lam (cubeSet R) a :=
    IsEllipticFieldOn.mono hEll (measurableSet_cubeSet R)
      (cubeSet_subset_of_mem_descendantsAtScale hlQ hR)
  have hRle :
      normalizedBlockResponseMax R a a0 ≤
        maxDescendantNormalizedBlockResponseAtScale R k a a0 :=
    normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale_of_isEllipticFieldOn
      (Q := R) (k := k) hkR a a0 hEllR
  have hRQ :
      maxDescendantNormalizedBlockResponseAtScale R k a a0 ≤
        maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
    exact maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := l) (l := k) a a0 hR hkR
  exact le_trans hRle hRQ

theorem maxDescendantBBlockNormAtScale_le_of_le_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k l : ℤ}
    (hkl : k ≤ l) (hlQ : l ≤ Q.scale) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    maxDescendantBBlockNormAtScale Q l a ≤ maxDescendantBBlockNormAtScale Q k a := by
  unfold maxDescendantBBlockNormAtScale finsetSsup
  have hne :
      ((fun R => coarseBBlockNorm R a) ''
        (↑(descendantsAtScale Q l) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hlQ with ⟨R, hR⟩
    exact ⟨coarseBBlockNorm R a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hRscale : R.scale = l := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hkR : k ≤ R.scale := by
    simpa [hRscale] using hkl
  have hEllR :
      IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtScale hlQ hR)
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    hData.of_mem_descendantsAtScale hlQ hR
  have hRle :
      coarseBBlockNorm R a ≤ maxDescendantBBlockNormAtScale R k a :=
    coarseBBlockNorm_le_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := R) (k := k) hkR a hEllR hDataR
  have hRQ :
      maxDescendantBBlockNormAtScale R k a ≤ maxDescendantBBlockNormAtScale Q k a := by
    exact maxDescendantBBlockNormAtScale_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := l) (l := k) a hR hkR
  exact le_trans hRle hRQ

theorem maxDescendantSigmaStarInvNormAtScale_le_of_le_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k l : ℤ}
    (hkl : k ≤ l) (hlQ : l ≤ Q.scale) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    maxDescendantSigmaStarInvNormAtScale Q l a ≤
      maxDescendantSigmaStarInvNormAtScale Q k a := by
  unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
  have hne :
      ((fun R => coarseSigmaStarInvBlockNorm R a) ''
        (↑(descendantsAtScale Q l) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hlQ with ⟨R, hR⟩
    exact ⟨coarseSigmaStarInvBlockNorm R a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hRscale : R.scale = l := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hkR : k ≤ R.scale := by
    simpa [hRscale] using hkl
  have hEllR :
      IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtScale hlQ hR)
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    hData.of_mem_descendantsAtScale hlQ hR
  have hRle :
      coarseSigmaStarInvBlockNorm R a ≤ maxDescendantSigmaStarInvNormAtScale R k a :=
    coarseSigmaStarInvBlockNorm_le_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := R) (k := k) hkR a hEllR hDataR
  have hRQ :
      maxDescendantSigmaStarInvNormAtScale R k a ≤
        maxDescendantSigmaStarInvNormAtScale Q k a := by
    exact maxDescendantSigmaStarInvNormAtScale_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := l) (l := k) a hR hkR
  exact le_trans hRle hRQ

theorem maxDescendantBBlockNormAtScale_nonneg {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) :
    0 ≤ maxDescendantBBlockNormAtScale Q k a := by
  rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
  exact le_trans (coarseBBlockNorm_nonneg R a)
    (coarseBBlockNorm_le_maxDescendantBBlockNormAtScale a hR)

theorem maxDescendantSigmaStarInvNormAtScale_nonneg {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) :
    0 ≤ maxDescendantSigmaStarInvNormAtScale Q k a := by
  rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
  exact le_trans (coarseSigmaStarInvBlockNorm_nonneg R a)
    (coarseSigmaStarInvBlockNorm_le_maxDescendantSigmaStarInvNormAtScale a hR)

theorem maxDescendantNormalizedBlockResponseAtScale_nonneg {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (a0 : Mat d) :
    0 ≤ maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
  exact le_trans (normalizedBlockResponseMax_nonneg R a a0)
    (normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale a a0 hR)

theorem scaleResponseAtScale_infinity_nonneg {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (a0 : Mat d) :
    0 ≤ scaleResponseAtScale Q k .infinity a a0 := by
  rw [scaleResponseAtScale_infinity_eq]
  exact Real.rpow_nonneg
    (maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk a a0) _

theorem scaleResponseAtScale_infinity_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k l : ℤ} (a : CoeffField d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    scaleResponseAtScale R l .infinity a a0 ≤ scaleResponseAtScale Q l .infinity a a0 := by
  rw [scaleResponseAtScale_infinity_eq, scaleResponseAtScale_infinity_eq]
  refine Real.rpow_le_rpow
    (maxDescendantNormalizedBlockResponseAtScale_nonneg R hl a a0)
    (maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale a a0 hR hl) ?_
  norm_num

theorem scaleResponseAtScale_infinity_le_of_le_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k l : ℤ}
    (hkl : k ≤ l) (hlQ : l ≤ Q.scale) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    scaleResponseAtScale Q l .infinity a a0 ≤
      scaleResponseAtScale Q k .infinity a a0 := by
  rw [scaleResponseAtScale_infinity_eq, scaleResponseAtScale_infinity_eq]
  refine Real.rpow_le_rpow
    (maxDescendantNormalizedBlockResponseAtScale_nonneg Q hlQ a a0)
    (maxDescendantNormalizedBlockResponseAtScale_le_of_le_of_isEllipticFieldOn
      (Q := Q) (k := k) (l := l) hkl hlQ a a0 hEll) ?_
  norm_num

theorem scaleResponseAtScale_infinity_self_le_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    scaleResponseAtScale Q Q.scale .infinity a a0 ≤
      scaleResponseAtScale Q k .infinity a a0 := by
  rw [scaleResponseAtScale_infinity_self_eq, scaleResponseAtScale_infinity_eq]
  refine Real.rpow_le_rpow (normalizedBlockResponseMax_nonneg Q a a0) ?_ ?_
  · have hmax :
        maxDescendantNormalizedBlockResponseAtScale Q Q.scale a a0 ≤
          maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
      exact maxDescendantNormalizedBlockResponseAtScale_le_of_le_of_isEllipticFieldOn
        (Q := Q) (k := k) (l := Q.scale) hk le_rfl a a0
        hEll
    simpa [maxDescendantNormalizedBlockResponseAtScale_self] using hmax
  · norm_num

theorem scaleResponseAtScale_infinity_self_le_homogenizationErrorOnCube_infinity_one_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) {lam Lam : ℝ} (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    scaleResponseAtScale Q Q.scale .infinity a a0 ≤
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  let c : ℝ := scaleResponseAtScale Q Q.scale .infinity a a0
  let g : ℕ → ℝ := fun n => geometricWeight s 1 n * c
  let f : ℕ → ℝ := fun n =>
    geometricWeight s 1 n * scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0
  have hgSummable : Summable g := by
    dsimp [g]
    exact (summable_geometricWeight_one hs).mul_right c
  have hterm : ∀ n : ℕ, g n ≤ f n := by
    intro n
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hresp :
        scaleResponseAtScale Q Q.scale .infinity a a0 ≤
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0 := by
      exact scaleResponseAtScale_infinity_self_le_of_isEllipticFieldOn
        Q hk a a0 hEll
    dsimp [g, f]
    exact mul_le_mul_of_nonneg_left hresp (geometricWeight_nonneg n (by simpa using hs.le))
  have hsumLe : ∑' n : ℕ, g n ≤ ∑' n : ℕ, f n :=
    Summable.tsum_le_tsum hterm hgSummable hsum
  have hgEq : ∑' n : ℕ, g n = c := by
    dsimp [g, c]
    rw [tsum_mul_right, tsum_geometricWeight_one_eq_one hs, one_mul]
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
  calc
    scaleResponseAtScale Q Q.scale .infinity a a0 = ∑' n : ℕ, g n := by
      exact hgEq.symm
    _ ≤ ∑' n : ℕ, f n := hsumLe

theorem homogenizationErrorOnCube_infinity_one_le_of_lt_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {t s : ℝ} {lam Lam : ℝ} (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 ≤
      HomogenizationErrorOnCube Q t .infinity (.finite 1) a a0 := by
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum,
    homogenizationErrorOnCube_infinity_one_eq_tsum]
  refine tsum_geometricWeight_one_le_of_monotone ?_ ?_ ht hts hsum_t
  · intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by
      linarith
    have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
    exact scaleResponseAtScale_infinity_le_of_le_of_isEllipticFieldOn
      (Q := Q) (k := Q.scale - (n : ℤ)) (l := Q.scale - (m : ℤ))
      hkl hlQ a a0
      hEll
  · intro n
    exact scaleResponseAtScale_infinity_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0

end

end Homogenization
