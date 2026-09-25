/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue

/-! # Public RHSScalar -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public RHS Scalar Bounds for Coarse Caccioppoli with RHS

This file is split mechanically out of `CoarseCaccioppoliRHS.lean`.

## Audit tag

Claim: prove nonnegativity and scalar monotonicity facts for the public
`boundaryCaccioppoliWithRHSRHS` terms.

Downstream target: `CoarseCaccioppoliRHS/FinalBounds.lean`.  This file should
contain scalar RHS bounds only; public theorem packages belong in
`CoarseCaccioppoliRHS/Theory.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- The forcing-only term inside `boundaryCaccioppoliWithRHSRHS` is
nonnegative. -/
theorem boundaryCaccioppoliWithRHS_forceTerm_nonneg
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {t : ℝ} {g : Vec d → Vec d}
    (ht : 0 < t) (ht_lt : t < 1 / 2) :
    0 ≤
      (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
        Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2 := by
  have hden_pos : 0 < 1 - 2 * t := by linarith
  have hlambda_pos : 0 < Ch02.lambdaS Q t a := by
    unfold Ch02.lambdaS
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)
  have ht_rpow_nonneg : 0 ≤ Real.rpow t (-8 : ℝ) :=
    Real.rpow_nonneg ht.le _
  have hdiv_nonneg : 0 ≤ Real.rpow t (-8 : ℝ) / (1 - 2 * t) :=
    div_nonneg ht_rpow_nonneg hden_pos.le
  have hlambda_factor_nonneg :
      0 ≤ Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) :=
    Real.rpow_nonneg hlambda_pos.le _
  exact mul_nonneg (mul_nonneg hdiv_nonneg hlambda_factor_nonneg)
    (sq_nonneg (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g))

private theorem boundaryCaccioppoliWithRHS_parentTerm_nonneg
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g) (ht : 0 < t) :
    0 ≤
      Ch02.lambdaS Q t a *
        Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
        boundaryForcedCaccioppoliParentL2Sq u := by
  have hlambda : 0 ≤ Ch02.lambdaS Q t a := by
    unfold Ch02.lambdaS
    exact (Ch02.lambdaSq_finite_pos Q a ht
      (by norm_num : (1 : ℝ) ≤ 1)).le
  have hscale :
      0 ≤ Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hparent :
      0 ≤ boundaryForcedCaccioppoliParentL2Sq u :=
    normalizedL2SqOnSet_nonneg (openCubeSet Q) u.toH1.toFun
      (measurableSet_openCubeSet Q)
  exact mul_nonneg (mul_nonneg hlambda hscale) hparent

/-- The displayed forced boundary Caccioppoli RHS is nonnegative in the theorem
range. -/
theorem boundaryCaccioppoliWithRHSRHS_nonneg
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) :
    0 ≤ boundaryCaccioppoliWithRHSRHS C s t u := by
  let P : ℝ := caccioppoliWithRHSPrefactor C Q a s t
  let A : ℝ :=
    Ch02.lambdaS Q t a *
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
      boundaryForcedCaccioppoliParentL2Sq u
  let B : ℝ :=
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact caccioppoliWithRHSPrefactor_nonneg hC_nonneg hs ht hst
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using boundaryCaccioppoliWithRHS_parentTerm_nonneg (Q := Q) (a := a) u ht
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact boundaryCaccioppoliWithRHS_forceTerm_nonneg
      (Q := Q) (a := a) (t := t) (g := g) ht ht_lt
  calc
    0 ≤ P * (A + B) := mul_nonneg hP_nonneg (add_nonneg hA_nonneg hB_nonneg)
    _ = boundaryCaccioppoliWithRHSRHS C s t u := by
        rfl

/-- The forcing-only summand is contained in the displayed RHS once the
prefactor constant is at least `1`. -/
theorem boundaryCaccioppoliWithRHS_forceTerm_le_RHS
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (hC : 1 ≤ C)
    (hs : 0 < s) (hs_lt : s < 1) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) :
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
        Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2 ≤
      boundaryCaccioppoliWithRHSRHS C s t u := by
  let P : ℝ := caccioppoliWithRHSPrefactor C Q a s t
  let A : ℝ :=
    Ch02.lambdaS Q t a *
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
      boundaryForcedCaccioppoliParentL2Sq u
  let B : ℝ :=
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  have hP_one : 1 ≤ P := by
    dsimp [P]
    exact one_le_caccioppoliWithRHSPrefactor hC hs hs_lt ht hst
  have hP_nonneg : 0 ≤ P := le_trans zero_le_one hP_one
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using boundaryCaccioppoliWithRHS_parentTerm_nonneg (Q := Q) (a := a) u ht
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact boundaryCaccioppoliWithRHS_forceTerm_nonneg
      (Q := Q) (a := a) (t := t) (g := g) ht ht_lt
  have hsum_nonneg : 0 ≤ A + B := add_nonneg hA_nonneg hB_nonneg
  calc
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
        Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
        = B := rfl
    _ ≤ A + B := le_add_of_nonneg_left hA_nonneg
    _ ≤ P * (A + B) := by
        calc
          A + B = 1 * (A + B) := by ring
          _ ≤ P * (A + B) :=
            mul_le_mul_of_nonneg_right hP_one hsum_nonneg
    _ = boundaryCaccioppoliWithRHSRHS C s t u := by
        rfl

/-- Any dimension-only multiple already bounded by `C^2` of the forcing
summand is contained in the displayed RHS.  This is the scalar absorption
hook used after the corrector estimates have been reduced to the forcing
summand. -/
theorem boundaryCaccioppoliWithRHS_const_mul_forceTerm_le_RHS
    {d : ℕ} [NeZero d] {K C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (hKC : K ≤ C ^ 2) (hC : 1 ≤ C)
    (hs : 0 < s) (hs_lt : s < 1) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) :
    K *
      ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
        Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) ≤
      boundaryCaccioppoliWithRHSRHS C s t u := by
  let P : ℝ := caccioppoliWithRHSPrefactor C Q a s t
  let A : ℝ :=
    Ch02.lambdaS Q t a *
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
      boundaryForcedCaccioppoliParentL2Sq u
  let B : ℝ :=
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  have hP_ge_C2 : C ^ 2 ≤ P := by
    dsimp [P]
    exact sq_le_caccioppoliWithRHSPrefactor hC hs hs_lt ht hst
  have hK_le_P : K ≤ P := hKC.trans hP_ge_C2
  have hP_nonneg : 0 ≤ P := by
    have hC2_nonneg : 0 ≤ C ^ 2 := sq_nonneg C
    exact hC2_nonneg.trans hP_ge_C2
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using boundaryCaccioppoliWithRHS_parentTerm_nonneg (Q := Q) (a := a) u ht
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact boundaryCaccioppoliWithRHS_forceTerm_nonneg
      (Q := Q) (a := a) (t := t) (g := g) ht ht_lt
  calc
    K *
      ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
        Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2)
        = K * B := rfl
    _ ≤ P * B := mul_le_mul_of_nonneg_right hK_le_P hB_nonneg
    _ ≤ P * (A + B) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA_nonneg) hP_nonneg
    _ = boundaryCaccioppoliWithRHSRHS C s t u := by
        rfl

/-- The squared zero-Dirichlet RHS is controlled by the forcing summand used
in the boundary Caccioppoli-with-RHS statement.  This is the scalar
`q = 2` to `q = 1` lower-ellipticity conversion plus the `t^{-8}` buffer. -/
theorem zeroDirichletEnergyWithRHSRHS_sq_le_const_mul_forceTerm
    {d : ℕ} [NeZero d] {C₀ : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    {g : Vec d → Vec d}
    (ht : 0 < t) (ht_lt : t < 1 / 2) :
    (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2 ≤
      ((25 * Real.exp 4) * C₀ ^ 2) *
        ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) := by
  let L₂ : ℝ := Ch02.lambdaSq Q t (.finite 2) a
  let L₁ : ℝ := Ch02.lambdaS Q t a
  let B : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g
  let K : ℝ := 25 * Real.exp 4
  have ht_le_one : t ≤ 1 := by linarith
  have hden_pos : 0 < 1 - 2 * t := by linarith
  have hL₂_pos : 0 < L₂ := by
    dsimp [L₂]
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 2)
  have hL₁_pos : 0 < L₁ := by
    dsimp [L₁]
    unfold Ch02.lambdaS
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)
  have hlower :
      Real.rpow L₂ (-1 : ℝ) ≤
        K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ) := by
    have hchange :=
      Ch02.lambdaSqFinite_inv_le_change_exponent
        (Q := Q) (a := a) (s := t) (p := (1 : ℝ)) (q := (2 : ℝ))
        ht ht_le_one (by norm_num : (1 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) ≤ 2)
    have hchange' :
        Real.rpow L₂ (-1 : ℝ) ≤
          K * Real.rpow t (2 / (2 : ℝ) - 2 / (1 : ℝ)) *
            Real.rpow L₁ (-1 : ℝ) := by
      dsimp [K, L₂, L₁]
      simpa [Ch02.lambdaS, Real.rpow_neg_one] using hchange
    calc
      Real.rpow L₂ (-1 : ℝ) ≤
          K * Real.rpow t (2 / (2 : ℝ) - 2 / (1 : ℝ)) *
            Real.rpow L₁ (-1 : ℝ) := hchange'
      _ = K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ) := by norm_num
  have ht_sq :
      (Real.rpow t (-(3 / 2 : ℝ))) ^ 2 = Real.rpow t (-3 : ℝ) := by
    calc
      (Real.rpow t (-(3 / 2 : ℝ))) ^ 2 =
          Real.rpow (Real.rpow t (-(3 / 2 : ℝ))) (2 : ℝ) :=
            (Real.rpow_two _).symm
      _ = Real.rpow t (-(3 / 2 : ℝ) * (2 : ℝ)) :=
            (Real.rpow_mul ht.le (-(3 / 2 : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow t (-3 : ℝ) := by norm_num
  have hL₂_sq :
      (poincareLowerEllipticityFactor Q a t (.finite 2)) ^ 2 =
        Real.rpow L₂ (-1 : ℝ) := by
    unfold poincareLowerEllipticityFactor
    dsimp [L₂]
    calc
      (Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-(1 / 2 : ℝ))) ^ 2 =
          Real.rpow
            (Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-(1 / 2 : ℝ)))
            (2 : ℝ) := (Real.rpow_two _).symm
      _ =
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a)
            (-(1 / 2 : ℝ) * (2 : ℝ)) :=
            (Real.rpow_mul hL₂_pos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) := by
            norm_num
  have hZsq :
      (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2 =
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ^ 2 := by
    unfold zeroDirichletEnergyWithRHSRHS
    change
      (C₀ * Real.rpow t (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor Q a t (.finite 2) * B) ^ 2 =
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ^ 2
    rw [show
        (C₀ * Real.rpow t (-(3 / 2 : ℝ)) *
            poincareLowerEllipticityFactor Q a t (.finite 2) *
            B) ^ 2 =
          C₀ ^ 2 * (Real.rpow t (-(3 / 2 : ℝ))) ^ 2 *
            (poincareLowerEllipticityFactor Q a t (.finite 2)) ^ 2 *
            B ^ 2 by
        ring]
    rw [ht_sq, hL₂_sq]
  have htime_mul :
      Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ) =
        Real.rpow t (-4 : ℝ) := by
    calc
      Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ) =
          Real.rpow t ((-3 : ℝ) + (-1 : ℝ)) :=
            (Real.rpow_add ht (-3 : ℝ) (-1 : ℝ)).symm
      _ = Real.rpow t (-4 : ℝ) := by norm_num
  have htime_to_buffer :
      Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ) ≤
        Real.rpow t (-8 : ℝ) / (1 - 2 * t) := by
    have hpow48 :
        Real.rpow t (-4 : ℝ) ≤ Real.rpow t (-8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht_le_one (by norm_num)
    have hpow8_nonneg : 0 ≤ Real.rpow t (-8 : ℝ) :=
      Real.rpow_nonneg ht.le _
    have hpow8_le_div :
        Real.rpow t (-8 : ℝ) ≤ Real.rpow t (-8 : ℝ) / (1 - 2 * t) := by
      have hden_le_one : 1 - 2 * t ≤ 1 := by linarith
      exact (le_div_iff₀ hden_pos).2
        (by
          calc
            Real.rpow t (-8 : ℝ) * (1 - 2 * t) ≤
                Real.rpow t (-8 : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hden_le_one hpow8_nonneg
            _ = Real.rpow t (-8 : ℝ) := by ring)
    calc
      Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ) =
          Real.rpow t (-4 : ℝ) := htime_mul
      _ ≤ Real.rpow t (-8 : ℝ) / (1 - 2 * t) :=
          hpow48.trans hpow8_le_div
  have hC_sq_nonneg : 0 ≤ C₀ ^ 2 := sq_nonneg C₀
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have htime3_nonneg : 0 ≤ Real.rpow t (-3 : ℝ) :=
    Real.rpow_nonneg ht.le _
  have htime1_nonneg : 0 ≤ Real.rpow t (-1 : ℝ) :=
    Real.rpow_nonneg ht.le _
  have hL₁_inv_nonneg : 0 ≤ Real.rpow L₁ (-1 : ℝ) :=
    Real.rpow_nonneg hL₁_pos.le _
  have hBsq_nonneg : 0 ≤ B ^ 2 := sq_nonneg B
  have hstep_lambda :
      C₀ ^ 2 * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ^ 2 ≤
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ)) *
          B ^ 2 := by
    have hfront_nonneg :
        0 ≤ C₀ ^ 2 * Real.rpow t (-3 : ℝ) :=
      mul_nonneg hC_sq_nonneg htime3_nonneg
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlower hfront_nonneg) hBsq_nonneg
  have hstep_time :
      C₀ ^ 2 * Real.rpow t (-3 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ)) *
          B ^ 2 ≤
        (K * C₀ ^ 2) *
          (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow L₁ (-1 : ℝ) * B ^ 2 := by
    have hKA_nonneg : 0 ≤ K * C₀ ^ 2 :=
      mul_nonneg hK_nonneg hC_sq_nonneg
    have htail_nonneg : 0 ≤ Real.rpow L₁ (-1 : ℝ) * B ^ 2 :=
      mul_nonneg hL₁_inv_nonneg hBsq_nonneg
    calc
      C₀ ^ 2 * Real.rpow t (-3 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ)) *
          B ^ 2 =
        (K * C₀ ^ 2) *
          ((Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ)) *
            (Real.rpow L₁ (-1 : ℝ) * B ^ 2)) := by ring
      _ ≤
        (K * C₀ ^ 2) *
          ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            (Real.rpow L₁ (-1 : ℝ) * B ^ 2)) := by
          have htime_tail :
              (Real.rpow t (-3 : ℝ) * Real.rpow t (-1 : ℝ)) *
                  (Real.rpow L₁ (-1 : ℝ) * B ^ 2) ≤
                (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
                  (Real.rpow L₁ (-1 : ℝ) * B ^ 2) :=
            mul_le_mul_of_nonneg_right htime_to_buffer htail_nonneg
          exact mul_le_mul_of_nonneg_left htime_tail hKA_nonneg
      _ =
        (K * C₀ ^ 2) *
          (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow L₁ (-1 : ℝ) * B ^ 2 := by ring
  calc
    (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2 =
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ^ 2 := hZsq
    _ ≤
        C₀ ^ 2 * Real.rpow t (-3 : ℝ) *
            (K * Real.rpow t (-1 : ℝ) * Real.rpow L₁ (-1 : ℝ)) *
          B ^ 2 := hstep_lambda
    _ ≤
        (K * C₀ ^ 2) *
          (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow L₁ (-1 : ℝ) * B ^ 2 := hstep_time
    _ =
      ((25 * Real.exp 4) * C₀ ^ 2) *
        ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2) := by
        simp [K, L₁, B, mul_assoc, mul_left_comm, mul_comm]

/-- Squared lower-ellipticity conversion used for the corrector parent `L²`
bridge.

The public RHS Poincare estimate gives the corrector gradient with a
`lambda_{t,2}^{-1}` factor.  After squaring and multiplying by `lambdaS`
this lemma converts the two `q = 2` lower-ellipticity factors to the displayed
`q = 1` factor, spending exactly the `t^{-8}` buffer. -/
theorem lambdaS_mul_tpow_lambdaSqTwo_inv_sq_le_forceTime
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {t B : ℝ} (ht : 0 < t) (ht_lt : t < 1 / 2) :
    Ch02.lambdaS Q t a *
        (Real.rpow t (-3 : ℝ) *
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) * B) ^ 2 ≤
      (25 * Real.exp 4) ^ 2 *
        (Real.rpow t (-8 : ℝ) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) * B ^ 2) := by
  let L₂ : ℝ := Ch02.lambdaSq Q t (.finite 2) a
  let L₁ : ℝ := Ch02.lambdaS Q t a
  let A : ℝ := 25 * Real.exp 4
  let T3 : ℝ := Real.rpow t (-3 : ℝ)
  let T1 : ℝ := Real.rpow t (-1 : ℝ)
  let I₂ : ℝ := Real.rpow L₂ (-1 : ℝ)
  let I₁ : ℝ := Real.rpow L₁ (-1 : ℝ)
  have ht_le_one : t ≤ 1 := by nlinarith
  have hL₂_pos : 0 < L₂ := by
    dsimp [L₂]
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 2)
  have hL₁_pos : 0 < L₁ := by
    dsimp [L₁]
    unfold Ch02.lambdaS
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hchange : I₂ ≤ A * T1 * I₁ := by
    have h := Ch02.lambdaSqFinite_inv_le_change_exponent
        (Q := Q) (a := a) (s := t) (p := (1 : ℝ)) (q := (2 : ℝ))
        ht ht_le_one (by norm_num : (1 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) ≤ 2)
    have h' :
        I₂ ≤ A * Real.rpow t (2 / (2 : ℝ) - 2 / (1 : ℝ)) * I₁ := by
      dsimp [A, L₂, L₁, I₂, I₁]
      simpa [Ch02.lambdaS, Real.rpow_neg_one] using h
    calc
      I₂ ≤ A * Real.rpow t (2 / (2 : ℝ) - 2 / (1 : ℝ)) * I₁ := h'
      _ = A * T1 * I₁ := by norm_num [T1]
  have hI₂_nonneg : 0 ≤ I₂ := by
    dsimp [I₂]
    exact Real.rpow_nonneg hL₂_pos.le _
  have hT1_nonneg : 0 ≤ T1 := by
    dsimp [T1]
    exact Real.rpow_nonneg ht.le _
  have hL₁_mul_inv : L₁ * I₁ = 1 := by
    have hI : I₁ = L₁⁻¹ := by
      dsimp [I₁]
      exact Real.rpow_neg_one L₁
    rw [hI]
    field_simp [ne_of_gt hL₁_pos]
  have hL₁_L₂_once : L₁ * I₂ ≤ A * T1 := by
    have hmul := mul_le_mul_of_nonneg_left hchange hL₁_pos.le
    calc
      L₁ * I₂ ≤ L₁ * (A * T1 * I₁) := hmul
      _ = A * T1 * (L₁ * I₁) := by ring
      _ = A * T1 := by rw [hL₁_mul_inv]; ring
  have hfirst_nonneg : 0 ≤ A * T1 := mul_nonneg hA_nonneg hT1_nonneg
  have hL₁_L₂_sq :
      L₁ * I₂ ^ 2 ≤ A ^ 2 * T1 ^ 2 * I₁ := by
    have hstep := mul_le_mul hL₁_L₂_once hchange hI₂_nonneg hfirst_nonneg
    calc
      L₁ * I₂ ^ 2 = (L₁ * I₂) * I₂ := by ring
      _ ≤ (A * T1) * (A * T1 * I₁) := hstep
      _ = A ^ 2 * T1 ^ 2 * I₁ := by ring
  have hT3_sq : T3 ^ 2 = Real.rpow t (-6 : ℝ) := by
    dsimp [T3]
    calc
      (Real.rpow t (-3 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow t (-3 : ℝ)) (2 : ℝ) :=
            (Real.rpow_two _).symm
      _ = Real.rpow t ((-3 : ℝ) * (2 : ℝ)) :=
            (Real.rpow_mul ht.le (-3 : ℝ) (2 : ℝ)).symm
      _ = Real.rpow t (-6 : ℝ) := by norm_num
  have hT1_sq : T1 ^ 2 = Real.rpow t (-2 : ℝ) := by
    dsimp [T1]
    calc
      (Real.rpow t (-1 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow t (-1 : ℝ)) (2 : ℝ) :=
            (Real.rpow_two _).symm
      _ = Real.rpow t ((-1 : ℝ) * (2 : ℝ)) :=
            (Real.rpow_mul ht.le (-1 : ℝ) (2 : ℝ)).symm
      _ = Real.rpow t (-2 : ℝ) := by norm_num
  have ht_time :
      Real.rpow t (-6 : ℝ) * Real.rpow t (-2 : ℝ) =
        Real.rpow t (-8 : ℝ) := by
    calc
      Real.rpow t (-6 : ℝ) * Real.rpow t (-2 : ℝ) =
          Real.rpow t ((-6 : ℝ) + (-2 : ℝ)) :=
            (Real.rpow_add ht (-6 : ℝ) (-2 : ℝ)).symm
      _ = Real.rpow t (-8 : ℝ) := by norm_num
  have hT3sq_nonneg : 0 ≤ T3 ^ 2 := sq_nonneg T3
  have hBsq_nonneg : 0 ≤ B ^ 2 := sq_nonneg B
  calc
    Ch02.lambdaS Q t a *
        (Real.rpow t (-3 : ℝ) *
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) * B) ^ 2 =
      T3 ^ 2 * (L₁ * I₂ ^ 2) * B ^ 2 := by
        dsimp [T3, I₂, L₁, L₂]
        ring
    _ ≤ T3 ^ 2 * (A ^ 2 * T1 ^ 2 * I₁) * B ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL₁_L₂_sq hT3sq_nonneg) hBsq_nonneg
    _ = A ^ 2 * ((T3 ^ 2 * T1 ^ 2) * I₁ * B ^ 2) := by ring
    _ =
      A ^ 2 * ((Real.rpow t (-6 : ℝ) * Real.rpow t (-2 : ℝ)) *
        I₁ * B ^ 2) := by
        rw [hT3_sq, hT1_sq]
    _ = A ^ 2 * (Real.rpow t (-8 : ℝ) * I₁ * B ^ 2) := by
        rw [ht_time]
    _ = (25 * Real.exp 4) ^ 2 *
        (Real.rpow t (-8 : ℝ) *
          Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) * B ^ 2) := by
        simp [A, I₁, L₁]

/-- Once the zero-Dirichlet energy estimate is inserted, the public RHS
Poincare gradient bound for the zero-trace corrector has the exact force scale
needed by the Caccioppoli parent `L²` bridge. -/
theorem coarsePoincareWithRHSGradientRHS_le_corrector_forceScale
    {d : ℕ} [NeZero d] {C : ℝ} (hC_nonneg : 0 ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (ht : 0 < t) (_ht_lt : t < 1 / 2)
    (hg : ForceBesovRegularity Q (2 * t) g)
    (henergy :
      forcedSolutionEnergyNorm Q a u ≤ zeroDirichletEnergyWithRHSRHS C Q a t g) :
    coarsePoincareWithRHSGradientRHS C Q a (2 * t) g u ≤
      (C ^ 2 + C) *
        (Real.rpow t (-3 : ℝ) *
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) := by
  let L₂ : ℝ := Ch02.lambdaSq Q t (.finite 2) a
  let B : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g
  let P : ℝ := poincareLowerEllipticityFactor Q a t (.finite 2)
  let E : ℝ := forcedSolutionEnergyNorm Q a u
  have htwo_t_pos : 0 < 2 * t := by nlinarith
  have ht_le_two_t : t ≤ 2 * t := by nlinarith
  have hpow_two_t_32 :
      Real.rpow (2 * t) (-(3 / 2 : ℝ)) ≤
        Real.rpow t (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht ht_le_two_t (by norm_num)
  have hpow_two_t_3 :
      Real.rpow (2 * t) (-3 : ℝ) ≤ Real.rpow t (-3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ht ht_le_two_t (by norm_num)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (Q := Q) (s := 2 * t) (g := g) hg
  have hL₂_pos : 0 < L₂ := by
    dsimp [L₂]
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 2)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P, poincareLowerEllipticityFactor]
    exact Real.rpow_nonneg hL₂_pos.le _
  have hP_sq : P ^ 2 = Real.rpow L₂ (-1 : ℝ) := by
    dsimp [P, L₂, poincareLowerEllipticityFactor]
    calc
      (Real.rpow (Ch02.lambdaSq Q t (Ch02.MultiscaleExponent.finite 2) a)
          (-(1 / 2 : ℝ))) ^ 2 =
        Real.rpow
          (Real.rpow (Ch02.lambdaSq Q t (Ch02.MultiscaleExponent.finite 2) a)
            (-(1 / 2 : ℝ))) (2 : ℝ) := (Real.rpow_two _).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (Ch02.MultiscaleExponent.finite 2) a)
            (-(1 / 2 : ℝ) * (2 : ℝ)) :=
          (Real.rpow_mul hL₂_pos.le (-(1 / 2 : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (Ch02.MultiscaleExponent.finite 2) a)
            (-1 : ℝ) := by norm_num
  have ht_pow32_mul :
      Real.rpow t (-(3 / 2 : ℝ)) * Real.rpow t (-(3 / 2 : ℝ)) =
        Real.rpow t (-3 : ℝ) := by
    calc
      Real.rpow t (-(3 / 2 : ℝ)) * Real.rpow t (-(3 / 2 : ℝ)) =
        Real.rpow t (-(3 / 2 : ℝ) + -(3 / 2 : ℝ)) :=
          (Real.rpow_add ht (-(3 / 2 : ℝ)) (-(3 / 2 : ℝ))).symm
      _ = Real.rpow t (-3 : ℝ) := by norm_num
  have htime32_nonneg : 0 ≤ Real.rpow t (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg ht.le _
  have hL₂_inv_nonneg : 0 ≤ Real.rpow L₂ (-1 : ℝ) :=
    Real.rpow_nonneg hL₂_pos.le _
  have hEbound : E ≤ C * Real.rpow t (-(3 / 2 : ℝ)) * P * B := by
    dsimp [E]
    calc
      forcedSolutionEnergyNorm Q a u ≤
          zeroDirichletEnergyWithRHSRHS C Q a t g := henergy
      _ = C * Real.rpow t (-(3 / 2 : ℝ)) * P * B := by
          unfold zeroDirichletEnergyWithRHSRHS
          dsimp [P, B]
  have hfront_nonneg :
      0 ≤ C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) * P := by
    exact mul_nonneg
      (mul_nonneg hC_nonneg (Real.rpow_nonneg htwo_t_pos.le _)) hP_nonneg
  have hterm1 :
      C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) * P * E ≤
        C ^ 2 *
          (Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B) := by
    calc
      C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) * P * E ≤
          C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) * P *
            (C * Real.rpow t (-(3 / 2 : ℝ)) * P * B) :=
        mul_le_mul_of_nonneg_left hEbound hfront_nonneg
      _ ≤
          C * Real.rpow t (-(3 / 2 : ℝ)) * P *
            (C * Real.rpow t (-(3 / 2 : ℝ)) * P * B) := by
        have hcoeff :
            C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) * P ≤
              C * Real.rpow t (-(3 / 2 : ℝ)) * P := by
          have hCP_nonneg : 0 ≤ C * P := mul_nonneg hC_nonneg hP_nonneg
          calc
            C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) * P =
                (C * P) * Real.rpow (2 * t) (-(3 / 2 : ℝ)) := by ring
            _ ≤ (C * P) * Real.rpow t (-(3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hpow_two_t_32 hCP_nonneg
            _ = C * Real.rpow t (-(3 / 2 : ℝ)) * P := by ring
        have htail_nonneg :
            0 ≤ C * Real.rpow t (-(3 / 2 : ℝ)) * P * B := by
          exact mul_nonneg
            (mul_nonneg (mul_nonneg hC_nonneg htime32_nonneg) hP_nonneg)
            hB_nonneg
        exact mul_le_mul_of_nonneg_right hcoeff htail_nonneg
      _ = C ^ 2 *
          (Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B) := by
        rw [← ht_pow32_mul, ← hP_sq]
        ring
  have hterm2 :
      C * Real.rpow (2 * t) (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B ≤
        C * (Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B) := by
    calc
      C * Real.rpow (2 * t) (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B =
          (C * Real.rpow (2 * t) (-3 : ℝ) *
            Real.rpow L₂ (-1 : ℝ)) * B := by ring
      _ ≤ (C * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ)) * B := by
        have hcoeff :
            C * Real.rpow (2 * t) (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) ≤
              C * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) := by
          have hCI_nonneg : 0 ≤ C * Real.rpow L₂ (-1 : ℝ) :=
            mul_nonneg hC_nonneg hL₂_inv_nonneg
          calc
            C * Real.rpow (2 * t) (-3 : ℝ) *
                Real.rpow L₂ (-1 : ℝ) =
              (C * Real.rpow L₂ (-1 : ℝ)) *
                Real.rpow (2 * t) (-3 : ℝ) := by ring
            _ ≤ (C * Real.rpow L₂ (-1 : ℝ)) * Real.rpow t (-3 : ℝ) :=
                mul_le_mul_of_nonneg_left hpow_two_t_3 hCI_nonneg
            _ = C * Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) := by
                ring
        exact mul_le_mul_of_nonneg_right hcoeff hB_nonneg
      _ = C * (Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B) := by
          ring
  have hhalf : (2 * t) / 2 = t := by ring
  calc
    coarsePoincareWithRHSGradientRHS C Q a (2 * t) g u =
        C * Real.rpow (2 * t) (-(3 / 2 : ℝ)) * P * E +
          C * Real.rpow (2 * t) (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B := by
      unfold coarsePoincareWithRHSGradientRHS
      dsimp [E, P, B, L₂]
      rw [hhalf]
    _ ≤
        C ^ 2 * (Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B) +
          C * (Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B) :=
      add_le_add hterm1 hterm2
    _ = (C ^ 2 + C) *
        (Real.rpow t (-3 : ℝ) * Real.rpow L₂ (-1 : ℝ) * B) := by ring
    _ = (C ^ 2 + C) *
        (Real.rpow t (-3 : ℝ) *
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) := by
        rfl

/-- The corrector core-energy scalar term produced by the zero-Dirichlet
estimate is absorbed by the forcing part of the final RHS once the final
constant is large enough. -/
theorem boundaryCaccioppoliWithRHS_zeroDirichletSqTerm_le_RHS
    {d : ℕ} [NeZero d] {C C₀ : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (hKC :
      (2 * (18 : ℝ) ^ d) * ((25 * Real.exp 4) * C₀ ^ 2) ≤ C ^ 2)
    (hC : 1 ≤ C)
    (hs : 0 < s) (hs_lt : s < 1) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) :
    2 * ((18 : ℝ) ^ d * (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2) ≤
      boundaryCaccioppoliWithRHSRHS C s t u := by
  let F : ℝ :=
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  let K₀ : ℝ := (25 * Real.exp 4) * C₀ ^ 2
  let K : ℝ := (2 * (18 : ℝ) ^ d) * K₀
  have hZ :
      (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2 ≤ K₀ * F := by
    dsimp [K₀, F]
    exact zeroDirichletEnergyWithRHSRHS_sq_le_const_mul_forceTerm
      (C₀ := C₀) (Q := Q) (a := a) (t := t) (g := g) ht ht_lt
  have hfront_nonneg : 0 ≤ 2 * (18 : ℝ) ^ d := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ (18 : ℝ)) d)
  have hterm :
      2 * ((18 : ℝ) ^ d * (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2)
        ≤ K * F := by
    calc
      2 * ((18 : ℝ) ^ d *
          (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2) =
        (2 * (18 : ℝ) ^ d) *
          (zeroDirichletEnergyWithRHSRHS C₀ Q a t g) ^ 2 := by ring
      _ ≤ (2 * (18 : ℝ) ^ d) * (K₀ * F) :=
        mul_le_mul_of_nonneg_left hZ hfront_nonneg
      _ = K * F := by
        dsimp [K]
        ring
  have hKRHS :
      K * F ≤ boundaryCaccioppoliWithRHSRHS C s t u := by
    dsimp [F, K]
    exact boundaryCaccioppoliWithRHS_const_mul_forceTerm_le_RHS
      (K := (2 * (18 : ℝ) ^ d) * ((25 * Real.exp 4) * C₀ ^ 2))
      (C := C) u hKC hC hs hs_lt ht ht_lt hst
  exact hterm.trans hKRHS

/-- The first term of the forced boundary Caccioppoli RHS contains the
homogeneous parent-`L²` contribution with the same displayed prefactor. -/
theorem caccioppoliPrefactor_mul_forcedParentL2_le_boundaryCaccioppoliWithRHSRHS
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} {x : Vec d} {g : Vec d → Vec d}
    (u : BoundaryForcedCaccioppoliDatum Q a x g)
    (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hst : s + t < 1) :
    caccioppoliPrefactor C Q a s t *
        boundaryForcedCaccioppoliParentL2Sq u ≤
      boundaryCaccioppoliWithRHSRHS C s t u := by
  let P : ℝ := caccioppoliWithRHSPrefactor C Q a s t
  let L : ℝ := Ch02.lambdaS Q t a
  let S : ℝ := Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))
  let U0 : ℝ := boundaryForcedCaccioppoliParentL2Sq u
  let A : ℝ :=
    (L * S) * U0
  let B : ℝ :=
    (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
      Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
      (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact caccioppoliWithRHSPrefactor_nonneg hC_nonneg hs ht hst
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact boundaryCaccioppoliWithRHS_forceTerm_nonneg
      (Q := Q) (a := a) (t := t) (g := g) ht ht_lt
  have hid :=
    caccioppoliPrefactor_eq_caccioppoliWithRHSPrefactor_mul_lambdaS_scale
      (C := C) (Q := Q) (a := a) hs ht hst
  have hid' :
      caccioppoliPrefactor C Q a s t = P * (L * S) := by
    dsimp [P, L, S]
    exact hid
  calc
    caccioppoliPrefactor C Q a s t *
        boundaryForcedCaccioppoliParentL2Sq u =
      P * A := by
        dsimp [A, U0]
        rw [hid']
        ring
    _ ≤ P * (A + B) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB_nonneg) hP_nonneg
    _ =
      boundaryCaccioppoliWithRHSRHS C s t u := by
        rfl



end

end Ch03
end Book
end Homogenization
