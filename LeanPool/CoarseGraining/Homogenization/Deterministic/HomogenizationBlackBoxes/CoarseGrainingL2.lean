/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse
public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesPositiveQTwo
public import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities

/-! # Coarse Graining L2 -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Deterministic homogenization black boxes: general coarse graining in `L²`

This file contains the Section 3.3.B theorem surface from
`coarsegraining/chapters/ch3_deterministic_theory.tex`, lines 3009--3253.

The theorem is stated as the deterministic composition step: once the local
coarse flux-defect estimate from the preceding Chapter-3 files supplies the
single hypothesis `hcoarseFluxDefect`, the duality lemma from Section 3.3.A
turns it into the global comparison estimate.  The right-hand side below is the
manuscript expression in the existing Lean notation:

* `coarseGrainingHomogenizationErrorAtDepth Q a a0 s j` is
  `𝓔_{s,∞,1}(Q,n;a,a₀)` with depth `j = m - n`;
* `lambdaSq` and `LambdaSq` are the scale-local multiscale ellipticity
  quantities, not the qualitative uniform ellipticity constants;
* `cubeBesovPositiveVectorSeminormTwo` is the note-normalized
  `3^{sm}[g]_{\underline B^s_{2,2}(Q)}`.
-/

open scoped BigOperators ENNReal

/--
The truncated homogenization-error quantity
`𝓔_{s,∞,1}(Q,n;a,a₀)` from Proposition
`p.general.coarse.graining.p2.deterministic.theory`.

In Lean, the parent cube is `Q` and the scale gap `m - n` is the descendant
depth `j`, so the truncation is the supremum over descendants of `Q` at depth
`j`.
-/
noncomputable def coarseGrainingHomogenizationErrorAtDepth {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ) (j : ℕ) : ℝ :=
  finsetSsup (descendantsAtDepth Q j) fun R =>
    HomogenizationErrorOnCube R s .infinity (.finite 1) a a0

/-- At depth zero the truncated homogenization error is the one-cube error. -/
@[simp] theorem coarseGrainingHomogenizationErrorAtDepth_zero {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ) :
    coarseGrainingHomogenizationErrorAtDepth Q a a0 s 0 =
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  simp [coarseGrainingHomogenizationErrorAtDepth]

/-- The q=1 homogenization error on one cube is nonnegative. -/
theorem homogenizationErrorOnCube_infinity_one_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {s : ℝ}
    (hs : 0 ≤ s) :
    0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
  refine tsum_nonneg ?_
  intro n
  exact mul_nonneg (geometricWeight_nonneg n (by simpa using hs))
    (scaleResponseAtScale_infinity_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0)

/-- Each descendant error is bounded by the depth-truncated parent error. -/
theorem homogenizationErrorOnCube_le_coarseGrainingHomogenizationErrorAtDepth
    {d : ℕ} {Q R : TriadicCube d} {a : CoeffField d} {a0 : Mat d}
    {s : ℝ} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
      coarseGrainingHomogenizationErrorAtDepth Q a a0 s j := by
  unfold coarseGrainingHomogenizationErrorAtDepth finsetSsup
  have hBdd :
      BddAbove
        ((fun S : TriadicCube d =>
            HomogenizationErrorOnCube S s .infinity (.finite 1) a a0) ''
          (↑(descendantsAtDepth Q j) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image
      (fun S : TriadicCube d =>
        HomogenizationErrorOnCube S s .infinity (.finite 1) a a0)).bddAbove
  exact le_csSup hBdd ⟨R, hR, rfl⟩

/-- The depth-truncated parent homogenization error is nonnegative. -/
theorem coarseGrainingHomogenizationErrorAtDepth_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {s : ℝ} (j : ℕ)
    (hs : 0 ≤ s) :
    0 ≤ coarseGrainingHomogenizationErrorAtDepth Q a a0 s j := by
  obtain ⟨R0, hR0⟩ := descendantsAtDepth_nonempty Q j
  exact (homogenizationErrorOnCube_infinity_one_nonneg R0 a a0 hs).trans
    (homogenizationErrorOnCube_le_coarseGrainingHomogenizationErrorAtDepth hR0)

/--
The explicit right-hand side inside the dimension-only constant in the general
coarse-graining estimate, manuscript lines 3026--3057.

This is intentionally separated from the final theorem so downstream callers
can produce a bound on the local flux defect once and then compose it through
`solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxDefect_le`.
-/
noncomputable def coarseGrainingL2FluxDefectBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d) : ℝ :=
  (s⁻¹) * Real.sqrt (matNorm a0) *
      coarseGrainingHomogenizationErrorAtDepth Q a a0 s j *
      Real.sqrt (cubeAverage Q (coefficientEnergyDensity a gradU)) +
    (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
        Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
        Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
        coarseGrainingHomogenizationErrorAtDepth Q a a0 s j +
      Real.rpow s (-(5 / 2 : ℝ)) *
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
        Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) +
      Real.rpow s (-3 : ℝ) *
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
      cubeBesovPositiveVectorSeminormTwo Q s g

/-- The first, energy-only term in `coarseGrainingL2FluxDefectBound`. -/
noncomputable def coarseGrainingL2FluxDefectEnergyTerm {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU : Vec d → Vec d) : ℝ :=
  (s⁻¹) * Real.sqrt (matNorm a0) *
    coarseGrainingHomogenizationErrorAtDepth Q a a0 s j *
      Real.sqrt (cubeAverage Q (coefficientEnergyDensity a gradU))

/-- The positive-Besov forcing tail in `coarseGrainingL2FluxDefectBound`. -/
noncomputable def coarseGrainingL2FluxDefectForcingTerm {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (g : Vec d → Vec d) : ℝ :=
  (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
      Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
      coarseGrainingHomogenizationErrorAtDepth Q a a0 s j +
    Real.rpow s (-(5 / 2 : ℝ)) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) +
    Real.rpow s (-3 : ℝ) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
    cubeBesovPositiveVectorSeminormTwo Q s g

/-- Scale-separated positive-Besov forcing tail in the repaired Section 3.3.B
RHS.  The flux-response exponent is `s`, while the force is measured at the
stronger positive exponent `t`. -/
noncomputable def coarseGrainingL2FluxDefectForcingTermTwoExponent {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s t : ℝ) (j : ℕ) (g : Vec d → Vec d) : ℝ :=
  (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
      Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
      coarseGrainingHomogenizationErrorAtDepth Q a a0 s j +
    Real.rpow s (-(5 / 2 : ℝ)) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) +
    Real.rpow s (-3 : ℝ) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
    ((Real.rpow (3 : ℝ) (t * (j : ℝ)))⁻¹ *
      cubeBesovPositiveVectorSeminormTwo Q t g)

/-- Repaired scale-separated local flux-defect RHS in Section 3.3.B. -/
noncomputable def coarseGrainingL2FluxDefectBoundTwoExponent {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s t : ℝ) (j : ℕ) (gradU g : Vec d → Vec d) : ℝ :=
  coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU +
    coarseGrainingL2FluxDefectForcingTermTwoExponent Q a a0 s t j g

theorem coarseGrainingL2FluxDefectBound_eq_energyTerm_add_forcingTerm {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d) :
    coarseGrainingL2FluxDefectBound Q a a0 s j gradU g =
      coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU +
        coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g := by
  rfl

theorem coarseGrainingL2FluxDefectBoundTwoExponent_eq_energyTerm_add_forcingTerm {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s t : ℝ) (j : ℕ) (gradU g : Vec d → Vec d) :
    coarseGrainingL2FluxDefectBoundTwoExponent Q a a0 s t j gradU g =
      coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU +
        coarseGrainingL2FluxDefectForcingTermTwoExponent Q a a0 s t j g := by
  rfl

theorem coarseGrainingL2FluxDefectEnergyTerm_le_coarseGrainingL2FluxDefectBound_of_forcingTerm_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d)
    (hforcing_nonneg : 0 ≤ coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g := by
  rw [coarseGrainingL2FluxDefectBound_eq_energyTerm_add_forcingTerm]
  linarith

/-- The positive-Besov forcing tail in the Section 3.3.B RHS is nonnegative. -/
theorem coarseGrainingL2FluxDefectForcingTerm_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d)
    (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    0 ≤ coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g := by
  have hE_nonneg :
      0 ≤ coarseGrainingHomogenizationErrorAtDepth Q a a0 s j :=
    coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 j hs.le
  have hLambda_nonneg :
      0 ≤ LambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith)
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith)
  have hB_nonneg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g :=
    by
      have h0_le :
          cubeBesovPositiveVectorPartialSeminormTwo Q s 0 g ≤
            cubeBesovPositiveVectorSeminormTwo Q s g := by
        unfold cubeBesovPositiveVectorSeminormTwo
        exact le_csSup hgBdd ⟨0, rfl⟩
      exact (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s 0 g).trans h0_le
  have hs_rpow_five_half_nonneg : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have hs_rpow_three_nonneg : 0 ≤ Real.rpow s (-3 : ℝ) :=
    Real.rpow_nonneg hs.le _
  have hpow_half_nonneg :
      0 ≤ Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hLambda_sqrt_nonneg :
      0 ≤ Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) :=
    Real.sqrt_nonneg _
  have hmat_sqrt_nonneg : 0 ≤ Real.sqrt (matNorm a0) :=
    Real.sqrt_nonneg _
  have hlambda_inv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  have hlambda_inv_sqrt_nonneg :
      0 ≤ Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) :=
    Real.sqrt_nonneg _
  have hterm₁ :
      0 ≤
        Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
          Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
          coarseGrainingHomogenizationErrorAtDepth Q a a0 s j := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hs_rpow_five_half_nonneg hmat_sqrt_nonneg)
            hpow_half_nonneg)
          hlambda_inv_sqrt_nonneg)
        hE_nonneg
  have hterm₂ :
      0 ≤
        Real.rpow s (-(5 / 2 : ℝ)) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg hs_rpow_five_half_nonneg hpow_nonneg)
          hLambda_sqrt_nonneg)
        hlambda_inv_sqrt_nonneg
  have hterm₃ :
      0 ≤
        Real.rpow s (-3 : ℝ) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg hs_rpow_three_nonneg hpow_nonneg)
          (matNorm_nonneg a0))
        hlambda_inv_nonneg
  have hsum_nonneg :
      0 ≤
        Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
            Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
            Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
            coarseGrainingHomogenizationErrorAtDepth Q a a0 s j +
          Real.rpow s (-(5 / 2 : ℝ)) *
            Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
            Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) +
          Real.rpow s (-3 : ℝ) *
            Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact add_nonneg (add_nonneg hterm₁ hterm₂) hterm₃
  unfold coarseGrainingL2FluxDefectForcingTerm
  exact mul_nonneg hsum_nonneg hB_nonneg

/--
With depth zero and zero forcing, the general Section 3.3.B flux-defect RHS
collapses to the homogeneous RHS term from manuscript lines 3264--3292.
-/
@[simp] theorem coarseGrainingL2FluxDefectBound_depth_zero_zero_forcing {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU : Vec d → Vec d) :
    coarseGrainingL2FluxDefectBound Q a a0 s 0 gradU (0 : Vec d → Vec d) =
      (s⁻¹) * Real.sqrt (matNorm a0) *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
          Real.sqrt (cubeAverage Q (coefficientEnergyDensity a gradU)) := by
  simp [coarseGrainingL2FluxDefectBound]

/--
Localized `q = 2` response-average bound produced by applying the `q = 1`
coarse-flux response estimate on each descendant cube.

This is the scalar quantity that still has to be localized into the manuscript
`coarseGrainingL2FluxDefectBound` when assembling the fully internal Section
3.3.B wrapper.
-/
noncomputable def localizedCoarseFluxResponseAverageBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (energy : Vec d → ℝ) : ℝ :=
  Real.sqrt
    (descendantsAverage Q j fun R =>
      ((geometricDiscount s 1)⁻¹ *
        HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
          (Real.sqrt (((4 : ℝ) * matNorm a0)) *
            Real.sqrt (cubeAverage R energy))) ^ 2)

/--
If the localized response square is pointwise bounded by a constant multiple of
the local energy average, then the descendant `L²` response average is bounded
by that constant times the square root of the averaged energy.
-/
theorem localizedCoarseFluxResponseAverageBound_le_const_mul_sqrt_of_descendantsAverage_energy_bound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (energy : Vec d → ℝ) {C A : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ((geometricDiscount s 1)⁻¹ *
          HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (Real.sqrt (((4 : ℝ) * matNorm a0)) *
              Real.sqrt (cubeAverage R energy))) ^ 2 ≤
          C ^ 2 * cubeAverage R energy)
    (havg : descendantsAverage Q j (fun R => cubeAverage R energy) ≤ A) :
    localizedCoarseFluxResponseAverageBound Q a a0 s j energy ≤
      C * Real.sqrt A := by
  let T : TriadicCube d → ℝ := fun R =>
    (geometricDiscount s 1)⁻¹ *
      HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
        (Real.sqrt (((4 : ℝ) * matNorm a0)) *
          Real.sqrt (cubeAverage R energy))
  have hdesc :
      descendantsAverage Q j (fun R => (T R) ^ 2) ≤
        descendantsAverage Q j (fun R => C ^ 2 * cubeAverage R energy) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    exact hpoint R hR
  have hconst :
      descendantsAverage Q j (fun R => C ^ 2 * cubeAverage R energy) =
        C ^ 2 * descendantsAverage Q j (fun R => cubeAverage R energy) := by
    exact descendantsAverage_mul_left Q j (C ^ 2) (fun R => cubeAverage R energy)
  have hscaled :
      C ^ 2 * descendantsAverage Q j (fun R => cubeAverage R energy) ≤ C ^ 2 * A := by
    exact mul_le_mul_of_nonneg_left havg (sq_nonneg C)
  have hinside :
      descendantsAverage Q j (fun R => (T R) ^ 2) ≤ C ^ 2 * A := by
    calc
      descendantsAverage Q j (fun R => (T R) ^ 2)
          ≤ descendantsAverage Q j (fun R => C ^ 2 * cubeAverage R energy) := hdesc
      _ = C ^ 2 * descendantsAverage Q j (fun R => cubeAverage R energy) := hconst
      _ ≤ C ^ 2 * A := hscaled
  calc
    localizedCoarseFluxResponseAverageBound Q a a0 s j energy
        = Real.sqrt (descendantsAverage Q j fun R => (T R) ^ 2) := by
          rfl
    _ ≤ Real.sqrt (C ^ 2 * A) := Real.sqrt_le_sqrt hinside
    _ = C * Real.sqrt A := by
          rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC_nonneg]

/--
Parent-cube energy localization form of
`localizedCoarseFluxResponseAverageBound_le_const_mul_sqrt_of_descendantsAverage_energy_bound`.
-/
theorem localizedCoarseFluxResponseAverageBound_le_const_mul_sqrt_cubeAverage_of_pointwise_sq_bound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (energy : Vec d → ℝ) {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ((geometricDiscount s 1)⁻¹ *
          HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (Real.sqrt (((4 : ℝ) * matNorm a0)) *
              Real.sqrt (cubeAverage R energy))) ^ 2 ≤
          C ^ 2 * cubeAverage R energy) :
    localizedCoarseFluxResponseAverageBound Q a a0 s j energy ≤
      C * Real.sqrt (cubeAverage Q energy) := by
  have havg_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) =
        cubeAverage Q energy := by
    symm
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j energy henergy_int
  exact
    localizedCoarseFluxResponseAverageBound_le_const_mul_sqrt_of_descendantsAverage_energy_bound
      Q a a0 s j energy hC_nonneg hpoint (le_of_eq havg_eq)

/--
The localized response average is bounded by the parent depth-truncated
homogenization error with the raw q=1 geometric prefactor.
-/
theorem localizedCoarseFluxResponseAverageBound_le_invGeom_mul_errorAtDepth_mul_sqrt_four_matNorm_sqrt_cubeAverage
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (energy : Vec d → ℝ)
    (hs : 0 < s)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (henergy_avg_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ cubeAverage R energy)
    (herror_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) :
    localizedCoarseFluxResponseAverageBound Q a a0 s j energy ≤
      ((geometricDiscount s 1)⁻¹ *
        coarseGrainingHomogenizationErrorAtDepth Q a a0 s j *
          Real.sqrt (((4 : ℝ) * matNorm a0))) *
        Real.sqrt (cubeAverage Q energy) := by
  let H : ℝ := (geometricDiscount s 1)⁻¹
  let E : ℝ := coarseGrainingHomogenizationErrorAtDepth Q a a0 s j
  let M : ℝ := Real.sqrt (((4 : ℝ) * matNorm a0))
  let C : ℝ := H * E * M
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    exact inv_nonneg.mpr (geometricDiscount_pos (by simpa using hs)).le
  have hE_nonneg : 0 ≤ E := by
    obtain ⟨R0, hR0⟩ := descendantsAtDepth_nonempty Q j
    exact (herror_nonneg R0 hR0).trans
      (homogenizationErrorOnCube_le_coarseGrainingHomogenizationErrorAtDepth hR0)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Real.sqrt_nonneg _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hH_nonneg hE_nonneg) hM_nonneg
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ((geometricDiscount s 1)⁻¹ *
          HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (Real.sqrt (((4 : ℝ) * matNorm a0)) *
              Real.sqrt (cubeAverage R energy))) ^ 2 ≤
          C ^ 2 * cubeAverage R energy := by
    intro R hR
    have hER_nonneg :
        0 ≤ HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 :=
      herror_nonneg R hR
    have hER_le :
        HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤ E := by
      dsimp [E]
      exact homogenizationErrorOnCube_le_coarseGrainingHomogenizationErrorAtDepth hR
    have hA_nonneg : 0 ≤ cubeAverage R energy := henergy_avg_nonneg R hR
    have hsqrtA_nonneg : 0 ≤ Real.sqrt (cubeAverage R energy) := Real.sqrt_nonneg _
    have hbase_le :
        H * HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 * M ≤
          H * E * M := by
      have hleft :
          H * HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
            H * E := by
        exact mul_le_mul_of_nonneg_left hER_le hH_nonneg
      exact mul_le_mul_of_nonneg_right hleft hM_nonneg
    have hterm_nonneg :
        0 ≤ H * HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
          (M * Real.sqrt (cubeAverage R energy)) := by
      exact mul_nonneg (mul_nonneg hH_nonneg hER_nonneg)
        (mul_nonneg hM_nonneg hsqrtA_nonneg)
    have hterm_le :
        H * HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (M * Real.sqrt (cubeAverage R energy)) ≤
          C * Real.sqrt (cubeAverage R energy) := by
      calc
        H * HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (M * Real.sqrt (cubeAverage R energy))
            =
          (H * HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 * M) *
            Real.sqrt (cubeAverage R energy) := by
              ring
        _ ≤ (H * E * M) * Real.sqrt (cubeAverage R energy) := by
              exact mul_le_mul_of_nonneg_right hbase_le hsqrtA_nonneg
        _ = C * Real.sqrt (cubeAverage R energy) := by
              simp [C]
    have hsquare :=
      pow_le_pow_left₀ hterm_nonneg hterm_le 2
    calc
      ((geometricDiscount s 1)⁻¹ *
          HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (Real.sqrt (((4 : ℝ) * matNorm a0)) *
              Real.sqrt (cubeAverage R energy))) ^ 2
          =
        (H * HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (M * Real.sqrt (cubeAverage R energy))) ^ 2 := by
            simp [H, M]
      _ ≤ (C * Real.sqrt (cubeAverage R energy)) ^ 2 := hsquare
      _ = C ^ 2 * cubeAverage R energy := by
            rw [mul_pow, Real.sq_sqrt hA_nonneg]
  simpa [H, E, M, C] using
    localizedCoarseFluxResponseAverageBound_le_const_mul_sqrt_cubeAverage_of_pointwise_sq_bound
      Q a a0 s j energy hC_nonneg henergy_int hpoint

/--
Constant-adequacy form of the localized response average: once the scalar
geometric reciprocal has been bounded by `5 * s⁻¹`, the raw q=1 response
prefactor is controlled by ten times the manuscript energy term.
-/
theorem localizedCoarseFluxResponseAverageBound_le_ten_mul_energyTerm_of_invGeom_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (energy : Vec d → ℝ)
    (hs : 0 < s)
    (hgeom_le : (geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (henergy_avg_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ cubeAverage R energy)
    (herror_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) :
    localizedCoarseFluxResponseAverageBound Q a a0 s j energy ≤
      10 * ((s⁻¹) * Real.sqrt (matNorm a0) *
        coarseGrainingHomogenizationErrorAtDepth Q a a0 s j *
          Real.sqrt (cubeAverage Q energy)) := by
  let H : ℝ := (geometricDiscount s 1)⁻¹
  let E : ℝ := coarseGrainingHomogenizationErrorAtDepth Q a a0 s j
  let S : ℝ := Real.sqrt (matNorm a0)
  have hE_nonneg : 0 ≤ E := by
    obtain ⟨R0, hR0⟩ := descendantsAtDepth_nonempty Q j
    exact (herror_nonneg R0 hR0).trans
      (homogenizationErrorOnCube_le_coarseGrainingHomogenizationErrorAtDepth hR0)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Real.sqrt_nonneg _
  have hsqrtQ_nonneg : 0 ≤ Real.sqrt (cubeAverage Q energy) := Real.sqrt_nonneg _
  have hroot_four : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq
      (by norm_num : 0 ≤ (4 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hsqrt_four :
      Real.sqrt (((4 : ℝ) * matNorm a0)) = 2 * S := by
    dsimp [S]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), hroot_four]
  have htwoH_le : 2 * H ≤ 10 * s⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hgeom_le (by norm_num : 0 ≤ (2 : ℝ))
    dsimp [H]
    nlinarith
  have hcoef0 :
      H * Real.sqrt (((4 : ℝ) * matNorm a0)) ≤ (10 * s⁻¹) * S := by
    calc
      H * Real.sqrt (((4 : ℝ) * matNorm a0))
          = H * (2 * S) := by rw [hsqrt_four]
      _ = (2 * H) * S := by ring
      _ ≤ (10 * s⁻¹) * S := by
            exact mul_le_mul_of_nonneg_right htwoH_le hS_nonneg
  have hcoef :
      H * E * Real.sqrt (((4 : ℝ) * matNorm a0)) ≤
        ((10 * s⁻¹) * S) * E := by
    calc
      H * E * Real.sqrt (((4 : ℝ) * matNorm a0))
          = (H * Real.sqrt (((4 : ℝ) * matNorm a0))) * E := by ring
      _ ≤ ((10 * s⁻¹) * S) * E := by
            exact mul_le_mul_of_nonneg_right hcoef0 hE_nonneg
  calc
    localizedCoarseFluxResponseAverageBound Q a a0 s j energy
        ≤ (H * E * Real.sqrt (((4 : ℝ) * matNorm a0))) *
            Real.sqrt (cubeAverage Q energy) := by
          simpa [H, E] using
            localizedCoarseFluxResponseAverageBound_le_invGeom_mul_errorAtDepth_mul_sqrt_four_matNorm_sqrt_cubeAverage
              Q a a0 j energy hs henergy_int henergy_avg_nonneg herror_nonneg
    _ ≤ (((10 * s⁻¹) * S) * E) * Real.sqrt (cubeAverage Q energy) := by
          exact mul_le_mul_of_nonneg_right hcoef hsqrtQ_nonneg
    _ = 10 * ((s⁻¹) * Real.sqrt (matNorm a0) *
          coarseGrainingHomogenizationErrorAtDepth Q a a0 s j *
            Real.sqrt (cubeAverage Q energy)) := by
          simp [S, E]
          ring

/--
For the coefficient-energy density, the ten-factor response control is
absorbed by ten times the full Section 3.3.B flux-defect RHS whenever the
forcing tail is nonnegative.
-/
theorem localizedCoarseFluxResponseAverageBound_coefficientEnergy_le_ten_mul_coarseGrainingL2FluxDefectBound_of_invGeom_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d)
    (hs : 0 < s)
    (hgeom_le : (geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume)
    (henergy_avg_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ cubeAverage R (coefficientEnergyDensity a gradU))
    (herror_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ HomogenizationErrorOnCube R s .infinity (.finite 1) a a0)
    (hforcing_nonneg :
      0 ≤ coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    localizedCoarseFluxResponseAverageBound Q a a0 s j
        (coefficientEnergyDensity a gradU) ≤
      10 * coarseGrainingL2FluxDefectBound Q a a0 s j gradU g := by
  have hresponse_energy :
      localizedCoarseFluxResponseAverageBound Q a a0 s j
          (coefficientEnergyDensity a gradU) ≤
        10 * coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU := by
    simpa [coarseGrainingL2FluxDefectEnergyTerm] using
      localizedCoarseFluxResponseAverageBound_le_ten_mul_energyTerm_of_invGeom_le
        Q a a0 j (coefficientEnergyDensity a gradU) hs hgeom_le
        henergy_int henergy_avg_nonneg herror_nonneg
  have henergy_le :
      coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
    coarseGrainingL2FluxDefectEnergyTerm_le_coarseGrainingL2FluxDefectBound_of_forcingTerm_nonneg
      Q a a0 s j gradU g hforcing_nonneg
  exact hresponse_energy.trans
    (mul_le_mul_of_nonneg_left henergy_le (by norm_num : 0 ≤ (10 : ℝ)))

/--
Localized `q = 2` flux-defect bound obtained by applying the `q = 1`
coarse-flux response theorem on every descendant cube and then averaging the
result.

This is the bridge between the Section 3.2 flux-response estimates and the
single localized flux-defect hypothesis consumed by the Section 3.3.B
coarse-graining apex.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_descendant_coarseFluxResponse
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (defect : Vec d → Vec d) (energy : Vec d → ℝ) (j : ℕ)
    (hs : 0 < s)
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R, 0 ≤ energy x)
    (henergy_int :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume)
    (hresp :
      ∀ R ∈ descendantsAtDepth Q j,
        CubeAverageFluxResponseControl R a a0 defect energy)
    (hpartialBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminorm R s N defect))
    (hsum :
      ∀ R ∈ descendantsAtDepth Q j,
        Summable (fun n : ℕ =>
          geometricWeight s 1 n *
            scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0)) :
    localizedFluxDefectNegativeBesovAverageTwo Q s defect j ≤
      Real.sqrt
        (descendantsAverage Q j fun R =>
          ((geometricDiscount s 1)⁻¹ *
            HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
              (Real.sqrt (((4 : ℝ) * matNorm a0)) *
                Real.sqrt (cubeAverage R energy))) ^ 2) := by
  refine
    localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_qonePartialBound
      Q s defect j
      (fun R =>
        (geometricDiscount s 1)⁻¹ *
          HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (Real.sqrt (((4 : ℝ) * matNorm a0)) *
              Real.sqrt (cubeAverage R energy))) ?_
  intro R hR N
  calc
    cubeBesovNegativeVectorPartialSeminorm R s N defect
        ≤ cubeBesovNegativeVectorSeminorm R s defect := by
          unfold cubeBesovNegativeVectorSeminorm
          exact le_csSup (hpartialBdd R hR) ⟨N, rfl⟩
    _ ≤
        (geometricDiscount s 1)⁻¹ *
          HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
            (Real.sqrt (((4 : ℝ) * matNorm a0)) *
              Real.sqrt (cubeAverage R energy)) :=
          coarseFluxResponse_qone_of_cubeAverageFluxResponseControl
            (Q := R) (a := a) (a0 := a0) (s := s) hs
            (defect := defect) (energy := energy)
            (henergy_nonneg R hR) (henergy_int R hR)
            (hresp R hR) (hsum R hR)

/--
Localized flux-defect bridge with the existing descendant canonical response
data package exposed directly.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_descendantScalarCanonicalFluxDefectData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (defect : Vec d → Vec d) (energy : Vec d → ℝ) (j : ℕ)
    {lam0 Lam0 : ℝ}
    (hs : 0 < s)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hdesc :
      ∀ R ∈ descendantsAtDepth Q j,
        DescendantScalarCanonicalFluxDefectData R a a0 defect energy)
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R, 0 ≤ energy x)
    (henergy_int :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume)
    (hpartialBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminorm R s N defect))
    (hsum :
      ∀ R ∈ descendantsAtDepth Q j,
        Summable (fun n : ℕ =>
          geometricWeight s 1 n *
            scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0)) :
    localizedFluxDefectNegativeBesovAverageTwo Q s defect j ≤
      Real.sqrt
        (descendantsAverage Q j fun R =>
          ((geometricDiscount s 1)⁻¹ *
            HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 *
              (Real.sqrt (((4 : ℝ) * matNorm a0)) *
                Real.sqrt (cubeAverage R energy))) ^ 2) :=
  localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_descendant_coarseFluxResponse
    Q a a0 s defect energy j hs henergy_nonneg henergy_int
    (fun R hR =>
      cubeAverageFluxResponseControl_of_descendantScalarCanonicalFluxDefectData
        (Q := R) (a := a) (a0 := a0) (defect := defect) (energy := energy)
        ha0 ha0symm (hdesc R hR))
    hpartialBdd hsum

/-- Named response-average version of
`localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_descendant_coarseFluxResponse`.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_le_localizedCoarseFluxResponseAverageBound_of_descendant_coarseFluxResponse
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (defect : Vec d → Vec d) (energy : Vec d → ℝ) (j : ℕ)
    (hs : 0 < s)
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R, 0 ≤ energy x)
    (henergy_int :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume)
    (hresp :
      ∀ R ∈ descendantsAtDepth Q j,
        CubeAverageFluxResponseControl R a a0 defect energy)
    (hpartialBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminorm R s N defect))
    (hsum :
      ∀ R ∈ descendantsAtDepth Q j,
        Summable (fun n : ℕ =>
          geometricWeight s 1 n *
            scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0)) :
    localizedFluxDefectNegativeBesovAverageTwo Q s defect j ≤
      localizedCoarseFluxResponseAverageBound Q a a0 s j energy := by
  simpa [localizedCoarseFluxResponseAverageBound] using
    localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_descendant_coarseFluxResponse
      Q a a0 s defect energy j hs henergy_nonneg henergy_int hresp hpartialBdd hsum

/-- Named response-average version with descendant scalar-canonical data. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_le_localizedCoarseFluxResponseAverageBound_of_descendantScalarCanonicalFluxDefectData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (defect : Vec d → Vec d) (energy : Vec d → ℝ) (j : ℕ)
    {lam0 Lam0 : ℝ}
    (hs : 0 < s)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hdesc :
      ∀ R ∈ descendantsAtDepth Q j,
        DescendantScalarCanonicalFluxDefectData R a a0 defect energy)
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R, 0 ≤ energy x)
    (henergy_int :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume)
    (hpartialBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminorm R s N defect))
    (hsum :
      ∀ R ∈ descendantsAtDepth Q j,
        Summable (fun n : ℕ =>
          geometricWeight s 1 n *
            scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0)) :
    localizedFluxDefectNegativeBesovAverageTwo Q s defect j ≤
      localizedCoarseFluxResponseAverageBound Q a a0 s j energy := by
  simpa [localizedCoarseFluxResponseAverageBound] using
    localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_descendantScalarCanonicalFluxDefectData
      Q a a0 s defect energy j hs ha0 ha0symm hdesc henergy_nonneg henergy_int
      hpartialBdd hsum

/-- The full Section 3.3.B right-hand side after applying the duality constant. -/
noncomputable def coarseGrainingL2Rhs {d : ℕ} [NeZero d]
    (Cdual : ℝ) (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d) : ℝ :=
  Cdual * s⁻¹ *
    coarseGrainingL2FluxDefectBound Q a a0 s j gradU g

/--
With depth zero and zero forcing, the full Section 3.3.B RHS collapses to the
homogeneous RHS after multiplication by the duality constant.
-/
@[simp] theorem coarseGrainingL2Rhs_depth_zero_zero_forcing {d : ℕ} [NeZero d]
    (Cdual : ℝ) (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU : Vec d → Vec d) :
    coarseGrainingL2Rhs Cdual Q a a0 s 0 gradU (0 : Vec d → Vec d) =
      Cdual * s⁻¹ *
        ((s⁻¹) * Real.sqrt (matNorm a0) *
          HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
            Real.sqrt (cubeAverage Q (coefficientEnergyDensity a gradU))) := by
  simp [coarseGrainingL2Rhs]

/--
Note-facing general coarse-graining apex for
`coarsegraining/chapters/ch3_deterministic_theory.tex`, lines 3009--3253.

This is Proposition `p.general.coarse.graining.p2.deterministic.theory` in the
project's modular form.  The displayed PDE equations for `u` and `v` are
represented by the equivalent weak comparison predicate
`IsHomogenizationComparisonPairOn`; the local Section-3.2.3 operator estimate
is represented by the single hypothesis `hcoarseFluxDefect`.  No quantitative
uniform ellipticity constants appear in the conclusion.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 gradU) j ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j gradU g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j gradU g := by
  subst a0
  calc
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) gradU gradV
        ≤ Cdual *
            s⁻¹ *
            localizedFluxDefectNegativeBesovAverageTwo Q s
              (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j :=
      solution_diff_l2_le_dualityConstant_mul_localizedFluxDefect_of_fluxDefect_negativeBesov_le
        hdual Q a sigma0 gradU gradV j hsigma0 hs_pos hs_lt_one hEll hcomparison
    _ ≤ Cdual * s⁻¹ *
          coarseGrainingL2FluxDefectBound Q a
            (scalarMatrix (d := d) sigma0) s j gradU g := by
        exact mul_le_mul_of_nonneg_left hcoarseFluxDefect
          (mul_nonneg hdual.1 (inv_nonneg.mpr hs_pos.le))
    _ = coarseGrainingL2Rhs Cdual Q a (scalarMatrix (d := d) sigma0) s j gradU g := rfl

/--
Constant-envelope version of
`solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxDefect_le`.

This is the form needed when the local flux-defect theorem supplies a
dimension-only multiple of the displayed Section 3.3.B flux-defect RHS.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_mul_const_of_coarseFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual K : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 gradU) j ≤
        K * coarseGrainingL2FluxDefectBound Q a a0 s j gradU g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs (Cdual * K) Q a a0 s j gradU g := by
  subst a0
  calc
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) gradU gradV
        ≤ Cdual *
            s⁻¹ *
            localizedFluxDefectNegativeBesovAverageTwo Q s
              (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j :=
      solution_diff_l2_le_dualityConstant_mul_localizedFluxDefect_of_fluxDefect_negativeBesov_le
        hdual Q a sigma0 gradU gradV j hsigma0 hs_pos hs_lt_one hEll hcomparison
    _ ≤ Cdual * s⁻¹ *
          (K * coarseGrainingL2FluxDefectBound Q a
            (scalarMatrix (d := d) sigma0) s j gradU g) := by
        exact mul_le_mul_of_nonneg_left hcoarseFluxDefect
          (mul_nonneg hdual.1 (inv_nonneg.mpr hs_pos.le))
    _ =
        coarseGrainingL2Rhs (Cdual * K) Q a
          (scalarMatrix (d := d) sigma0) s j gradU g := by
        simp [coarseGrainingL2Rhs]
        ring

/--
General coarse-graining comparison with a caller-supplied scalar upper bound
for the Section 3.3.B flux-defect RHS.

This is a downstream-friendly reformulation of manuscript lines 3009--3253:
once the local coarse flux-defect estimate gives the note RHS and the caller
has bounded that RHS by `coarseGrainingBound`, the comparison estimate is
immediate with the same dimension-only duality constant.
-/
theorem solution_diff_l2_le_dualityConstant_mul_coarseGrainingBound_of_coarseFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s coarseGrainingBound : ℝ} (j : ℕ)
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 gradU) j ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j gradU g)
    (hcoarseGrainingBound :
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g ≤ coarseGrainingBound) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      Cdual * s⁻¹ * coarseGrainingBound :=
  by
  subst a0
  exact
  solution_diff_l2_le_dualityConstant_mul_fluxDefectBound_of_localizedFluxDefect_le
    hdual Q a sigma0 gradU gradV j hsigma0 hs_pos hs_lt_one hEll hcomparison
    (hcoarseFluxDefect.trans hcoarseGrainingBound)

/--
Note-facing general coarse-graining apex with the manuscript PDE hypotheses
exposed directly.

This is Proposition `p.general.coarse.graining.p2.deterministic.theory`,
manuscript lines 3009--3253.  The equations
`-div(a∇u)=div g` and `-div(a₀∇v)=div g` are represented by the `H¹` weak
solution predicates below, while the boundary condition is the zero-trace
potentiality of `∇u - ∇v`.  The local Section-3.2.3 flux-defect estimate still
enters as the single quantitative hypothesis `hcoarseFluxDefect`.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_of_coarseFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.grad) j ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j u.grad g) :
    solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j u.grad g := by
  subst a0
  exact
  solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxDefect_le
    hdual Q a (scalarMatrix (d := d) sigma0) sigma0 u.grad v.grad g j
      hsigma0 rfl hs_pos hs_lt_one hEll
      (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
        hEll (isEllipticMatrix_scalarMatrix hsigma0) u v g hu hv hzeroTrace)
      hcoarseFluxDefect

/--
Same-right-hand-side version with a caller-supplied nonnegative constant in the
local flux-defect bound.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_mul_const_of_sameRhs_of_coarseFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual K : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.grad) j ≤
        K * coarseGrainingL2FluxDefectBound Q a a0 s j u.grad g) :
    solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
      coarseGrainingL2Rhs (Cdual * K) Q a a0 s j u.grad g := by
  subst a0
  exact
  solution_diff_l2_le_coarseGrainingL2Rhs_mul_const_of_coarseFluxDefect_le
    hdual Q a (scalarMatrix (d := d) sigma0) sigma0 u.grad v.grad g j
      hsigma0 rfl hs_pos hs_lt_one hEll
      (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
        hEll (isEllipticMatrix_scalarMatrix hsigma0) u v g hu hv hzeroTrace)
      hcoarseFluxDefect

/--
Same-right-hand-side general coarse-graining comparison with a caller-supplied
scalar upper bound for the Section 3.3.B flux-defect RHS.
-/
theorem solution_diff_l2_le_dualityConstant_mul_coarseGrainingBound_of_sameRhs_of_coarseFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d)
    {s coarseGrainingBound : ℝ} (j : ℕ) {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.grad) j ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j u.grad g)
    (hcoarseGrainingBound :
      coarseGrainingL2FluxDefectBound Q a a0 s j u.grad g ≤ coarseGrainingBound) :
    solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
      Cdual * s⁻¹ * coarseGrainingBound :=
  by
  subst a0
  exact
  solution_diff_l2_le_dualityConstant_mul_coarseGrainingBound_of_coarseFluxDefect_le
    hdual Q a (scalarMatrix (d := d) sigma0) sigma0 u.grad v.grad g j
      hsigma0 rfl hs_pos hs_lt_one hEll
      (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
        hEll (isEllipticMatrix_scalarMatrix hsigma0) u v g hu hv hzeroTrace)
      hcoarseFluxDefect hcoarseGrainingBound

end

end Homogenization
