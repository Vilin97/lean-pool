/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.Response
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.SeminormRecurrence
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesPositiveQTwo
import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities

/-! # RHS -/

namespace Real

/-- Square-root comparison from a nonnegative square-side bound. -/
theorem sqrt_le_of_le_sq {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A ≤ B ^ 2) :
    Real.sqrt A ≤ B := by
  refine le_of_sq_le_sq ?_ hB
  simpa [Real.sq_sqrt hA] using hAB

end Real

namespace Homogenization

noncomputable section

/-!
# Coarse-flux response with right-hand side

This file starts the Lean surface for manuscript §3.2.4,
`l.coarse.grained.flux.response.RHS.deterministic.theory`.

The key distinction from §3.2.3 is the field being controlled: §3.2.3 estimates
`a∇u`, while §3.2.4 estimates the actual coarse flux defect `(a-a₀)∇u`.
The first lemmas here package the homogeneous response contribution in the
`q = 2` negative seminorm used by the downstream §3.3 duality lemma.
-/

open scoped BigOperators ENNReal

/-- The q=1 homogeneous coarse-flux response bound from §3.1.3. -/
noncomputable def coarseFluxResponseQOneBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : AHarmonicFunction a (cubeSet Q)) : ℝ :=
  (geometricDiscount s 1)⁻¹ *
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
      (Real.sqrt (((4 : ℝ) * matNorm a0)) *
        Real.sqrt (cubeAverage Q (scalarVariationEnergyIntegrand a u)))

/--
The one-cube §3.2.4 RHS flux-response bound, before the descendant-depth
inflation used in §3.3.B.

This mirrors the manuscript display
`e.coarse.grained.flux.response.RHS.deterministic.theory` on one cube.
-/
noncomputable def coarseFluxResponseRHSBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d) : ℝ :=
  (s⁻¹) * Real.sqrt (matNorm a0) *
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
      Real.sqrt (cubeAverage Q (coefficientEnergyDensity a gradU)) +
    (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
        Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 +
      Real.rpow s (-(5 / 2 : ℝ)) *
        Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
        Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) +
      Real.rpow s (-3 : ℝ) *
        matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
      cubeBesovPositiveVectorSeminormTwo Q s g

/-- The `∇u`-energy part of the §3.2.4 RHS flux-response bound. -/
noncomputable def coarseFluxResponseRHSEnergyBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU : Vec d → Vec d) : ℝ :=
  (s⁻¹) * Real.sqrt (matNorm a0) *
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
      Real.sqrt (cubeAverage Q (coefficientEnergyDensity a gradU))

/--
The forcing contribution in the homogeneous-response part of the §3.2.4 split.
It comes from replacing the harmonic energy of `w = u - v` by the energy of
`u` plus the zero-Dirichlet RHS energy estimate for `v`.
-/
noncomputable def coarseFluxResponseRHSResponseCorrectionBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
    Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
    cubeBesovPositiveVectorSeminormTwo Q s g

/-- The weak-flux estimate contribution for the correction field `a∇v`. -/
noncomputable def coarseFluxResponseRHSWeakFluxCorrectionBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  Real.rpow s (-(5 / 2 : ℝ)) *
    Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
    Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
    cubeBesovPositiveVectorSeminormTwo Q s g

/-- The RHS Poincare contribution for the constant-coefficient correction `a₀∇v`. -/
noncomputable def coarseFluxResponseRHSPoincareCorrectionBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  Real.rpow s (-3 : ℝ) *
    matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
    cubeBesovPositiveVectorSeminormTwo Q s g

/-- The homogeneous split component after the zero-Dirichlet energy correction. -/
noncomputable def coarseFluxResponseRHSHomogeneousSplitBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d) : ℝ :=
  coarseFluxResponseRHSEnergyBound Q a a0 s gradU +
    coarseFluxResponseRHSResponseCorrectionBound Q a a0 s g

/--
The explicit split-envelope produced by the Lean q=2 triangle wrappers before
absorbing harmless dimensional constants into the manuscript's `C(d)`.
-/
noncomputable def coarseFluxResponseRHSSplitEnvelope {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d) : ℝ :=
  Real.sqrt 2 *
    (Real.sqrt 2 *
      (coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g +
        coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) +
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g)

theorem coarseFluxResponseRHSBound_eq_component_sum {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d) :
    coarseFluxResponseRHSBound Q a a0 s gradU g =
      coarseFluxResponseRHSEnergyBound Q a a0 s gradU +
        coarseFluxResponseRHSResponseCorrectionBound Q a a0 s g +
        coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g +
        coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  unfold coarseFluxResponseRHSBound
    coarseFluxResponseRHSEnergyBound
    coarseFluxResponseRHSResponseCorrectionBound
    coarseFluxResponseRHSWeakFluxCorrectionBound
    coarseFluxResponseRHSPoincareCorrectionBound
  ring

private theorem coarseFluxResponse_homogenizationErrorOnCube_infinity_one_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
  apply tsum_nonneg
  intro n
  exact mul_nonneg (geometricWeight_nonneg n (by simpa using hs))
    (scaleResponseAtScale_infinity_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0)

/--
The descendant ellipticity hypothesis includes the parent cube itself at
depth zero.
-/
theorem isEllipticFieldOn_self_of_descendant_isEllipticFieldOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a) :
    IsEllipticFieldOn lam Lam (cubeSet Q) a :=
  hEll_desc Q ⟨0, by simp⟩

/-- Coefficient-energy cube averages are nonnegative under ellipticity. -/
theorem cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (F : Vec d → Vec d)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    0 ≤ cubeAverage Q (coefficientEnergyDensity a F) :=
  cubeAverage_nonneg_of_nonneg_on (Q := Q)
    (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll F)

/--
Descendant version of coefficient-energy average nonnegativity from a
descendant ellipticity hypothesis.
-/
theorem cubeAverage_coefficientEnergyDensity_nonneg_of_descendant_isEllipticFieldOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (F : Vec d → Vec d)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a) :
    ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
      0 ≤ cubeAverage R (coefficientEnergyDensity a F) := by
  intro n R hR
  exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
    R a F (hEll_desc R ⟨n, hR⟩)

theorem coarseFluxResponseRHSEnergyBound_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradU : Vec d → Vec d) (hs : 0 < s) :
    0 ≤ coarseFluxResponseRHSEnergyBound Q a a0 s gradU := by
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have herror_nonneg :
      0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 :=
    coarseFluxResponse_homogenizationErrorOnCube_infinity_one_nonneg Q a a0 hs.le
  unfold coarseFluxResponseRHSEnergyBound
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hs_inv_nonneg (Real.sqrt_nonneg _))
        herror_nonneg)
      (Real.sqrt_nonneg _)

theorem coarseFluxResponseRHSResponseCorrectionBound_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    0 ≤ coarseFluxResponseRHSResponseCorrectionBound Q a a0 s g := by
  have hs_rpow_nonneg : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have herror_nonneg :
      0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 :=
    coarseFluxResponse_homogenizationErrorOnCube_infinity_one_nonneg Q a a0 hs.le
  have hB_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hgBdd
  unfold coarseFluxResponseRHSResponseCorrectionBound
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hs_rpow_nonneg (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        herror_nonneg)
      hB_nonneg

theorem coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    {s : ℝ} (g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  have hs_rpow_nonneg : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have hB_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hgBdd
  unfold coarseFluxResponseRHSWeakFluxCorrectionBound
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hs_rpow_nonneg (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
      hB_nonneg

theorem coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    0 ≤ coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  have hs_rpow_nonneg : 0 ≤ Real.rpow s (-3 : ℝ) :=
    Real.rpow_nonneg hs.le _
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith)
  have hlambda_inv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  have hB_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hgBdd
  unfold coarseFluxResponseRHSPoincareCorrectionBound
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hs_rpow_nonneg (matNorm_nonneg a0))
        hlambda_inv_nonneg)
      hB_nonneg

theorem coarseFluxResponseRHSBound_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradU g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    0 ≤ coarseFluxResponseRHSBound Q a a0 s gradU g := by
  rw [coarseFluxResponseRHSBound_eq_component_sum]
  exact
    add_nonneg
      (add_nonneg
        (add_nonneg
          (coarseFluxResponseRHSEnergyBound_nonneg Q a a0 gradU hs)
          (coarseFluxResponseRHSResponseCorrectionBound_nonneg_of_bddAbove
            Q a a0 g hs hgBdd))
        (coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
          Q a g hs hgBdd))
      (coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
        Q a a0 g hs hgBdd)

/--
Homogeneous §3.2.4 component: the q=1 coarse-flux response theorem for an
`a`-harmonic field supplies the q=2 flux-defect control required by the
inhomogeneous split.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseQOneBound_of_aHarmonicFunction
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) {lam Lam lam0 Lam0 : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (u : AHarmonicFunction a (cubeSet Q))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad) ≤
      coarseFluxResponseQOneBound Q a a0 s u := by
  refine
    cubeBesovNegativeVectorSeminormTwo_le_of_qone_partialBound
      Q s (fluxDefect a a0 u.toH1.grad) ?_
  intro N
  simpa [fluxDefect, coarseFluxResponseQOneBound] using!
    coarseFluxResponse_qone_partialSeminorm_le_of_aHarmonicFunction
      (Q := Q) (a := a) (a0 := a0) (s := s)
      hs hEll ha0 ha0symm u hsum N

/-- A bounded q=1 finite-depth family gives a bounded q=2 finite-depth family. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_partialSeminorm_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hpartialBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s N u)) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N u) := by
  rcases hpartialBdd with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rintro y ⟨N, rfl⟩
  exact
    (cubeBesovNegativeVectorPartialSeminormTwo_le_partialSeminorm Q s N u).trans
      (hB ⟨N, rfl⟩)

/-- Pointwise algebra behind the §3.2.4 split
`(a - a₀)∇u = (a - a₀)∇w + a∇v - a₀∇v`. -/
theorem fluxDefect_eq_add_sub_of_eq_add_on_cubeSet
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (gradU gradW gradV : Vec d → Vec d)
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = gradW x + gradV x) :
    ∀ x ∈ cubeSet Q,
      fluxDefect a a0 gradU x =
        fluxDefect a a0 gradW x + matVecMul (a x) (gradV x) -
          matVecMul a0 (gradV x) := by
  intro x hx
  ext i
  simp [fluxDefect, hgrad x hx, matVecMul_add, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

/--
Recompose the three §3.2.4 split components in the note-normalized negative
`q = 2` seminorm.

This is the Lean form of the triangle-inequality step in
`e.cg.flux.response.RHS.split.deterministic.theory`.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_split_components
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU gradW gradV : Vec d → Vec d)
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = gradW x + gradV x)
    (hdefectW_mem :
      MemVectorL2 (cubeSet Q) (fluxDefect a a0 gradW))
    (hfluxV_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (gradV x)))
    (ha0V_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (gradV x)))
    (hdefectW_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 gradW)))
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (gradV x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (gradV x)))) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      Real.sqrt 2 *
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradW) +
            cubeBesovNegativeVectorSeminormTwo Q s
              (fun x => matVecMul (a x) (gradV x))) +
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul a0 (gradV x))) := by
  let splitField : Vec d → Vec d :=
    fun x =>
      fluxDefect a a0 gradW x + matVecMul (a x) (gradV x) -
        matVecMul a0 (gradV x)
  have hEq :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) =
        cubeBesovNegativeVectorSeminormTwo Q s splitField := by
    exact cubeBesovNegativeVectorSeminormTwo_eq_of_eq_on_cubeSet
      (Q := Q) s (fluxDefect_eq_add_sub_of_eq_add_on_cubeSet Q a a0
        gradU gradW gradV hgrad)
  rw [hEq]
  exact
    cubeBesovNegativeVectorSeminormTwo_add_sub_le_sqrtTwo_mul_add_sqrtTwo_mul_add_of_bddAbove
      Q s (fluxDefect a a0 gradW)
      (fun x => matVecMul (a x) (gradV x))
      (fun x => matVecMul a0 (gradV x))
      hdefectW_mem hfluxV_mem ha0V_mem
      hdefectW_bdd hfluxV_bdd ha0V_bdd

/--
Component-facing §3.2.4 split theorem.  The hypotheses are exactly the three
estimates produced by the manuscript proof after splitting `u = w + v`:

* homogeneous response for `(a-a₀)∇w`, including the RHS energy correction;
* weak-flux RHS control of `a∇v`;
* RHS Poincare control of `a₀∇v`.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseRHSSplitEnvelope_of_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU gradW gradV g : Vec d → Vec d)
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = gradW x + gradV x)
    (hdefectW_mem :
      MemVectorL2 (cubeSet Q) (fluxDefect a a0 gradW))
    (hfluxV_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (gradV x)))
    (ha0V_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (gradV x)))
    (hdefectW_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 gradW)))
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (gradV x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (gradV x))))
    (hdefectW :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradW) ≤
        coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g)
    (hfluxV :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) ≤
        coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g)
    (ha0V :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤
        coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      coarseFluxResponseRHSSplitEnvelope Q a a0 s gradU g := by
  have hsplit :=
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_split_components
      Q a a0 s gradU gradW gradV hgrad
      hdefectW_mem hfluxV_mem ha0V_mem
      hdefectW_bdd hfluxV_bdd ha0V_bdd
  calc
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU)
        ≤
      Real.sqrt 2 *
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradW) +
            cubeBesovNegativeVectorSeminormTwo Q s
              (fun x => matVecMul (a x) (gradV x))) +
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul a0 (gradV x))) := hsplit
    _ ≤ coarseFluxResponseRHSSplitEnvelope Q a a0 s gradU g := by
          unfold coarseFluxResponseRHSSplitEnvelope
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          exact add_le_add
            (mul_le_mul_of_nonneg_left (add_le_add hdefectW hfluxV)
              (Real.sqrt_nonneg _))
            ha0V

/--
The same split-envelope theorem with the homogeneous component discharged by
the already-formalized q=1 coarse-flux response for an `a`-harmonic remainder.

The remaining hypotheses are the two correction estimates (`a∇v` and `a₀∇v`)
and the scalar comparison which replaces the harmonic-response energy of `w`
by the §3.2.4 homogeneous split bound.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseRHSSplitEnvelope_of_aHarmonicFunction_component_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) {lam Lam lam0 Lam0 : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (gradU gradV g : Vec d → Vec d)
    (w : AHarmonicFunction a (cubeSet Q))
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = w.toH1.grad x + gradV x)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0))
    (hhomogeneousEnergy :
      coarseFluxResponseQOneBound Q a a0 s w ≤
        coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g)
    (hfluxV_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (gradV x)))
    (ha0V_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (gradV x)))
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (gradV x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (gradV x))))
    (hfluxV :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) ≤
        coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g)
    (ha0V :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤
        coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      coarseFluxResponseRHSSplitEnvelope Q a a0 s gradU g := by
  have hfluxW_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (w.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2
  have ha0Field :
      IsEllipticFieldOn lam0 Lam0 (cubeSet Q) (constantCoeffField a0) :=
    isEllipticFieldOn_constantCoeffField (measurableSet_cubeSet Q) ha0
  have ha0W_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (w.toH1.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn ha0Field w.toH1.grad_memVectorL2
  have hdefectW_mem :
      MemVectorL2 (cubeSet Q) (fluxDefect a a0 w.toH1.grad) := by
    unfold fluxDefect
    exact hfluxW_mem.sub ha0W_mem
  have hdefectW_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 w.toH1.grad)) := by
    refine ⟨coarseFluxResponseQOneBound Q a a0 s w, ?_⟩
    rintro y ⟨N, rfl⟩
    exact
      (cubeBesovNegativeVectorPartialSeminormTwo_le_partialSeminorm
        Q s N (fluxDefect a a0 w.toH1.grad)).trans <| by
        simpa [fluxDefect, coarseFluxResponseQOneBound] using!
          coarseFluxResponse_qone_partialSeminorm_le_of_aHarmonicFunction
            (Q := Q) (a := a) (a0 := a0) (s := s)
            hs hEll ha0 ha0symm w hsum N
  have hdefectW :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 w.toH1.grad) ≤
        coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g := by
    exact
      (cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseQOneBound_of_aHarmonicFunction
        Q a a0 s hs hEll ha0 ha0symm w hsum).trans
        hhomogeneousEnergy
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseRHSSplitEnvelope_of_split_component_bounds
      Q a a0 s gradU w.toH1.grad gradV g hgrad
      hdefectW_mem hfluxV_mem ha0V_mem
      hdefectW_bdd hfluxV_bdd ha0V_bdd
      hdefectW hfluxV ha0V

/--
Note-facing recomposition wrapper for §3.2.4: once the harmonic defect,
corrector flux, and constant-coefficient corrector-gradient components have
been bounded by the manuscript RHS, the split theorem yields the desired
coarse-flux-response bound for `(a - a₀)∇u`.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseRHSBound_of_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU gradW gradV g : Vec d → Vec d)
    {BdefectW BfluxV Ba0V : ℝ}
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = gradW x + gradV x)
    (hdefectW_mem :
      MemVectorL2 (cubeSet Q) (fluxDefect a a0 gradW))
    (hfluxV_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (gradV x)))
    (ha0V_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (gradV x)))
    (hdefectW_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 gradW)))
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (gradV x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (gradV x))))
    (hdefectW :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradW) ≤ BdefectW)
    (hfluxV :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) ≤ BfluxV)
    (ha0V :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤ Ba0V)
    (hcomponents :
      Real.sqrt 2 * (Real.sqrt 2 * (BdefectW + BfluxV) + Ba0V) ≤
        coarseFluxResponseRHSBound Q a a0 s gradU g) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      coarseFluxResponseRHSBound Q a a0 s gradU g := by
  have hsplit :=
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_split_components
      Q a a0 s gradU gradW gradV hgrad
      hdefectW_mem hfluxV_mem ha0V_mem
      hdefectW_bdd hfluxV_bdd ha0V_bdd
  calc
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU)
        ≤
      Real.sqrt 2 *
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradW) +
            cubeBesovNegativeVectorSeminormTwo Q s
              (fun x => matVecMul (a x) (gradV x))) +
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul a0 (gradV x))) := hsplit
    _ ≤ Real.sqrt 2 * (Real.sqrt 2 * (BdefectW + BfluxV) + Ba0V) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          exact add_le_add
            (mul_le_mul_of_nonneg_left (add_le_add hdefectW hfluxV)
              (Real.sqrt_nonneg _))
            ha0V
    _ ≤ coarseFluxResponseRHSBound Q a a0 s gradU g := hcomponents

/--
Descendant `L²` average of the one-cube §3.2.4 RHS flux-response bound.
This is the scalar localization target that §3.3 has to compare with
`coarseGrainingL2FluxDefectBound`.
-/
noncomputable def localizedCoarseFluxResponseRHSBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d) : ℝ :=
  Real.sqrt
    (descendantsAverage Q j fun R =>
      (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2)

@[simp] theorem localizedCoarseFluxResponseRHSBound_zero {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d) :
    localizedCoarseFluxResponseRHSBound Q a a0 s 0 gradU g =
      |coarseFluxResponseRHSBound Q a a0 s gradU g| := by
  simp [localizedCoarseFluxResponseRHSBound, descendantsAverage, Real.sqrt_sq_eq_abs]

theorem localizedCoarseFluxResponseRHSBound_zero_of_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d)
    (hbound_nonneg : 0 ≤ coarseFluxResponseRHSBound Q a a0 s gradU g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s 0 gradU g =
      coarseFluxResponseRHSBound Q a a0 s gradU g := by
  rw [localizedCoarseFluxResponseRHSBound_zero, abs_of_nonneg hbound_nonneg]

theorem localizedCoarseFluxResponseRHSBound_zero_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradU g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    localizedCoarseFluxResponseRHSBound Q a a0 s 0 gradU g =
      coarseFluxResponseRHSBound Q a a0 s gradU g :=
  localizedCoarseFluxResponseRHSBound_zero_of_nonneg Q a a0 s gradU g
    (coarseFluxResponseRHSBound_nonneg_of_bddAbove Q a a0 gradU g hs hgBdd)

/--
If each descendant one-cube RHS bound is nonnegative and pointwise bounded by a
single scalar `B`, then its descendant `L²` average is bounded by `B`.
-/
theorem localizedCoarseFluxResponseRHSBound_le_of_descendant_bound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d) {B : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hbound_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSBound R a a0 s gradU g)
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSBound R a a0 s gradU g ≤ B) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤ B := by
  have hsq :
      descendantsAverage Q j
          (fun R => (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) ≤
        descendantsAverage Q j (fun _ : TriadicCube d => B ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    exact pow_le_pow_left₀ (hbound_nonneg R hR) (hpoint R hR) 2
  calc
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g
        ≤ Real.sqrt (descendantsAverage Q j (fun _ : TriadicCube d => B ^ 2)) := by
          exact Real.sqrt_le_sqrt hsq
    _ = B := by
          rw [descendantsAverage_const, Real.sqrt_sq hB_nonneg]

/--
Bounded-positive-Besov version of
`localizedCoarseFluxResponseRHSBound_le_of_descendant_bound`.
-/
theorem localizedCoarseFluxResponseRHSBound_le_of_descendant_bound_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d) {B : ℝ}
    (hs : 0 < s) (hB_nonneg : 0 ≤ B)
    (hgBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSBound R a a0 s gradU g ≤ B) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤ B :=
  localizedCoarseFluxResponseRHSBound_le_of_descendant_bound Q a a0 s j gradU g
    hB_nonneg
    (fun R hR =>
      coarseFluxResponseRHSBound_nonneg_of_bddAbove R a a0 gradU g hs
        (hgBdd R hR))
    hpoint

/--
Descendant-localized §3.2.4 RHS handoff from pointwise one-cube
coarse-flux-response bounds.

This is the averaging wrapper needed by the downstream §3.3.B duality surface:
if every depth-`j` descendant has the one-cube RHS bound, then the localized
`q = 2` average is bounded by the descendant `ℓ²` average of those RHS values.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_coarseFluxResponseRHSBound_sq_of_descendant_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d) (j : ℕ)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hbound :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      Real.sqrt
        (descendantsAverage Q j fun R =>
          (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) := by
  refine
    localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_pointwiseBound
      Q s (fluxDefect a a0 gradU) j
      (fun R => coarseFluxResponseRHSBound R a a0 s gradU g) ?_ hbound
  intro R hR
  exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove R s
    (fluxDefect a a0 gradU) (hdefect_bdd R hR)

/--
Named localized §3.2.4 RHS handoff from pointwise one-cube bounds.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_localizedCoarseFluxResponseRHSBound_of_descendant_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d) (j : ℕ)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hbound :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g := by
  simpa [localizedCoarseFluxResponseRHSBound] using
    localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_coarseFluxResponseRHSBound_sq_of_descendant_bounds
      Q a a0 s gradU g j hdefect_bdd hbound

/--
Descendant-localized §3.2.4 RHS handoff with the split components exposed on
each descendant cube.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_coarseFluxResponseRHSBound_sq_of_descendant_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU gradW gradV g : Vec d → Vec d) (j : ℕ)
    {BdefectW BfluxV Ba0V : TriadicCube d → ℝ}
    (hgrad :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ x ∈ cubeSet R, gradU x = gradW x + gradV x)
    (hdefectW_mem :
      ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) (fluxDefect a a0 gradW))
    (hfluxV_mem :
      ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (gradV x)))
    (ha0V_mem :
      ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) (fun x => matVecMul a0 (gradV x)))
    (hdefectU_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hdefectW_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradW)))
    (hfluxV_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (gradV x))))
    (ha0V_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul a0 (gradV x))))
    (hdefectW :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradW) ≤
          BdefectW R)
    (hfluxV :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (gradV x)) ≤ BfluxV R)
    (ha0V :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul a0 (gradV x)) ≤ Ba0V R)
    (hcomponents :
      ∀ R ∈ descendantsAtDepth Q j,
        Real.sqrt 2 * (Real.sqrt 2 * (BdefectW R + BfluxV R) + Ba0V R) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      Real.sqrt
        (descendantsAverage Q j fun R =>
          (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) := by
  refine
    localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_coarseFluxResponseRHSBound_sq_of_descendant_bounds
      Q a a0 s gradU g j hdefectU_bdd ?_
  intro R hR
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseRHSBound_of_split_component_bounds
      R a a0 s gradU gradW gradV g
      (hgrad R hR)
      (hdefectW_mem R hR) (hfluxV_mem R hR) (ha0V_mem R hR)
      (hdefectW_bdd R hR) (hfluxV_bdd R hR) (ha0V_bdd R hR)
      (hdefectW R hR) (hfluxV R hR) (ha0V R hR)
      (hcomponents R hR)

/--
Named localized §3.2.4 RHS handoff with the split components exposed on each
descendant cube.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_localizedCoarseFluxResponseRHSBound_of_descendant_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU gradW gradV g : Vec d → Vec d) (j : ℕ)
    {BdefectW BfluxV Ba0V : TriadicCube d → ℝ}
    (hgrad :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ x ∈ cubeSet R, gradU x = gradW x + gradV x)
    (hdefectW_mem :
      ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) (fluxDefect a a0 gradW))
    (hfluxV_mem :
      ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (gradV x)))
    (ha0V_mem :
      ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) (fun x => matVecMul a0 (gradV x)))
    (hdefectU_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hdefectW_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradW)))
    (hfluxV_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (gradV x))))
    (ha0V_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul a0 (gradV x))))
    (hdefectW :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradW) ≤
          BdefectW R)
    (hfluxV :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (gradV x)) ≤ BfluxV R)
    (ha0V :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul a0 (gradV x)) ≤ Ba0V R)
    (hcomponents :
      ∀ R ∈ descendantsAtDepth Q j,
        Real.sqrt 2 * (Real.sqrt 2 * (BdefectW R + BfluxV R) + Ba0V R) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g := by
  simpa [localizedCoarseFluxResponseRHSBound] using
    localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_coarseFluxResponseRHSBound_sq_of_descendant_split_component_bounds
      Q a a0 s gradU gradW gradV g j hgrad hdefectW_mem hfluxV_mem
      ha0V_mem hdefectU_bdd hdefectW_bdd hfluxV_bdd ha0V_bdd
      hdefectW hfluxV ha0V hcomponents

end

end Homogenization
