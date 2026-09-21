/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHS

/-! # RHSConstant Envelope -/

namespace Homogenization

noncomputable section

/-!
# Constant envelopes for the RHS coarse-flux response

The manuscript statement of §3.2.4 carries an unspecified dimensional constant
`C(d)`.  The base `coarseFluxResponseRHSBound` names the displayed scalar RHS
without this constant.  This leaf module keeps the harmless constant envelope
available at the split/recomposition and descendant-averaging surfaces.
-/

open scoped BigOperators ENNReal

private theorem sqrt_two_mul_add_le_two_mul_add {A B : ℝ}
    (hB : 0 ≤ B) :
    Real.sqrt 2 * (Real.sqrt 2 * A + B) ≤ 2 * (A + B) := by
  have hsqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hsqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
    have hlt : Real.sqrt 2 < (3 / 2 : ℝ) := Real.sqrt_two_lt_three_halves
    linarith
  calc
    Real.sqrt 2 * (Real.sqrt 2 * A + B)
        = (Real.sqrt 2 * Real.sqrt 2) * A + Real.sqrt 2 * B := by
          ring
    _ = 2 * A + Real.sqrt 2 * B := by
          rw [hsqrt_two_sq]
    _ ≤ 2 * A + 2 * B := by
          exact add_le_add (le_refl (2 * A))
            (mul_le_mul_of_nonneg_right hsqrt_two_le_two hB)
    _ = 2 * (A + B) := by ring

/--
Generic target version of the §3.2.4 split-component recomposition theorem.
This is useful when the component estimates close into `C(d)` times the named
bare RHS rather than the bare RHS itself.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_of_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU gradW gradV : Vec d → Vec d)
    {BdefectW BfluxV Ba0V B : ℝ}
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
      Real.sqrt 2 * (Real.sqrt 2 * (BdefectW + BfluxV) + Ba0V) ≤ B) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤ B := by
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
    _ ≤ B := hcomponents

/--
Constant-envelope version of the one-cube §3.2.4 split recomposition.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_const_mul_coarseFluxResponseRHSBound_of_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (gradU gradW gradV g : Vec d → Vec d)
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
        C * coarseFluxResponseRHSBound Q a a0 s gradU g) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      C * coarseFluxResponseRHSBound Q a a0 s gradU g :=
  cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_of_split_component_bounds
    Q a a0 s gradU gradW gradV hgrad
    hdefectW_mem hfluxV_mem ha0V_mem
    hdefectW_bdd hfluxV_bdd ha0V_bdd
    hdefectW hfluxV ha0V hcomponents

/--
The split-envelope triangle constants for component bounds that already carry
the same nonnegative multiplier `C`.
-/
theorem coarseFluxResponseRHSScaledSplitEnvelope_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {C s : ℝ} (gradU g : Vec d → Vec d)
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    Real.sqrt 2 *
        (Real.sqrt 2 *
          (C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g +
            C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) +
          C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ≤
      2 * C * coarseFluxResponseRHSBound Q a a0 s gradU g := by
  have hpoincare_nonneg :
      0 ≤ C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g :=
    mul_nonneg hC_nonneg
      (coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
        Q a a0 g hs hgBdd)
  calc
    Real.sqrt 2 *
        (Real.sqrt 2 *
          (C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g +
            C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) +
          C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g)
        ≤
      2 *
        ((C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g +
            C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) +
          C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :=
          sqrt_two_mul_add_le_two_mul_add hpoincare_nonneg
    _ = 2 * C * coarseFluxResponseRHSBound Q a a0 s gradU g := by
          rw [coarseFluxResponseRHSBound_eq_component_sum]
          unfold coarseFluxResponseRHSHomogeneousSplitBound
          ring

/--
Split-component recomposition when every component estimate closes into the
same constant multiple of its compact §3.2.4 component.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_const_mul_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {C s : ℝ} (gradU gradW gradV g : Vec d → Vec d)
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
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
        C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g)
    (hfluxV :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) ≤
        C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g)
    (ha0V :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤
        C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      2 * C * coarseFluxResponseRHSBound Q a a0 s gradU g :=
  cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_of_split_component_bounds
    Q a a0 s gradU gradW gradV hgrad
    hdefectW_mem hfluxV_mem ha0V_mem
    hdefectW_bdd hfluxV_bdd ha0V_bdd
    hdefectW hfluxV ha0V
    (coarseFluxResponseRHSScaledSplitEnvelope_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_bddAbove
      Q a a0 gradU g hC_nonneg hs hgBdd)

/--
Descendant-localized split-component handoff to an arbitrary scalar envelope.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_bound_sq_of_descendant_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU gradW gradV : Vec d → Vec d) (j : ℕ)
    {BdefectW BfluxV Ba0V B : TriadicCube d → ℝ}
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
          B R) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      Real.sqrt (descendantsAverage Q j fun R => (B R) ^ 2) := by
  refine
    localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_pointwiseBound
      Q s (fluxDefect a a0 gradU) j B ?_ ?_
  · intro R hR
    exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove R s
      (fluxDefect a a0 gradU) (hdefectU_bdd R hR)
  · intro R hR
    exact
      cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_of_split_component_bounds
        R a a0 s gradU gradW gradV
        (hgrad R hR)
        (hdefectW_mem R hR) (hfluxV_mem R hR) (ha0V_mem R hR)
        (hdefectW_bdd R hR) (hfluxV_bdd R hR) (ha0V_bdd R hR)
        (hdefectW R hR) (hfluxV R hR) (ha0V R hR)
        (hcomponents R hR)

/--
Descendant-localized split-component handoff to `C` times the named bare
one-cube RHS on every descendant.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_const_mul_coarseFluxResponseRHSBound_sq_of_descendant_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (gradU gradW gradV g : Vec d → Vec d) (j : ℕ)
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
          C * coarseFluxResponseRHSBound R a a0 s gradU g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      Real.sqrt
        (descendantsAverage Q j fun R =>
          (C * coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) :=
  localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_bound_sq_of_descendant_split_component_bounds
    Q a a0 s gradU gradW gradV j
    hgrad hdefectW_mem hfluxV_mem ha0V_mem
    hdefectU_bdd hdefectW_bdd hfluxV_bdd ha0V_bdd
    hdefectW hfluxV ha0V hcomponents

/--
Pull a nonnegative scalar outside the descendant `L²` average of the named
one-cube §3.2.4 RHS bound.
-/
theorem sqrt_descendantsAverage_const_mul_coarseFluxResponseRHSBound_sq_eq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {C s : ℝ} (gradU g : Vec d → Vec d) (j : ℕ)
    (hC_nonneg : 0 ≤ C) :
    Real.sqrt
        (descendantsAverage Q j fun R =>
          (C * coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) =
      C * localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g := by
  have havg_nonneg :
      0 ≤ descendantsAverage Q j fun R =>
        (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2 :=
    descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  have hscaled :
      descendantsAverage Q j
          (fun R => (C * coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) =
        C ^ 2 *
          descendantsAverage Q j
            (fun R => (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) := by
    calc
      descendantsAverage Q j
          (fun R => (C * coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2)
          =
        descendantsAverage Q j
          (fun R => C ^ 2 * (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) := by
            apply congrArg (descendantsAverage Q j)
            funext R
            ring
      _ =
        C ^ 2 *
          descendantsAverage Q j
            (fun R => (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) :=
          descendantsAverage_mul_left Q j (C ^ 2)
            (fun R => (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2)
  calc
    Real.sqrt
        (descendantsAverage Q j fun R =>
          (C * coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2)
        =
      Real.sqrt
        (C ^ 2 *
          descendantsAverage Q j
            (fun R => (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2)) := by
          rw [hscaled]
    _ =
      C *
        Real.sqrt
          (descendantsAverage Q j
            (fun R => (coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg C),
            Real.sqrt_sq hC_nonneg]
    _ = C * localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g := rfl

/--
Descendant-localized §3.2.4 handoff from pointwise one-cube bounds with a
caller-supplied scalar envelope.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_const_mul_coarseFluxResponseRHSBound_sq_of_descendant_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (gradU g : Vec d → Vec d) (j : ℕ)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hbound :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          C * coarseFluxResponseRHSBound R a a0 s gradU g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      Real.sqrt
        (descendantsAverage Q j fun R =>
          (C * coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) := by
  refine
    localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_pointwiseBound
      Q s (fluxDefect a a0 gradU) j
      (fun R => C * coarseFluxResponseRHSBound R a a0 s gradU g) ?_ hbound
  intro R hR
  exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove R s
    (fluxDefect a a0 gradU) (hdefect_bdd R hR)

/--
Named descendant-localized §3.2.4 handoff with the nonnegative scalar envelope
pulled outside the localized RHS norm.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_const_mul_localizedCoarseFluxResponseRHSBound_of_descendant_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {C s : ℝ} (gradU g : Vec d → Vec d) (j : ℕ)
    (hC_nonneg : 0 ≤ C)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hbound :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          C * coarseFluxResponseRHSBound R a a0 s gradU g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      C * localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g := by
  calc
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j
        ≤
      Real.sqrt
        (descendantsAverage Q j fun R =>
          (C * coarseFluxResponseRHSBound R a a0 s gradU g) ^ 2) :=
        localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_sqrt_descendantsAverage_const_mul_coarseFluxResponseRHSBound_sq_of_descendant_bounds
          Q a a0 C s gradU g j hdefect_bdd hbound
    _ = C * localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g :=
        sqrt_descendantsAverage_const_mul_coarseFluxResponseRHSBound_sq_eq
          Q a a0 gradU g j hC_nonneg

/--
Descendant-localized handoff for one-cube apex estimates whose target already
contains the formal split/recomposition constant `2 * C`.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_two_mul_const_mul_localizedCoarseFluxResponseRHSBound_of_descendant_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {C s : ℝ} (gradU g : Vec d → Vec d) (j : ℕ)
    (hC_nonneg : 0 ≤ C)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hbound :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          2 * C * coarseFluxResponseRHSBound R a a0 s gradU g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      2 * C * localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g := by
  exact
    localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_const_mul_localizedCoarseFluxResponseRHSBound_of_descendant_bounds
      Q a a0 gradU g j (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hC_nonneg)
      hdefect_bdd hbound

/--
Descendant-localized split-component handoff with the formal `2 * C`
split/recomposition constant already included in the localized endpoint.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_two_mul_const_mul_localizedCoarseFluxResponseRHSBound_of_descendant_const_mul_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {C s : ℝ} (gradU gradW gradV g : Vec d → Vec d) (j : ℕ)
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
    (hgBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
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
          C * coarseFluxResponseRHSHomogeneousSplitBound R a a0 s gradU g)
    (hfluxV :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (gradV x)) ≤
          C * coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (ha0V :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul a0 (gradV x)) ≤
          C * coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a a0 gradU) j ≤
      2 * C * localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g := by
  refine
    localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_two_mul_const_mul_localizedCoarseFluxResponseRHSBound_of_descendant_bounds
      Q a a0 gradU g j hC_nonneg hdefectU_bdd ?_
  intro R hR
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_const_mul_split_component_bounds
      (Q := R) (a := a) (a0 := a0) (C := C) (s := s)
      (gradU := gradU) (gradW := gradW) (gradV := gradV) (g := g)
      hC_nonneg hs (hgBdd R hR)
      (hgrad R hR)
      (hdefectW_mem R hR) (hfluxV_mem R hR) (ha0V_mem R hR)
      (hdefectW_bdd R hR) (hfluxV_bdd R hR) (ha0V_bdd R hR)
      (hdefectW R hR) (hfluxV R hR) (ha0V R hR)

end

end Homogenization
