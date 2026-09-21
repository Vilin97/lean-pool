/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletTail

/-! # RHSConstant Apex Zero Dirichlet Estimates -/

namespace Homogenization

noncomputable section

/-!
# Split estimate targets for the zero-Dirichlet RHS flux-response apex

This leaf separates the remaining analytic inputs to the §3.2.4
zero-Dirichlet one-cube apex into the two pieces supplied by the manuscript:

* the harmonic-remainder `BV` tail estimate;
* the displayed weak-flux and Poincare component inequalities.
-/

open scoped BigOperators ENNReal

namespace ZeroTraceDirichletCorrectorData

/--
Square expansion for the compact weak-flux correction factor.  This is the
scalar core needed by the displayed weak-flux radicand estimate.
-/
theorem coarseFluxResponseRHSWeakFluxCorrectionBound_sq_eq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g : Vec d → Vec d) (hs : 0 < s) :
    (coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2 =
      (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hLambda_nonneg :
      0 ≤ LambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambda_inv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  unfold coarseFluxResponseRHSWeakFluxCorrectionBound
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hLambda_nonneg,
    Real.sq_sqrt hlambda_inv_nonneg]

/--
Square expansion for the constant-multiplied compact weak-flux correction
factor.  This is the exact right-hand side shape of the displayed weak-flux
radicand estimate after the manuscript's constant `C(d)` is inserted.
-/
theorem const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_sq_eq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (C : ℝ) {s : ℝ}
    (g : Vec d → Vec d) (hs : 0 < s) :
    (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2 =
      C ^ 2 *
        (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  rw [mul_pow, coarseFluxResponseRHSWeakFluxCorrectionBound_sq_eq Q a g hs]
  ring

/--
Square expansion for the compact Poincare correction factor.  This is the
scalar core needed by the displayed Poincare radicand estimate.
-/
theorem coarseFluxResponseRHSPoincareCorrectionBound_sq_eq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (g : Vec d → Vec d) :
    (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 =
      (Real.rpow s (-3 : ℝ)) ^ 2 *
        (matNorm a0) ^ 2 *
        ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  unfold coarseFluxResponseRHSPoincareCorrectionBound
  ring

/--
Square expansion for the constant-multiplied compact Poincare correction
factor.  This is the exact right-hand side shape of the displayed Poincare
radicand estimate after the manuscript's constant `C(d)` is inserted.
-/
theorem const_mul_coarseFluxResponseRHSPoincareCorrectionBound_sq_eq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (C s : ℝ)
    (g : Vec d → Vec d) :
    (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 =
      C ^ 2 *
        (Real.rpow s (-3 : ℝ)) ^ 2 *
        (matNorm a0) ^ 2 *
        ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  rw [mul_pow, coarseFluxResponseRHSPoincareCorrectionBound_sq_eq Q a a0 s g]
  ring

/-- Boundedness side of the harmonic-remainder tail package. -/
def zeroTraceDirichletHarmonicRemainderTailBounded {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (s : ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    ∀ ω : MeanZeroNeumannCorrectorData R a
        (fun x => g x - cubeAverageVec R g),
      ∀ w0 : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          ρ.toH10.toH1Function.grad x =
            w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => w0.toH1.grad x))

/-- Squared `BV` estimate side of the harmonic-remainder tail package. -/
def zeroTraceDirichletHarmonicRemainderBVEstimate {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (s BV : ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    ∀ ω : MeanZeroNeumannCorrectorData R a
        (fun x => g x - cubeAverageVec R g),
      ∀ w0 : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          ρ.toH10.toH1Function.grad x =
            w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => w0.toH1.grad x)) ^ 2 ≤
          (coarsePoincareRHSDepthWeight s j)⁻¹ * BV

theorem zeroTraceDirichletHarmonicRemainderBVEstimate_mono {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {ρ : ZeroTraceDirichletCorrectorData Q a g}
    {s BV BV' : ℝ}
    (hBV : BV ≤ BV')
    (hestimate : zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV) :
    zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV' := by
  intro j R hR ω w0 hdecomp
  have hweight_nonneg : 0 ≤ (coarsePoincareRHSDepthWeight s j)⁻¹ := by
    have hweight_pos : 0 < coarsePoincareRHSDepthWeight s j := by
      unfold coarsePoincareRHSDepthWeight
      exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
    exact inv_nonneg.mpr hweight_pos.le
  exact
    (hestimate j R hR ω w0 hdecomp).trans
      (mul_le_mul_of_nonneg_left hBV hweight_nonneg)

theorem zeroTraceDirichletHarmonicRemainderTailBounded_of_pos {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s : ℝ} (hs : 0 < s) :
    zeroTraceDirichletHarmonicRemainderTailBounded ρ s := by
  intro j R hR ω w0 hdecomp
  exact
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs
      (fun x => w0.toH1.grad x)
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R
        w0.toH1.grad_memVectorL2)

theorem zeroTraceDirichletHarmonicRemainderTailClose_bounded {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {ρ : ZeroTraceDirichletCorrectorData Q a g}
    {s BV : ℝ}
    (h : zeroTraceDirichletHarmonicRemainderTailClose ρ s BV) :
    zeroTraceDirichletHarmonicRemainderTailBounded ρ s := by
  intro j R hR ω w0 hdecomp
  exact (zeroTraceDirichletHarmonicRemainderTailClose_constructed h
    j R hR ω w0 hdecomp).1

theorem zeroTraceDirichletHarmonicRemainderTailClose_bvEstimate {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {ρ : ZeroTraceDirichletCorrectorData Q a g}
    {s BV : ℝ}
    (h : zeroTraceDirichletHarmonicRemainderTailClose ρ s BV) :
    zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV := by
  intro j R hR ω w0 hdecomp
  exact (zeroTraceDirichletHarmonicRemainderTailClose_constructed h
    j R hR ω w0 hdecomp).2

theorem zeroTraceDirichletHarmonicRemainderTailClose_of_bounded_of_bvEstimate
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s BV : ℝ}
    (hBV_nonneg : 0 ≤ BV)
    (hbounded : zeroTraceDirichletHarmonicRemainderTailBounded ρ s)
    (hestimate : zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV) :
    zeroTraceDirichletHarmonicRemainderTailClose ρ s BV :=
  zeroTraceDirichletHarmonicRemainderTailClose_of_bounds ρ hBV_nonneg
    (by
      intro j R hR ω w0 hdecomp
      exact ⟨hbounded j R hR ω w0 hdecomp,
        hestimate j R hR ω w0 hdecomp⟩)

theorem zeroTraceDirichletHarmonicRemainderTailClose_of_bvEstimate {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s BV : ℝ}
    (hs : 0 < s)
    (hBV_nonneg : 0 ≤ BV)
    (hestimate : zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV) :
    zeroTraceDirichletHarmonicRemainderTailClose ρ s BV :=
  zeroTraceDirichletHarmonicRemainderTailClose_of_bounded_of_bvEstimate
    ρ hBV_nonneg
    (zeroTraceDirichletHarmonicRemainderTailBounded_of_pos ρ hs)
    hestimate

theorem zeroTraceDirichletHarmonicRemainderTailClose_iff_bounded_and_bvEstimate
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {ρ : ZeroTraceDirichletCorrectorData Q a g}
    {s BV : ℝ} :
    zeroTraceDirichletHarmonicRemainderTailClose ρ s BV ↔
      0 ≤ BV ∧
        zeroTraceDirichletHarmonicRemainderTailBounded ρ s ∧
        zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV :=
  ⟨fun h =>
      ⟨zeroTraceDirichletHarmonicRemainderTailClose_nonneg h,
        zeroTraceDirichletHarmonicRemainderTailClose_bounded h,
        zeroTraceDirichletHarmonicRemainderTailClose_bvEstimate h⟩,
    fun h =>
      zeroTraceDirichletHarmonicRemainderTailClose_of_bounded_of_bvEstimate
        ρ h.1 h.2.1 h.2.2⟩

theorem zeroTraceDirichletHarmonicRemainderTailClose_iff_bvEstimate_of_pos
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {ρ : ZeroTraceDirichletCorrectorData Q a g}
    {s BV : ℝ} (hs : 0 < s) :
    zeroTraceDirichletHarmonicRemainderTailClose ρ s BV ↔
      0 ≤ BV ∧ zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV :=
  ⟨fun h =>
      ⟨zeroTraceDirichletHarmonicRemainderTailClose_nonneg h,
        zeroTraceDirichletHarmonicRemainderTailClose_bvEstimate h⟩,
    fun h =>
      zeroTraceDirichletHarmonicRemainderTailClose_of_bvEstimate
        ρ hs h.1 h.2⟩

/--
A descendantwise zero-trace harmonic-remainder `BV` estimate controls the
scaled averaged harmonic-remainder tail used by the weak-flux RHS iteration,
for any selector whose values are produced by the local Neumann-corrector
decompositions.
-/
theorem zeroTraceDirichletHarmonicRemainderScaledAveragedTail_le_of_bvEstimate_of_selector
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {ρ : ZeroTraceDirichletCorrectorData Q a g}
    {s BV : ℝ}
    (hestimate : zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV)
    (v : TriadicCube d → Vec d → Vec d)
    (hselector :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∃ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∃ w0 : AHarmonicFunction a (cubeSet R),
            v R = (fun x => w0.toH1.grad x) ∧
            ∀ x ∈ cubeSet R,
              ρ.toH10.toH1Function.grad x =
                w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (m : ℕ) :
    ∀ k : ℕ,
      weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v (m + k) ≤
        BV := by
  exact
    weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_tail_le_of_descendant_scaled_sq_bound
      Q s v m
      (by
        intro k R hR
        rcases hselector R ⟨m + k, hR⟩ with
          ⟨ω, w0, hv_eq, hdecomp⟩
        have hsq := hestimate (m + k) R hR ω w0 hdecomp
        simpa [hv_eq] using hsq)

/--
The zero-force coarse-Poincare RHS theorem reduces the harmonic-remainder
`BV` estimate to descendantwise coefficient-energy control of the selected
harmonic remainders.
-/
theorem zeroTraceDirichletHarmonicRemainderBVEstimate_of_zeroForce_energy_bounds
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s BV lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (henergy :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∀ w0 : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              ρ.toH10.toH1Function.grad x =
                w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            250 * (s⁻¹) ^ 2 *
                (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage R
                  (coefficientEnergyDensity a
                    (fun x => w0.toH1.grad x)) ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV) :
    zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV := by
  intro j R hR ω w0 hdecomp
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll_desc R ⟨j, hR⟩
  have hzeroMem :
      MeasureTheory.MemLp (0 : Vec d → Vec d) (2 : ENNReal)
        (normalizedCubeMeasure R) := by
    simp
  have hsol :
      IsSolenoidalOn (cubeSet R)
        (fun x => matVecMul (a x) (w0.toH1.grad x) -
          (0 : Vec d → Vec d) x) := by
    simpa using w0.isHarmonic.2
  have hsq :
      (cubeBesovNegativeVectorSeminormTwo R s
        (fun x => w0.toH1.grad x)) ^ 2 ≤
        250 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => w0.toH1.grad x)) := by
    simpa using
      sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
        (Q := R) (a := a) (g := (0 : Vec d → Vec d))
        (u := fun x => w0.toH1.grad x)
        (s := s) (lam := lam) (Lam := Lam)
        hs hs_le hEllR w0.isHarmonic.1 hsol hzeroMem
        (cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove R s)
  exact hsq.trans (henergy j R hR ω w0 hdecomp)

/--
The local identity `ρ = w0 + ω` reduces the harmonic-remainder `BV` estimate
to separate coefficient-energy tail bounds for the zero-trace gradient and the
centered Neumann corrector.
-/
theorem zeroTraceDirichletHarmonicRemainderBVEstimate_of_corrector_neumann_energy_bounds
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s BV Bρ Bω lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hρEnergy :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) ≤
          (coarsePoincareRHSDepthWeight s j)⁻¹ * Bρ)
    (hωEnergy :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          500 * (s⁻¹) ^ 2 *
              (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
              cubeAverage R
                (coefficientEnergyDensity a
                  (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
            (coarsePoincareRHSDepthWeight s j)⁻¹ * Bω)
    (hbudget : Bρ + Bω ≤ BV) :
    zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV := by
  refine
    zeroTraceDirichletHarmonicRemainderBVEstimate_of_zeroForce_energy_bounds
      ρ hs hs_le hEll_desc ?_
  intro j R hR ω w0 hdecomp
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll_desc R ⟨j, hR⟩
  have hρMemQ :
      MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      ρ.toH10.toH1Function.grad_memVectorL2
  have hρMemR :
      MemVectorL2 (cubeSet R)
        (fun x => ρ.toH10.toH1Function.grad x) :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
      (memLp_on_descendant_of_memLp_generic (E := Vec d) hR hρMemQ)
  have hsplit :
      cubeAverage R
          (coefficientEnergyDensity a
            (fun x => w0.toH1.grad x)) ≤
        2 * cubeAverage R
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x)) +
        2 * cubeAverage R
          (coefficientEnergyDensity a
            (fun x => ω.toH1MeanZero.toH1Function.grad x)) :=
    ω.cubeAverage_coefficientEnergyDensity_harmonic_le_two_mul_add
      (u := fun x => ρ.toH10.toH1Function.grad x) w0 hEllR hdecomp
      hρMemR
  have hlambda_nonneg :
      0 ≤ lambdaSq R (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg R (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hcoeff_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 *
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  have hsplit_weighted :
      250 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage R
            (coefficientEnergyDensity a
              (fun x => w0.toH1.grad x)) ≤
        500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) +
          500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
    nlinarith [mul_le_mul_of_nonneg_left hsplit hcoeff_nonneg]
  have hsplit_bound :
      500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) +
          500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
        (coarsePoincareRHSDepthWeight s j)⁻¹ * Bρ +
          (coarsePoincareRHSDepthWeight s j)⁻¹ * Bω :=
    add_le_add (hρEnergy j R hR) (hωEnergy j R hR ω)
  have hweight_nonneg :
      0 ≤ (coarsePoincareRHSDepthWeight s j)⁻¹ := by
    have hweight_pos : 0 < coarsePoincareRHSDepthWeight s j := by
      unfold coarsePoincareRHSDepthWeight
      exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
    exact inv_nonneg.mpr hweight_pos.le
  have hbudget_weighted :
      (coarsePoincareRHSDepthWeight s j)⁻¹ * Bρ +
          (coarsePoincareRHSDepthWeight s j)⁻¹ * Bω ≤
        (coarsePoincareRHSDepthWeight s j)⁻¹ * BV := by
    calc
      (coarsePoincareRHSDepthWeight s j)⁻¹ * Bρ +
          (coarsePoincareRHSDepthWeight s j)⁻¹ * Bω
          =
        (coarsePoincareRHSDepthWeight s j)⁻¹ * (Bρ + Bω) := by
          ring
      _ ≤ (coarsePoincareRHSDepthWeight s j)⁻¹ * BV :=
          mul_le_mul_of_nonneg_left hbudget hweight_nonneg
  exact hsplit_weighted.trans (hsplit_bound.trans hbudget_weighted)

/--
The centered Neumann-corrector energy identity controls the Neumann half of
the harmonic-remainder `BV` reduction by the product of the corrector negative
seminorm and the centered forcing positive seminorm.
-/
theorem zeroTraceDirichletHarmonicRemainderBVEstimate_of_corrector_energy_and_neumann_seminorm_bounds
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s BV Bρ Bω lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hg_mem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R))
    (hgBdd_centered_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    (hρEnergy :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) ≤
          (coarsePoincareRHSDepthWeight s j)⁻¹ * Bρ)
    (hωSeminormTail :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          500 * (s⁻¹) ^ 2 *
              (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
                cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => ω.toH1MeanZero.toH1Function.grad x) *
                cubeBesovPositiveVectorSeminormTwo R s
                  (fun x => g x - cubeAverageVec R g))) ≤
            (coarsePoincareRHSDepthWeight s j)⁻¹ * Bω)
    (hbudget : Bρ + Bω ≤ BV) :
    zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV := by
  refine
    zeroTraceDirichletHarmonicRemainderBVEstimate_of_corrector_neumann_energy_bounds
      ρ hs hs_le hEll_desc hρEnergy ?_ hbudget
  intro j R hR ω
  have hgR :
      MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R) :=
    hg_mem_desc j R hR
  have hgMemR : MemVectorL2 (cubeSet R) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R hgR
  have hωgrad :
      MeasureTheory.MemLp (fun x => ω.toH1MeanZero.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R
      ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hωBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs
      (fun x => ω.toH1MeanZero.toH1Function.grad x) hωgrad
  have hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N
          (fun x => g x - cubeAverageVec R g)) :=
    hgBdd_centered_desc j R hR
  have hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo R s
        (fun x => g x - cubeAverageVec R g) :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove R s
      (fun x => g x - cubeAverageVec R g) hgBdd
  have henergy :=
    ω.coefficientEnergy_average_le_collapsed_note_term_centered_two_two
      (s := s)
      (Bω :=
        cubeBesovNegativeVectorSeminormTwo R s
          (fun x => ω.toH1MeanZero.toH1Function.grad x))
      (Bg :=
        cubeBesovPositiveVectorSeminormTwo R s
          (fun x => g x - cubeAverageVec R g))
      hs hgMemR hgR hωgrad hBg
      (fun N =>
        cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          R s (fun x => ω.toH1MeanZero.toH1Function.grad x) hωBdd N)
      (fun N =>
        cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          R s (fun x => g x - cubeAverageVec R g) hgBdd N)
  have hlambda_nonneg :
      0 ≤ lambdaSq R (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg R (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hcoeff_nonneg :
      0 ≤ 500 * (s⁻¹) ^ 2 *
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (500 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  exact
    (mul_le_mul_of_nonneg_left henergy hcoeff_nonneg).trans
      (hωSeminormTail j R hR ω)

theorem zeroTraceDirichletHarmonicRemainderBVEstimate_of_corrector_energy_and_neumann_young_bounds
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s BV Bρ BωNeg BωForce lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hg_mem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R))
    (hgBdd_centered_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    (hρEnergy :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) ≤
          (coarsePoincareRHSDepthWeight s j)⁻¹ * Bρ)
    (hωNegSqTail :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          250 * (s⁻¹) ^ 2 *
              (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
              (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) ^ 2 ≤
            (coarsePoincareRHSDepthWeight s j)⁻¹ * BωNeg)
    (hcenteredForceSqTail :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        250 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
              cubeBesovPositiveVectorSeminormTwo R s
                (fun x => g x - cubeAverageVec R g))) ^ 2 ≤
          (coarsePoincareRHSDepthWeight s j)⁻¹ * BωForce)
    (hbudget : Bρ + (BωNeg + BωForce) ≤ BV) :
    zeroTraceDirichletHarmonicRemainderBVEstimate ρ s BV := by
  refine
    zeroTraceDirichletHarmonicRemainderBVEstimate_of_corrector_energy_and_neumann_seminorm_bounds
      ρ hs hs_le hEll_desc hg_mem_desc hgBdd_centered_desc hρEnergy ?_
      hbudget
  intro j R hR ω
  let W : ℝ :=
    cubeBesovNegativeVectorSeminormTwo R s
      (fun x => ω.toH1MeanZero.toH1Function.grad x)
  let G : ℝ :=
    cubeBesovPositiveVectorSeminormTwo R s
      (fun x => g x - cubeAverageVec R g)
  let M : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
  let K : ℝ :=
    250 * (s⁻¹) ^ 2 * (lambdaSq R (s / 2) (.finite 2) a)⁻¹
  have hlambda_nonneg :
      0 ≤ lambdaSq R (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg R (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  have hYoung :
      500 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * W * G)) ≤
        K * W ^ 2 + K * (M * G) ^ 2 := by
    have hbase : 2 * W * (M * G) ≤ W ^ 2 + (M * G) ^ 2 := by
      nlinarith [sq_nonneg (W - M * G)]
    have hscaled := mul_le_mul_of_nonneg_left hbase hK_nonneg
    calc
      500 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * W * G))
          =
        K * (2 * W * (M * G)) := by
          dsimp [K, M]
          ring
      _ ≤ K * (W ^ 2 + (M * G) ^ 2) := hscaled
      _ = K * W ^ 2 + K * (M * G) ^ 2 := by ring
  have htail_sum :
      K * W ^ 2 + K * (M * G) ^ 2 ≤
        (coarsePoincareRHSDepthWeight s j)⁻¹ * (BωNeg + BωForce) := by
    have hsum :=
      add_le_add (hωNegSqTail j R hR ω) (hcenteredForceSqTail j R hR)
    calc
      K * W ^ 2 + K * (M * G) ^ 2
          ≤
        (coarsePoincareRHSDepthWeight s j)⁻¹ * BωNeg +
          (coarsePoincareRHSDepthWeight s j)⁻¹ * BωForce := by
          simpa [K, W, G, M, mul_assoc, mul_left_comm, mul_comm] using hsum
      _ =
        (coarsePoincareRHSDepthWeight s j)⁻¹ * (BωNeg + BωForce) := by
          ring
  exact hYoung.trans htail_sum

/-- Displayed Poincare component estimates after inserting the energy envelope. -/
def zeroTraceDirichletPoincareDisplayedComponentBoundsClose {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d) : Prop :=
  ∃ BPoincareEnergy BPoincareForce : ℝ,
    (matNorm a0) ^ 2 *
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          zeroTraceDirichletEnergyEnvelope Q a s g) ≤
      BPoincareEnergy ∧
    (matNorm a0) ^ 2 *
        (15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
      BPoincareForce ∧
    BPoincareEnergy + BPoincareForce ≤
      (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2

theorem zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d)
    {BPoincareEnergy BPoincareForce : ℝ}
    (hPoincareEnergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            zeroTraceDirichletEnergyEnvelope Q a s g) ≤
        BPoincareEnergy)
    (hPoincareForce :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        BPoincareForce)
    (hPoincareBudget :
      BPoincareEnergy + BPoincareForce ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    zeroTraceDirichletPoincareDisplayedComponentBoundsClose Q a a0 C s g :=
  ⟨BPoincareEnergy, BPoincareForce, hPoincareEnergy, hPoincareForce,
    hPoincareBudget⟩

theorem zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_displayed_bound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d)
    (hPoincareBudget :
      zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    zeroTraceDirichletPoincareDisplayedComponentBoundsClose Q a a0 C s g :=
  zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_bounds
    (Q := Q) (a := a) (a0 := a0) (C := C) (s := s) (g := g)
    (BPoincareEnergy :=
      (matNorm a0) ^ 2 *
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          zeroTraceDirichletEnergyEnvelope Q a s g))
    (BPoincareForce :=
      (matNorm a0) ^ 2 *
        (15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))
    le_rfl le_rfl
    (by simpa [zeroTraceDirichletPoincareDisplayedScalarBudget] using
      hPoincareBudget)

theorem zeroTraceDirichletPoincareDisplayedComponentBoundsClose_displayed_bound
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {a0 : Mat d}
    {C s : ℝ} {g : Vec d → Vec d}
    (h :
      zeroTraceDirichletPoincareDisplayedComponentBoundsClose Q a a0 C s g) :
    zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
      (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 := by
  rcases h with
    ⟨BPoincareEnergy, BPoincareForce, hPoincareEnergy, hPoincareForce,
      hPoincareBudget⟩
  unfold zeroTraceDirichletPoincareDisplayedScalarBudget
  nlinarith [hPoincareEnergy, hPoincareForce, hPoincareBudget]

theorem zeroTraceDirichletPoincareDisplayedComponentBoundsClose_iff_displayed_bound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d) :
    zeroTraceDirichletPoincareDisplayedComponentBoundsClose Q a a0 C s g ↔
      zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 :=
  ⟨zeroTraceDirichletPoincareDisplayedComponentBoundsClose_displayed_bound,
    zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_displayed_bound
      Q a a0 C s g⟩

end ZeroTraceDirichletCorrectorData

end

end Homogenization
