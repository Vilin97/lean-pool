/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesQTwo
public import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic

/-! # Duality -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Deterministic homogenization black boxes: duality

This file contains the Section 3.3.A deterministic duality surface from
`coarsegraining/chapters/ch3_deterministic_theory.tex`, lines 2804--3008.

The Lean statement is written on an arbitrary triadic cube `Q` and a descendant
depth `j`.  This is the existing codebase's scale convention: `j` represents
the manuscript scale gap `m - n`, and the quantities
`cubeBesovNegativeVectorSeminormTwo` are already note-normalized, i.e. they
include the displayed factors `3^{-sm}` and `3^{-sn}`.
-/

open scoped BigOperators

/-- Constant coefficient field associated to a matrix. -/
abbrev constantCoeffField {d : ℕ} (a0 : Mat d) : CoeffField d :=
  fun _ => a0

/-- A constant elliptic matrix defines an elliptic coefficient field on every measurable set. -/
theorem isEllipticFieldOn_constantCoeffField {d : ℕ} {U : Set (Vec d)}
    {a0 : Mat d} {lam0 Lam0 : ℝ}
    (hU : MeasurableSet U) (ha0 : IsEllipticMatrix lam0 Lam0 a0) :
    IsEllipticFieldOn lam0 Lam0 U (constantCoeffField a0) := by
  classical
  constructor
  · apply (measurable_pi_iff).2
    intro i
    apply (measurable_pi_iff).2
    intro j
    have hpiece :
        Measurable (U.piecewise (fun _ : Vec d => a0 i j) (fun _ => 0)) :=
      measurable_const.piecewise hU measurable_const
    simpa [Set.piecewise, constantCoeffField] using! hpiece
  · intro x hx
    simpa [constantCoeffField] using ha0

/-- The flux defect `(a - a₀)∇u`, written in terms of the gradient field. -/
noncomputable def fluxDefect {d : ℕ} (a : CoeffField d) (a0 : Mat d)
    (gradU : Vec d → Vec d) : Vec d → Vec d :=
  fun x => matVecMul (a x) (gradU x) - matVecMul a0 (gradU x)

/-- The constant-coefficient gradient comparison field `a₀(∇u - ∇v)`. -/
noncomputable def constantGradientComparison {d : ℕ} (a0 : Mat d)
    (gradU gradV : Vec d → Vec d) : Vec d → Vec d :=
  fun x => matVecMul a0 (gradU x - gradV x)

/-- The full flux comparison `a∇u - a₀∇v`. -/
noncomputable def fluxComparison {d : ℕ} (a : CoeffField d) (a0 : Mat d)
    (gradU gradV : Vec d → Vec d) : Vec d → Vec d :=
  fun x => matVecMul (a x) (gradU x) - matVecMul a0 (gradV x)

/--
Weak `H¹` formulation of `- div (a ∇u) = div g` on `U`, tested against
zero-trace functions.

Unlike `IsZeroTraceDirichletRhsWeakSolution`, this predicate does not impose a
zero boundary condition on `u`; it matches the comparison hypotheses in
manuscript lines 3020--3029, where only `u - v ∈ H¹₀` is prescribed.
-/
def IsH1DirichletRhsWeakSolutionOn {d : ℕ}
    (a : CoeffField d) (U : Set (Vec d)) (u : H1Function U)
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U,
    ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)
      ∂MeasureTheory.volume =
    ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume

namespace IsH1DirichletRhsWeakSolutionOn

/--
An `H¹` function whose flux is solenoidal solves the zero-right-hand-side weak
Dirichlet equation.
-/
theorem of_isSolenoidalOn_zero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U}
    (hsol : IsSolenoidalOn U (fun x => matVecMul (a x) (u.grad x))) :
    IsH1DirichletRhsWeakSolutionOn a U u (0 : Vec d → Vec d) := by
  intro φ
  rw [hsol φ]
  simp [vecDot_zero_left]

/-- A packaged `a`-harmonic function solves the zero-right-hand-side weak equation. -/
theorem of_aHarmonicFunction {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u : AHarmonicFunction a U) :
    IsH1DirichletRhsWeakSolutionOn a U u.toH1 (0 : Vec d → Vec d) :=
  of_isSolenoidalOn_zero u.isHarmonic.2

/--
The weak equation `-div(a grad u) = div g`, in the codebase's sign convention,
says exactly that the residual flux `a grad u - g` is solenoidal.
-/
theorem residual_solenoidal {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {g : Vec d → Vec d} {lam Lam : ℝ}
    (h : IsH1DirichletRhsWeakSolutionOn a U u g)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hg : MemVectorL2 U g) :
    IsSolenoidalOn U (fun x => matVecMul (a x) (u.grad x) - g x) := by
  intro φ
  have hflux_mem :
      MemVectorL2 U (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hflux_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hflux_mem φ.toH1Function.grad_memVectorL2
  have hg_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (g x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hg φ.toH1Function.grad_memVectorL2
  have hfun :
      (fun x => vecDot (matVecMul (a x) (u.grad x) - g x)
          (φ.toH1Function.grad x)) =
        fun x =>
          vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) -
            vecDot (g x) (φ.toH1Function.grad x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  rw [hfun, MeasureTheory.integral_sub hflux_int hg_int, h φ]
  ring

end IsH1DirichletRhsWeakSolutionOn

/--
Weak formulation of the comparison system in Lemma
`l.duality.from.flux.defect.deterministic.theory`.

The manuscript states
`div (a∇u - a₀∇v) = 0` and `u - v ∈ H¹₀`.  The existing PDE layer represents
these exactly as solenoidality of the flux comparison and zero-trace
potentiality of the gradient difference.
-/
def IsHomogenizationComparisonPairOn {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (a0 : Mat d) (gradU gradV : Vec d → Vec d) : Prop :=
  IsSolenoidalOn U (fluxComparison a a0 gradU gradV) ∧
    IsPotentialZeroTraceOn U (fun x => gradU x - gradV x)

namespace IsHomogenizationComparisonPairOn

/--
Build the comparison-pair hypothesis for a harmonic function and its
constant-coefficient harmonic replacement from the manuscript boundary
condition `u - v ∈ H¹₀`.
-/
theorem of_aHarmonicFunctions {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {a0 : Mat d} {lam Lam lam0 Lam0 : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (constantCoeffField a0) U)
    (hzeroTrace :
      IsPotentialZeroTraceOn U (fun x => u.toH1.grad x - v.toH1.grad x)) :
    IsHomogenizationComparisonPairOn U a a0 u.toH1.grad v.toH1.grad := by
  have hEll0 : IsEllipticFieldOn lam0 Lam0 U (constantCoeffField a0) :=
    isEllipticFieldOn_constantCoeffField (measurableSet_of_isEllipticFieldOn hEll) ha0
  have huFluxL2 :
      MemVectorL2 U (fun x => matVecMul (a x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  have hvFluxL2 :
      MemVectorL2 U (fun x => matVecMul a0 (v.toH1.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 v.toH1.grad_memVectorL2
  have huSol :
      IsSolenoidalOn U (fun x => matVecMul (a x) (u.toH1.grad x)) :=
    u.isHarmonic.2
  have hvSol :
      IsSolenoidalOn U (fun x => matVecMul a0 (v.toH1.grad x)) := by
    simpa [constantCoeffField] using v.isHarmonic.2
  have hvNegFluxL2 :
      MemVectorL2 U (fun x => -matVecMul a0 (v.toH1.grad x)) := by
    simpa [Pi.smul_apply] using! hvFluxL2.const_smul (-1 : ℝ)
  have hvNegSol :
      IsSolenoidalOn U (fun x => -matVecMul a0 (v.toH1.grad x)) := by
    simpa [Pi.smul_apply] using! isSolenoidalOn_smul hvSol (-1 : ℝ)
  have hfluxSol :
      IsSolenoidalOn U
        ((fun x => matVecMul (a x) (u.toH1.grad x)) +
          fun x => -matVecMul a0 (v.toH1.grad x)) :=
    isSolenoidalOn_add_of_memVectorL2 huFluxL2 hvNegFluxL2 huSol hvNegSol
  constructor
  · simpa [fluxComparison, Pi.add_apply, sub_eq_add_neg] using! hfluxSol
  · exact hzeroTrace

/--
Build the comparison-pair hypothesis from the Section 3.3.B weak equations
with common right-hand side and the manuscript boundary condition
`u - v ∈ H¹₀`.
-/
theorem of_sameRhs_h1Functions {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {a0 : Mat d} {lam Lam lam0 Lam0 : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (u v : H1Function U) (g : Vec d → Vec d)
    (hu : IsH1DirichletRhsWeakSolutionOn a U u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) U v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn U (fun x => u.grad x - v.grad x)) :
    IsHomogenizationComparisonPairOn U a a0 u.grad v.grad := by
  have hEll0 : IsEllipticFieldOn lam0 Lam0 U (constantCoeffField a0) :=
    isEllipticFieldOn_constantCoeffField (measurableSet_of_isEllipticFieldOn hEll) ha0
  have huFluxL2 :
      MemVectorL2 U (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hvFluxL2 :
      MemVectorL2 U (fun x => matVecMul a0 (v.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 v.grad_memVectorL2
  constructor
  · intro φ
    have huInt :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 huFluxL2 φ.toH1Function.grad_memVectorL2
    have hvInt :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (matVecMul a0 (v.grad x)) (φ.toH1Function.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 hvFluxL2 φ.toH1Function.grad_memVectorL2
    have hfun :
        (fun x =>
          vecDot (fluxComparison a a0 u.grad v.grad x) (φ.toH1Function.grad x)) =
          fun x =>
            vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) -
              vecDot (matVecMul a0 (v.grad x)) (φ.toH1Function.grad x) := by
      funext x
      simp [fluxComparison, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    have hvφ :
        ∫ x in U, vecDot (matVecMul a0 (v.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
      simpa [constantCoeffField] using hv φ
    calc
      ∫ x in U,
          vecDot (fluxComparison a a0 u.grad v.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
          =
        ∫ x in U,
          (vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) -
            vecDot (matVecMul a0 (v.grad x)) (φ.toH1Function.grad x))
          ∂MeasureTheory.volume := by
            rw [hfun]
      _ =
        ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume -
        ∫ x in U, vecDot (matVecMul a0 (v.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_sub huInt hvInt]
      _ =
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume -
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
            rw [hu φ, hvφ]
      _ = 0 := by ring
  · exact hzeroTrace

end IsHomogenizationComparisonPairOn

/--
The left-hand side of the duality estimate:
`[a₀(∇u-∇v)]_{B^{-s}_{2,2}} + [a∇u-a₀∇v]_{B^{-s}_{2,2}}`, with the note
normalization already included in each cube seminorm.
-/
noncomputable def solutionComparisonNegativeBesovLhs {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (a0 : Mat d)
    (gradU gradV : Vec d → Vec d) : ℝ :=
  cubeBesovNegativeVectorSeminormTwo Q s (constantGradientComparison a0 gradU gradV) +
    cubeBesovNegativeVectorSeminormTwo Q s (fluxComparison a a0 gradU gradV)

/--
The localized `ℓ²` average of the local flux-defect negative Besov seminorms.
For a parent cube of scale `m`, depth `j = m - n` corresponds to the manuscript
average over `3^n ℤ^d ∩ □_m`.
-/
noncomputable def localizedFluxDefectNegativeBesovAverageTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (defect : Vec d → Vec d) (j : ℕ) : ℝ :=
  Real.sqrt <|
    descendantsAverage Q j fun R => (cubeBesovNegativeVectorSeminormTwo R s defect) ^ 2

theorem localizedFluxDefectNegativeBesovAverageTwo_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (defect : Vec d → Vec d) (j : ℕ) :
    0 ≤ localizedFluxDefectNegativeBesovAverageTwo Q s defect j := by
  unfold localizedFluxDefectNegativeBesovAverageTwo
  exact Real.sqrt_nonneg _

private theorem one_le_inv_of_pos_of_lt_one {s : ℝ} (hs : 0 < s) (hs_lt : s < 1) :
    (1 : ℝ) ≤ s⁻¹ :=
  (one_le_inv₀ hs).2 hs_lt.le

private theorem mul_le_mul_inv_mul_of_pos_of_lt_one_of_nonneg
    {C s X : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs_lt : s < 1) (hX : 0 ≤ X) :
    C * X ≤ C * s⁻¹ * X := by
  have hinv : (1 : ℝ) ≤ s⁻¹ := one_le_inv_of_pos_of_lt_one hs hs_lt
  calc
    C * X = C * (1 * X) := by ring
    _ ≤ C * (s⁻¹ * X) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hinv hX) hC
    _ = C * s⁻¹ * X := by ring

/--
At depth zero the localized flux-defect average is the absolute value of the
one-cube negative Besov seminorm.  Later callers may remove the absolute value
when they have the usual boundedness or `L²` hypotheses giving nonnegativity of
the seminorm.
-/
@[simp] theorem localizedFluxDefectNegativeBesovAverageTwo_depth_zero_abs {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (defect : Vec d → Vec d) :
    localizedFluxDefectNegativeBesovAverageTwo Q s defect 0 =
      |cubeBesovNegativeVectorSeminormTwo Q s defect| := by
  unfold localizedFluxDefectNegativeBesovAverageTwo descendantsAverage
  simp [Real.sqrt_sq_eq_abs]

/--
At depth zero, if the one-cube negative Besov seminorm is known nonnegative,
the localized flux-defect average is exactly that seminorm.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_depth_zero_of_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (defect : Vec d → Vec d)
    (hdefect_nonneg : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s defect) :
    localizedFluxDefectNegativeBesovAverageTwo Q s defect 0 =
      cubeBesovNegativeVectorSeminormTwo Q s defect := by
  rw [localizedFluxDefectNegativeBesovAverageTwo_depth_zero_abs]
  exact abs_of_nonneg hdefect_nonneg

/--
Localized `q = 2` flux-defect averages inherit pointwise bounds on every
descendant cube.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_pointwiseBound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (defect : Vec d → Vec d) (j : ℕ)
    (B : TriadicCube d → ℝ)
    (hseminorm_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ cubeBesovNegativeVectorSeminormTwo R s defect)
    (hbound :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s defect ≤ B R) :
    localizedFluxDefectNegativeBesovAverageTwo Q s defect j ≤
      Real.sqrt (descendantsAverage Q j fun R => (B R) ^ 2) := by
  unfold localizedFluxDefectNegativeBesovAverageTwo
  refine Real.sqrt_le_sqrt ?_
  refine descendantsAverage_le_descendantsAverage Q j ?_
  intro R hR
  exact pow_le_pow_left₀ (hseminorm_nonneg R hR) (hbound R hR) 2

/--
Localized `q = 2` flux-defect averages from descendantwise `q = 1` partial
seminorm bounds. This is the handoff shape used by coarse-flux response
estimates before they are averaged over descendants.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_qonePartialBound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (defect : Vec d → Vec d) (j : ℕ)
    (B : TriadicCube d → ℝ)
    (hpartial :
      ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm R s N defect ≤ B R) :
    localizedFluxDefectNegativeBesovAverageTwo Q s defect j ≤
      Real.sqrt (descendantsAverage Q j fun R => (B R) ^ 2) := by
  refine
    localizedFluxDefectNegativeBesovAverageTwo_le_sqrt_descendantsAverage_sq_of_pointwiseBound
      Q s defect j B ?_ ?_
  · intro R hR
    have hBdd :
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N defect) := by
      use B R
      rintro x ⟨N, rfl⟩
      exact
        (cubeBesovNegativeVectorPartialSeminormTwo_le_partialSeminorm
          R s N defect).trans (hpartial R hR N)
    have hzero_le :
        cubeBesovNegativeVectorPartialSeminormTwo R s 0 defect ≤
          cubeBesovNegativeVectorSeminormTwo R s defect := by
      unfold cubeBesovNegativeVectorSeminormTwo
      exact le_csSup hBdd ⟨0, rfl⟩
    exact (cubeBesovNegativeVectorPartialSeminormTwo_nonneg R s 0 defect).trans hzero_le
  · intro R hR
    exact
      cubeBesovNegativeVectorSeminormTwo_le_of_qone_partialBound
        R s defect (hpartial R hR)

/--
Direct arbitrary-matrix solution-comparison duality estimate.

This is the active deterministic interface for Lemma
`l.duality.from.flux.defect.deterministic.theory`: the comparison fields are
controlled directly by the localized flux defect.  It deliberately does not
depend on the abandoned Ch1 route.
-/
def SolutionComparisonDualityEstimate
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) (a0 : Mat d) (w F : Vec d → Vec d)
      {s : ℝ} (j : ℕ) {lam0 Lam0 : ℝ},
      0 < s →
      s < 1 →
      IsEllipticMatrix lam0 Lam0 a0 →
      a0.IsSymm →
      IsPotentialZeroTraceOn (cubeSet Q) w →
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul a0 (w x) + F x) →
      cubeBesovNegativeVectorSeminormTwo Q s (fun x => matVecMul a0 (w x)) +
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul a0 (w x) + F x) ≤
        C * localizedFluxDefectNegativeBesovAverageTwo Q s F j

/--
The comparison-pair left-hand side is exactly the pair
`(a₀(∇u-∇v), a₀(∇u-∇v) + (a-a₀)∇u)`.
-/
theorem solutionComparisonNegativeBesovLhs_eq_comparisonPair
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (a0 : Mat d)
    (gradU gradV : Vec d → Vec d) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV =
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul a0 (gradU x - gradV x)) +
        cubeBesovNegativeVectorSeminormTwo Q s
          (fun x =>
            matVecMul a0 (gradU x - gradV x) +
              fluxDefect a a0 gradU x) := by
  unfold solutionComparisonNegativeBesovLhs constantGradientComparison fluxComparison fluxDefect
  congr 2
  funext x
  ext i
  simp [sub_eq_add_neg, matVecMul, mul_add, Finset.sum_add_distrib]
  ring

/--
The solenoidal part of a homogenization comparison pair has the normal form
`a₀(∇u-∇v) + (a-a₀)∇u`.
-/
theorem IsHomogenizationComparisonPairOn.comparisonPair_solenoidal
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {a0 : Mat d}
    {gradU gradV : Vec d → Vec d}
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV) :
    IsSolenoidalOn (cubeSet Q)
      (fun x =>
        matVecMul a0 (gradU x - gradV x) + fluxDefect a a0 gradU x) := by
  have hfield :
      (fun x =>
          matVecMul a0 (gradU x - gradV x) + fluxDefect a a0 gradU x) =
        fluxComparison a a0 gradU gradV := by
    funext x
    ext i
    simp [fluxComparison, fluxDefect, sub_eq_add_neg, matVecMul, mul_add,
      Finset.sum_add_distrib]
    ring
  simpa [hfield] using hcomparison.1

/-- Use the direct arbitrary-matrix solution-comparison duality estimate on a
homogenization comparison pair. -/
theorem solutionComparisonNegativeBesovLhs_le_of_solutionComparisonDualityEstimate
    {d : ℕ} [NeZero d] {C : ℝ}
    (hduality : SolutionComparisonDualityEstimate d C)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (gradU gradV : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      C * localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 gradU) j := by
  have hbound :=
    hduality.2 Q a0 (fun x => gradU x - gradV x) (fluxDefect a a0 gradU) j
      hs_pos hs_lt_one ha0 ha0symm hcomparison.2
      hcomparison.comparisonPair_solenoidal
  rwa [solutionComparisonNegativeBesovLhs_eq_comparisonPair]

/--
Existence of a dimension-only direct duality constant gives the arbitrary-matrix
Section 3.3.A duality estimate surface.
-/
theorem exists_solutionComparisonNegativeBesovLhsBound_of_solutionComparisonDualityEstimate
    (d : ℕ) [NeZero d]
    (hduality : ∃ C : ℝ, SolutionComparisonDualityEstimate d C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
        (gradU gradV : Vec d → Vec d) {s : ℝ} (j : ℕ)
        {lam Lam lam0 Lam0 : ℝ},
        0 < s →
        s < 1 →
        IsEllipticFieldOn lam Lam (cubeSet Q) a →
        IsEllipticMatrix lam0 Lam0 a0 →
        a0.IsSymm →
        IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV →
        solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
          C * localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 gradU) j := by
  rcases hduality with ⟨C, hC⟩
  refine ⟨C, hC.1, ?_⟩
  intro Q a a0 gradU gradV s j lam Lam lam0 Lam0 hs_pos hs_lt_one _hEll ha0 ha0symm
    hcomparison
  exact
    solutionComparisonNegativeBesovLhs_le_of_solutionComparisonDualityEstimate
      hC Q a a0 gradU gradV j hs_pos hs_lt_one ha0 ha0symm hcomparison

/--
Direct scalar-background solution-comparison duality estimate.

This is the scalar form consumed by the existing Chapter 3 coarse-graining
wrappers.  It is a direct flux-defect duality input, not a proof obligation
about the abandoned Ch1 route.
-/
def ScalarSolutionComparisonDualityEstimate
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) (sigma0 : ℝ) (w F : Vec d → Vec d)
      {s : ℝ} (j : ℕ),
      0 < sigma0 →
      0 < s →
      s < 1 →
      IsPotentialZeroTraceOn (cubeSet Q) w →
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) →
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) +
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) ≤
        C * s⁻¹ * localizedFluxDefectNegativeBesovAverageTwo Q s F j

/-- The arbitrary-matrix direct duality estimate specializes to the scalar route. -/
theorem SolutionComparisonDualityEstimate.to_scalar
    {d : ℕ} [NeZero d] {C : ℝ}
    (hduality : SolutionComparisonDualityEstimate d C) :
    ScalarSolutionComparisonDualityEstimate d C := by
  refine ⟨hduality.1, ?_⟩
  intro Q sigma0 w F s j hsigma0 hs_pos hs_lt_one hw hsol
  have hbound :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) +
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) ≤
        C * localizedFluxDefectNegativeBesovAverageTwo Q s F j :=
    hduality.2 Q (scalarMatrix (d := d) sigma0) w F j
      hs_pos hs_lt_one (isEllipticMatrix_scalarMatrix hsigma0)
      (scalarMatrix_isSymm sigma0) hw hsol
  exact hbound.trans
    (mul_le_mul_inv_mul_of_pos_of_lt_one_of_nonneg hduality.1 hs_pos hs_lt_one
      (localizedFluxDefectNegativeBesovAverageTwo_nonneg Q s F j))

/-- Existence of the arbitrary-matrix direct duality constant implies the scalar one. -/
theorem exists_scalarSolutionComparisonDualityEstimate_of_solutionComparisonDualityEstimate
    {d : ℕ} [NeZero d]
    (hduality : ∃ C : ℝ, SolutionComparisonDualityEstimate d C) :
    ∃ C : ℝ, ScalarSolutionComparisonDualityEstimate d C := by
  rcases hduality with ⟨C, hC⟩
  exact ⟨C, hC.to_scalar⟩

/-- Use the direct scalar-background duality estimate on a comparison pair. -/
theorem solutionComparisonNegativeBesovLhs_le_of_scalarSolutionComparisonDualityEstimate
    {d : ℕ} [NeZero d] {C : ℝ}
    (hduality : ScalarSolutionComparisonDualityEstimate d C)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (gradU gradV : Vec d → Vec d) {s : ℝ} (j : ℕ)
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a
        (scalarMatrix (d := d) sigma0) gradU gradV) :
    solutionComparisonNegativeBesovLhs Q s a (scalarMatrix (d := d) sigma0) gradU gradV ≤
      C * s⁻¹ * localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j := by
  have hbound :=
    hduality.2 Q sigma0 (fun x => gradU x - gradV x)
      (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j
      hsigma0 hs_pos hs_lt_one hcomparison.2 hcomparison.comparisonPair_solenoidal
  rwa [solutionComparisonNegativeBesovLhs_eq_comparisonPair]

/--
Existence of the scalar direct duality constant gives the corrected
scalar-background Section 3.3.A duality surface.
-/
theorem exists_scalarSolutionComparisonDualityConstant_of_scalarSolutionComparisonDualityEstimate
    (d : ℕ) [NeZero d]
    (hduality : ∃ C : ℝ, ScalarSolutionComparisonDualityEstimate d C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
        (gradU gradV : Vec d → Vec d) {s : ℝ} (j : ℕ)
        {lam Lam : ℝ},
        0 < sigma0 →
        0 < s →
        s < 1 →
        IsEllipticFieldOn lam Lam (cubeSet Q) a →
        IsHomogenizationComparisonPairOn (cubeSet Q) a
          (scalarMatrix (d := d) sigma0) gradU gradV →
        solutionComparisonNegativeBesovLhs Q s a
            (scalarMatrix (d := d) sigma0) gradU gradV ≤
          C * s⁻¹ * localizedFluxDefectNegativeBesovAverageTwo Q s
            (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j := by
  rcases hduality with ⟨C, hC⟩
  refine ⟨C, hC.1, ?_⟩
  intro Q a sigma0 gradU gradV s j lam Lam hsigma0 hs_pos hs_lt_one _hEll
    hcomparison
  exact
    solutionComparisonNegativeBesovLhs_le_of_scalarSolutionComparisonDualityEstimate
      hC Q a sigma0 gradU gradV j hsigma0 hs_pos hs_lt_one hcomparison

/--
Scalar-background duality apex for
`coarsegraining/chapters/ch3_deterministic_theory.tex`, lines 2804--3008.

The corrected route exposes the remaining analytic input directly:
`hdual` is the scalar solution-comparison duality estimate.  No arbitrary-matrix
dimension-only theorem data is assumed here.
-/
theorem solution_diff_l2_le_dualityConstant_mul_localizedFluxDefect_of_fluxDefect_negativeBesov_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (gradU gradV : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (_hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a
        (scalarMatrix (d := d) sigma0) gradU gradV) :
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) gradU gradV ≤
      Cdual * s⁻¹ * localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j :=
  solutionComparisonNegativeBesovLhs_le_of_scalarSolutionComparisonDualityEstimate
    hdual Q a sigma0 gradU gradV j hsigma0 hs_pos hs_lt_one hcomparison

/--
Scalar-background duality bound with an arbitrary caller-supplied upper bound
on the localized flux defect.
-/
theorem solution_diff_l2_le_dualityConstant_mul_fluxDefectBound_of_localizedFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (gradU gradV : Vec d → Vec d) {s fluxDefectBound : ℝ} (j : ℕ)
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a
        (scalarMatrix (d := d) sigma0) gradU gradV)
    (hfluxDefectBound :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j ≤
        fluxDefectBound) :
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) gradU gradV ≤
      Cdual * s⁻¹ * fluxDefectBound := by
  calc
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) gradU gradV
        ≤ Cdual * s⁻¹ *
            localizedFluxDefectNegativeBesovAverageTwo Q s
              (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j :=
      solution_diff_l2_le_dualityConstant_mul_localizedFluxDefect_of_fluxDefect_negativeBesov_le
        hdual Q a sigma0 gradU gradV j hsigma0 hs_pos hs_lt_one hEll hcomparison
    _ ≤ Cdual * s⁻¹ * fluxDefectBound := by
      exact mul_le_mul_of_nonneg_left hfluxDefectBound
        (mul_nonneg hdual.1 (inv_nonneg.mpr hs_pos.le))

/--
Scalar-background depth-zero duality bound from a direct one-cube negative
Besov bound on the flux defect, with nonnegativity supplied separately.
-/
theorem solution_diff_l2_le_dualityConstant_mul_cubeBesovNegativeFluxDefectBound_of_depth_zero_of_nonneg
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (gradU gradV : Vec d → Vec d) {s fluxDefectBound : ℝ}
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a
        (scalarMatrix (d := d) sigma0) gradU gradV)
    (hdefect_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s
        (fluxDefect a (scalarMatrix (d := d) sigma0) gradU))
    (hfluxDefectBound :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) ≤
        fluxDefectBound) :
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) gradU gradV ≤
      Cdual * s⁻¹ * fluxDefectBound :=
  solution_diff_l2_le_dualityConstant_mul_fluxDefectBound_of_localizedFluxDefect_le
    hdual Q a sigma0 gradU gradV 0 hsigma0 hs_pos hs_lt_one hEll hcomparison
    (by
      rw [localizedFluxDefectNegativeBesovAverageTwo_depth_zero_of_nonneg]
      · exact hfluxDefectBound
      · exact hdefect_nonneg)

/--
Scalar-background duality apex with the Section 3.3.B PDE hypotheses exposed
directly.
-/
theorem solution_diff_l2_le_dualityConstant_mul_localizedFluxDefect_of_sameRhs
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv :
      IsH1DirichletRhsWeakSolutionOn
        (constantCoeffField (scalarMatrix (d := d) sigma0)) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x)) :
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) u.grad v.grad ≤
      Cdual * s⁻¹ *
        localizedFluxDefectNegativeBesovAverageTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) u.grad) j :=
  solution_diff_l2_le_dualityConstant_mul_localizedFluxDefect_of_fluxDefect_negativeBesov_le
    hdual Q a sigma0 u.grad v.grad j hsigma0 hs_pos hs_lt_one hEll
      (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
        hEll (isEllipticMatrix_scalarMatrix hsigma0) u v g hu hv hzeroTrace)

/-- Scalar-background same-right-hand-side duality bound with a supplied
localized flux-defect upper bound. -/
theorem solution_diff_l2_le_dualityConstant_mul_fluxDefectBound_of_sameRhs_of_localizedFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d)
    {s fluxDefectBound : ℝ} (j : ℕ) {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv :
      IsH1DirichletRhsWeakSolutionOn
        (constantCoeffField (scalarMatrix (d := d) sigma0)) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hfluxDefectBound :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) u.grad) j ≤
        fluxDefectBound) :
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) u.grad v.grad ≤
      Cdual * s⁻¹ * fluxDefectBound :=
  solution_diff_l2_le_dualityConstant_mul_fluxDefectBound_of_localizedFluxDefect_le
    hdual Q a sigma0 u.grad v.grad j hsigma0 hs_pos hs_lt_one hEll
      (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
        hEll (isEllipticMatrix_scalarMatrix hsigma0) u v g hu hv hzeroTrace)
      hfluxDefectBound

/--
Scalar-background same-right-hand-side depth-zero duality bound from a direct
one-cube negative Besov bound on the flux defect.
-/
theorem solution_diff_l2_le_dualityConstant_mul_cubeBesovNegativeFluxDefectBound_of_sameRhs_of_depth_zero_of_nonneg
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d)
    {s fluxDefectBound : ℝ} {lam Lam : ℝ}
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv :
      IsH1DirichletRhsWeakSolutionOn
        (constantCoeffField (scalarMatrix (d := d) sigma0)) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hdefect_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s
        (fluxDefect a (scalarMatrix (d := d) sigma0) u.grad))
    (hfluxDefectBound :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) u.grad) ≤
        fluxDefectBound) :
    solutionComparisonNegativeBesovLhs Q s a
        (scalarMatrix (d := d) sigma0) u.grad v.grad ≤
      Cdual * s⁻¹ * fluxDefectBound :=
  solution_diff_l2_le_dualityConstant_mul_cubeBesovNegativeFluxDefectBound_of_depth_zero_of_nonneg
    hdual Q a sigma0 u.grad v.grad hsigma0 hs_pos hs_lt_one hEll
      (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
        hEll (isEllipticMatrix_scalarMatrix hsigma0) u v g hu hv hzeroTrace)
      hdefect_nonneg hfluxDefectBound

end

end Homogenization
