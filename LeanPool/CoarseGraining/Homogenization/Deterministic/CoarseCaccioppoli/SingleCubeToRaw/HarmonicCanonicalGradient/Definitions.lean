/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicGradientControls
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalizedEnergyProfile
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.TriadicScale
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare

/-! # Definitions -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Fully canonical harmonic-gradient Caccioppoli endpoints

This sidecar keeps `HarmonicGradientControls.lean` under the preferred file-size
ceiling while adding the next Phase 2 specialization: the canonical gradient
`Acirc` factors are paired with the exact harmonic `L²` radius profile in the
coefficient-bound package.
-/

/-- Exact harmonic `L²` profile used as the canonical `U` envelope for the
gradient-component Caccioppoli endpoints. -/
noncomputable def coarseCaccioppoliCanonicalHarmonicL2Profile {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : ℝ → ℝ → ℝ :=
  fun ρ₁ ρ₂ => cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x)

/-- The exact projected mean-zero Poincare family still needed by the
canonical gradient-component Caccioppoli endpoint.  This is the remaining
Besov/Poincare bridge for the actual Chapter 3 auxiliary field
`g = partial_i w`. -/
def CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
    CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
      (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
      (fun x => (w ρ₁ ρ₂).toH1.grad x i) N

theorem CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily.projectedPoincare
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {C : ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)} {i : Fin d}
    (hproj :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂)
    (hρ₂ : ρ₂ ≤ 1) (N : ℕ) :
    CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
      (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
      (fun x => (w ρ₁ ρ₂).toH1.grad x i) N :=
  hproj hρ₁ hlt hρ₂ N

/-! ### Vector replacement for the projected Poincare family

The componentwise `…ProjectedPoincareFamily Q a C w i` above is mathematically
**too strong** when applied to a single coordinate of a harmonic gradient:
an affine harmonic function `u(x) = x_j` (with `j ≠ i`) has zero `i`-th
partial derivative but nonzero oscillation. The vector replacement below
controls oscillation by a sum over coordinates; this is the actual
Sobolev/Besov negative-norm Poincare statement that holds on harmonic
fields. -/

/-- Vector form of the projected mean-zero Poincare family for the
canonical gradient Caccioppoli endpoint: at every radius pair and every
multiscale depth, the `cubeFluctuation` of `w ρ₁ ρ₂` is controlled (on every
descendant) by the sum over coordinates of the dual seminorms of the
projected gradient components. -/
def CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
    CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C
      (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
      (fun x => (w ρ₁ ρ₂).toH1.grad x) N

theorem CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily.vectorPoincare
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {C : ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    (hproj :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily Q a C w)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂)
    (hρ₂ : ρ₂ ≤ 1) (N : ℕ) :
    CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C
      (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
      (fun x => (w ρ₁ ρ₂).toH1.grad x) N :=
  hproj hρ₁ hlt hρ₂ N

/-- Descendant-local version of the canonical projected vector Poincare
family.  This is the Poincare input needed by the small-cube Caccioppoli
proof on a depth-`j` descendant `R`; the oscillation is recentered from the
parent cube average to the local cube average. -/
theorem CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily.vectorPoincare_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {a : CoeffField d} {C : ℝ} {j : ℕ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    (hproj :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily Q a C w)
    (hR : R ∈ descendantsAtDepth Q j)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂)
    (hρ₂ : ρ₂ ≤ 1) :
    ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C
        (cubeFluctuation R (fun x => (w ρ₁ ρ₂).toH1 x))
        (fun x => (w ρ₁ ρ₂).toH1.grad x) N := by
  refine
    CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate.restrict_fluctuation_to_descendant
      hR ?_ ?_
  · intro n S hS
    have hSQ : S ∈ descendantsAtDepth Q (j + n) := mem_descendantsAtDepth_add hR hS
    exact
      memLp_on_descendant_of_memLp (Q := Q) (R := S) (j := j + n) hSQ
        (memLp_harmonicFunction_normalizedCubeMeasure Q a (w ρ₁ ρ₂))
  · intro M
    exact hproj.vectorPoincare hρ₁ hlt hρ₂ M

/-- Enlarge the constant in the canonical projected vector Poincare family. -/
theorem CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily.mono_C
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {C₁ C₂ : ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    (hproj :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily Q a C₁ w)
    (hC : C₁ ≤ C₂) :
    CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily Q a C₂ w := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂ N
  exact (hproj hρ₁ hlt hρ₂ N).mono_C hC

/-- Infinite-depth vector full-dual Poincare family for the canonical gradient
Caccioppoli endpoint. This is the constant-mode-safe replacement for the legacy
mean-zero dual family: the right-hand side uses `cubeBesovDualFullNorm`, so
affine/constant-gradient modes are retained. -/
def CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
    CubeDescendantDualFullVectorPoincareEstimate Q C
      (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
      (fun x => (w ρ₁ ρ₂).toH1.grad x) N

theorem CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily.vectorPoincare
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {C : ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    (hproj :
      CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily Q a C w)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂)
    (hρ₂ : ρ₂ ≤ 1) (N : ℕ) :
    CubeDescendantDualFullVectorPoincareEstimate Q C
      (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
      (fun x => (w ρ₁ ρ₂).toH1.grad x) N :=
  hproj hρ₁ hlt hρ₂ N

/-- Enlarge the constant in the canonical full-dual vector Poincare family. -/
theorem CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily.mono_C
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {C₁ C₂ : ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    (hfull :
      CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily Q a C₁ w)
    (hC : C₁ ≤ C₂) :
    CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily Q a C₂ w := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂ N
  exact (hfull hρ₁ hlt hρ₂ N).mono_C hC

/-- Descendant-local version of the canonical full-dual vector Poincare
family.  This is the corrected local input for consumers that work on a
depth-`j` descendant `R`, with the oscillation recentered at the local cube. -/
theorem CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily.vectorPoincare_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {a : CoeffField d} {C : ℝ} {j : ℕ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    (hfull :
      CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily Q a C w)
    (hR : R ∈ descendantsAtDepth Q j)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂)
    (hρ₂ : ρ₂ ≤ 1) :
    ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C
        (cubeFluctuation R (fun x => (w ρ₁ ρ₂).toH1 x))
        (fun x => (w ρ₁ ρ₂).toH1.grad x) N := by
  refine
    CubeDescendantDualFullVectorPoincareEstimate.restrict_fluctuation_to_descendant
      hR ?_ ?_
  · intro n S hS
    have hSQ : S ∈ descendantsAtDepth Q (j + n) := mem_descendantsAtDepth_add hR hS
    exact
      memLp_on_descendant_of_memLp (Q := Q) (R := S) (j := j + n) hSQ
        (memLp_harmonicFunction_normalizedCubeMeasure Q a (w ρ₁ ρ₂))
  · intro M
    exact hfull.vectorPoincare hρ₁ hlt hρ₂ M

/-! ### Analytical input stubs (to be discharged by Sobolev/Besov pass)

These constructors expose the precise contract that the analytical
Sobolev/Besov negative-norm Poincare proof has to deliver. The public corrected
full-dual route uses the cube-only `fullVectorPoincareCubeConstant Q`, selected
as a parent-cube uniform analytic constant in
`Sobolev/Foundations/CubeBesovPoincare.lean`, so descendant estimates use the
same parent constant on every local cube.

**No harmonicity is required at the analytic level**: the inequality
`‖u − ⟨u⟩_R‖_{L²(R)} ≲ ∑_i ‖∂_i u‖_{B^{-1}_{2,1},full(R)}` is a duality fact
about `H¹` on the corrected surface. The load-bearing full-dual constructor
`of_h1Function` therefore takes an arbitrary `H1Function (openCubeSet Q)`;
the harmonic specialisations
`of_aHarmonicFunction` (per-function and family) are one-line corollaries
that simply pass `u.toH1`. The `L²` membership of the value and gradient
fields is supplied automatically by the `H1Function` structure.
-/

/-- Constructor for the infinite-depth vector full-dual Poincare estimate
specialised to a scalar `A`-harmonic function. One-line corollary of the
corrected `H1Function` full-dual constructor. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.of_aHarmonicFunction
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (u : AHarmonicFunction a (openCubeSet Q)) (N : ℕ) :
    CubeDescendantDualFullVectorPoincareEstimate Q
      (fullVectorPoincareCubeConstant Q)
      (cubeFluctuation Q (fun x => u.toH1 x))
      (fun x => u.toH1.grad x) N :=
  CubeDescendantDualFullVectorPoincareEstimate.of_h1Function
    Q u.toH1 N

/-- Variant exposing the Sobolev-level selected corrected uniform analytic
constant directly. This is definitionally the same constant as
`fullVectorPoincareCubeConstant Q`. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.of_aHarmonicFunction_uniformAnalyticConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (u : AHarmonicFunction a (openCubeSet Q)) (N : ℕ) :
    CubeDescendantDualFullVectorPoincareEstimate Q
      (cubeFullVectorPoincareUniformAnalyticConstant Q)
      (cubeFluctuation Q (fun x => u.toH1 x))
      (fun x => u.toH1.grad x) N :=
  CubeDescendantDualFullVectorPoincareEstimate.of_h1Function_uniformAnalyticConstant
    Q u.toH1 N

/-- Specialisation: the corrected infinite-depth full-dual vector Poincare
family is realised on any harmonic family `w` with the public corrected
cube constant `fullVectorPoincareCubeConstant Q`. -/
theorem CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily.of_aHarmonicFunction
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) :
    CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily Q a
      (fullVectorPoincareCubeConstant Q) w := by
  intro ρ₁ ρ₂ _ _ _ N
  exact CubeDescendantDualFullVectorPoincareEstimate.of_aHarmonicFunction
    Q a (w ρ₁ ρ₂) N

/-- Specialisation using the selected corrected uniform analytic constant over
all descendants of `Q`. -/
theorem CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily.of_aHarmonicFunction_uniformAnalyticConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) :
    CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily Q a
      (cubeFullVectorPoincareUniformAnalyticConstant Q) w := by
  intro ρ₁ ρ₂ _ _ _ N
  exact
    CubeDescendantDualFullVectorPoincareEstimate.of_aHarmonicFunction_uniformAnalyticConstant
      Q a (w ρ₁ ρ₂) N

/-- The two genuinely solution-dependent strict positivity facts still needed
by the canonical gradient endpoint.  Positivity of the canonical `Acirc1`
coefficient is separated out below as a coefficient-side `lambdaSq` hypothesis. -/
def CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    0 < cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ∧
    0 <
      Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))

theorem coarseCaccioppoli_cubeBesovScaleWeight_pos {d : ℕ} (s : ℝ)
    (Q : TriadicCube d) :
    0 < cubeBesovScaleWeight s Q := by
  unfold cubeBesovScaleWeight
  exact Real.rpow_pos_of_pos
    (by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
    _

theorem coarseCaccioppoliCanonicalGradientAcirc_pos_of_lambdaSq_pos {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {r : ℝ}
    (hr : 0 < r) (hlambda : 0 < lambdaSq Q r (.finite 1) a) :
    0 < coarseCaccioppoliCanonicalGradientAcirc Q a r := by
  unfold coarseCaccioppoliCanonicalGradientAcirc
  have hdisc_pos : 0 < geometricDiscount r 1 :=
    geometricDiscount_pos (by simpa using hr)
  exact
    mul_pos (coarseCaccioppoli_cubeBesovScaleWeight_pos (-r) Q)
      (mul_pos (inv_pos.mpr hdisc_pos) (Real.rpow_pos_of_pos hlambda _))

theorem coarseCaccioppoliCanonicalGradientAcircOne_pos_of_lambdaSq_pos {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (ρ₁ ρ₂ : ℝ)
    (hlambda : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a) :
    0 < coarseCaccioppoliCanonicalGradientAcircOne Q a ρ₁ ρ₂ := by
  simpa [coarseCaccioppoliCanonicalGradientAcircOne] using
    coarseCaccioppoliCanonicalGradientAcirc_pos_of_lambdaSq_pos
      Q a (by norm_num : 0 < (1 : ℝ)) hlambda

theorem CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors.to_positiveFactors
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (hlambda : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hnonzero :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w) :
    CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hnonzero hρ₁ hlt hρ₂ with ⟨hU, henergy⟩
  exact
    ⟨hU,
      coarseCaccioppoliCanonicalGradientAcircOne_pos_of_lambdaSq_pos Q a ρ₁ ρ₂ hlambda,
      henergy⟩

/-- Boundary canonical harmonic Caccioppoli with the concrete Chapter 3
`U/A1/AS` choices installed in the coefficient-bound package:

* `U` is the exact harmonic `L²` profile;
* `A1` is the canonical gradient `Acirc(1)` profile;
* `AS` is the canonical gradient `Acirc(1-s)` profile. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hprofileLower :
      CoarseCaccioppoliLocalizedEnergyProfileLowerControls Q F
        (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalGradientAcircCoefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (w := w) (i := i)
      (U := coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
      hC hs ht hst hu hnonneg hbounded hscale
      (hprofileLower.to_canonicalCutoffLower
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).1)
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1))
      henergyAvg
      hfluxEnergy
      (hnonzeroFactors.to_positiveFactors Q a w hlambda1) hgrad
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ N =>
        hprojected.projectedPoincare (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂ N)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      hcoeff hEll hData hSigmaSum_t

/-- Interior canonical harmonic Caccioppoli with the concrete Chapter 3
`U/A1/AS` choices installed in the coefficient-bound package. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hprofileLower :
      CoarseCaccioppoliLocalizedEnergyProfileLowerControls Q G₀
        (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          G₀ ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalGradientAcircCoefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (G₀ := G₀) (w := w) (i := i)
      (U := coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale
      (hprofileLower.to_canonicalCutoffLower
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).1)
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1))
      henergyAvg
      hfluxEnergy
      (hnonzeroFactors.to_positiveFactors Q a w hlambda1) hgrad
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ N =>
        hprojected.projectedPoincare (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂ N)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      hcoeff hEll hData hSigmaSum_t

/-- Boundary canonical harmonic Caccioppoli specialized to a fixed localized
energy radius profile.  This removes the public `hnonneg`, `hbounded`, and
localized-profile-lower hypotheses from the strongest boundary surface; the
only remaining profile-specific input is the pointwise agreement of the fixed
energy with the pair-dependent local energy on the inner cube. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ)
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinner_energy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁,
          baseEnergy x = scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k)
      (F := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (w := w) (i := i)
      hC hs ht hst hu
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg Q hbase_nonneg)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove Q hbase_nonneg hbase_int)
      hscale
      (CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_eq_pairEnergy
        Q hbase_int
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1)
        hinner_energy)
      henergyAvg hfluxEnergy hnonzeroFactors hlambda1 hgrad hprojected hcoeff
      hEll hData hSigmaSum_t

end

end Homogenization
