/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Fourier.AddCircle
import LeanPool.PoincareThreeBody.ChapterVIDarboux
import LeanPool.PoincareThreeBody.ChapterVILatticeReduction
import LeanPool.PoincareThreeBody.LocalEnergyLeaf

/-!
# Poincaré, *Méthodes nouvelles*, Volume I, Chapter VI

This file isolates the interface between the restricted problem formalized in this project and
the decisive complex-singularity calculation in Chapter VI of Poincaré's first volume.

## Passage-by-passage status

* §90 (pp. 269--272): Poincaré writes the full three-body Hamiltonian as `F₀ + μ F₁` and isolates
  the mutual-distance part of `F₁`.  The restricted analogue is
  `hasDerivAt_hamiltonian_mass_zero`, with the resulting coefficient
  `firstMassPerturbation`; this is a different Hamiltonian, not a verification of Poincaré's
  displayed full-problem formula.
* §91--92 (pp. 272--278): Poincaré discusses osculating coordinates and the first homological
  equation.  `firstHomologicalEquation_of_poissonBracket_zero` verifies the parameter
  product-rule step, while
  `IsFirstIntegralFamily.firstHomologicalEquation_on_resonantKeplerOrbit` and the averaging
  lemmas verify its restricted resonant-orbit consequence.  The coordinate comparison in §92
  is not formalized.
* §93 (pp. 278--280): Poincaré recalls Darboux's one-variable coefficient estimates.
  `eventually_ne_zero_of_tendsto_div_one` verifies their elementary eventual-nonvanishing
  consequence, but the complex-analytic coefficient estimates themselves are not formalized.
* §94 (pp. 280--285): Poincaré reduces coefficients of a Fourier series in two mean anomalies,
  along an integral ray, to Laurent coefficients of a one-variable contour integral `Phi(z)`.
  `chapterVIShearExponent_eq_iff_mem_affineRay`,
  `chapterVIFiniteFourierPolynomial_substitution`, and
  `chapterVIReducedCoefficient_eq_sum_affineRay` verify the exact reduction for finite Fourier
  polynomials.  Extension to convergent infinite series and the contour integral is not yet
  formalized.  The restricted problem has only one moving Kepler ellipse; the definition
  `chapterVIOrientationCoefficient` below records the corresponding one-circle coefficient, but
  is not itself Poincaré's full two-variable perturbing function.
* §95--98 (pp. 285--314): Poincaré complexifies the eccentric anomalies, finds candidate branch
  points, and decides by contour deformation which singularities are admissible.  This
  Riemann-surface and contour-deformation argument is **not yet formalized**.  Poincaré himself
  describes the general discussion in §98 as only sketched.
* §99--101 (pp. 314--325): local singular expansions and Darboux asymptotics show that high-order
  resonant coefficients do not vanish.
  `eventually_coefficient_ne_zero_of_chapterVI_darboux_asymptotic` verifies asymptotics-to-
  nonvanishing for Poincaré's leading model.  Deriving the asymptotic from the singular expansion
  remains open.  The predicates below state the corresponding restricted-problem inputs.
* §102--103 (pp. 325--334): Poincaré uses the dependence of complex singular points on orbital
  parameters and an algebraic-curve intersection count to contradict an additional uniform
  integral.  That dimension/counting argument is not formalized.  The theorems at the end of
  this file instead connect coefficient nonvanishing to the restricted dense Poincaré set and
  thence to the project's modified nonintegrability proof.

The unconditional theorem `nonintegrability_of_collisionBand` uses a modification: a real
logarithmic collision blow-up and analytic continuation replace §§93--101.  Consequently this
project proves a restricted nonintegrability theorem, but it does not yet verify Poincaré's
original complex-singularity/Darboux calculations in Chapter VI.
-/

noncomputable section

open AddCircle
open scoped Real

namespace LeanPool.PoincareThreeBody

open Asymptotics Filter

/-- The orientation-dependent resonant average, descended to the circle of period `2 * pi`.

This is the one-angle restricted-problem counterpart of the functions whose two-angle Fourier
coefficients Poincaré studies in §94. -/
def chapterVIResonantAverageOnCircle (p q : ℕ) (eccentricity : ℝ) :
    AddCircle (2 * Real.pi) → ℂ :=
  let average : ℝ → ℝ := resonantDisturbingAverage p q eccentricity
  let periodic : Function.Periodic average (2 * Real.pi) :=
    fun orientation ↦ resonantDisturbingAverage_add_orientation_two_pi
      p q eccentricity orientation
  fun orientation ↦ (periodic.lift orientation : ℂ)

/-- The `n`th Fourier coefficient of the restricted resonant average.

Poincaré's §94 instead begins with coefficients `A_(m₁,m₂)` of the full perturbing function in
two mean anomalies and studies the ray `(m₁,m₂) = (a n + b, c n + d)`. -/
def chapterVIOrientationCoefficient
    (p q : ℕ) (eccentricity : ℝ) (n : ℤ) : ℂ :=
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  fourierCoeff (chapterVIResonantAverageOnCircle p q eccentricity) n

/-- A nonzero nonconstant Fourier mode prevents the resonant average from being constant. -/
theorem exists_values_ne_of_chapterVIOrientationCoefficient_ne_zero
    {p q : ℕ} {eccentricity : ℝ} {n : ℤ}
    (hn : n ≠ 0)
    (hcoefficient : chapterVIOrientationCoefficient p q eccentricity n ≠ 0) :
    ∃ phaseA phaseB : ℝ,
      resonantDisturbingAverage p q eccentricity phaseA ≠
        resonantDisturbingAverage p q eccentricity phaseB := by
  by_contra hvalues
  push Not at hvalues
  have hcircle : chapterVIResonantAverageOnCircle p q eccentricity =
      fun _ ↦ (resonantDisturbingAverage p q eccentricity 0 : ℂ) := by
    funext orientation
    induction orientation using QuotientAddGroup.induction_on'
    simp only [chapterVIResonantAverageOnCircle]
    exact_mod_cast hvalues _ 0
  apply hcoefficient
  unfold chapterVIOrientationCoefficient
  rw [hcircle]
  let _ : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  change fourierCoeff
      (fun _ : AddCircle (2 * Real.pi) ↦
        (resonantDisturbingAverage p q eccentricity 0 : ℂ)) n = 0
  let value : ℂ := resonantDisturbingAverage p q eccentricity 0
  have hfunction : (fun _ : AddCircle (2 * Real.pi) ↦ value) =
      fun orientation ↦ value * fourier 0 orientation := by
    funext orientation
    simp
  rw [hfunction, fourierCoeff.const_mul]
  rw [congrFun (fourierCoeff_fourier (T := 2 * Real.pi) 0) n]
  simp [hn]

/-- A restricted-problem analogue of the output that §§93--101 of Chapter VI are intended to
establish: at every positive rational resonance with a nonempty admissible eccentricity range,
one admissible parameter has a nonzero nonconstant Fourier mode.

This predicate deliberately packages the missing Darboux calculation as a hypothesis.  It is not
asserted as an axiom and the unconditional proof in this project does not use it. -/
def HasChapterVIDarbouxNonvanishing : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q →
    (admissibleResonantEccentricitySet p q).Nonempty →
    ∃ eccentricity ∈ admissibleResonantEccentricitySet p q,
      ∃ n : ℤ, n ≠ 0 ∧
        chapterVIOrientationCoefficient p q eccentricity n ≠ 0

/-- A stronger, explicitly asymptotic form of the missing restricted Darboux calculation.  It
matches Poincaré's pattern of an exponential singularity factor times a nonzero inverse-power
leading term. -/
def HasChapterVIDarbouxAsymptotics : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q →
    (admissibleResonantEccentricitySet p q).Nonempty →
    ∃ eccentricity ∈ admissibleResonantEccentricitySet p q,
      ∃ singularityInverse leadingCoefficient : ℂ,
        singularityInverse ≠ 0 ∧ leadingCoefficient ≠ 0 ∧
          (fun index : ℕ ↦ chapterVIOrientationCoefficient p q eccentricity (index + 1))
            ~[atTop]
          chapterVILeadingDarbouxModel singularityInverse leadingCoefficient

/-- The formalized Darboux consequence: a nonzero leading asymptotic model supplies an actual
nonzero Fourier mode on every admissible resonance. -/
theorem hasChapterVIDarbouxNonvanishing_of_asymptotics
    (hasymptotics : HasChapterVIDarbouxAsymptotics) :
    HasChapterVIDarbouxNonvanishing := by
  intro p q hp hq hnonempty
  rcases hasymptotics p q hp hq hnonempty with
    ⟨eccentricity, heccentricity, singularityInverse, leadingCoefficient,
      hsingularity, hleading, hasymptotic⟩
  have hnonzero :=
    eventually_coefficient_ne_zero_of_chapterVI_darboux_asymptotic
      hsingularity hleading hasymptotic
  rcases hnonzero.exists with ⟨index, hindex⟩
  refine ⟨eccentricity, heccentricity, index + 1, ?_, hindex⟩
  exact_mod_cast Nat.succ_ne_zero index

/-- The Darboux nonvanishing output supplies a separating pair of orientations at one admissible
eccentricity on every rational resonance. -/
theorem hasSeparatingResonantAverages_of_chapterVI
    (hDarboux : HasChapterVIDarbouxNonvanishing) :
    HasSeparatingResonantAverages := by
  intro p q hp hq hnonempty
  rcases hDarboux p q hp hq hnonempty with
    ⟨eccentricity, heccentricity, n, hn, hcoefficient⟩
  rcases exists_values_ne_of_chapterVIOrientationCoefficient_ne_zero
      hn hcoefficient with ⟨phaseA, phaseB, hvalues⟩
  exact ⟨phaseA, phaseB, eccentricity, heccentricity, sub_ne_zero.mpr hvalues⟩

/-- Restricted replacement for the final step of Chapter VI: the Darboux output makes the
restricted classical Poincaré set dense.  This is not Poincaré's singularity-parameter count in
§§102--103. -/
theorem hasDenseClassicalPoincareSet_of_chapterVI
    (hDarboux : HasChapterVIDarbouxNonvanishing) :
    HasDenseClassicalPoincareSet :=
  hasDenseClassicalPoincareSet_of_analytic_separation
    (hasAnalyticSeparatingResonantAverages_of_separation
      (hasSeparatingResonantAverages_of_chapterVI hDarboux))

/-- Conditional Chapter VI route to the project's restricted nonintegrability statement.

The hypothesis is precisely where the still-unformalized complex singularity classification,
admissibility argument, local expansions, and Darboux estimates of §§93--101 enter. -/
theorem nonintegrability_of_chapterVI
    (hDarboux : HasChapterVIDarbouxNonvanishing) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F :=
  nonintegrability_of_denseClassicalPoincareSet
    (hasDenseClassicalPoincareSet_of_chapterVI hDarboux)

/-- Conditional restricted nonintegrability directly from Darboux-type coefficient asymptotics. -/
theorem nonintegrability_of_chapterVI_asymptotics
    (hasymptotics : HasChapterVIDarbouxAsymptotics) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F :=
  nonintegrability_of_chapterVI
    (hasChapterVIDarbouxNonvanishing_of_asymptotics hasymptotics)

end LeanPool.PoincareThreeBody
