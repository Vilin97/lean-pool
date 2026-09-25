/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section51.AnnealedConvergence
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Public
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEllipticityBridge
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.SobolevPublic

/-!
# Main results: elliptic homogenization in the uniformly elliptic case

This file states the two main theorems of the manuscript, specialized to a
random coefficient field that is **uniformly elliptic**.

The ambient object is a `Setup`: a probability law `P` on `d × d`
divergence-form coefficient fields that is

* stationary, of unit range, isotropic, and adjoint-invariant (`hStruct`),
* equipped with the standard measurability/ellipticity data (`hP`), and
* **uniformly elliptic**: almost surely `lam I ≤ a ≤ Lam I` on every triadic
  cube, with deterministic constants `0 < lam ≤ Lam` (`hUE`).

The two results are:

* `annealedConvergence_uniformEllipticity` — the annealed contrast `Θ` converges
  to `1` at an algebraic rate beyond an explicit entry scale.
* `homogenizationComparison_uniformEllipticity` — above a random minimal scale
  `𝒳`, the legacy dual-Besov compatibility defect between the heterogeneous and
  homogenized solutions decays at algebraic rate `(3ᵐ / 𝒳)^(-α)`, with fixed
  public exponents and constants chosen before the law.

Both are proved in full, with no remaining proof obligations, from the general
theorems `Ch05.Section51.annealedConvergence_homogenizationScale` and
`Ch05.homogenization_quenched_homogenization_comparison`.

## Where the definitions live

The local wrappers `Setup`, `ComparisonPair`, `comparisonDefect`,
`comparisonData`, `IsMinimalScale`, and `originCube` are all defined **in this
file**, each with a docstring giving its mathematical meaning. They are thin
views on objects defined elsewhere (paths relative to the repository root; in an
editor every name is clickable and hovers its own docstring):

* ambient hypotheses `Ch04.RestrictionLawCarrier` (probability/measurability/local
  ellipticity) and `Ch04.RestrictionStructuralLaw` (stationarity, unit-range dependence,
  isotropy, adjoint invariance), and `Ch04.AELocallyUniformlyEllipticField`:
  `Homogenization/Book/Ch04/Law.lean`;
* `UniformEllipticityBounds`, the bridge to the coarse-grained inputs, and
  `mainResultsThetaHat`:
  `Homogenization/Book/Ch05/Theorems/Section57/UniformEllipticityBridge.lean`;
* the legacy dual-Besov comparison
  `Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS`, legacy
  fractional-Sobolev force seminorm
  `Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo`, and
  `Ch03.Legacy.ForceSobolevRegularity`, together with the bridges to the
  internal Besov theorem:
  `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean`;
  the energy norm `h1EnergyNormOnCube`:
  `Homogenization/Book/Ch03/Definitions.lean`;
* `assemblyComparisonDatumOfScalar`, `assemblyConstantCoeffMatrixOfScalar`, and
  `assemblyOriginCube`:
  `Homogenization/Book/Ch05/Theorems/Section57/HomogenizationAssembly.lean`;
  the homogenized scalar `barSigmaLimit`:
  `Homogenization/Book/Ch05/Theorems/Section57/AnnealedLimit.lean`;
* the general (non-uniform) theorems specialized here:
  `Homogenization/Book/Ch05/Theorems/Section51/AnnealedConvergence.lean` and
  `Homogenization/Book/Ch05/Theorems/Public.lean`.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace MainResults

open MeasureTheory
open IndependentSums
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- Almost-sure uniform ellipticity of the law `P` with deterministic constants
`lam`, `Lam` (`lam I ≤ a ≤ Lam I` a.s. on every triadic cube). -/
abbrev UniformEllipticityBounds {d : ℕ}
    (P : Ch04.RestrictionCoeffLaw d) (lam Lam : ℝ) : Prop :=
  Ch05.Section57.UniformEllipticityBounds P lam Lam

/-- The triadic cube `□ₘ` of side `3ᵐ` at the origin, on which the comparison is
stated. -/
abbrev originCube (d : ℕ) [NeZero d] (m : ℕ) : TriadicCube d :=
  Ch05.Section57.assemblyOriginCube d m

/-- Fixed public stochastic exponent for the law-independent comparison theorem.

The value is chosen only for a clean manuscript-facing corollary with no
remaining exponent parameters. -/
noncomputable abbrev fixedComparisonT : ℝ := 1 / 8

/-- Fixed exponent used by the legacy fractional-Sobolev compatibility lane of
the law-independent comparison theorem.

It satisfies `4 * fixedComparisonT < fixedComparisonS < 1`. -/
noncomputable abbrev fixedComparisonS : ℝ := 3 / 4

/-- Internal moment parameters used for the fixed-exponent comparison theorem.

These are strictly below `fixedComparisonT`; they are not exposed in the public
statement. -/
noncomputable def fixedQuenchedParams (d : ℕ) (hd : 2 ≤ d) :
    Ch05.Section57.GammaCoarseGrainedEllipticityParams d where
  sUpper := 1 / 16
  sLower := 1 / 16
  two_le_dim := hd
  sUpper_pos := by norm_num
  sUpper_lt_one := by norm_num
  sLower_pos := by norm_num
  sLower_lt_one := by norm_num
  sum_lt_one := by norm_num

/-- The ambient data for the main results: a stationary, unit-range, isotropic,
adjoint-invariant, uniformly elliptic random coefficient field in dimension
`d ≥ 2`. -/
structure Setup (d : ℕ) [NeZero d] where
  /-- The dimension is at least two. -/
  two_le_dim : 2 ≤ d
  /-- The probability law on coefficient fields. -/
  P : Ch04.RestrictionCoeffLaw d
  /-- Probability/measurability/local-ellipticity data carried by the law. -/
  hP : Ch04.RestrictionLawCarrier P
  /-- Stationarity, unit-range dependence, isotropy, and adjoint invariance of
  the law. -/
  hStruct : Ch04.RestrictionStructuralLaw P
  /-- Lower ellipticity constant. -/
  lam : ℝ
  /-- Upper ellipticity constant. -/
  Lam : ℝ
  /-- Almost-sure uniform ellipticity with constants `lam`, `Lam`. -/
  hUE : UniformEllipticityBounds P lam Lam

namespace Setup

variable {d : ℕ} [NeZero d] (S : Setup d)

/-- The deterministic endpoint size `θ̂`, a function of the ellipticity ratio
`Lam / lam`. -/
noncomputable def thetaHat : ℝ :=
  Ch05.Section57.mainResultsThetaHat d S.lam S.Lam

/-- A fixed admissible coarse-grained ellipticity parameter bundle
(`s₁ = s₂ = 1/8`). It is used only internally, to recover the `(P4)`/`(P5)`
inputs from uniform ellipticity; none of its exponents appear in the public
statements. -/
noncomputable def gammaParams :
    Ch05.Section57.GammaCoarseGrainedEllipticityParams d where
  sUpper := 1 / 8
  sLower := 1 / 8
  two_le_dim := S.two_le_dim
  sUpper_pos := by norm_num
  sUpper_lt_one := by norm_num
  sLower_pos := by norm_num
  sLower_lt_one := by norm_num
  sum_lt_one := by norm_num

/-- The `(P4)` quantitative coarse-grained ellipticity input recovered from
uniform ellipticity. -/
noncomputable def p4 : Ch05.QuantitativeCoarseGrainedEllipticity S.P :=
  Ch05.Section57.UniformEllipticityBounds.toQuantitativeCoarseGrainedEllipticity
    S.hUE S.hP S.gammaParams.toQuantitativeParams

/-- The `σ = ∞` endpoint input recovered from uniform ellipticity (built from the
fixed parameters, hence independent of the exponents `t`, `s`). -/
noncomputable def endpoint :
    Ch05.Section57.GammaInfinityCoarseGrainedEllipticityNoXi S.P S.hP S.hStruct :=
  S.hUE.toGammaInfinityCoarseGrainedEllipticityNoXi S.hP S.hStruct S.gammaParams

/-- Positivity of the homogenized scalar `σ̄`, independent of the exponents. -/
theorem barSigmaLimit_pos :
    0 < Ch05.Section57.barSigmaLimit S.hP S.hStruct :=
  (S.endpoint.withInternalXi.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos

/-- The homogenized constant coefficient matrix `ā = σ̄ I`. -/
noncomputable def homogenizedMatrix : Ch03.ConstantCoeffMatrix d :=
  Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
    (Ch05.Section57.barSigmaLimit S.hP S.hStruct) S.barSigmaLimit_pos

/-- A comparison pair on the triadic cube `□ₘ`: weak solutions `u, v ∈ H¹(□ₘ)`
with the same right-hand side `∇·g` and the same boundary data, where `u` solves
the heterogeneous equation `-∇·a∇u = ∇·g`, `v` solves the homogenized equation
`-∇·ā∇v = ∇·g`, and `u - v ∈ H¹₀(□ₘ)`.  Wraps
`Ch05.Section57.assemblyComparisonDatumOfScalar`; `pair.u` and `pair.v` are the
two solutions. -/
abbrev ComparisonPair (aω : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m : ℕ) (g : Vec d → Vec d) : Type :=
  Ch05.Section57.assemblyComparisonDatumOfScalar
    (Ch05.Section57.barSigmaLimit S.hP S.hStruct) S.barSigmaLimit_pos aω ha m g

/-- The legacy dual-Besov compatibility defect at exponent `s`.

This wraps `Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS`; it is not
an identification with either Chapter 1 negative-Sobolev primitive. -/
noncomputable def comparisonDefect (s : ℝ)
    {aω : RegCoeffField d} {ha : Ch04.AELocallyUniformlyEllipticField aω}
    {m : ℕ} {g : Vec d → Vec d}
    (pair : S.ComparisonPair aω ha m g) : ℝ :=
  Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS
    (originCube d m)
    (Ch05.Section57.assemblyCoeffFamily aω ha)
    S.homogenizedMatrix s pair.u pair.v

/-- The data norm controlling the compatibility defect.

Its force term is the componentwise legacy fractional-Sobolev seminorm; it
wraps `Ch03.h1EnergyNormOnCube` and
`Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo`. -/
noncomputable def comparisonData (s : ℝ)
    {aω : RegCoeffField d} {ha : Ch04.AELocallyUniformlyEllipticField aω}
    {m : ℕ} {g : Vec d → Vec d}
    (pair : S.ComparisonPair aω ha m g) : ℝ :=
  Real.sqrt (Ch05.Section57.barSigmaLimit S.hP S.hStruct) *
      Ch03.h1EnergyNormOnCube (originCube d m)
        (Ch05.Section57.assemblyCoeffFamily aω ha) pair.u +
    Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
      (originCube d m) s g

/-- `𝒳` is a minimal scale: it is bounded below by `1` and has `Γ_d`
(stretched-exponential, exponent `d`) upper tails of size
`exp ( Cscale · log²(2 + θ̂) )`. -/
def IsMinimalScale (𝒳 : RegCoeffField d → ℝ) (Cscale : ℝ) : Prop :=
  (∀ aω, 1 ≤ 𝒳 aω) ∧
    Ch04.IsBigO S.P (gammaSigma ((d : ℕ) : ℝ)) 𝒳
      (Real.exp (Cscale * (Real.log (2 + S.thetaHat)) ^ (2 : ℕ)))

/-- The entry scale `N₀` past which the annealed contrast decays algebraically. -/
noncomputable def annealedEntryScale (C : ℝ) : ℕ :=
  Ch05.annealedAlgebraicEntryScale S.P S.p4 C

/-- The internal `σ = ∞` endpoint parameters for the quenched theorem
(`s₁ = s₂ = t/2`), chosen below the public exponent `t`. -/
noncomputable def quenchedParams {t s : ℝ}
    (ht : 0 < t) (hts : 4 * t < s) (hs : s < 1) :
    Ch05.Section57.GammaCoarseGrainedEllipticityParams d where
  sUpper := t / 2
  sLower := t / 2
  two_le_dim := S.two_le_dim
  sUpper_pos := by linarith
  sUpper_lt_one := by linarith
  sLower_pos := by linarith
  sLower_lt_one := by linarith
  sum_lt_one := by
    have : t < 1 := by linarith
    linarith

end Setup

/-- **Convergence of the annealed contrast (uniformly elliptic case).**

For a stationary, unit-range, isotropic, adjoint-invariant, uniformly elliptic
law `S`, the annealed contrast `Θ` converges to `1` at an algebraic rate: there
are constants `C, α > 0` such that for every `n`, the contrast at scale
`S.annealedEntryScale C + n` is at most `1 + 3^(-α n)`. -/
theorem annealedConvergence_uniformEllipticity
    {d : ℕ} [NeZero d] (S : Setup d) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
      ∀ n : ℕ,
        Ch05.thetaAtScale S.hP S.hStruct ((S.annealedEntryScale C + n : ℕ) : ℤ) ≤
          1 + Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
  obtain ⟨C, α, hC, hα, hmain⟩ :=
    Ch05.Section51.annealedConvergence_homogenizationScale
      S.gammaParams.toQuantitativeParams
  refine ⟨C, α, hC, hα, fun n => ?_⟩
  have hparams : S.p4.params = S.gammaParams.toQuantitativeParams := rfl
  have h := hmain S.hP S.hStruct S.p4 hparams n
  simpa [Setup.annealedEntryScale, Setup.p4] using h

/-- Auxiliary variable-exponent quenched comparison corollary.

For a stationary, unit-range, isotropic, adjoint-invariant, uniformly elliptic
law `S`, and exponents `t, s` with `0 < t`, `4t < s`, `s < 1`, there is a
random minimal scale `𝒳` (with `Γ_d` tails) such that, almost surely, on every
triadic cube `□ₘ` with `𝒳 ≤ 3ᵐ`, for every comparison pair `u, v` and every
force satisfying the legacy fractional-Sobolev compatibility condition, the
legacy dual-Besov compatibility defect is controlled by the corresponding data
norm at the algebraic rate `(3ᵐ / 𝒳)^(-α)`.

This theorem keeps the exponents variable, so its constants are selected after
`S`, `t`, and `s`. The public compatibility theorem below fixes the
exponents and chooses the constants before the law. -/
theorem homogenizationComparison_uniformEllipticity_variableExponents
    {d : ℕ} [NeZero d] (S : Setup d) :
    ∀ {t s : ℝ}, 0 < t → 4 * t < s → s < 1 →
      ∃ C α Cscale : ℝ,
        0 < C ∧ 0 < α ∧ 0 < Cscale ∧
        ∃ 𝒳 : RegCoeffField d → ℝ,
          S.IsMinimalScale 𝒳 Cscale ∧
          ∀ᵐ aω ∂S.P,
            ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
              {m : ℕ} {g : Vec d → Vec d}
              (pair : S.ComparisonPair aω ha m g),
              𝒳 aω ≤ (3 : ℝ) ^ m →
              Ch03.Legacy.ForceSobolevRegularity (originCube d m) s g →
              S.comparisonDefect s pair ≤
                C * ((3 : ℝ) ^ m / 𝒳 aω) ^ (-α) * S.comparisonData s pair := by
  intro t s ht hts hs
  let params : Ch05.Section57.GammaCoarseGrainedEllipticityParams d :=
    S.quenchedParams ht hts hs
  obtain ⟨α, hα, hendpoint⟩ :=
    (Ch05.homogenization_quenched_homogenization_comparison params).2
  have hmax : max params.sUpper params.sLower < t := by
    simp only [params, Setup.quenchedParams, max_self]
    linarith
  obtain ⟨C0, Cscale, hC0, hCscale, hlaw⟩ := hendpoint hmax hts hs
  let Kneg : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)
  let Kpos : ℝ := (3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d
  let Kdata : ℝ := 1 + Kpos
  let C : ℝ := Kneg * Kdata * C0
  have hd_pos_nat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hKneg_pos : 0 < Kneg := by
    exact mul_pos hd_pos (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _)
  have hKpos_nonneg : 0 ≤ Kpos := by
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (le_of_lt (Ch01.Legacy.wspVsBsppConstant_pos d))
  have hKdata_pos : 0 < Kdata := by
    dsimp [Kdata]
    nlinarith
  have hKdata_ge_one : 1 ≤ Kdata := by
    dsimp [Kdata]
    nlinarith
  have hKpos_le_Kdata : Kpos ≤ Kdata := by
    dsimp [Kdata]
    nlinarith
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos hKneg_pos hKdata_pos) hC0
  let hInf :
      Ch05.Section57.GammaInfinityCoarseGrainedEllipticityNoXi S.P S.hP S.hStruct :=
    S.hUE.toGammaInfinityCoarseGrainedEllipticityNoXi S.hP S.hStruct params
  have hparams : hInf.params = params := rfl
  obtain ⟨X, hX, hX_one, hmain⟩ := hlaw S.hP S.hStruct hInf hparams
  refine ⟨C, α, Cscale, hC, hα, hCscale, X, ⟨hX_one, ?_⟩, ?_⟩
  · simpa [Setup.thetaHat, hInf, Setup.endpoint,
      Ch05.Section57.UniformEllipticityBounds.toGammaInfinityCoarseGrainedEllipticityNoXi]
      using hX
  · filter_upwards [hmain] with aω haω
    intro ha m g pair hXm hg
    have hs_pos : 0 < s := by linarith
    have hs_le_one : s ≤ 1 := le_of_lt hs
    have hgBesov : Ch03.ForceBesovRegularity (originCube d m) s g :=
      hg.toForceBesovRegularity hs_pos hs_le_one
    have hstep := haω ha (m := m) (g := g) pair hXm hgBesov
    let rate : ℝ := ((3 : ℝ) ^ m / X aω) ^ (-α)
    let E : ℝ :=
      Real.sqrt (Ch05.Section57.barSigmaLimit S.hP S.hStruct) *
        Ch03.h1EnergyNormOnCube (originCube d m)
          (Ch05.Section57.assemblyCoeffFamily aω ha) pair.u
    let B : ℝ :=
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
        (originCube d m) s g
    let H : ℝ :=
      Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (originCube d m) s g
    have hrate_nonneg : 0 ≤ rate := by
      have hX_pos : 0 < X aω := lt_of_lt_of_le zero_lt_one (hX_one aω)
      have hbase_nonneg : 0 ≤ (3 : ℝ) ^ m / X aω := by
        exact div_nonneg (le_of_lt (pow_pos (by norm_num : 0 < (3 : ℝ)) m))
          (le_of_lt hX_pos)
      exact Real.rpow_nonneg hbase_nonneg _
    have hE_nonneg : 0 ≤ E := by
      dsimp [E]
      exact mul_nonneg (Real.sqrt_nonneg _)
        (by
          unfold Ch03.h1EnergyNormOnCube
          exact Real.sqrt_nonneg _)
    have hH_nonneg : 0 ≤ H := by
      dsimp [H]
      exact Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo_nonneg
        (originCube d m) s g
    have hB_le_H : B ≤ Kpos * H := by
      dsimp [B, H, Kpos]
      exact Ch03.Legacy.scaleNormalizedPositiveBesovVectorSeminormTwo_le_const_mul_sobolev
        (originCube d m) (s := s) g hs_pos hs_le_one hg
    have hdata : E + B ≤ Kdata * (E + H) := by
      have hE_le : E ≤ Kdata * E := by
        calc
          E = 1 * E := by ring
          _ ≤ Kdata * E :=
            mul_le_mul_of_nonneg_right hKdata_ge_one hE_nonneg
      have hB_le_Kdata : B ≤ Kdata * H := by
        exact hB_le_H.trans
          (mul_le_mul_of_nonneg_right hKpos_le_Kdata hH_nonneg)
      calc
        E + B ≤ Kdata * E + Kdata * H := add_le_add hE_le hB_le_Kdata
        _ = Kdata * (E + H) := by ring
    have hold :
        Ch03.homogenizationComparisonNegativeBesovLHS
            (originCube d m)
            (Ch05.Section57.assemblyCoeffFamily aω ha)
            S.homogenizedMatrix s pair.u pair.v ≤
          C0 * rate * (E + B) := by
      simpa [rate, E, B, Setup.homogenizedMatrix,
        Setup.ComparisonPair, Setup.barSigmaLimit_pos, hInf, Setup.endpoint]
        using! hstep
    have hneg :
        S.comparisonDefect s pair ≤
          Kneg *
            Ch03.homogenizationComparisonNegativeBesovLHS
              (originCube d m)
              (Ch05.Section57.assemblyCoeffFamily aω ha)
              S.homogenizedMatrix s pair.u pair.v := by
      simpa [Setup.comparisonDefect, Kneg, Setup.homogenizedMatrix,
        Setup.ComparisonPair, Setup.barSigmaLimit_pos]
        using
          Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS_le_const_mul_negativeBesovLHS
            (originCube d m)
            (Ch05.Section57.assemblyCoeffFamily aω ha)
            S.homogenizedMatrix s pair.u pair.v hs_pos
    calc
      S.comparisonDefect s pair
          ≤
            Kneg *
              Ch03.homogenizationComparisonNegativeBesovLHS
                (originCube d m)
                (Ch05.Section57.assemblyCoeffFamily aω ha)
                S.homogenizedMatrix s pair.u pair.v := hneg
      _ ≤ Kneg * (C0 * rate * (E + B)) := by
            exact mul_le_mul_of_nonneg_left hold (le_of_lt hKneg_pos)
      _ ≤ Kneg * (C0 * rate * (Kdata * (E + H))) := by
            have hcoef_nonneg : 0 ≤ C0 * rate :=
              mul_nonneg (le_of_lt hC0) hrate_nonneg
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hdata hcoef_nonneg)
              (le_of_lt hKneg_pos)
      _ = C * rate * (E + H) := by
            dsimp [C]
            ring
      _ = C * ((3 : ℝ) ^ m / X aω) ^ (-α) * S.comparisonData s pair := by
            dsimp [rate, E, H]
            simp [Setup.comparisonData]

/-- **Quenched homogenization above the minimal scale, fixed-exponent form.**

This is the law-independent-constant public compatibility corollary used by the
comparator audit. The compatibility exponents are fixed to `t = 1/8` and
`s = 3/4`; consequently the constants `C`, `α`, and `Cscale` are chosen before the probability law
`S : Setup d`.  In particular they do not depend on the law, on the ellipticity
constants, on the realization, or on any solution data. -/
theorem homogenizationComparison_uniformEllipticity
    {d : ℕ} [NeZero d] :
    ∃ C α Cscale : ℝ,
      0 < C ∧ 0 < α ∧ 0 < Cscale ∧
      ∀ S : Setup d,
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : RegCoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ aω ∂S.P,
              ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : S.ComparisonPair aω ha m g),
                X aω ≤ (3 : ℝ) ^ m →
                Ch03.Legacy.ForceSobolevRegularity (originCube d m) fixedComparisonS g →
                S.comparisonDefect fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X aω) ^ (-α) *
                    S.comparisonData fixedComparisonS pair := by
  classical
  by_cases hdim : 2 ≤ d
  · let params : Ch05.Section57.GammaCoarseGrainedEllipticityParams d :=
      fixedQuenchedParams d hdim
    obtain ⟨α, hα, hendpoint⟩ :=
      (Ch05.homogenization_quenched_homogenization_comparison params).2
    have hmax : max params.sUpper params.sLower < fixedComparisonT := by
      norm_num [params, fixedQuenchedParams, fixedComparisonT]
    have hts : 4 * fixedComparisonT < fixedComparisonS := by
      norm_num [fixedComparisonT, fixedComparisonS]
    have hs : fixedComparisonS < 1 := by
      norm_num [fixedComparisonS]
    obtain ⟨C0, Cscale, hC0, hCscale, hlaw⟩ := hendpoint hmax hts hs
    let Kneg : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + fixedComparisonS)
    let Kpos : ℝ := (3 : ℝ) ^ ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d
    let Kdata : ℝ := 1 + Kpos
    let C : ℝ := Kneg * Kdata * C0
    have hd_pos_nat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
    have hKneg_pos : 0 < Kneg := by
      exact mul_pos hd_pos (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _)
    have hKpos_nonneg : 0 ≤ Kpos := by
      exact mul_nonneg
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (le_of_lt (Ch01.Legacy.wspVsBsppConstant_pos d))
    have hKdata_pos : 0 < Kdata := by
      dsimp [Kdata]
      nlinarith
    have hKdata_ge_one : 1 ≤ Kdata := by
      dsimp [Kdata]
      nlinarith
    have hKpos_le_Kdata : Kpos ≤ Kdata := by
      dsimp [Kdata]
      nlinarith
    have hC : 0 < C := by
      dsimp [C]
      exact mul_pos (mul_pos hKneg_pos hKdata_pos) hC0
    refine ⟨C, α, Cscale, hC, hα, hCscale, ?_⟩
    intro S
    let sigmaBar : ℝ :=
      Ch05.Section57.barSigmaLimit S.hP S.hStruct
    have hsigma : 0 < sigmaBar := by
      dsimp [sigmaBar]
      exact S.barSigmaLimit_pos
    let hInf :
        Ch05.Section57.GammaInfinityCoarseGrainedEllipticityNoXi S.P S.hP S.hStruct :=
      S.hUE.toGammaInfinityCoarseGrainedEllipticityNoXi S.hP S.hStruct params
    have hparams : hInf.params = params := rfl
    obtain ⟨X, hX, hX_one, hmain⟩ := hlaw S.hP S.hStruct hInf hparams
    refine ⟨sigmaBar, hsigma, X, ⟨hX_one, ?_⟩, ?_⟩
    · simpa [Setup.thetaHat, hInf,
        Ch05.Section57.UniformEllipticityBounds.toGammaInfinityCoarseGrainedEllipticityNoXi]
        using hX
    · filter_upwards [hmain] with aω haω
      intro ha m g pair hXm hg
      have hs_pos : 0 < fixedComparisonS := by
        norm_num [fixedComparisonS]
      have hs_le_one : fixedComparisonS ≤ 1 := by
        norm_num [fixedComparisonS]
      have hgBesov : Ch03.ForceBesovRegularity (originCube d m) fixedComparisonS g :=
        hg.toForceBesovRegularity hs_pos hs_le_one
      have hstep := haω ha (m := m) (g := g) pair hXm hgBesov
      let rate : ℝ := ((3 : ℝ) ^ m / X aω) ^ (-α)
      let E : ℝ :=
        Real.sqrt (Ch05.Section57.barSigmaLimit S.hP S.hStruct) *
          Ch03.h1EnergyNormOnCube (originCube d m)
            (Ch05.Section57.assemblyCoeffFamily aω ha) pair.u
      let B : ℝ :=
        Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
          (originCube d m) fixedComparisonS g
      let H : ℝ :=
        Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
          (originCube d m) fixedComparisonS g
      have hrate_nonneg : 0 ≤ rate := by
        have hX_pos : 0 < X aω := lt_of_lt_of_le zero_lt_one (hX_one aω)
        have hbase_nonneg : 0 ≤ (3 : ℝ) ^ m / X aω := by
          exact div_nonneg (le_of_lt (pow_pos (by norm_num : 0 < (3 : ℝ)) m))
            (le_of_lt hX_pos)
        exact Real.rpow_nonneg hbase_nonneg _
      have hE_nonneg : 0 ≤ E := by
        dsimp [E]
        exact mul_nonneg (Real.sqrt_nonneg _)
          (by
            unfold Ch03.h1EnergyNormOnCube
            exact Real.sqrt_nonneg _)
      have hH_nonneg : 0 ≤ H := by
        dsimp [H]
        exact Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo_nonneg
          (originCube d m) fixedComparisonS g
      have hB_le_H : B ≤ Kpos * H := by
        dsimp [B, H, Kpos]
        exact Ch03.Legacy.scaleNormalizedPositiveBesovVectorSeminormTwo_le_const_mul_sobolev
          (originCube d m) (s := fixedComparisonS) g hs_pos hs_le_one hg
      have hdata : E + B ≤ Kdata * (E + H) := by
        have hE_le : E ≤ Kdata * E := by
          calc
            E = 1 * E := by ring
            _ ≤ Kdata * E :=
              mul_le_mul_of_nonneg_right hKdata_ge_one hE_nonneg
        have hB_le_Kdata : B ≤ Kdata * H := by
          exact hB_le_H.trans
            (mul_le_mul_of_nonneg_right hKpos_le_Kdata hH_nonneg)
        calc
          E + B ≤ Kdata * E + Kdata * H := add_le_add hE_le hB_le_Kdata
          _ = Kdata * (E + H) := by ring
      have hold :
          Ch03.homogenizationComparisonNegativeBesovLHS
              (originCube d m)
              (Ch05.Section57.assemblyCoeffFamily aω ha)
              S.homogenizedMatrix fixedComparisonS pair.u pair.v ≤
            C0 * rate * (E + B) := by
        simpa [rate, E, B, Setup.homogenizedMatrix,
          Setup.ComparisonPair, Setup.barSigmaLimit_pos, hInf]
          using! hstep
      have hneg :
          S.comparisonDefect fixedComparisonS pair ≤
            Kneg *
              Ch03.homogenizationComparisonNegativeBesovLHS
                (originCube d m)
                (Ch05.Section57.assemblyCoeffFamily aω ha)
                S.homogenizedMatrix fixedComparisonS pair.u pair.v := by
        simpa [Setup.comparisonDefect, Kneg, Setup.homogenizedMatrix,
          Setup.ComparisonPair, Setup.barSigmaLimit_pos]
          using
            Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS_le_const_mul_negativeBesovLHS
              (originCube d m)
              (Ch05.Section57.assemblyCoeffFamily aω ha)
              S.homogenizedMatrix fixedComparisonS pair.u pair.v hs_pos
      calc
        S.comparisonDefect fixedComparisonS pair
            ≤
              Kneg *
                Ch03.homogenizationComparisonNegativeBesovLHS
                  (originCube d m)
                  (Ch05.Section57.assemblyCoeffFamily aω ha)
                  S.homogenizedMatrix fixedComparisonS pair.u pair.v := hneg
        _ ≤ Kneg * (C0 * rate * (E + B)) := by
              exact mul_le_mul_of_nonneg_left hold (le_of_lt hKneg_pos)
        _ ≤ Kneg * (C0 * rate * (Kdata * (E + H))) := by
              have hcoef_nonneg : 0 ≤ C0 * rate :=
                mul_nonneg (le_of_lt hC0) hrate_nonneg
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hdata hcoef_nonneg)
                (le_of_lt hKneg_pos)
        _ = C * rate * (E + H) := by
              dsimp [C]
              ring
        _ = C * ((3 : ℝ) ^ m / X aω) ^ (-α) *
              S.comparisonData fixedComparisonS pair := by
              dsimp [rate, E, H]
              simp [Setup.comparisonData]
  · refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro S
    exact False.elim (hdim S.two_le_dim)

end

end MainResults
end Book
end Homogenization
