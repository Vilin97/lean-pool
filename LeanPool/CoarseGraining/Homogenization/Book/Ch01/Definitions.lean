/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.IntegralLpSeminorm
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Full
public import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactCircDomination
public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.FieldSpaces
public import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedConvexDomain
public import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedDomainCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.NegativeSobolev
public import LeanPool.CoarseGraining.Homogenization.Sobolev.NormalizedLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Normalized

/-! # Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch01

open scoped BigOperators ENNReal

/-!
# Chapter 1 public vocabulary

This file gives Chapter 1 a note-facing entry point without redefining the
underlying analysis. The unqualified names expose the exact proof-carrying
normalized and Besov kernels. Earlier totalized and disjoint-cube conventions
are retained only in `Book.Ch01.Legacy`.
-/

/-- The ambient coordinate space used throughout Chapter 1. -/
abbrev Vec (d : ℕ) :=
  Homogenization.Vec d

/-- The translated triadic cubes used throughout Chapter 1. -/
abbrev Cube (d : ℕ) :=
  Homogenization.TriadicCube d

noncomputable section

/-! ## Exact normalized cube quantities -/

/-- The proof-carrying normalized Bochner average on a triadic cube. -/
noncomputable abbrev normalizedAverage {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : Cube d) (f : Vec d → E)
    (hf : MeasureTheory.Integrable f
      (Homogenization.cubeBoundedMeasurableDomain Q).restrictedVolume) : E :=
  (Homogenization.cubeBoundedMeasurableDomain Q).average f hf

/-- The exact set-integral formula for the normalized Bochner cube average. -/
theorem normalizedAverage_eq_volume_toReal_inv_smul_setIntegral {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : Cube d)
    (f : Vec d → E)
    (hf : MeasureTheory.Integrable f
      (Homogenization.cubeBoundedMeasurableDomain Q).restrictedVolume) :
    normalizedAverage Q f hf =
      (MeasureTheory.volume (Homogenization.cubeSet Q)).toReal⁻¹ •
        ∫ x in Homogenization.cubeSet Q, f x ∂MeasureTheory.volume :=
  Homogenization.BoundedMeasurableDomain.average_eq_volume_toReal_inv_smul_setIntegral
    (Homogenization.cubeBoundedMeasurableDomain Q) f hf

/-- For scalar functions, the proof-carrying average is the established cube average. -/
theorem normalizedAverage_eq_cubeAverage {d : ℕ} (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.Integrable f
      (Homogenization.cubeBoundedMeasurableDomain Q).restrictedVolume) :
    normalizedAverage Q f hf = Homogenization.cubeAverage Q f :=
  Homogenization.cubeBoundedMeasurableDomain_average_eq_cubeAverage Q f hf

/-- The extended normalized cube `L^p` value. -/
noncomputable abbrev normalizedLpENorm {d : ℕ} {E : Type*} [ENorm E]
    (Q : Cube d) (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  (Homogenization.cubeBoundedMeasurableDomain Q).normalizedLpENorm p f

/-- The finite normalized cube `L^p` value certified by a `MemLp` witness. -/
noncomputable abbrev normalizedLpNorm {d : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (Q : Cube d) (p : ℝ≥0∞)
    (f : Vec d → E)
    (hf : MeasureTheory.MemLp f p
      (Homogenization.cubeBoundedMeasurableDomain Q).normalizedVolume) : ℝ :=
  (Homogenization.cubeBoundedMeasurableDomain Q).normalizedLpNorm p f hf

/-- The cube integral seminorm uses normalized cube measure, including for nonmeasurable functions. -/
theorem normalizedLpENorm_eq_integralLpSeminorm_normalizedCubeMeasure {d : ℕ}
    {E : Type*} [ENorm E] (Q : Cube d) (p : ℝ≥0∞) (f : Vec d → E) :
    normalizedLpENorm Q p f =
      Gagliardo.integralLpSeminorm f p (Homogenization.normalizedCubeMeasure Q) := by
  unfold normalizedLpENorm Homogenization.BoundedMeasurableDomain.normalizedLpENorm
    Gagliardo.integralLpSeminorm
  rw [Homogenization.cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]

/-- For measurable functions the cube extended norm agrees with Mathlib’s norm. -/
theorem normalizedLpENorm_eq_eLpNorm_normalizedCubeMeasure {d : ℕ}
    {E : Type*} [ENorm E] [TopologicalSpace E]
    (Q : Cube d) (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f (Homogenization.normalizedCubeMeasure Q)) :
    normalizedLpENorm Q p f =
      MeasureTheory.eLpNorm f p (Homogenization.normalizedCubeMeasure Q) := by
  rw [normalizedLpENorm_eq_integralLpSeminorm_normalizedCubeMeasure,
    Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _ hf]

/-- For finite `p ≥ 1`, the exact normalized cube norm has the manuscript moment formula. -/
theorem normalizedLpNorm_eq_integral_rpow {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : Cube d) (p : ℝ≥0∞) (hp_one : 1 ≤ p)
    (hp_top : p ≠ ∞) (f : Vec d → E)
    (hf : MeasureTheory.MemLp f p
      (Homogenization.cubeBoundedMeasurableDomain Q).normalizedVolume) :
    normalizedLpNorm Q p f hf =
      (∫ x, ‖f x‖ ^ p.toReal ∂Homogenization.normalizedCubeMeasure Q) ^ p.toReal⁻¹ := by
  change (Homogenization.cubeBoundedMeasurableDomain Q).normalizedLpNorm p f hf = _
  rw [Homogenization.BoundedMeasurableDomain.normalizedLpNorm_eq_normalizedLpMoment_rpow
    (Homogenization.cubeBoundedMeasurableDomain Q) p hp_one hp_top f hf]
  simp only [Homogenization.BoundedMeasurableDomain.normalizedLpMoment,
    Homogenization.cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]

/-- At `p = ∞`, the exact normalized cube value is the essential supremum. -/
theorem normalizedLpENorm_top_eq_essSup {d : ℕ} {E : Type*} [ENorm E]
    (Q : Cube d) (f : Vec d → E) :
    normalizedLpENorm Q ∞ f =
      essSup (fun x => ‖f x‖ₑ) (Homogenization.normalizedCubeMeasure Q) := by
  change (Homogenization.cubeBoundedMeasurableDomain Q).normalizedLpENorm ∞ f = _
  rw [Homogenization.BoundedMeasurableDomain.normalizedLpENorm_top_eq_essSup
      (Homogenization.cubeBoundedMeasurableDomain Q) f,
    Homogenization.cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]

/-- The extended normalized Euclidean `L^p` value of a vector field. -/
noncomputable abbrev normalizedEuclideanLpENorm {d n : ℕ} (Q : Cube d)
    (p : ℝ≥0∞) (f : Vec d → Vec n) : ℝ≥0∞ :=
  (Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p f

/-- The finite normalized Euclidean `L^p` value certified by a `MemLp` witness. -/
noncomputable abbrev normalizedEuclideanLpNorm {d n : ℕ} (Q : Cube d)
    (p : ℝ≥0∞) (f : Vec d → Vec n)
    (hf : MeasureTheory.MemLp (fun x => Homogenization.euclideanNorm (f x)) p
      (Homogenization.cubeBoundedMeasurableDomain Q).normalizedVolume) : ℝ :=
  (Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpNorm p f hf

/-- For finite `p ≥ 1`, the vector lane uses explicit Euclidean magnitude. -/
theorem normalizedEuclideanLpNorm_eq_integral_rpow {d n : ℕ} (Q : Cube d)
    (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (f : Vec d → Vec n)
    (hf : MeasureTheory.MemLp (fun x => Homogenization.euclideanNorm (f x)) p
      (Homogenization.cubeBoundedMeasurableDomain Q).normalizedVolume) :
    normalizedEuclideanLpNorm Q p f hf =
      (∫ x, Homogenization.euclideanNorm (f x) ^ p.toReal
        ∂Homogenization.normalizedCubeMeasure Q) ^ p.toReal⁻¹ := by
  change Homogenization.BoundedMeasurableDomain.normalizedEuclideanLpNorm
    (Homogenization.cubeBoundedMeasurableDomain Q) p f hf = _
  rw [Homogenization.BoundedMeasurableDomain.normalizedEuclideanLpNorm_eq_integral_rpow
      (Homogenization.cubeBoundedMeasurableDomain Q) p hp_one hp_top f hf,
    Homogenization.cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]

/-- At `p = ∞`, the vector lane is the essential supremum of Euclidean magnitude. -/
theorem normalizedEuclideanLpENorm_top_eq_essSup {d n : ℕ} (Q : Cube d)
    (f : Vec d → Vec n) :
    normalizedEuclideanLpENorm Q ∞ f =
      essSup (fun x => ENNReal.ofReal (Homogenization.euclideanNorm (f x)))
        (Homogenization.normalizedCubeMeasure Q) := by
  change Homogenization.BoundedMeasurableDomain.normalizedEuclideanLpENorm
    (Homogenization.cubeBoundedMeasurableDomain Q) ∞ f = _
  rw [Homogenization.BoundedMeasurableDomain.normalizedEuclideanLpENorm_top_eq_essSup
      (Homogenization.cubeBoundedMeasurableDomain Q) f,
    Homogenization.cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]

/-! ## Normalized Sobolev quantities -/

/-- Legacy cube `W^{1,p}` seminorm with an arbitrary gradient representative.
This is a cube-specialized compatibility alias, not the Chapter 1 weak-Sobolev
carrier. -/
noncomputable abbrev legacyCubeW1pSeminorm {d : ℕ} (Q : Cube d)
    (p : ℝ≥0∞) (Du : Vec d → Vec d) : ℝ :=
  Homogenization.cubeW1pSeminorm Q p Du

/-- Legacy cube `W^{1,p}` norm with an arbitrary gradient representative.
This is a cube-specialized compatibility alias, not the Chapter 1 weak-Sobolev
carrier. -/
noncomputable abbrev legacyCubeW1pNorm {d : ℕ} (Q : Cube d)
    (p : ℝ≥0∞) (u : Vec d → ℝ) (Du : Vec d → Vec d) : ℝ :=
  Homogenization.cubeW1pNorm Q p u Du

/-- The Chapter 1 finite-exponent normalized `W^{1,p}` seminorm on a genuine
weak-Sobolev witness over a nonempty bounded open convex domain. -/
noncomputable abbrev normalizedW1pSeminorm {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (u : W1pFunction U p) : ℝ :=
  BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
    (hU.toBoundedMeasurableDomain hne) p hp_one hp_top u

/-- The Chapter 1 finite-exponent normalized `W^{1,p}` norm on a genuine
weak-Sobolev witness over a nonempty bounded open convex domain. -/
noncomputable abbrev normalizedW1pNorm {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (u : W1pFunction U p) : ℝ :=
  BoundedMeasurableDomain.NormalizedW1pKernel.norm
    (hU.toBoundedMeasurableDomain hne) p hp_one hp_top u

/-- The Chapter 1 normalized `W^{1,∞}` seminorm on a genuine weak-Sobolev
witness over a nonempty bounded open convex domain. -/
noncomputable abbrev normalizedW1pSeminormTop {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (u : W1pFunction U ∞) : ℝ :=
  BoundedMeasurableDomain.NormalizedW1pKernel.seminormTop
    (hU.toBoundedMeasurableDomain hne) u

/-- The Chapter 1 normalized `W^{1,∞}` norm on a genuine weak-Sobolev witness,
over a nonempty bounded open convex domain, using the manuscript's additive
endpoint formula. -/
noncomputable abbrev normalizedW1pNormTop {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (u : W1pFunction U ∞) : ℝ :=
  BoundedMeasurableDomain.NormalizedW1pKernel.normTop
    (hU.toBoundedMeasurableDomain hne) u

/-! ## Exact negative Sobolev quantities -/

/-- The normalized zero-boundary `W^{-1,p'}` seminorm on `U`, with `p` the
positive test exponent. Its test class is literal smooth compact support. -/
noncomputable abbrev normalizedZeroBoundaryWMinusOneSeminorm {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p)
      (hU.toBoundedMeasurableDomain hne).normalizedVolume) : ℝ≥0∞ :=
  NegativeSobolev.smoothNegativeSobolevSeminorm hU hne p hp_one hp_top f hf

/-- The normalized mean-zero `W^{-1,p'}` seminorm on `U`, with `p` the
positive test exponent. Its test class consists of genuine mean-zero weak
`W^{1,p}` witnesses. -/
noncomputable abbrev normalizedMeanZeroWMinusOneSeminorm {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p)
      (hU.toBoundedMeasurableDomain hne).normalizedVolume) : ℝ≥0∞ :=
  NegativeSobolev.meanZeroNegativeSobolevSeminorm hU hne p hp_one hp_top f hf

/-- The zero-boundary normalized `H^{-1}` seminorm on `U`; this is the
`p = 2` instance with smooth compactly supported tests. -/
noncomputable abbrev normalizedZeroBoundaryHMinusOneSeminorm {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent (2 : ENNReal))
      (hU.toBoundedMeasurableDomain hne).normalizedVolume) : ℝ≥0∞ :=
  NegativeSobolev.smoothNegativeHMinusOneSeminorm hU hne f hf

/-- The mean-zero normalized `H^{-1}` seminorm on `U`; this is the distinct
`p = 2` convention with genuine mean-zero weak `W^{1,2}` tests. -/
noncomputable abbrev normalizedMeanZeroHMinusOneSeminorm {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent (2 : ENNReal))
      (hU.toBoundedMeasurableDomain hne).normalizedVolume) : ℝ≥0∞ :=
  NegativeSobolev.meanZeroNegativeHMinusOneSeminorm hU hne f hf

/-! ## Exact positive overlap Besov quantities -/

/-- Finite-`q` source parameters for the exact positive overlap Besov lane. -/
abbrev PositiveBesovFiniteParameters :=
  Homogenization.ExactOverlapFiniteParameters

/-- `q = ∞` source parameters for the exact positive overlap Besov lane. -/
abbrev PositiveBesovTopParameters :=
  Homogenization.ExactOverlapTopParameters

/-- Integrability witnesses for all averages in the exact positive Besov lane. -/
abbrev PositiveBesovIntegrable {d : ℕ} (Q : Cube d) (u : Vec d → ℝ) :=
  Homogenization.ExactOverlapIntegrable Q u

/-- The exact finite-`q` positive overlap Besov seminorm. -/
noncomputable abbrev positiveBesovFiniteSeminorm {d : ℕ}
    (P : PositiveBesovFiniteParameters) (Q : Cube d) (u : Vec d → ℝ)
    (hu : PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  Homogenization.exactOverlapFiniteSeminorm P Q u hu

/-- The exact finite-`q` positive overlap Besov norm. -/
noncomputable abbrev positiveBesovFiniteNorm {d : ℕ}
    (P : PositiveBesovFiniteParameters) (Q : Cube d) (u : Vec d → ℝ)
    (hu : PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  Homogenization.exactOverlapFiniteNorm P Q u hu

/-- The exact `q = ∞` positive overlap Besov seminorm. -/
noncomputable abbrev positiveBesovTopSeminorm {d : ℕ}
    (P : PositiveBesovTopParameters) (Q : Cube d) (u : Vec d → ℝ)
    (hu : PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  Homogenization.exactOverlapTopSeminorm P Q u hu

/-- The exact `q = ∞` positive overlap Besov norm. -/
noncomputable abbrev positiveBesovTopNorm {d : ℕ}
    (P : PositiveBesovTopParameters) (Q : Cube d) (u : Vec d → ℝ)
    (hu : PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  Homogenization.exactOverlapTopNorm P Q u hu

/-- Formula for the exact finite-`q` positive overlap Besov seminorm. -/
theorem positiveBesovFiniteSeminorm_eq {d : ℕ} (P : PositiveBesovFiniteParameters)
    (Q : Cube d) (u : Vec d → ℝ) (hu : PositiveBesovIntegrable Q u) :
    positiveBesovFiniteSeminorm P Q u hu =
      (∑' j : ℕ, (Homogenization.exactOverlapDepthTerm Q P.s P.p u hu j) ^ P.q) ^
        P.q⁻¹ :=
  Homogenization.exactOverlapFiniteSeminorm_eq P Q u hu

/-- Formula for the exact finite-`q` positive overlap Besov norm. -/
theorem positiveBesovFiniteNorm_eq {d : ℕ} (P : PositiveBesovFiniteParameters)
    (Q : Cube d) (u : Vec d → ℝ) (hu : PositiveBesovIntegrable Q u) :
    positiveBesovFiniteNorm P Q u hu = positiveBesovFiniteSeminorm P Q u hu +
      Homogenization.exactOverlapRootWeight Q P.s *
        ENNReal.ofReal |Homogenization.exactOverlapRootMean Q u hu.root| :=
  Homogenization.exactOverlapFiniteNorm_eq P Q u hu

/-- Formula for the exact `q = ∞` positive overlap Besov seminorm. -/
theorem positiveBesovTopSeminorm_eq {d : ℕ} (P : PositiveBesovTopParameters)
    (Q : Cube d) (u : Vec d → ℝ) (hu : PositiveBesovIntegrable Q u) :
    positiveBesovTopSeminorm P Q u hu =
      ⨆ j : ℕ, Homogenization.exactOverlapDepthTerm Q P.s P.p u hu j :=
  Homogenization.exactOverlapTopSeminorm_eq P Q u hu

/-- Formula for the exact `q = ∞` positive overlap Besov norm. -/
theorem positiveBesovTopNorm_eq {d : ℕ} (P : PositiveBesovTopParameters)
    (Q : Cube d) (u : Vec d → ℝ) (hu : PositiveBesovIntegrable Q u) :
    positiveBesovTopNorm P Q u hu = positiveBesovTopSeminorm P Q u hu +
      Homogenization.exactOverlapRootWeight Q P.s *
        ENNReal.ofReal |Homogenization.exactOverlapRootMean Q u hu.root| :=
  Homogenization.exactOverlapTopNorm_eq P Q u hu

/-! ## Exact dual negative Besov quantities -/

/-- Parameters for the exact negative `q = 1` dual Besov lane. -/
abbrev DualNegativeBesovQOneParameters :=
  Homogenization.ExactDualQOneParameters

/-- Parameters for the exact negative finite-interior dual Besov lane. -/
abbrev DualNegativeBesovFiniteParameters :=
  Homogenization.ExactDualFiniteParameters

/-- Parameters for the exact negative `q = ∞` dual Besov lane. -/
abbrev DualNegativeBesovTopParameters :=
  Homogenization.ExactDualTopParameters

/-- Full test carrier for the exact negative `q = 1` dual Besov norm. -/
abbrev DualNegativeBesovQOneFullTest {d : ℕ} (P : DualNegativeBesovQOneParameters)
    (Q : Cube d) :=
  Homogenization.ExactDualQOneFullTest P Q

/-- Hatted test carrier for the exact negative `q = 1` dual Besov seminorm. -/
abbrev DualNegativeBesovQOneHattedTest {d : ℕ} (P : DualNegativeBesovQOneParameters)
    (Q : Cube d) :=
  Homogenization.ExactDualQOneHattedTest P Q

/-- Full test carrier for the exact negative finite-interior dual Besov norm. -/
abbrev DualNegativeBesovFiniteFullTest {d : ℕ}
    (P : DualNegativeBesovFiniteParameters) (Q : Cube d) :=
  Homogenization.ExactDualFiniteFullTest P Q

/-- Hatted test carrier for the exact negative finite-interior dual Besov seminorm. -/
abbrev DualNegativeBesovFiniteHattedTest {d : ℕ}
    (P : DualNegativeBesovFiniteParameters) (Q : Cube d) :=
  Homogenization.ExactDualFiniteHattedTest P Q

/-- Full test carrier for the exact negative `q = ∞` dual Besov norm. -/
abbrev DualNegativeBesovTopFullTest {d : ℕ} (P : DualNegativeBesovTopParameters)
    (Q : Cube d) :=
  Homogenization.ExactDualTopFullTest P Q

/-- Hatted test carrier for the exact negative `q = ∞` dual Besov seminorm. -/
abbrev DualNegativeBesovTopHattedTest {d : ℕ} (P : DualNegativeBesovTopParameters)
    (Q : Cube d) :=
  Homogenization.ExactDualTopHattedTest P Q

/-- The exact negative `q = 1` hatted dual Besov seminorm. -/
noncomputable abbrev dualNegativeBesovQOneHattedSeminorm {d : ℕ}
    (P : DualNegativeBesovQOneParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  Homogenization.exactDualQOneHattedSeminorm P Q f hf

/-- The exact negative `q = 1` full dual Besov norm. -/
noncomputable abbrev dualNegativeBesovQOneFullNorm {d : ℕ}
    (P : DualNegativeBesovQOneParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  Homogenization.exactDualQOneFullNorm P Q f hf

/-- The exact negative finite-interior hatted dual Besov seminorm. -/
noncomputable abbrev dualNegativeBesovFiniteHattedSeminorm {d : ℕ}
    (P : DualNegativeBesovFiniteParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  Homogenization.exactDualFiniteHattedSeminorm P Q f hf

/-- The exact negative finite-interior full dual Besov norm. -/
noncomputable abbrev dualNegativeBesovFiniteFullNorm {d : ℕ}
    (P : DualNegativeBesovFiniteParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  Homogenization.exactDualFiniteFullNorm P Q f hf

/-- The exact negative `q = ∞` hatted dual Besov seminorm. -/
noncomputable abbrev dualNegativeBesovTopHattedSeminorm {d : ℕ}
    (P : DualNegativeBesovTopParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  Homogenization.exactDualTopHattedSeminorm P Q f hf

/-- The exact negative `q = ∞` full dual Besov norm. -/
noncomputable abbrev dualNegativeBesovTopFullNorm {d : ℕ}
    (P : DualNegativeBesovTopParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  Homogenization.exactDualTopFullNorm P Q f hf

/-- Formula for the exact negative `q = 1` hatted dual Besov seminorm. -/
theorem dualNegativeBesovQOneHattedSeminorm_eq {d : ℕ}
    (P : DualNegativeBesovQOneParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    dualNegativeBesovQOneHattedSeminorm P Q f hf =
      ⨆ T : DualNegativeBesovQOneHattedTest P Q, T.pairing hf :=
  Homogenization.exactDualQOneHattedSeminorm_eq P Q f hf

/-- Formula for the exact negative `q = 1` full dual Besov norm. -/
theorem dualNegativeBesovQOneFullNorm_eq {d : ℕ}
    (P : DualNegativeBesovQOneParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    dualNegativeBesovQOneFullNorm P Q f hf =
      ⨆ T : DualNegativeBesovQOneFullTest P Q, T.pairing hf :=
  Homogenization.exactDualQOneFullNorm_eq P Q f hf

/-- Formula for the exact negative finite-interior hatted dual Besov seminorm. -/
theorem dualNegativeBesovFiniteHattedSeminorm_eq {d : ℕ}
    (P : DualNegativeBesovFiniteParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    dualNegativeBesovFiniteHattedSeminorm P Q f hf =
      ⨆ T : DualNegativeBesovFiniteHattedTest P Q, T.pairing hf :=
  Homogenization.exactDualFiniteHattedSeminorm_eq P Q f hf

/-- Formula for the exact negative finite-interior full dual Besov norm. -/
theorem dualNegativeBesovFiniteFullNorm_eq {d : ℕ}
    (P : DualNegativeBesovFiniteParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    dualNegativeBesovFiniteFullNorm P Q f hf =
      ⨆ T : DualNegativeBesovFiniteFullTest P Q, T.pairing hf :=
  Homogenization.exactDualFiniteFullNorm_eq P Q f hf

/-- Formula for the exact negative `q = ∞` hatted dual Besov seminorm. -/
theorem dualNegativeBesovTopHattedSeminorm_eq {d : ℕ}
    (P : DualNegativeBesovTopParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    dualNegativeBesovTopHattedSeminorm P Q f hf =
      ⨆ T : DualNegativeBesovTopHattedTest P Q, T.pairing hf :=
  Homogenization.exactDualTopHattedSeminorm_eq P Q f hf

/-- Formula for the exact negative `q = ∞` full dual Besov norm. -/
theorem dualNegativeBesovTopFullNorm_eq {d : ℕ}
    (P : DualNegativeBesovTopParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    dualNegativeBesovTopFullNorm P Q f hf =
      ⨆ T : DualNegativeBesovTopFullTest P Q, T.pairing hf :=
  Homogenization.exactDualTopFullNorm_eq P Q f hf

/-! ## Exact concrete circ negative Besov quantities -/

/-- Parameters for the exact finite-`q` concrete circ Besov seminorm. -/
abbrev CircNegativeBesovFiniteParameters :=
  Homogenization.ExactCircFiniteParameters

/-- Parameters for the exact `q = ∞` concrete circ Besov seminorm. -/
abbrev CircNegativeBesovTopParameters :=
  Homogenization.ExactCircTopParameters

/-- Integrability witnesses for all disjoint block means in the exact circ lane. -/
abbrev CircNegativeBesovIntegrable {d : ℕ} (Q : Cube d) (f : Vec d → ℝ) :=
  Homogenization.ExactCircIntegrable Q f

/-- The exact finite-`q` concrete circ negative Besov seminorm. -/
noncomputable abbrev circNegativeBesovFiniteSeminorm {d : ℕ}
    (P : CircNegativeBesovFiniteParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : CircNegativeBesovIntegrable Q f) : ℝ≥0∞ :=
  Homogenization.exactCircFiniteSeminorm P Q f hf

/-- The exact `q = ∞` concrete circ negative Besov seminorm. -/
noncomputable abbrev circNegativeBesovTopSeminorm {d : ℕ}
    (P : CircNegativeBesovTopParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : CircNegativeBesovIntegrable Q f) : ℝ≥0∞ :=
  Homogenization.exactCircTopSeminorm P Q f hf

/-- Formula for the exact finite-`q` concrete circ negative Besov seminorm. -/
theorem circNegativeBesovFiniteSeminorm_eq {d : ℕ}
    (P : CircNegativeBesovFiniteParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : CircNegativeBesovIntegrable Q f) :
    circNegativeBesovFiniteSeminorm P Q f hf =
      (∑' j : ℕ, (Homogenization.exactCircDepthTerm Q P.s P.p f hf j) ^ P.q) ^
        P.q⁻¹ :=
  Homogenization.exactCircFiniteSeminorm_eq P Q f hf

/-- Formula for the exact `q = ∞` concrete circ negative Besov seminorm. -/
theorem circNegativeBesovTopSeminorm_eq {d : ℕ}
    (P : CircNegativeBesovTopParameters) (Q : Cube d) (f : Vec d → ℝ)
    (hf : CircNegativeBesovIntegrable Q f) :
    circNegativeBesovTopSeminorm P Q f hf =
      ⨆ j : ℕ, Homogenization.exactCircDepthTerm Q P.s P.p f hf j :=
  Homogenization.exactCircTopSeminorm_eq P Q f hf

/-! ## Legacy totalized and disjoint-cube compatibility vocabulary -/

namespace Legacy

/-- Legacy totalized cube average. This is not the proof-carrying Chapter 1 average. -/
noncomputable abbrev normalizedAverage {d : ℕ} (Q : Cube d)
    (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeAverage Q u

/-- Legacy totalized cube `L^p` norm. This is not the exact Chapter 1 norm. -/
noncomputable abbrev normalizedLpNorm {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : Cube d) (p : ℝ≥0∞) (u : Vec d → E) : ℝ :=
  Homogenization.cubeLpNorm Q p u

/-- Legacy finite-depth positive Besov norm using disjoint descendants. -/
noncomputable abbrev positiveBesovPartialNorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDisjointPartialNorm Q s p q N u

/-- Legacy finite-depth positive `q = ∞` Besov norm using disjoint descendants. -/
noncomputable abbrev positiveBesovPartialNormTop {d : ℕ} (Q : Cube d)
    (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDisjointPartialNormTop Q s p N u

/-- Legacy finite-depth positive `q = 2` Besov seminorm using disjoint descendants. -/
noncomputable abbrev positiveBesovPartialSeminormTwo {d : ℕ} (Q : Cube d)
    (s : ℝ) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDisjointPartialSeminorm Q s
    (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u

/-- Legacy totalized infinite-depth positive `q = 2` Besov seminorm. -/
noncomputable abbrev positiveBesovSeminormTwo {d : ℕ} (Q : Cube d)
    (s : ℝ) (u : Vec d → ℝ) : ℝ :=
  sSup (Set.range fun N : ℕ =>
    Homogenization.cubeBesovDisjointPartialSeminorm Q s
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u)

/-- Legacy finite-depth positive `q = 2` Besov norm using disjoint descendants. -/
noncomputable abbrev positiveBesovPartialNormTwo {d : ℕ} (Q : Cube d)
    (s : ℝ) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDisjointPartialNorm Q s
    (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u

/-- Legacy totalized infinite-depth positive `q = 2` Besov norm. -/
noncomputable abbrev positiveBesovNormTwo {d : ℕ} (Q : Cube d)
    (s : ℝ) (u : Vec d → ℝ) : ℝ :=
  sSup (Set.range fun N : ℕ =>
    Homogenization.cubeBesovDisjointPartialNorm Q s
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) u)

/-- Legacy dimension-shaped localization constant for the disjoint positive lane. -/
noncomputable abbrev positiveBesovLocalizeConstant (_d : ℕ) : ℝ := 2

/-- Legacy dimension-shaped localization constant for the totalized negative lane. -/
noncomputable abbrev negativeBesovLocalizeConstant (_d : ℕ) : ℝ := 2

/-- Legacy totalized infinite-depth positive `q = ∞` Besov norm. -/
noncomputable abbrev positiveBesovNormTop {d : ℕ} (Q : Cube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (Set.range fun N : ℕ =>
    Homogenization.cubeBesovDisjointPartialNormTop Q s p (N + 1) u)

/-- Legacy componentwise vector-valued positive `q = ∞` Besov norm.
The manuscript does not select this componentwise convention. -/
noncomputable abbrev positiveBesovVectorNormTop {d : ℕ} (Q : Cube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → Vec d) : ℝ :=
  ∑ i : Fin d, positiveBesovNormTop Q s p (fun x => u x i)

/-- Legacy totalized concrete circ negative Besov norm. -/
noncomputable abbrev circNegativeBesovNorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovCircNorm Q s p q u

/-- Legacy finite-depth totalized concrete circ negative Besov norm. -/
noncomputable abbrev circNegativeBesovPartialNorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovCircPartialNorm Q s p q N u

/-- Legacy totalized mean-zero dual negative Besov seminorm. -/
noncomputable abbrev dualNegativeBesovSeminorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDualMeanZeroSeminorm Q s p q u

/-- Legacy totalized full dual negative Besov norm. -/
noncomputable abbrev dualNegativeBesovNorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDualFullNorm Q s p q u

end Legacy

end

end Ch01
end Book
end Homogenization
