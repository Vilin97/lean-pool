/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicCoefficientBounds

/-! # Harmonic Scalar Controls -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Harmonic scalar-control factors

This file packages the remaining Phase 2 scalar-control primitives for the
canonical harmonic coarse-Caccioppoli wrappers.  The raw bundled hypothesis
`CoarseCaccioppoliScalarCutoffControls` has already been removed from the
strongest localization-data endpoints; this sidecar replaces the two exact
cutoff-size positivity hypotheses by simpler positive factor assumptions.
-/

/-- Vector `L²` data on the open cube also gives `L²` data for the normalized
closed-cube measure. -/
theorem memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → Vec d}
    (hf : MemVectorL2 (openCubeSet Q) f) :
    MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hfCube :
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (MeasureTheory.volume.restrict (cubeSet Q)) := by
    simpa [MemVectorL2, volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using hf
  exact
    hfCube.of_measure_le_smul (c := ENNReal.ofReal ((cubeVolume Q)⁻¹))
      ENNReal.ofReal_ne_top (by rw [normalizedCubeMeasure, cubeMeasure])

/-- Scalar `L²` data on the open cube also gives `L²` data for the normalized
closed-cube measure. -/
theorem memLp_normalizedCubeMeasure_of_memL2On_openCubeSet {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet Q) f) :
    MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hfCube :
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (MeasureTheory.volume.restrict (cubeSet Q)) := by
    simpa [MemL2On, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using hf
  exact
    hfCube.of_measure_le_smul (c := ENNReal.ofReal ((cubeVolume Q)⁻¹))
      ENNReal.ofReal_ne_top (by rw [normalizedCubeMeasure, cubeMeasure])

/-- An open-cube harmonic function is `L²` for the normalized closed-cube
measure. -/
theorem memLp_harmonicFunction_normalizedCubeMeasure {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (w : AHarmonicFunction a (openCubeSet Q)) :
    MeasureTheory.MemLp (fun x => w.toH1 x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  simpa using memLp_normalizedCubeMeasure_of_memL2On_openCubeSet Q w.toH1.memL2

/-- The flux of an open-cube harmonic function is `L²` for the normalized
closed-cube measure under ellipticity. -/
theorem memLp_harmonicFlux_normalizedCubeMeasure {d : ℕ} {lam Lam : ℝ}
    (Q : TriadicCube d) (a : CoeffField d)
    (w : AHarmonicFunction a (openCubeSet Q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    MeasureTheory.MemLp
      (fun x => matVecMul (a x) (w.toH1.grad x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  exact
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2)

/-- The flux-energy package already includes the `B`-coefficient summability
needed by the final radius bridge.  A single fixed admissible radius pair is
enough because this summability does not depend on the radius pair. -/
theorem summable_bBlock_geometricWeight_s_of_fluxEnergyControls_family {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    {flux : ℝ → ℝ → Vec d → Vec d} {energy : ℝ → ℝ → Vec d → ℝ}
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂)) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  exact
    (hfluxEnergy (ρ₁ := (1 / 3 : ℝ)) (ρ₂ := (2 / 3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)).2.2.2.2

/-- Radius-wise primitive data that generate the scalar cutoff-control bundle
for the canonical Chapter 3 cutoff. -/
def CoarseCaccioppoliBoundaryCanonicalScalarControlFactors {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ) (Acirc1 AcircS : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    0 < cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ∧
    0 < Acirc1 ρ₁ ρ₂ ∧
    0 ≤ AcircS ρ₁ ρ₂ ∧
    0 <
      Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)) ∧
    (∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
        (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x)) (g ρ₁ ρ₂) N) ∧
    (∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
        Acirc1 ρ₁ ρ₂ *
          Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))) ∧
    (∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
        AcircS ρ₁ ρ₂ *
          Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))

/-- The nondegeneracy/positivity part of the canonical scalar-control factors.

This is deliberately separated from the actual projected-Poincare/circ content:
the latter is the real Besov/Poincare input for Phase 2. -/
def CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (Acirc1 AcircS : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    0 < cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ∧
    0 < Acirc1 ρ₁ ρ₂ ∧
    0 ≤ AcircS ρ₁ ρ₂ ∧
    0 <
      Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))

/-- The actual projected-Poincare and `circ` estimates needed for Phase 2. -/
def CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ) (Acirc1 AcircS : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    (∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
        (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x)) (g ρ₁ ρ₂) N) ∧
    (∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
        Acirc1 ρ₁ ρ₂ *
          Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))) ∧
    (∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
        AcircS ρ₁ ρ₂ *
          Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))

theorem CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.cubeLpNorm_pos
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    {Acirc1 AcircS : ℝ → ℝ → ℝ}
    (hpos : CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    0 < cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) :=
  (hpos hρ₁ hlt hρ₂).1

theorem CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.acirc1_pos
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    {Acirc1 AcircS : ℝ → ℝ → ℝ}
    (hpos : CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    0 < Acirc1 ρ₁ ρ₂ :=
  (hpos hρ₁ hlt hρ₂).2.1

theorem CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.acirc1_nonneg
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    {Acirc1 AcircS : ℝ → ℝ → ℝ}
    (hpos : CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    0 ≤ Acirc1 ρ₁ ρ₂ :=
  (hpos.acirc1_pos hρ₁ hlt hρ₂).le

theorem CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.acircS_nonneg
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    {Acirc1 AcircS : ℝ → ℝ → ℝ}
    (hpos : CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    0 ≤ AcircS ρ₁ ρ₂ :=
  (hpos hρ₁ hlt hρ₂).2.2.1

theorem CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.energySqrt_pos
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    {Acirc1 AcircS : ℝ → ℝ → ℝ}
    (hpos : CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    0 < Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)) :=
  (hpos hρ₁ hlt hρ₂).2.2.2

theorem CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.projectedPoincare
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {s C : ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    {g : ℝ → ℝ → Vec d → ℝ} {Acirc1 AcircS : ℝ → ℝ → ℝ}
    (hctrl :
      CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds Q a s C w g Acirc1 AcircS)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1)
    (N : ℕ) :
    CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
      (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x)) (g ρ₁ ρ₂) N :=
  (hctrl hρ₁ hlt hρ₂).1 N

theorem CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.circPartialNorm_one_le
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {s C : ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    {g : ℝ → ℝ → Vec d → ℝ} {Acirc1 AcircS : ℝ → ℝ → ℝ}
    (hctrl :
      CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds Q a s C w g Acirc1 AcircS)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1)
    (N : ℕ) :
    cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
      Acirc1 ρ₁ ρ₂ *
        Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)) :=
  (hctrl hρ₁ hlt hρ₂).2.1 N

theorem CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.circPartialNorm_one_sub_le
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {s C : ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    {g : ℝ → ℝ → Vec d → ℝ} {Acirc1 AcircS : ℝ → ℝ → ℝ}
    (hctrl :
      CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds Q a s C w g Acirc1 AcircS)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1)
    (N : ℕ) :
    cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
      AcircS ρ₁ ρ₂ *
        Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)) :=
  (hctrl hρ₁ hlt hρ₂).2.2 N

/-- Build the projected-Poincare/`circ` package when the scalar auxiliary
field is one component of a vector field whose negative Besov partial seminorms
already dominate the desired `circ` factors.  This is the local scalarization
bridge used before the final concrete choice of `g` is fixed. -/
theorem CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_component_negativeVectorBounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (G : ℝ → ℝ → Vec d → Vec d) (i : Fin d)
    (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => G ρ₁ ρ₂ x i) N)
    (hneg1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        cubeBesovScaleWeight (-1) Q *
            cubeBesovNegativeVectorPartialSeminorm Q 1 N (G ρ₁ ρ₂) ≤
          Acirc1 ρ₁ ρ₂ *
            Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
    (hnegS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        cubeBesovScaleWeight (-(1 - s)) Q *
            cubeBesovNegativeVectorPartialSeminorm Q (1 - s) N (G ρ₁ ρ₂) ≤
          AcircS ρ₁ ρ₂ *
            Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))) :
    CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds
      Q a s C w (fun ρ₁ ρ₂ x => G ρ₁ ρ₂ x i) Acirc1 AcircS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  refine ⟨?_, ?_, ?_⟩
  · intro N
    exact hproj hρ₁ hlt hρ₂ N
  · intro N
    calc
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => G ρ₁ ρ₂ x i)
          ≤ cubeBesovScaleWeight (-1) Q *
              cubeBesovNegativeVectorPartialSeminorm Q 1 N (G ρ₁ ρ₂) := by
            exact
              cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
                Q 1 (G ρ₁ ρ₂) i N
      _ ≤
          Acirc1 ρ₁ ρ₂ *
            Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)) :=
            hneg1 hρ₁ hlt hρ₂ N
  · intro N
    calc
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => G ρ₁ ρ₂ x i)
          ≤ cubeBesovScaleWeight (-(1 - s)) Q *
              cubeBesovNegativeVectorPartialSeminorm Q (1 - s) N (G ρ₁ ρ₂) := by
            exact
              cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
                Q (1 - s) (G ρ₁ ρ₂) i N
      _ ≤
          AcircS ρ₁ ρ₂ *
            Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)) :=
            hnegS hρ₁ hlt hρ₂ N

/-- Build the projected-Poincare/`circ` package for a component of a vector
field whose descendant gradient-energy controls supply the note's `lambdaSq`
factors.  This is the concrete gradient-side scalarization bridge; the
projected mean-zero Poincare family remains as the analytic input. -/
theorem CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_component_gradientEnergyControl
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (G : ℝ → ℝ → Vec d → Vec d) (i : Fin d)
    (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hs1 : s < 1)
    (henergy_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ cubeSet Q, 0 ≤ scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergy_int :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.IntegrableOn
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (cubeSet Q) MeasureTheory.volume)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (G ρ₁ ρ₂)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => G ρ₁ ρ₂ x i) N)
    (hAcirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          Acirc1 ρ₁ ρ₂)
    (hAcircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-(1 - s)) Q *
            ((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          AcircS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds
      Q a s C w (fun ρ₁ ρ₂ x => G ρ₁ ρ₂ x i) Acirc1 AcircS := by
  refine
    CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_component_negativeVectorBounds
      Q a s C w G i Acirc1 AcircS hproj ?_ ?_
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂ N
    let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x
    have hpartial :
        cubeBesovNegativeVectorPartialSeminorm Q (1 : ℝ) N (G ρ₁ ρ₂) ≤
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
            Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ) *
            Real.sqrt (cubeAverage Q energy) := by
      exact
        coarseCaccioppoli_gradient_qone_partialBound_of_cubeAverageEnergyControl
          Q a (1 : ℝ) (by norm_num) (G ρ₁ ρ₂) energy N
          (henergy_nonneg hρ₁ hlt hρ₂) (henergy_int hρ₁ hlt hρ₂)
          (hgrad hρ₁ hlt hρ₂) hsum1
    have hE_nonneg : 0 ≤ Real.sqrt (cubeAverage Q energy) :=
      Real.sqrt_nonneg _
    calc
      cubeBesovScaleWeight (-1) Q *
          cubeBesovNegativeVectorPartialSeminorm Q 1 N (G ρ₁ ρ₂)
          ≤
        cubeBesovScaleWeight (-1) Q *
          (((geometricDiscount (1 : ℝ) 1)⁻¹ *
            Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) *
            Real.sqrt (cubeAverage Q energy)) := by
            exact mul_le_mul_of_nonneg_left hpartial (cubeBesovScaleWeight_nonneg (-1) Q)
      _ =
        (cubeBesovScaleWeight (-1) Q *
          ((geometricDiscount (1 : ℝ) 1)⁻¹ *
            Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ))) *
            Real.sqrt (cubeAverage Q energy) := by
            ring
      _ ≤
          Acirc1 ρ₁ ρ₂ * Real.sqrt (cubeAverage Q energy) := by
            exact mul_le_mul_of_nonneg_right (hAcirc1 hρ₁ hlt hρ₂) hE_nonneg
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂ N
    let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x
    have hs_pos : 0 < 1 - s := by linarith
    have hpartial :
        cubeBesovNegativeVectorPartialSeminorm Q (1 - s) N (G ρ₁ ρ₂) ≤
          (geometricDiscount (1 - s) 1)⁻¹ *
            Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ) *
            Real.sqrt (cubeAverage Q energy) := by
      exact
        coarseCaccioppoli_gradient_qone_partialBound_of_cubeAverageEnergyControl
          Q a (1 - s) hs_pos (G ρ₁ ρ₂) energy N
          (henergy_nonneg hρ₁ hlt hρ₂) (henergy_int hρ₁ hlt hρ₂)
          (hgrad hρ₁ hlt hρ₂) hsumS
    have hE_nonneg : 0 ≤ Real.sqrt (cubeAverage Q energy) :=
      Real.sqrt_nonneg _
    calc
      cubeBesovScaleWeight (-(1 - s)) Q *
          cubeBesovNegativeVectorPartialSeminorm Q (1 - s) N (G ρ₁ ρ₂)
          ≤
        cubeBesovScaleWeight (-(1 - s)) Q *
          (((geometricDiscount (1 - s) 1)⁻¹ *
            Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) *
            Real.sqrt (cubeAverage Q energy)) := by
            exact mul_le_mul_of_nonneg_left hpartial
              (cubeBesovScaleWeight_nonneg (-(1 - s)) Q)
      _ =
        (cubeBesovScaleWeight (-(1 - s)) Q *
          ((geometricDiscount (1 - s) 1)⁻¹ *
            Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ))) *
            Real.sqrt (cubeAverage Q energy) := by
            ring
      _ ≤
          AcircS ρ₁ ρ₂ * Real.sqrt (cubeAverage Q energy) := by
            exact mul_le_mul_of_nonneg_right (hAcircS hρ₁ hlt hρ₂) hE_nonneg

/-- Concrete harmonic-gradient version of
`CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_component_gradientEnergyControl`.

Once the projected mean-zero Poincare family is available for the component
`∂ᵢ w`, the gradient-energy bridge supplies both scalar `circ` estimates for
that same component. -/
theorem CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hs1 : s < 1)
    (henergy_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ cubeSet Q, 0 ≤ scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergy_int :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.IntegrableOn
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (cubeSet Q) MeasureTheory.volume)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hAcirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          Acirc1 ρ₁ ρ₂)
    (hAcircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-(1 - s)) Q *
            ((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          AcircS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i) Acirc1 AcircS := by
  exact
    CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_component_gradientEnergyControl
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x) i Acirc1 AcircS
      hs1 henergy_nonneg henergy_int hgrad hsum1 hsumS hproj hAcirc1 hAcircS

theorem CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_projectedPoincareCircBounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ) (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hpos : CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    (hctrl :
      CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds Q a s C w g Acirc1 AcircS) :
    CoarseCaccioppoliBoundaryCanonicalScalarControlFactors Q a s C w g Acirc1 AcircS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hpos hρ₁ hlt hρ₂ with ⟨hu_pos, hAcirc1_pos, hAcircS_nonneg, hE_pos⟩
  rcases hctrl hρ₁ hlt hρ₂ with ⟨hproj, hgCirc1, hgCircS⟩
  exact ⟨hu_pos, hAcirc1_pos, hAcircS_nonneg, hE_pos, hproj, hgCirc1, hgCircS⟩

/-- Full scalar-control factors for the concrete scalar field `partial_i w`.

This is the Phase 2 bridge used by the final Caccioppoli wrappers once the
projected mean-zero Poincare estimate for `partial_i w` has been supplied. -/
theorem CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_harmonicGradientComponent
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hpos : CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    (hs1 : s < 1)
    (henergy_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ cubeSet Q, 0 ≤ scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergy_int :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.IntegrableOn
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (cubeSet Q) MeasureTheory.volume)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hAcirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          Acirc1 ρ₁ ρ₂)
    (hAcircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-(1 - s)) Q *
            ((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          AcircS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryCanonicalScalarControlFactors
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i) Acirc1 AcircS := by
  exact
    CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_projectedPoincareCircBounds
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i) Acirc1 AcircS hpos
      (CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent
        Q a s C w i Acirc1 AcircS hs1 henergy_nonneg henergy_int hgrad hsum1 hsumS
        hproj hAcirc1 hAcircS)

theorem CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.to_scalarCutoffControls
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s C ρ₁ ρ₂ : ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ) (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hfactors : CoarseCaccioppoliBoundaryCanonicalScalarControlFactors Q a s C w g Acirc1 AcircS)
    (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 < C)
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    CoarseCaccioppoliScalarCutoffControls Q s
      (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
      (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C := by
  rcases hfactors hρ₁ hlt hρ₂ with
    ⟨hu_pos, hAcirc1_pos, hAcircS_nonneg, hE_pos, hproj, hgCirc1, hgCircS⟩
  exact
    CoarseCaccioppoliScalarCutoffControls.of_canonicalQuantitativeCutoff_of_positiveFactors
      (Q := Q) (s := s) (C := C) hρ₁ hlt
      (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
      (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
      hs0 hs1 hu_pos hAcirc1_pos hAcircS_nonneg hE_pos hC hproj hgCirc1 hgCircS

theorem CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.acirc1_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {s C ρ₁ ρ₂ : ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ) (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hfactors : CoarseCaccioppoliBoundaryCanonicalScalarControlFactors Q a s C w g Acirc1 AcircS)
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    0 ≤ Acirc1 ρ₁ ρ₂ := by
  exact (hfactors hρ₁ hlt hρ₂).2.1.le

theorem CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.acircS_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {s C ρ₁ ρ₂ : ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ) (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hfactors : CoarseCaccioppoliBoundaryCanonicalScalarControlFactors Q a s C w g Acirc1 AcircS)
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    0 ≤ AcircS ρ₁ ρ₂ := by
  exact (hfactors hρ₁ hlt hρ₂).2.2.1

/-- Boundary canonical harmonic Caccioppoli from primitive scalar-control
factors, without exposing the raw scalar-control bundle or exact cutoff-size
positivity hypotheses. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarControlFactors_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hscalarFactors :
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors Q a s C w g Acirc1 AcircS)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
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
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.to_scalarCutoffControls
        Q a w g Acirc1 AcircS hscalarFactors hs hs1 hC hρ₁ hlt hρ₂
  have hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂ := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.acirc1_nonneg
        Q a w g Acirc1 AcircS hscalarFactors hρ₁ hlt hρ₂
  have hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂ := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.acircS_nonneg
        Q a w g Acirc1 AcircS hscalarFactors hρ₁ hlt hρ₂
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (w := w) (g := g)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC.le hs ht hst hu hnonneg hbounded hscale hlower henergyAvg
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicFlux_normalizedCubeMeasure Q a (w ρ₁ ρ₂) hEll)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicFunction_normalizedCubeMeasure Q a (w ρ₁ ρ₂))
      hgMem hfluxEnergy hscalar hAcirc1_nonneg hAcircS_nonneg hU hA1 hAS hcoeff
      hEll hData
      (summable_bBlock_geometricWeight_s_of_fluxEnergyControls_family Q a s hfluxEnergy)
      hSigmaSum_t

/-- Interior canonical harmonic Caccioppoli from primitive scalar-control
factors, without exposing the raw scalar-control bundle or exact cutoff-size
positivity hypotheses. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarControlFactors_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          G₀ ρ₂)
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hscalarFactors :
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors Q a s C w g Acirc1 AcircS)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
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
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.to_scalarCutoffControls
        Q a w g Acirc1 AcircS hscalarFactors hs hs1 hC hρ₁ hlt hρ₂
  have hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂ := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.acirc1_nonneg
        Q a w g Acirc1 AcircS hscalarFactors hρ₁ hlt hρ₂
  have hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂ := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.acircS_nonneg
        Q a w g Acirc1 AcircS hscalarFactors hρ₁ hlt hρ₂
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (G₀ := G₀) (w := w) (g := g)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC.le hs ht hst hu hagree hG_nonneg hG_bounded hscale hlower henergyAvg
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicFlux_normalizedCubeMeasure Q a (w ρ₁ ρ₂) hEll)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicFunction_normalizedCubeMeasure Q a (w ρ₁ ρ₂))
      hgMem hfluxEnergy hscalar hAcirc1_nonneg hAcircS_nonneg
      hU hA1 hAS hcoeff hEll hData
      (summable_bBlock_geometricWeight_s_of_fluxEnergyControls_family Q a s hfluxEnergy)
      hSigmaSum_t

/-- Boundary canonical harmonic Caccioppoli from the split Phase 2 scalar
inputs: nondegenerate positive factors plus the genuine projected-Poincare
and `circ` bounds. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_projectedPoincareCircBounds_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    (hprojectedCirc :
      CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds
        Q a s C w g Acirc1 AcircS)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
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
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarControlFactors_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (w := w) (g := g)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hnonneg hbounded hscale hlower henergyAvg hgMem hfluxEnergy
      (CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_projectedPoincareCircBounds
        Q a s C w g Acirc1 AcircS hpositiveFactors hprojectedCirc)
      hU hA1 hAS hcoeff hEll hData hSigmaSum_t

/-- Interior canonical harmonic Caccioppoli from the split Phase 2 scalar
inputs: nondegenerate positive factors plus the genuine projected-Poincare
and `circ` bounds. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_projectedPoincareCircBounds_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          G₀ ρ₂)
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    (hprojectedCirc :
      CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds
        Q a s C w g Acirc1 AcircS)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
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
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarControlFactors_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (G₀ := G₀) (w := w) (g := g)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hlower henergyAvg
      hgMem hfluxEnergy
      (CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_projectedPoincareCircBounds
        Q a s C w g Acirc1 AcircS hpositiveFactors hprojectedCirc)
      hU hA1 hAS hcoeff hEll hData hSigmaSum_t

end

end Homogenization
