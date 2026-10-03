/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.DualityExponentLoss
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.GlobalComparison

/-! # Contracts -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Positive-test bridge contracts

The restored proof of the deterministic flux-defect duality lemma tests each
component of the solution-comparison field against a scalar unit full-dual
positive Besov test.  To feed that test into the discrete compatibility
Dirichlet theorem, we insert the scalar test into one vector coordinate and
need the resulting vector field to be admissible for the overlapping positive
norm used by the discrete compatibility statement
`DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform` (not the
source theorem pending the continuum `K`/`H^s` gate).

This file records that bridge with the true target norm.  The `MemLp` part is
formal and proved here; the remaining analytic comparison is the finite-overlap
positive-localization estimate.
-/

/-- Insert a scalar field into one vector coordinate. -/
def coordinateVectorField {d : ℕ} (i : Fin d) (g : Vec d → ℝ) :
    Vec d → Vec d :=
  fun x j => if j = i then g x else 0

@[simp] theorem coordinateVectorField_same {d : ℕ} (i : Fin d) (g : Vec d → ℝ)
    (x : Vec d) :
    coordinateVectorField i g x i = g x := by
  simp [coordinateVectorField]

@[simp] theorem coordinateVectorField_of_ne {d : ℕ} {i j : Fin d}
    (hji : j ≠ i) (g : Vec d → ℝ) (x : Vec d) :
    coordinateVectorField i g x j = 0 := by
  simp [coordinateVectorField, hji]

@[simp] theorem vecDot_coordinateVectorField {d : ℕ}
    (U : Vec d → Vec d) (i : Fin d) (g : Vec d → ℝ) (x : Vec d) :
    vecDot (U x) (coordinateVectorField i g x) = U x i * g x := by
  classical
  simp [vecDot, coordinateVectorField]

@[simp] theorem vecDot_coordinateVectorField_left {d : ℕ}
    (U : Vec d → Vec d) (i : Fin d) (g : Vec d → ℝ) (x : Vec d) :
    vecDot (coordinateVectorField i g x) (U x) = g x * U x i := by
  rw [vecDot_comm, vecDot_coordinateVectorField]
  ring

/-- A scalar component pairing is the vector pairing against the corresponding
coordinate-inserted vector field. -/
theorem cubeBesovPairing_component_eq_cubeAverage_vecDot_coordinateVectorField
    {d : ℕ} (Q : TriadicCube d) (U : Vec d → Vec d)
    (i : Fin d) (g : Vec d → ℝ) :
    cubeBesovPairing Q (fun x => U x i) g =
      cubeAverage Q (fun x => vecDot (U x) (coordinateVectorField i g x)) := by
  unfold cubeBesovPairing
  congr 1
  funext x
  rw [vecDot_coordinateVectorField]

/-- Unit full-dual tests at `p=q=2` are `L²`; inserting such a test into one
coordinate gives an `L²` vector field on the parent cube. -/
theorem coordinateVectorField_memLp_of_cubeBesovDualFullTest_two_two
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {i : Fin d} {g : Vec d → ℝ}
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    MeasureTheory.MemLp (coordinateVectorField i g) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hgL2 :
      MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [hconj] using hg.memLp
  refine MeasureTheory.MemLp.of_eval ?_
  intro j
  by_cases hji : j = i
  · subst j
    simpa [coordinateVectorField] using hgL2
  · have hfun : (fun x : Vec d => coordinateVectorField i g x j) =
        fun _ : Vec d => (0 : ℝ) := by
      funext x
      simp [coordinateVectorField, hji]
    rw [hfun]
    exact
      (MeasureTheory.memLp_const (0 : ℝ) :
        MeasureTheory.MemLp (fun _ : Vec d => (0 : ℝ)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q))

/--
The remaining local analytic estimate in budget form.

It pairs a flux-defect field `F` against any vector test field whose corrected
overlapping positive Besov norm is bounded by a caller-supplied budget `B`.
The explicit regularity hypothesis is part of the honest `sSup` interface:
without bounded positive partial sums, the full norm cannot be used to recover
finite-level test bounds.
The right side is the localized negative Besov flux-defect average times that
positive test budget, with the explicit `s⁻¹` loss from the LaTeX proof.
-/
def LocalizedFluxDefectPositivePairingEstimate
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) {s : ℝ} (j : ℕ)
      (F H : Vec d → Vec d) (B : ℝ),
      0 < s →
      s < 1 →
      MemVectorL2 (cubeSet Q) F →
      CubeVectorOverlappingBesovHRegularity Q s H →
      0 ≤ B →
      cubeBesovOverlappingPositiveVectorNormTwo Q s H ≤ B →
        |cubeAverage Q (fun x => vecDot (F x) (H x))| ≤
          C * s⁻¹ * localizedFluxDefectNegativeBesovAverageTwo Q s F j * B

theorem LocalizedFluxDefectPositivePairingEstimate.nonneg
    {d : ℕ} [NeZero d] {C : ℝ}
    (hpair : LocalizedFluxDefectPositivePairingEstimate d C) :
    0 ≤ C :=
  hpair.1

theorem LocalizedFluxDefectPositivePairingEstimate.bound
    {d : ℕ} [NeZero d] {C : ℝ}
    (hpair : LocalizedFluxDefectPositivePairingEstimate d C)
    (Q : TriadicCube d) {s : ℝ} (j : ℕ)
    (F H : Vec d → Vec d) (B : ℝ)
    (hs : 0 < s) (hs_lt_one : s < 1)
    (hF : MemVectorL2 (cubeSet Q) F)
    (hHreg : CubeVectorOverlappingBesovHRegularity Q s H) (hB : 0 ≤ B)
    (hH : cubeBesovOverlappingPositiveVectorNormTwo Q s H ≤ B) :
    |cubeAverage Q (fun x => vecDot (F x) (H x))| ≤
      C * s⁻¹ * localizedFluxDefectNegativeBesovAverageTwo Q s F j * B :=
  hpair.2 Q j F H B hs hs_lt_one hF hHreg hB hH

end

end Homogenization
