/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Localization
public import LeanPool.CoarseGraining.Homogenization.Besov.Negative
public import LeanPool.CoarseGraining.Homogenization.Besov.Positive
public import Mathlib.Data.Real.ConjExponents

/-! # Definitions -/

@[expose] public section

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

/-!
Finite disjoint duality scaffolding for cube Besov norms.

This checkpoint freezes the normalized cube pairing together with the
test-function conventions that define the two dual negative-order Besov
seminorms used later:

- the full dual seminorm, tested against positive Besov norms;
- the mean-zero-tested dual seminorm, matching the hat-seminorm in the notes.

At this stage we package the disjoint finite-depth definitions and the cheap
zero-function API. Overlap finite dual tests live in
`Homogenization.Besov.Duality.OverlapDefinitions`.
-/

noncomputable def cubeBesovPairing {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ) : ℝ :=
  cubeAverage Q (fun x => f x * g x)

noncomputable def cubeBesovConjExponent (p : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.conjExponent p

theorem cubeBesovConjExponent_ne_zero (p : ℝ≥0∞) :
    cubeBesovConjExponent p ≠ 0 := by
  simp [cubeBesovConjExponent, ENNReal.conjExponent]

noncomputable def cubeBesovDualTestNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : ℝ :=
  if cubeBesovConjExponent q = ∞ then
    cubeBesovPartialNormTop Q s (cubeBesovConjExponent p) N g
  else
    cubeBesovPartialNorm Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) N g

noncomputable def cubeBesovDualTestSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : ℝ :=
  if cubeBesovConjExponent q = ∞ then
    cubeBesovPartialSeminormTop Q s (cubeBesovConjExponent p) N g
  else
    cubeBesovPartialSeminorm Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) N g

@[simp] theorem cubeBesovDualTestNorm_of_conjExponent_eq_top {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (hq : cubeBesovConjExponent q = ∞) :
    cubeBesovDualTestNorm Q s p q N g =
      cubeBesovPartialNormTop Q s (cubeBesovConjExponent p) N g := by
  simp [cubeBesovDualTestNorm, hq]

@[simp] theorem cubeBesovDualTestNorm_of_conjExponent_ne_top {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (hq : cubeBesovConjExponent q ≠ ∞) :
    cubeBesovDualTestNorm Q s p q N g =
      cubeBesovPartialNorm Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) N g := by
  simp [cubeBesovDualTestNorm, hq]

@[simp] theorem cubeBesovDualTestSeminorm_of_conjExponent_eq_top {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (hq : cubeBesovConjExponent q = ∞) :
    cubeBesovDualTestSeminorm Q s p q N g =
      cubeBesovPartialSeminormTop Q s (cubeBesovConjExponent p) N g := by
  simp [cubeBesovDualTestSeminorm, hq]

@[simp] theorem cubeBesovDualTestSeminorm_of_conjExponent_ne_top {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (hq : cubeBesovConjExponent q ≠ ∞) :
    cubeBesovDualTestSeminorm Q s p q N g =
      cubeBesovPartialSeminorm Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) N g := by
  simp [cubeBesovDualTestSeminorm, hq]

theorem cubeBesovDualTestNorm_eq_cubeBesovDualTestSeminorm_of_cubeAverage_eq_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (havg : cubeAverage Q g = 0) :
    cubeBesovDualTestNorm Q s p q N g = cubeBesovDualTestSeminorm Q s p q N g := by
  by_cases hq : cubeBesovConjExponent q = ∞
  · rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s p q N g hq,
      cubeBesovDualTestSeminorm_of_conjExponent_eq_top Q s p q N g hq]
    unfold cubeBesovPartialNormTop
    rw [havg]
    simp
  · rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N g hq,
      cubeBesovDualTestSeminorm_of_conjExponent_ne_top Q s p q N g hq]
    unfold cubeBesovPartialNorm
    rw [havg]
    simp

def CubeBesovDualLocalMemLp {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : Prop :=
  ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
    MeasureTheory.MemLp (cubeFluctuation R g)
      (cubeBesovConjExponent p) (normalizedCubeMeasure R)

def CubeBesovDualTest {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : Prop :=
  cubeBesovDualTestNorm Q s p q N g ≤ 1 ∧
    CubeBesovDualLocalMemLp Q p N g

def CubeBesovDualMeanZeroTest {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : Prop :=
  cubeBesovDualTestSeminorm Q s p q N g ≤ 1 ∧
    cubeAverage Q g = 0 ∧
      CubeBesovDualLocalMemLp Q p N g

theorem CubeBesovDualTest.norm_le_one {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovDualTest Q s p q N g) :
    cubeBesovDualTestNorm Q s p q N g ≤ 1 :=
  hg.1

theorem CubeBesovDualTest.local_memLp {d : ℕ} {Q : TriadicCube d}
    {p : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovDualLocalMemLp Q p N g) :
    ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R) :=
  hg

theorem CubeBesovDualTest.memLp_admissible {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovDualTest Q s p q N g) :
    ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R) :=
  hg.2

theorem CubeBesovDualMeanZeroTest.seminorm_le_one {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovDualMeanZeroTest Q s p q N g) :
    cubeBesovDualTestSeminorm Q s p q N g ≤ 1 :=
  hg.1

theorem CubeBesovDualMeanZeroTest.cubeAverage_eq_zero {d : ℕ} {Q : TriadicCube d}
    {s : ℝ} {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovDualMeanZeroTest Q s p q N g) :
    cubeAverage Q g = 0 :=
  hg.2.1

theorem CubeBesovDualMeanZeroTest.memLp_admissible {d : ℕ} {Q : TriadicCube d}
    {s : ℝ} {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovDualMeanZeroTest Q s p q N g) :
    ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R) :=
  hg.2.2

theorem cubeBesovDualLocalMemLp_const {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (N : ℕ) (c : ℝ) :
    CubeBesovDualLocalMemLp Q p N (fun _ => c) := by
  intro j hj R hR
  rw [cubeFluctuation_const]
  exact
    (MeasureTheory.memLp_const (0 : ℝ) :
      MeasureTheory.MemLp (fun _ : Vec d => (0 : ℝ))
        (cubeBesovConjExponent p) (normalizedCubeMeasure R))

def cubeBesovDualPartialNormValueSet {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ) : Set ℝ :=
  {r | ∃ g : Vec d → ℝ, CubeBesovDualTest Q s p q N g ∧ r = |cubeBesovPairing Q f g|}

def cubeBesovDualPartialSeminormValueSet {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ) : Set ℝ :=
  {r | ∃ g : Vec d → ℝ, CubeBesovDualMeanZeroTest Q s p q N g ∧
      r = |cubeBesovPairing Q f g|}

noncomputable def cubeBesovDualPartialNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDualPartialNormValueSet Q s p q N f)

noncomputable def cubeBesovDualPartialSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDualPartialSeminormValueSet Q s p q N f)

theorem cubeBesovScaleWeight_mul_norm_cubeAverage_le_cubeBesovDualTestNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) :
    cubeBesovScaleWeight s Q * ‖cubeAverage Q g‖ ≤ cubeBesovDualTestNorm Q s p q N g := by
  by_cases hq : cubeBesovConjExponent q = ∞
  · rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s p q N g hq]
    unfold cubeBesovPartialNormTop
    exact le_add_of_nonneg_left
      (cubeBesovPartialSeminormTop_nonneg Q s (cubeBesovConjExponent p) N g)
  · rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N g hq]
    unfold cubeBesovPartialNorm
    exact le_add_of_nonneg_left
      (cubeBesovPartialSeminorm_nonneg Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) N g)

theorem CubeBesovDualMeanZeroTest.to_dual_test {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovDualMeanZeroTest Q s p q N g) :
    CubeBesovDualTest Q s p q N g := by
  rcases hg with ⟨hseminorm, havg, hmem⟩
  unfold CubeBesovDualTest
  rw [cubeBesovDualTestNorm_eq_cubeBesovDualTestSeminorm_of_cubeAverage_eq_zero
    Q s p q N g havg]
  exact ⟨hseminorm, hmem⟩

theorem CubeBesovDualTest.scaleWeight_mul_norm_cubeAverage_le_one {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovDualTest Q s p q N g) :
    cubeBesovScaleWeight s Q * ‖cubeAverage Q g‖ ≤ 1 := by
  exact le_trans
    (cubeBesovScaleWeight_mul_norm_cubeAverage_le_cubeBesovDualTestNorm Q s p q N g)
    hg.norm_le_one

theorem cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) :
    cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q = 1 := by
  have hpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  unfold cubeBesovScaleWeight
  rw [show -(-s) = s by ring, ← Real.rpow_add hpos]
  rw [show s + -s = 0 by ring, Real.rpow_zero]

theorem cubeBesovDualPartialSeminormValueSet_subset_cubeBesovDualPartialNormValueSet
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ) :
    cubeBesovDualPartialSeminormValueSet Q s p q N f ⊆
      cubeBesovDualPartialNormValueSet Q s p q N f := by
  intro r hr
  rcases hr with ⟨g, hg, rfl⟩
  exact ⟨g, hg.to_dual_test, rfl⟩

theorem cubeBesovDualPartialSeminorm_le_cubeBesovDualPartialNorm_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞)
    (hBdd : BddAbove (cubeBesovDualPartialNormValueSet Q s p q N f)) :
    cubeBesovDualPartialSeminorm Q s p q N f ≤ cubeBesovDualPartialNorm Q s p q N f := by
  unfold cubeBesovDualPartialSeminorm cubeBesovDualPartialNorm
  have hNonempty : (cubeBesovDualPartialSeminormValueSet Q s p q N f).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨fun _ => (0 : ℝ), ?_, ?_⟩
    refine ⟨?_, by simpa using cubeAverage_const Q (0 : ℝ), ?_⟩
    · unfold cubeBesovDualTestSeminorm
      by_cases hq : cubeBesovConjExponent q = ∞
      · rw [if_pos hq]
        rw [cubeBesovPartialSeminormTop_zero (Q := Q) (s := s) (p := cubeBesovConjExponent p)
          (N := N) hp0 hpTop]
        norm_num
      · have hq0 : cubeBesovConjExponent q ≠ 0 := cubeBesovConjExponent_ne_zero q
        rw [if_neg hq]
        rw [cubeBesovPartialSeminorm_zero (Q := Q) (s := s) (p := cubeBesovConjExponent p)
          (q := cubeBesovConjExponent q) (N := N) hp0 hpTop hq0 hq]
        norm_num
    · intro j hj R hR
      rw [cubeFluctuation_zero]
      exact
        (MeasureTheory.memLp_const (0 : ℝ) :
          MeasureTheory.MemLp (fun _ : Vec d => (0 : ℝ))
            (cubeBesovConjExponent p) (normalizedCubeMeasure R))
    · unfold cubeBesovPairing
      rw [show (fun x => f x * (0 : ℝ)) = fun _ => (0 : ℝ) by
        funext x
        simp]
      rw [cubeAverage_const]
      simp
  exact csSup_le_csSup hBdd
    hNonempty
    (cubeBesovDualPartialSeminormValueSet_subset_cubeBesovDualPartialNormValueSet
      (Q := Q) (s := s) (p := p) (q := q) (N := N) (f := f))

theorem abs_cubeBesovPairing_le_cubeBesovDualPartialNorm_of_dual_test {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (f g : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDualPartialNormValueSet Q s p q N f))
    (hg : CubeBesovDualTest Q s p q N g) :
    |cubeBesovPairing Q f g| ≤ cubeBesovDualPartialNorm Q s p q N f := by
  unfold cubeBesovDualPartialNorm
  exact le_csSup hBdd ⟨g, hg, rfl⟩

theorem abs_cubeBesovPairing_le_cubeBesovDualPartialSeminorm_of_dual_mean_zero_test {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (f g : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDualPartialSeminormValueSet Q s p q N f))
    (hg : CubeBesovDualMeanZeroTest Q s p q N g) :
    |cubeBesovPairing Q f g| ≤ cubeBesovDualPartialSeminorm Q s p q N f := by
  unfold cubeBesovDualPartialSeminorm
  exact le_csSup hBdd ⟨g, hg, rfl⟩

theorem abs_cubeBesovPairing_le_mul_cubeLpNorm_of_holderConjugate {d : ℕ}
    (Q : TriadicCube d) (p q : ℝ≥0∞) (f g : Vec d → ℝ)
    [ENNReal.HolderConjugate p q]
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g q (normalizedCubeMeasure Q)) :
    |cubeBesovPairing Q f g| ≤ cubeLpNorm Q p f * cubeLpNorm Q q g := by
  simpa [cubeBesovPairing] using
    abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate Q p q f g hf hg

theorem abs_cubeBesovPairing_le_mul_cubeLpNorm_conjExponent {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) :
    |cubeBesovPairing Q f g| ≤
      cubeLpNorm Q p f * cubeLpNorm Q (cubeBesovConjExponent p) g := by
  simpa [cubeBesovPairing, cubeBesovConjExponent] using
    abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent Q p f g hf hg hp


end Homogenization
