/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectionLimit
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Cube
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.FiniteMeasureDowngrade

/-! # Harmonic Gradient Iteration Geometry -/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# Central descendants for the harmonic gradient iteration

This file fixes the ordinary, geometrically central triadic descendants used
to iterate the local harmonic gradient gain.  They are deliberately distinct
from `ScalarOverlap.middleChildCube`: the latter is an overlap-indexing cube
whose carrier remains at the parent scale, whereas the cubes here are genuine
members of `childCubes` and hence contract by a factor of three at every step.
-/

namespace CubeCalderonZygmund

/-- The ordinary central triadic child of `Q`.  Its all-one digit vector makes
it a genuine member of `childCubes Q`, unlike the overlap-centre construction. -/
def centralChild {d : ℕ} (Q : TriadicCube d) : TriadicCube d :=
  { scale := Q.scale - 1
    index := fun i => 3 * Q.index i }

/-- The repeatedly central depth-`n` descendant used by the CZ iteration. -/
def centralDescendant {d : ℕ} (Q : TriadicCube d) : ℕ → TriadicCube d
  | 0 => Q
  | n + 1 => centralChild (centralDescendant Q n)

@[simp] theorem centralDescendant_zero {d : ℕ} (Q : TriadicCube d) :
    centralDescendant Q 0 = Q :=
  rfl

@[simp] theorem centralDescendant_succ {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    centralDescendant Q (n + 1) = centralChild (centralDescendant Q n) :=
  rfl

@[simp] theorem centralChild_scale {d : ℕ} (Q : TriadicCube d) :
    (centralChild Q).scale = Q.scale - 1 :=
  rfl

theorem centralChild_mem_childCubes {d : ℕ} (Q : TriadicCube d) :
    centralChild Q ∈ childCubes Q := by
  simpa [centralChild] using middleChild_mem_childCubes Q

theorem centralDescendant_mem_descendantsAtDepth {d : ℕ} (Q : TriadicCube d) :
    ∀ n : ℕ, centralDescendant Q n ∈ descendantsAtDepth Q n
  | 0 => by simp [centralDescendant]
  | n + 1 => by
      rw [mem_descendantsAtDepth_succ_iff]
      exact ⟨centralDescendant Q n, centralDescendant_mem_descendantsAtDepth Q n,
        by simpa using centralChild_mem_childCubes (centralDescendant Q n)⟩

theorem centralDescendant_scale {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    (centralDescendant Q n).scale = Q.scale - n :=
  scale_eq_sub_of_mem_descendantsAtDepth (centralDescendant_mem_descendantsAtDepth Q n)

/-- The index of a central descendant is obtained by multiplying the parent
index by the corresponding triadic power. -/
theorem centralDescendant_index {d : ℕ} (Q : TriadicCube d) :
    ∀ (n : ℕ) (i : Fin d), (centralDescendant Q n).index i = (3 : ℤ) ^ n * Q.index i
  | 0, i => by simp [centralDescendant]
  | n + 1, i => by
      rw [centralDescendant_succ]
      change 3 * (centralDescendant Q n).index i = (3 : ℤ) ^ (n + 1) * Q.index i
      rw [centralDescendant_index Q n i, pow_succ]
      ring

/-- Central descendants of the unit centered cube are precisely the centered
triadic cubes at the corresponding negative depth. -/
theorem centralDescendant_originCube_zero_eq_originCube_neg_nat {d : ℕ} (n : ℕ) :
    centralDescendant (originCube d 0) n = originCube d (-(n : ℤ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [centralDescendant_succ, ih]
      dsimp [centralChild, originCube]
      congr
      omega

theorem centralDescendant_cubeScaleFactor {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    cubeScaleFactor (centralDescendant Q n) = cubeScaleFactor Q / (3 : ℝ) ^ n :=
  cubeScaleFactor_descendant_eq_div_pow (centralDescendant_mem_descendantsAtDepth Q n)

theorem centralDescendant_cubeVolume_eq {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    cubeVolume Q = ((3 ^ d) ^ n : ℕ) * cubeVolume (centralDescendant Q n) := by
  rw [← descendantsAtDepth_card Q n]
  exact cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth
    (centralDescendant_mem_descendantsAtDepth Q n)

theorem centralDescendant_cubeVolume_ratio {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    cubeVolume Q / cubeVolume (centralDescendant Q n) = ((3 ^ d) ^ n : ℕ) := by
  rw [centralDescendant_cubeVolume_eq]
  field_simp [(cubeVolume_pos (centralDescendant Q n)).ne']

theorem centralDescendant_cubeSet_subset {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    cubeSet (centralDescendant Q n) ⊆ cubeSet Q :=
  cubeSet_subset_of_mem_descendantsAtDepth (centralDescendant_mem_descendantsAtDepth Q n)

theorem centralDescendant_openCubeSet_subset {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    openCubeSet (centralDescendant Q n) ⊆ openCubeSet Q :=
  openCubeSet_subset_of_mem_descendantsAtDepth (centralDescendant_mem_descendantsAtDepth Q n)

/-- One central child lies strictly inside the half-sized open cube of its
parent.  This is the geometric margin consumed at every harmonic-gain step. -/
theorem centralChild_cubeSet_subset_scaledOpenInnerHalf {d : ℕ} (Q : TriadicCube d) :
    cubeSet (centralChild Q) ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) := by
  intro x hx i
  have hscale : cubeScaleFactor (centralChild Q) = cubeScaleFactor Q / 3 := by
    simpa [centralChild] using cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  have hpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hx' := hx i
  rw [hscale] at hx'
  norm_num [centralChild, Int.cast_mul] at hx'
  change |x i - cubeCenter Q i| < (1 / 2 : ℝ) * cubeRadius Q
  rw [cubeCenter, cubeRadius, abs_lt]
  constructor <;> nlinarith

/-- The central step at depth `n` lies in the strict inner half of its depth
`n` predecessor, so the harmonic regularity engine can be iterated. -/
theorem centralDescendant_succ_cubeSet_subset_scaledOpenInnerHalf {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) :
    cubeSet (centralDescendant Q (n + 1)) ⊆
      scaledOpenCubeSet (centralDescendant Q n) (1 / 2 : ℝ) := by
  simpa only [centralDescendant_succ] using
    centralChild_cubeSet_subset_scaledOpenInnerHalf (centralDescendant Q n)

/-- Exact normalized-measure restriction formula for the central descendant.
The factor is the number of ordinary depth-`n` descendants. -/
theorem normalizedCubeMeasure_centralDescendant_eq_smul_restrict {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) :
    normalizedCubeMeasure (centralDescendant Q n) =
      ENNReal.ofReal (((3 ^ d) ^ n : ℕ) : ℝ) •
        (normalizedCubeMeasure Q).restrict (cubeSet (centralDescendant Q n)) := by
  rw [normalizedCubeMeasure_descendant_eq_smul_restrict
    (centralDescendant_mem_descendantsAtDepth Q n), centralDescendant_cubeVolume_ratio]

/-- The corresponding exact `Lᵖ` restriction formula. -/
theorem eLpNorm_centralDescendant_eq_rpow_smul_restrict {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) (p : FiniteLpExponent) (f : Vec d → ℝ) :
    MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure (centralDescendant Q n)) =
      ENNReal.ofReal (((3 ^ d) ^ n : ℕ) : ℝ) ^ (1 / p.exponent).toReal *
        MeasureTheory.eLpNorm f p.exponent
          ((normalizedCubeMeasure Q).restrict (cubeSet (centralDescendant Q n))) := by
  rw [normalizedCubeMeasure_centralDescendant_eq_smul_restrict]
  have hfactor : ENNReal.ofReal (((3 ^ d) ^ n : ℕ) : ℝ) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.2 (by positivity)
  simpa [smul_eq_mul] using MeasureTheory.eLpNorm_smul_measure_of_ne_zero hfactor f p.exponent
    ((normalizedCubeMeasure Q).restrict (cubeSet (centralDescendant Q n)))

/-- Restricting from a normalized cube to a central depth-`n` descendant has
at most the descendant-count loss.  The exact `p`-dependent root factor is
available in `eLpNorm_centralDescendant_eq_rpow_smul_restrict`; this coarser
form is convenient for the iteration bookkeeping. -/
theorem eLpNorm_centralDescendant_le_descendantCount_mul {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) (p : FiniteLpExponent) (f : Vec d → ℝ) :
    MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure (centralDescendant Q n)) ≤
      ENNReal.ofReal (((3 ^ d) ^ n : ℕ) : ℝ) *
        MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure Q) := by
  let N : ℝ≥0∞ := ENNReal.ofReal (((3 ^ d) ^ n : ℕ) : ℝ)
  have hN : 1 ≤ N := by
    dsimp [N]
    have hthree : (3 : ℕ) ≠ 0 := by norm_num
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (pow_ne_zero d hthree))
  have hp : 1 / p.exponent.toReal ≤ (1 : ℝ) := by
    have hp_one : 1 ≤ p.exponent.toReal :=
      ENNReal.toReal_mono p.lt_top.ne p.one_lt.le
    simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp_one)
  rw [eLpNorm_centralDescendant_eq_rpow_smul_restrict]
  change N ^ (1 / p.exponent).toReal * _ ≤ N * _
  calc
    N ^ (1 / p.exponent).toReal *
        MeasureTheory.eLpNorm f p.exponent
          ((normalizedCubeMeasure Q).restrict (cubeSet (centralDescendant Q n))) ≤
        N * MeasureTheory.eLpNorm f p.exponent
          ((normalizedCubeMeasure Q).restrict (cubeSet (centralDescendant Q n))) := by
      gcongr
      simpa [ENNReal.toReal_inv] using ENNReal.rpow_le_rpow_of_exponent_le hN hp
    _ ≤ N * MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure Q) := by
      exact mul_le_mul_right (MeasureTheory.eLpNorm_mono_measure f
        MeasureTheory.Measure.restrict_le_self) N

/-- Finite `Lᵖ` data on a cube restricts to every central descendant. -/
theorem memLp_centralDescendant_of_memLp {d : ℕ} {Q : TriadicCube d} {p : ℝ≥0∞}
    {f : Vec d → ℝ} (n : ℕ) (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (normalizedCubeMeasure (centralDescendant Q n)) :=
  memLp_on_descendant_of_memLp (centralDescendant_mem_descendantsAtDepth Q n) hf

/-- On the probability-normalized central descendant, every finite exponent
below `2` is bounded by the `L²` norm without a volume loss. -/
theorem eLpNorm_centralDescendant_downgrade_le {d : ℕ} (Q : TriadicCube d) (n : ℕ)
    (p : FiniteLpExponent) (hp : p.exponent ≤ 2) (f : Vec d → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable f
      (normalizedCubeMeasure (centralDescendant Q n))) :
    MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure (centralDescendant Q n)) ≤
      MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure (centralDescendant Q n)) :=
  eLpNorm_normalizedCubeMeasure_downgrade_le (centralDescendant Q n) p hp f hf

end CubeCalderonZygmund

end

end Homogenization
