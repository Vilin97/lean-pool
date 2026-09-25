/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectionLimit
public import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactCirc
public import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactDual

/-!
# Finite projected-pairing bridges for the exact Chapter 1 kernels

These lemmas isolate the pieces of the exact kernels that agree literally with
the finite projected-pairing infrastructure: normalized cube averages,
ordinary descendant-block means, and parent-to-block integrability transport.
They deliberately do not identify the extended exact aggregations with the
legacy real-valued partial norms.
-/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

private theorem cubeScaleFactor_div_pow_eq_sourceZPow {d : ℕ} (Q : TriadicCube d)
    (j : ℕ) :
    cubeScaleFactor Q / (3 : ℝ) ^ j = (3 : ℝ) ^ (Q.scale - (j : ℤ)) := by
  unfold cubeScaleFactor
  rw [zpow_sub₀]
  · simp [div_eq_mul_inv]
  · norm_num

/-- The exact overlap scale weight is the extended embedding of the legacy
overlap weight at the same source depth. -/
theorem exactOverlapDepthWeight_eq_ofReal_legacy {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (j : ℕ) :
    exactOverlapDepthWeight Q s j =
      ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j) := by
  unfold exactOverlapDepthWeight cubeBesovOverlapDepthWeight cubeBesovDepthWeight
  rw [cubeScaleFactor_div_pow_eq_sourceZPow]
  rw [← Real.rpow_intCast (3 : ℝ) (Q.scale - (j : ℤ)),
    ← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : 0 < (3 : ℝ))]
  congr 1
  · norm_num
  · change -(((Q.scale - (j : ℤ) : ℤ) : ℝ)) * s =
      ((Q.scale - (j : ℤ) : ℤ) : ℝ) * -s
    ring

/-- The exact root weight is the extended embedding of the legacy root-scale
weight. -/
theorem exactOverlapRootWeight_eq_ofReal_legacy {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) :
    exactOverlapRootWeight Q s = ENNReal.ofReal (cubeBesovScaleWeight s Q) := by
  rw [← exactOverlapDepthWeight_zero Q s,
    exactOverlapDepthWeight_eq_ofReal_legacy]
  simp [cubeBesovOverlapDepthWeight, cubeBesovDepthWeight_depth_zero]

/-- The exact circ scale weight is the extended embedding of the legacy circ
weight at the same source depth. -/
theorem exactCircDepthWeight_eq_ofReal_legacy {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (j : ℕ) :
    exactCircDepthWeight Q s j =
      ENNReal.ofReal (cubeBesovCircDepthWeight Q s j) := by
  unfold exactCircDepthWeight cubeBesovCircDepthWeight
  rw [cubeScaleFactor_div_pow_eq_sourceZPow]
  rw [← Real.rpow_intCast (3 : ℝ) (Q.scale - (j : ℤ)),
    ← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : 0 < (3 : ℝ))]
  congr 1
  norm_num

/-- Parent `MemLp` data at an admissible finite source exponent gives the
certified ordinary descendant-block integrals needed by the exact circ kernel.
-/
theorem exactCircIntegrable_of_memLp {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (hp : 1 ≤ p) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q)) : ExactCircIntegrable Q f where
  block := fun _ _ hR =>
    (memLp_on_descendant_of_memLp hR hf).integrable
      (ENNReal.one_le_ofReal.mpr hp)

/-- Parent `MemLp` data supplies the local fluctuation premise used by the
finite projected-pairing bound on every ordinary descendant block. -/
theorem cubeFluctuation_memLp_of_parent_memLp {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q))
    (j : ℕ) (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
    MeasureTheory.MemLp (cubeFluctuation R f) (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure R) := by
  exact (memLp_on_descendant_of_memLp hR hf).sub
    (MeasureTheory.memLp_const (cubeAverage R f))

/-- Every finite projection has the local `MemLp` premise required by the
projected-pairing bound after restricting it to an ordinary descendant block. -/
theorem cubeProjection_memLp_of_parent_descendant {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (f : Vec d → ℝ) (k j : ℕ) (R : TriadicCube d)
    (hR : R ∈ descendantsAtDepth Q j) :
    MeasureTheory.MemLp (cubeProjection Q k f) (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure R) := by
  exact memLp_on_descendant_of_memLp hR (cubeProjection_memLp Q k (ENNReal.ofReal p) f)

/-- The exact proof-carrying pairing is the absolute value of the legacy cube
pairing, embedded in `ENNReal`; its supplied product-integrability proof rules
out any undefined-integral interpretation. -/
theorem exactDualNormalizedPairing_eq_of_cubeBesovPairing {d : ℕ}
    (Q : TriadicCube d) (f g : Vec d → ℝ)
    (hfg : MeasureTheory.Integrable (fun x => f x * g x)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualNormalizedPairing Q f g hfg = ENNReal.ofReal |cubeBesovPairing Q f g| := by
  rw [exactDualNormalizedPairing_eq]
  congr 1
  unfold cubeBesovPairing
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]

/-- A certified exact circ block mean is the ordinary normalized cube average
used by the finite projected-pairing development. -/
theorem exactCircBlockMean_eq_cubeAverage {d : ℕ} (R : TriadicCube d)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.Integrable f (Homogenization.normalizedCubeMeasure R)) :
    exactCircBlockMean R f hf = cubeAverage R f := by
  rw [exactCircBlockMean_eq, cubeAverage_eq_integral_normalizedCubeMeasure]

/-- The exact positive root mean is the ordinary normalized cube average used
by the finite projected-pairing development. -/
theorem exactOverlapRootMean_eq_cubeAverage {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ)
    (hu : MeasureTheory.Integrable u (Homogenization.normalizedCubeMeasure Q)) :
    exactOverlapRootMean Q u hu = cubeAverage Q u := by
  rw [exactOverlapRootMean, cubeAverage_eq_integral_normalizedCubeMeasure]

/-- A certified exact overlap mean is the normalized scalar-overlap cube
average used by the finite overlap definitions. -/
theorem exactOverlapLocalMean_eq_scalarOverlapCubeAverage {d : ℕ} (S : TriadicCube d)
    (u : Vec d → ℝ)
    (hu : MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalMean S u hu = ScalarOverlap.cubeAverage S u := by
  rw [exactOverlapLocalMean_eq, ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure]

/-- At a finite exponent, parent/local `MemLp` makes the exact extended
oscillation precisely the `ENNReal` embedding of its legacy real counterpart. -/
theorem exactOverlapLocalOscillation_eq_ofReal_cubeBesovOverlapOscillation
    {d : ℕ} (S : TriadicCube d) (p : ℝ) (u : Vec d → ℝ)
    (hu : MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S))
    (hmem : MeasureTheory.MemLp u (ENNReal.ofReal p)
      (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalOscillation S (ENNReal.ofReal p) u hu =
      ENNReal.ofReal (cubeBesovOverlapOscillation S (ENNReal.ofReal p) u) := by
  have hsub : MeasureTheory.MemLp
      (fun x => u x - exactOverlapLocalMean S u hu) (ENNReal.ofReal p)
      (ScalarOverlap.normalizedCubeMeasure S) :=
    hmem.sub (MeasureTheory.memLp_const (exactOverlapLocalMean S u hu))
  rw [exactOverlapLocalOscillation_eq, ← ENNReal.ofReal_toReal hsub.eLpNorm_ne_top]
  unfold cubeBesovOverlapOscillation ScalarOverlap.cubeLpNorm
  rw [exactOverlapLocalMean_eq_scalarOverlapCubeAverage]

/-- At a finite source exponent, the certified exact overlap depth average is
the `ENNReal` embedding of the legacy finite overlap average. -/
theorem exactOverlapDepthAverage_eq_ofReal_cubeBesovOverlapDepthAverage
    {d : ℕ} (Q : TriadicCube d) (p : ℝ) (hp : 1 ≤ p) (u : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp u (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q)) (j : ℕ) :
    exactOverlapDepthAverage Q p u (exactDualOverlapIntegrable Q p hp hmem) j =
      ENNReal.ofReal (cubeBesovOverlapDepthAverage Q (ENNReal.ofReal p) u j) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hcard : (0 : ℝ) < ((ScalarOverlap.centersAtDepth Q j).card : ℝ) := by
    exact_mod_cast ScalarOverlap.centersAtDepth_card_pos Q j
  let g : TriadicCube d → ℝ≥0∞ := fun S =>
    if hS : S ∈ ScalarOverlap.centersAtDepth Q j then
      (exactOverlapLocalOscillation S (ENNReal.ofReal p) u
        ((exactDualOverlapIntegrable Q p hp hmem).overlap j S hS)) ^ p
    else 0
  rw [exactOverlapDepthAverage_eq]
  unfold cubeBesovOverlapDepthAverage ScalarOverlap.centersAverage
  rw [ENNReal.ofReal_mul]
  · rw [ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      calc
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
            (exactOverlapLocalOscillation S.1 (ENNReal.ofReal p) u
              ((exactDualOverlapIntegrable Q p hp hmem).overlap j S.1 S.2)) ^ p) =
            (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S => g S.1) := by
              apply Finset.sum_congr rfl
              intro S hS
              simp [g, S.2]
        _ = (ScalarOverlap.centersAtDepth Q j).sum g := Finset.sum_attach _ _
        _ = (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
            ENNReal.ofReal
              (cubeBesovOverlapOscillation S (ENNReal.ofReal p) u ^
                (ENNReal.ofReal p).toReal)) := by
          apply Finset.sum_congr rfl
          intro S hS
          simp only [g, dif_pos hS]
          rw [← ENNReal.ofReal_rpow_of_nonneg]
          · rw [exactOverlapLocalOscillation_eq_ofReal_cubeBesovOverlapOscillation S p u
              ((exactDualOverlapIntegrable Q p hp hmem).overlap j S hS)
              (ScalarOverlap.memLp_of_mem_centersAtDepth_of_memLp hS hmem)]
            simp [ENNReal.toReal_ofReal hp0]
          · exact cubeBesovOverlapOscillation_nonneg S (ENNReal.ofReal p) u
          · exact ENNReal.toReal_nonneg
    · intro S hS
      exact Real.rpow_nonneg
        (cubeBesovOverlapOscillation_nonneg S (ENNReal.ofReal p) u) _
  · exact inv_nonneg.mpr (by positivity)

/-- At a finite source exponent, the certified exact overlap depth term is
the `ENNReal` embedding of the legacy weighted overlap term. -/
theorem exactOverlapDepthTerm_eq_ofReal_cubeBesovOverlapDepthSeminorm
    {d : ℕ} (Q : TriadicCube d) (s p : ℝ) (hp : 1 ≤ p) (u : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp u (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q)) (j : ℕ) :
    exactOverlapDepthTerm Q s p u (exactDualOverlapIntegrable Q p hp hmem) j =
      ENNReal.ofReal (cubeBesovOverlapDepthSeminorm Q s (ENNReal.ofReal p) u j) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  rw [exactOverlapDepthTerm_eq, exactOverlapDepthWeight_eq_ofReal_legacy,
    exactOverlapDepthAverage_eq_ofReal_cubeBesovOverlapDepthAverage Q p hp u hmem j]
  unfold cubeBesovOverlapDepthSeminorm
  rw [ENNReal.toReal_ofReal hp0]
  rw [ENNReal.ofReal_mul]
  · rw [← ENNReal.ofReal_rpow_of_nonneg]
    · simp only [one_div]
    · exact cubeBesovOverlapDepthAverage_nonneg Q (ENNReal.ofReal p) u j
    · exact one_div_nonneg.mpr hp0
  · exact cubeBesovOverlapDepthWeight_nonneg Q s j

/-- The exact circ depth average has the finite descendant-average formula
with legacy normalized cube averages, while retaining its extended value. -/
theorem exactCircDepthAverage_eq_cubeAverage {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ) :
    exactCircDepthAverage Q p f hf j =
      ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (descendantsAtDepth Q j).attach.sum fun R =>
          (ENNReal.ofReal |cubeAverage R.1 f|) ^ p := by
  rw [exactCircDepthAverage_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro R _
  rw [exactCircBlockMean_eq_cubeAverage]

/-- At a finite source exponent, the certified exact circ depth average is
the `ENNReal` embedding of the legacy finite circ average. -/
theorem exactCircDepthAverage_eq_ofReal_cubeBesovCircDepthAverage
    {d : ℕ} (Q : TriadicCube d) (p : ℝ) (hp : 1 ≤ p) (f : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q)) (j : ℕ) :
    exactCircDepthAverage Q p f (exactCircIntegrable_of_memLp Q p hp hmem) j =
      ENNReal.ofReal (cubeBesovCircDepthAverage Q (ENNReal.ofReal p) f j) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
  let g : TriadicCube d → ℝ≥0∞ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      (ENNReal.ofReal |cubeAverage R f|) ^ p
    else 0
  rw [exactCircDepthAverage_eq_cubeAverage]
  unfold cubeBesovCircDepthAverage descendantsAverage
  rw [ENNReal.ofReal_mul]
  · rw [ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      calc
        (descendantsAtDepth Q j).attach.sum (fun R =>
            (ENNReal.ofReal |cubeAverage R.1 f|) ^ p) =
            (descendantsAtDepth Q j).attach.sum (fun R => g R.1) := by
              apply Finset.sum_congr rfl
              intro R hR
              simp [g, R.2]
        _ = (descendantsAtDepth Q j).sum g := Finset.sum_attach _ _
        _ = (descendantsAtDepth Q j).sum (fun R =>
            ENNReal.ofReal (‖cubeAverage R f‖ ^ (ENNReal.ofReal p).toReal)) := by
          apply Finset.sum_congr rfl
          intro R hR
          simp only [g, dif_pos hR]
          rw [← ENNReal.ofReal_rpow_of_nonneg]
          · simp [ENNReal.toReal_ofReal hp0]
          · exact abs_nonneg _
          · exact ENNReal.toReal_nonneg
    · intro R hR
      exact Real.rpow_nonneg (norm_nonneg _) _
  · exact inv_nonneg.mpr (by positivity)

/-- At a finite source exponent, the certified exact circ depth term is the
`ENNReal` embedding of the legacy weighted circ term. -/
theorem exactCircDepthTerm_eq_ofReal_cubeBesovCircDepthSeminorm
    {d : ℕ} (Q : TriadicCube d) (s p : ℝ) (hp : 1 ≤ p) (f : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q)) (j : ℕ) :
    exactCircDepthTerm Q s p f (exactCircIntegrable_of_memLp Q p hp hmem) j =
      ENNReal.ofReal (cubeBesovCircDepthSeminorm Q s (ENNReal.ofReal p) f j) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  rw [exactCircDepthTerm_eq, exactCircDepthWeight_eq_ofReal_legacy,
    exactCircDepthAverage_eq_ofReal_cubeBesovCircDepthAverage Q p hp f hmem j]
  unfold cubeBesovCircDepthSeminorm
  rw [ENNReal.toReal_ofReal hp0]
  rw [ENNReal.ofReal_mul]
  · rw [← ENNReal.ofReal_rpow_of_nonneg]
    · simp only [one_div]
    · exact cubeBesovCircDepthAverage_nonneg Q (ENNReal.ofReal p) f j
    · exact one_div_nonneg.mpr hp0
  · exact cubeBesovCircDepthWeight_nonneg Q s j

/-- The exact finite positive norm has the same root term as the finite
projected-pairing norm, with the exact extended seminorm left unchanged. -/
theorem exactOverlapFiniteNorm_eq_rootCubeAverage {d : ℕ}
    (P : ExactOverlapFiniteParameters) (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : ExactOverlapIntegrable Q u) :
    exactOverlapFiniteNorm P Q u hu = exactOverlapFiniteSeminorm P Q u hu +
      exactOverlapRootWeight Q P.s * ENNReal.ofReal |cubeAverage Q u| := by
  rw [exactOverlapFiniteNorm_eq, exactOverlapRootMean_eq_cubeAverage]

/-- The exact positive top norm has the same root term as the finite
projected-pairing norm, with the exact extended seminorm left unchanged. -/
theorem exactOverlapTopNorm_eq_rootCubeAverage {d : ℕ}
    (P : ExactOverlapTopParameters) (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : ExactOverlapIntegrable Q u) :
    exactOverlapTopNorm P Q u hu = exactOverlapTopSeminorm P Q u hu +
      exactOverlapRootWeight Q P.s * ENNReal.ofReal |cubeAverage Q u| := by
  rw [exactOverlapTopNorm_eq, exactOverlapRootMean_eq_cubeAverage]

end Homogenization
