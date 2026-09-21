/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.GlobalComparison

/-! # Caccioppoli Bridge -/

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeAverage_const_mul {d : ℕ} (Q : TriadicCube d) (c : ℝ) (f : Vec d → ℝ) :
    cubeAverage Q (fun x => c * f x) = c * cubeAverage Q f := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure, MeasureTheory.integral_const_mul,
    cubeAverage_eq_integral_normalizedCubeMeasure]

theorem cubeFluctuation_const_mul {d : ℕ} (Q : TriadicCube d) (c : ℝ) (f : Vec d → ℝ) :
    cubeFluctuation Q (fun x => c * f x) = fun x => c * cubeFluctuation Q f x := by
  funext x
  simp [cubeFluctuation, cubeAverage_const_mul, mul_sub]

theorem cubeLpNorm_const_mul {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (c : ℝ)
    (f : Vec d → ℝ) :
    cubeLpNorm Q p (fun x => c * f x) = ‖c‖ * cubeLpNorm Q p f := by
  unfold cubeLpNorm
  have hfun : (fun x => c * f x) = c • f := by
    funext x
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun, MeasureTheory.eLpNorm_const_smul]
  simp [ENNReal.toReal_mul]

theorem descendantsAverage_mul_left_local {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (c : ℝ) (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c * F R) = c * descendantsAverage Q j F := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  change ((D.card : ℝ)⁻¹ * ∑ R ∈ D, c * F R) = c * (((D.card : ℝ)⁻¹) * ∑ R ∈ D, F R)
  rw [← Finset.mul_sum]
  ring

theorem cubeBesovOscillation_two_const_mul {d : ℕ} (Q : TriadicCube d) (c : ℝ)
    (u : Vec d → ℝ) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => c * u x) =
      ‖c‖ * cubeBesovOscillation Q (2 : ℝ≥0∞) u := by
  unfold cubeBesovOscillation
  rw [cubeFluctuation_const_mul, cubeLpNorm_const_mul]

theorem cubeBesovDepthAverage_two_const_mul {d : ℕ} (Q : TriadicCube d) (c : ℝ)
    (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => c * u x) j =
      ‖c‖ ^ (2 : ℝ) * cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j := by
  have htwo : ENNReal.toReal (2 : ℝ≥0∞) = 2 := by norm_num
  unfold cubeBesovDepthAverage
  calc
    descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => c * u x)) ^
      ENNReal.toReal (2 : ℝ≥0∞))
        =
          descendantsAverage Q j (fun R => ‖c‖ ^ (2 : ℝ) *
            (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ ENNReal.toReal (2 : ℝ≥0∞)) := by
              refine congrArg (descendantsAverage Q j) ?_
              funext R
              rw [cubeBesovOscillation_two_const_mul, htwo]
              simpa using
                (Real.mul_rpow (norm_nonneg c)
                  (cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) u) :
                  (‖c‖ * cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ (2 : ℝ) =
                    ‖c‖ ^ (2 : ℝ) *
                      (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ (2 : ℝ))
    _ = ‖c‖ ^ (2 : ℝ) * descendantsAverage Q j
          (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ ENNReal.toReal (2 : ℝ≥0∞)) := by
            exact descendantsAverage_mul_left_local Q j (‖c‖ ^ (2 : ℝ))
              (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^
                ENNReal.toReal (2 : ℝ≥0∞))

theorem cubeBesovDepthSeminorm_two_const_mul {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (c : ℝ) (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => c * u x) j =
      ‖c‖ * cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j := by
  unfold cubeBesovDepthSeminorm
  rw [cubeBesovDepthAverage_two_const_mul]
  have hnorm_sq_nonneg : 0 ≤ ‖c‖ ^ (2 : ℝ) := by
    exact Real.rpow_nonneg (norm_nonneg c) _
  have havg_nonneg : 0 ≤ cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j :=
    cubeBesovDepthAverage_nonneg Q (2 : ℝ≥0∞) u j
  have hmul :
      (‖c‖ ^ (2 : ℝ) * cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ^ (1 / (2 : ℝ)) =
        (‖c‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ^ (1 / (2 : ℝ)) := by
    exact Real.mul_rpow hnorm_sq_nonneg havg_nonneg
  rw [show (1 / ((2 : ℝ≥0∞).toReal)) = (1 / (2 : ℝ)) by norm_num, hmul]
  have hnorm :
      (‖c‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖c‖ := by
    calc
      (‖c‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖c‖ ^ ((2 : ℝ) * (1 / (2 : ℝ))) := by
            symm
            exact Real.rpow_mul (norm_nonneg c) (2 : ℝ) (1 / (2 : ℝ))
      _ = ‖c‖ := by norm_num
  rw [hnorm]
  ring

theorem cubeBesovPartialSeminormTop_two_const_mul_le {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (c : ℝ) (u : Vec d → ℝ) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N (fun x => c * u x) ≤
      ‖c‖ * cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N u := by
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le (s := Finset.range (N + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => c * u x) j) ?_
  intro j hj
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => c * u x) j
        = ‖c‖ * cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j := by
            simpa using cubeBesovDepthSeminorm_two_const_mul Q s c u j
    _ ≤ ‖c‖ * (Finset.range (N + 1)).sup' ⟨0, by simp⟩
          (fun n => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u n) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.le_sup' (f := fun n => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u n) hj)
              (norm_nonneg c)

theorem cubeBesovPartialNormTop_two_const_mul_le {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (c : ℝ) (u : Vec d → ℝ) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) N (fun x => c * u x) ≤
      ‖c‖ * cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) N u := by
  have havg :
      cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => c * u x)‖ =
        ‖c‖ * (cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) := by
    rw [cubeAverage_const_mul, norm_mul]
    simp [Real.norm_eq_abs, mul_assoc, mul_comm]
  unfold cubeBesovPartialNormTop
  calc
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N (fun x => c * u x) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => c * u x)‖
        =
          cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N (fun x => c * u x) +
            ‖c‖ * (cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) := by
              rw [havg]
    _ ≤ ‖c‖ * cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N u +
          ‖c‖ * (cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) := by
            gcongr
            exact cubeBesovPartialSeminormTop_two_const_mul_le Q s N c u
    _ = ‖c‖ * cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) N u := by
          unfold cubeBesovPartialNormTop
          ring

theorem cubeBesovPartialSeminorm_two_const_mul_le {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (c : ℝ) (u : Vec d → ℝ) :
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => c * u x) ≤
      ‖c‖ * cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u := by
  have hsum :
      Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => c * u x) j) ^
            (2 : ℝ))
        =
      ‖c‖ ^ (2 : ℝ) *
        Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ (2 : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [cubeBesovDepthSeminorm_two_const_mul]
    exact Real.mul_rpow (norm_nonneg c)
      (cubeBesovDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) u j)
  have hsum_nonneg :
      0 ≤ Finset.sum (Finset.range (N + 1))
        (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ (2 : ℝ)) := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact Real.rpow_nonneg
      (cubeBesovDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) u j) _
  have hEq :
      cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => c * u x) =
        ‖c‖ * cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u := by
    have htoReal : ENNReal.toReal (2 : ℝ≥0∞) = 2 := by norm_num
    unfold cubeBesovPartialSeminorm
    calc
      (Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => c * u x) j) ^
            ENNReal.toReal (2 : ℝ≥0∞))) ^ (1 / ENNReal.toReal (2 : ℝ≥0∞))
          =
        (‖c‖ ^ (2 : ℝ) *
            Finset.sum (Finset.range (N + 1))
              (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ (2 : ℝ))) ^
            (1 / (2 : ℝ)) := by
              rw [htoReal]
              rw [hsum]
      _ = (‖c‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (Finset.sum (Finset.range (N + 1))
              (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ (2 : ℝ))) ^
              (1 / (2 : ℝ)) := by
                exact Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) _) hsum_nonneg
      _ = ‖c‖ *
            ((Finset.sum (Finset.range (N + 1))
              (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ (2 : ℝ))) ^
                (1 / (2 : ℝ))) := by
              congr 1
              calc
                (‖c‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖c‖ ^ ((2 : ℝ) * (1 / (2 : ℝ))) := by
                      symm
                      exact Real.rpow_mul (norm_nonneg c) (2 : ℝ) (1 / (2 : ℝ))
                _ = ‖c‖ := by norm_num
      _ = ‖c‖ *
            (Finset.sum (Finset.range (N + 1))
              (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^
                ENNReal.toReal (2 : ℝ≥0∞))) ^ (1 / ENNReal.toReal (2 : ℝ≥0∞)) := by
              rw [htoReal]
  exact le_of_eq hEq

theorem cubeBesovPartialNorm_two_const_mul_le {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (c : ℝ) (u : Vec d → ℝ) :
    cubeBesovPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => c * u x) ≤
      ‖c‖ * cubeBesovPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u := by
  have havg :
      cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => c * u x)‖ =
        ‖c‖ * (cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) := by
    rw [cubeAverage_const_mul, norm_mul]
    simp [Real.norm_eq_abs, mul_assoc, mul_comm]
  unfold cubeBesovPartialNorm
  calc
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => c * u x) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => c * u x)‖
        =
      cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => c * u x) +
        ‖c‖ * (cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) := by
          rw [havg]
    _ ≤ ‖c‖ * cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u +
          ‖c‖ * (cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) := by
            gcongr
            exact cubeBesovPartialSeminorm_two_const_mul_le Q s N c u
    _ = ‖c‖ * cubeBesovPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u := by
          unfold cubeBesovPartialNorm
          ring

theorem cubeBesovDualTestNorm_two_one_const_mul_le {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (c : ℝ) (g : Vec d → ℝ) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => c * g x) ≤
      ‖c‖ * cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hq : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
    N (fun x => c * g x) hq]
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g hq]
  simpa [hpConj] using cubeBesovPartialNormTop_two_const_mul_le Q s N c g

theorem cubeBesovDualTestNorm_two_two_const_mul_le {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (c : ℝ) (g : Vec d → ℝ) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => c * g x) ≤
      ‖c‖ * cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hq : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
    N (fun x => c * g x) hq]
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g hq]
  simpa [hpConj] using cubeBesovPartialNorm_two_const_mul_le Q s N c g

theorem cubeBesovDualLocalMemLpGlobal_two_const_mul {d : ℕ} {Q : TriadicCube d}
    {g : Vec d → ℝ} (c : ℝ)
    (hg : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => c * g x) := by
  intro j R hR
  simpa [Pi.smul_apply, smul_eq_mul, cubeFluctuation_const_mul] using!
    (hg j R hR).const_smul c

theorem cubeBesovPairing_const_mul_right {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ) (c : ℝ) :
    cubeBesovPairing Q f (fun x => c * g x) = c * cubeBesovPairing Q f g := by
  have hfun : (fun x => f x * (c * g x)) = fun x => c * (f x * g x) := by
    funext x
    ring
  unfold cubeBesovPairing
  simpa [hfun] using cubeAverage_const_mul Q c (fun x => f x * g x)

theorem cubeBesovDualFullNormValueSet_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBddCirc : BddAbove (cubeBesovCircNormValueSet Q s p q u))
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    BddAbove (cubeBesovDualFullNormValueSet Q s p q u) := by
  refine ⟨max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u, ?_⟩
  intro r hr
  rcases hr with ⟨g, hg, rfl⟩
  exact abs_cubeBesovPairing_le_max_mul_cubeBesovCircNorm_of_full_test
    Q s p q u g hBddCirc hu hp hpTop hpConjTop hq hg

theorem abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u g : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q)
    (hg : CubeBesovDualFullTest Q s p q g) :
    |cubeBesovPairing Q u g| ≤ cubeBesovDualFullNorm Q s p q u := by
  have hBddCirc := cubeBesovCircNormValueSet_bddAbove_of_memLp Q s p q u hs hu hp hpTop hq
  exact abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test
    Q s p q u g
    (cubeBesovDualFullNormValueSet_bddAbove Q s p q u hBddCirc hu hp hpTop hpConjTop hq)
    hg

theorem cubeBesovDualFullTest_two_one_of_uniform_bound {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (g : Vec d → ℝ) {B : ℝ}
    (hB : 0 < B)
    (hnorm : ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => B⁻¹ * g x) := by
  refine ⟨?_, ?_⟩
  · intro N
    calc
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => B⁻¹ * g x)
          ≤ ‖B⁻¹‖ * cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g := by
              exact cubeBesovDualTestNorm_two_one_const_mul_le Q s N B⁻¹ g
      _ ≤ ‖B⁻¹‖ * B := by
            gcongr
            exact hnorm N
      _ = 1 := by
            rw [Real.norm_of_nonneg (inv_nonneg.mpr hB.le), inv_mul_cancel₀ hB.ne']
  · exact cubeBesovDualLocalMemLpGlobal_two_const_mul B⁻¹ hmem

theorem cubeBesovDualFullTest_two_two_of_uniform_bound {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (g : Vec d → ℝ) {B : ℝ}
    (hB : 0 < B)
    (hnorm : ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => B⁻¹ * g x) := by
  refine ⟨?_, ?_⟩
  · intro N
    calc
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => B⁻¹ * g x)
          ≤ ‖B⁻¹‖ * cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g := by
              exact cubeBesovDualTestNorm_two_two_const_mul_le Q s N B⁻¹ g
      _ ≤ ‖B⁻¹‖ * B := by
            gcongr
            exact hnorm N
      _ = 1 := by
            rw [Real.norm_of_nonneg (inv_nonneg.mpr hB.le), inv_mul_cancel₀ hB.ne']
  · exact cubeBesovDualLocalMemLpGlobal_two_const_mul B⁻¹ hmem

theorem abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_one {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 < B)
    (hnorm : ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u * B := by
  let g' : Vec d → ℝ := fun x => B⁻¹ * g x
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hg' : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) g' :=
    cubeBesovDualFullTest_two_one_of_uniform_bound Q s g hB hnorm hmem
  have hpair :
      |cubeBesovPairing Q u g'| ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u := by
    exact abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp
      Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u g' hs hu (by norm_num) (by norm_num)
      (by
        intro htop
        simp [hpConj] at htop)
      (by norm_num) hg'
  have hg_eq : g = fun x => B * g' x := by
    funext x
    dsimp [g']
    field_simp [hB.ne']
  calc
    |cubeBesovPairing Q u g|
        = |cubeBesovPairing Q u (fun x => B * g' x)| := by rw [hg_eq]
    _ = |B * cubeBesovPairing Q u g'| := by
          rw [cubeBesovPairing_const_mul_right]
    _ = B * |cubeBesovPairing Q u g'| := by
          rw [abs_mul, abs_of_nonneg hB.le]
    _ ≤ B * cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u := by
          gcongr
    _ = cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u * B := by ring

theorem abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 < B)
    (hnorm : ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u * B := by
  let g' : Vec d → ℝ := fun x => B⁻¹ * g x
  have hpConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [show cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))]
    norm_num
  have hg' : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g' :=
    cubeBesovDualFullTest_two_two_of_uniform_bound Q s g hB hnorm hmem
  have hpair :
      |cubeBesovPairing Q u g'| ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u := by
    exact abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp
      Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u g' hs hu (by norm_num) (by norm_num)
      hpConjTop (by norm_num) hg'
  have hg_eq : g = fun x => B * g' x := by
    funext x
    dsimp [g']
    field_simp [hB.ne']
  calc
    |cubeBesovPairing Q u g|
        = |cubeBesovPairing Q u (fun x => B * g' x)| := by rw [hg_eq]
    _ = |B * cubeBesovPairing Q u g'| := by
          rw [cubeBesovPairing_const_mul_right]
    _ = B * |cubeBesovPairing Q u g'| := by
          rw [abs_mul, abs_of_nonneg hB.le]
    _ ≤ B * cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u := by
          gcongr
    _ = cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u * B := by ring

theorem abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_one {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 < B)
    (hnorm : ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) * B := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hpair :=
    abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_one
      Q s u g hs hu hB hnorm hmem
  have hfull :=
    cubeBesovDualFullNorm_le_note_rhs
      Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u hs hu (by norm_num) (by norm_num)
      (by
        intro htop
        simp [hpConj] at htop)
      (by norm_num)
  have hB_nonneg : 0 ≤ B := hB.le
  calc
    |cubeBesovPairing Q u g|
        ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u * B := hpair
    _ ≤
        ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) * B := by
            gcongr

/-- Sharp version of `abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_one`.
The depth-zero circ term already contains the average contribution, so this
matches the LaTeX negative-Besov estimate without the extra positive average
tail. -/
theorem abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 < B)
    (hnorm : ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) * B := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hpair :=
    abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_one
      Q s u g hs hu hB hnorm hmem
  have hfull :=
    cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm
      Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u hs hu (by norm_num) (by norm_num)
      (by
        intro htop
        simp [hpConj] at htop)
      (by norm_num)
  calc
    |cubeBesovPairing Q u g|
        ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u * B := hpair
    _ ≤
        ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) * B := by
            exact mul_le_mul_of_nonneg_right hfull hB.le

theorem abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) * B := by
  let A : ℝ :=
    (3 : ℝ) ^ ((d : ℝ) + s) *
      cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u
  have hCircBdd :
      BddAbove (cubeBesovCircNormValueSet Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) :=
    cubeBesovCircNormValueSet_bddAbove_of_memLp Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u
      hs hu (by norm_num) (by norm_num) (by norm_num)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (cubeBesovCircNorm_nonneg Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u hCircBdd)
  change |cubeBesovPairing Q u g| ≤ A * B
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (A + 1)
  have hA1_pos : 0 < A + 1 := by linarith
  have hδ_pos : 0 < δ := div_pos hε hA1_pos
  have hBδ_pos : 0 < B + δ := add_pos_of_nonneg_of_pos hB hδ_pos
  have hnormδ :
      ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B + δ := by
    intro N
    exact (hnorm N).trans (le_add_of_nonneg_right hδ_pos.le)
  have hstrict :=
    abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one
      Q s u g hs hu hBδ_pos hnormδ hmem
  have hAδ_le : A * δ ≤ ε := by
    have hratio : A / (A + 1) ≤ 1 := by
      exact (div_le_one hA1_pos).mpr (by linarith)
    calc
      A * δ = ε * (A / (A + 1)) := by
        dsimp [δ]
        field_simp [ne_of_gt hA1_pos]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := by ring
  calc
    |cubeBesovPairing Q u g| ≤ A * (B + δ) := by
      simpa [A] using hstrict
    _ = A * B + A * δ := by ring
    _ ≤ A * B + ε := by linarith

theorem abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_one_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) * B := by
  let A : ℝ :=
    (3 : ℝ) ^ ((d : ℝ) + s) *
        cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u +
      cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
  have hCircBdd :
      BddAbove (cubeBesovCircNormValueSet Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) :=
    cubeBesovCircNormValueSet_bddAbove_of_memLp Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u
      hs hu (by norm_num) (by norm_num) (by norm_num)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (cubeBesovCircNorm_nonneg Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u hCircBdd))
      (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (abs_nonneg _))
  dsimp [A]
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (A + 1)
  have hA1_pos : 0 < A + 1 := by linarith
  have hδ_pos : 0 < δ := div_pos hε hA1_pos
  have hBδ_pos : 0 < B + δ := add_pos_of_nonneg_of_pos hB hδ_pos
  have hnormδ :
      ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B + δ := by
    intro N
    exact (hnorm N).trans (le_add_of_nonneg_right hδ_pos.le)
  have hstrict :=
    abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_one
      Q s u g hs hu hBδ_pos hnormδ hmem
  have hAδ_le : A * δ ≤ ε := by
    have hratio : A / (A + 1) ≤ 1 := by
      exact (div_le_one hA1_pos).mpr (by linarith)
    calc
      A * δ = ε * (A / (A + 1)) := by
        dsimp [δ]
        field_simp [ne_of_gt hA1_pos]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := by ring
  calc
    |cubeBesovPairing Q u g| ≤ A * (B + δ) := by
      simpa [A] using hstrict
    _ = A * B + A * δ := by ring
    _ ≤ A * B + ε := by linarith

theorem abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_two {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 < B)
    (hnorm : ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) * B := by
  have hpConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [show cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))]
    norm_num
  have hpair :=
    abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two
      Q s u g hs hu hB hnorm hmem
  have hfull :=
    cubeBesovDualFullNorm_le_note_rhs
      Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u hs hu (by norm_num) (by norm_num) hpConjTop
      (by norm_num)
  calc
    |cubeBesovPairing Q u g|
        ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u * B := hpair
    _ ≤
        ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) * B := by
            gcongr

theorem abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_two_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) * B := by
  let A : ℝ :=
    (3 : ℝ) ^ ((d : ℝ) + s) *
        cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u +
      cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
  have hCircBdd :
      BddAbove (cubeBesovCircNormValueSet Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u) :=
    cubeBesovCircNormValueSet_bddAbove_of_memLp Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u
      hs hu (by norm_num) (by norm_num) (by norm_num)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (cubeBesovCircNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u hCircBdd))
      (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (abs_nonneg _))
  dsimp [A]
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (A + 1)
  have hA1_pos : 0 < A + 1 := by linarith
  have hδ_pos : 0 < δ := div_pos hε hA1_pos
  have hBδ_pos : 0 < B + δ := add_pos_of_nonneg_of_pos hB hδ_pos
  have hnormδ :
      ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B + δ := by
    intro N
    exact (hnorm N).trans (le_add_of_nonneg_right hδ_pos.le)
  have hstrict :=
    abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_two
      Q s u g hs hu hBδ_pos hnormδ hmem
  have hAδ_le : A * δ ≤ ε := by
    have hratio : A / (A + 1) ≤ 1 := by
      exact (div_le_one hA1_pos).mpr (by linarith)
    calc
      A * δ = ε * (A / (A + 1)) := by
        dsimp [δ]
        field_simp [ne_of_gt hA1_pos]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := by ring
  calc
    |cubeBesovPairing Q u g| ≤ A * (B + δ) := by
      simpa [A] using hstrict
    _ = A * B + A * δ := by ring
    _ ≤ A * B + ε := by linarith

end Homogenization
