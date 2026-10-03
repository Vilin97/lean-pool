/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Algebra.Order.Field.GeomSum
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Full
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectionLimit

/-! # Global Comparison -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal Topology

theorem finset_Lq_norm_le_sum_of_nonneg {ι : Type*} (s : Finset ι) {q : ℝ} (hq : 1 ≤ q)
    {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    (Finset.sum s fun i => f i ^ q) ^ (1 / q) ≤ Finset.sum s fun i => f i := by
  classical
  have hq0 : q ≠ 0 := by linarith
  induction s using Finset.induction_on with
  | empty =>
      simp [hq0]
  | @insert a s ha ih =>
    have hfa : 0 ≤ f a := hf a (by simp)
    have hfs : ∀ i ∈ s, 0 ≤ f i := by
      intro i hi
      exact hf i (by simp [hi])
    have hsum_nonneg : 0 ≤ Finset.sum s (fun i => f i ^ q) := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact Real.rpow_nonneg (hfs i hi) q
    calc
      (Finset.sum (insert a s) fun i => f i ^ q) ^ (1 / q)
          = (f a ^ q + Finset.sum s (fun i => f i ^ q)) ^ (1 / q) := by
              rw [Finset.sum_insert ha]
      _ = (f a ^ q + ((Finset.sum s fun i => f i ^ q) ^ (1 / q)) ^ q) ^ (1 / q) := by
            congr 1
            symm
            simpa [one_div] using Real.rpow_inv_rpow hsum_nonneg hq0
      _ ≤ f a + (Finset.sum s fun i => f i ^ q) ^ (1 / q) := by
            exact Real.rpow_add_rpow_le_add hfa (Real.rpow_nonneg hsum_nonneg (1 / q)) hq
      _ ≤ f a + Finset.sum s (fun i => f i) := by
            gcongr
            exact ih hfs
      _ = Finset.sum (insert a s) (fun i => f i) := by rw [Finset.sum_insert ha]

theorem cubeBesovCircDepthWeight_succ {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    cubeBesovCircDepthWeight Q s (j + 1) =
      (3 : ℝ) ^ (-s) * cubeBesovCircDepthWeight Q s j := by
  have hQ_nonneg : 0 ≤ cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
  have hA_nonneg : 0 ≤ cubeScaleFactor Q / (3 : ℝ) ^ j := by
    exact div_nonneg hQ_nonneg (by positivity)
  have hdiv :
      cubeScaleFactor Q / (3 : ℝ) ^ (j + 1) =
        (cubeScaleFactor Q / (3 : ℝ) ^ j) / 3 := by
    rw [pow_succ', div_eq_mul_inv, div_eq_mul_inv]
    ring
  unfold cubeBesovCircDepthWeight
  rw [hdiv, Real.div_rpow hA_nonneg (by positivity)]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  rw [← Real.rpow_neg (by positivity)]

theorem cubeBesovCircDepthWeight_eq_scaleWeight_neg_mul_geom {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    cubeBesovCircDepthWeight Q s j =
      cubeBesovScaleWeight (-s) Q * ((3 : ℝ) ^ (-s)) ^ j := by
  induction j with
  | zero =>
      simp [cubeBesovCircDepthWeight_depth_zero]
  | succ j ih =>
      rw [cubeBesovCircDepthWeight_succ, ih, pow_succ']
      ring

theorem cubeBesovCircDepthSeminorm_le_scaleWeight_neg_mul_geom_mul_cubeLpNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q)) :
    cubeBesovCircDepthSeminorm Q s p u j ≤
      cubeBesovScaleWeight (-s) Q * ((3 : ℝ) ^ (-s)) ^ j * cubeLpNorm Q p u := by
  have hp0 : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hdepth :
      cubeBesovCircDepthSeminorm Q s p u j ≤
        cubeBesovCircDepthWeight Q s j * cubeLpNorm Q p u := by
    unfold cubeBesovCircDepthSeminorm
    refine mul_le_mul_of_nonneg_left ?_ (cubeBesovCircDepthWeight_nonneg Q s j)
    calc
      (cubeBesovCircDepthAverage Q p u j) ^ (1 / p.toReal)
          ≤ ((cubeLpNorm Q p u) ^ p.toReal) ^ (1 / p.toReal) := by
              exact Real.rpow_le_rpow
                (cubeBesovCircDepthAverage_nonneg Q p u j)
                (cubeBesovCircDepthAverage_le_cubeLpNorm_rpow Q p u j hp hpTop hu)
                (show 0 ≤ 1 / p.toReal by positivity)
      _ = cubeLpNorm Q p u := by
            rw [← Real.rpow_mul (cubeLpNorm_nonneg Q p u)]
            field_simp [hp_pos.ne']
            rw [Real.rpow_one]
  calc
    cubeBesovCircDepthSeminorm Q s p u j
        ≤ cubeBesovCircDepthWeight Q s j * cubeLpNorm Q p u := hdepth
    _ = cubeBesovScaleWeight (-s) Q * ((3 : ℝ) ^ (-s)) ^ j * cubeLpNorm Q p u := by
          rw [cubeBesovCircDepthWeight_eq_scaleWeight_neg_mul_geom]

theorem cubeBesovCircPartialNorm_le_geometric_constant_of_memLp {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hq : 1 ≤ q) (hqTop : q ≠ ∞) :
    cubeBesovCircPartialNorm Q s p q N u ≤
      (cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
  let r : ℝ := (3 : ℝ) ^ (-s)
  let A : ℝ := cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) (cubeLpNorm_nonneg Q p u)
  have hqReal : 1 ≤ q.toReal := by
    rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hqTop]
  have hpartial_le_sum :
      cubeBesovCircPartialNorm Q s p q N u ≤
        Finset.sum (Finset.range (N + 1)) (fun j => cubeBesovCircDepthSeminorm Q s p u j) := by
    simpa [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm] using
      finset_Lq_norm_le_sum_of_nonneg
        (s := Finset.range (N + 1)) (q := q.toReal) hqReal
        (f := fun j => cubeBesovCircDepthSeminorm Q s p u j)
        (by
          intro j hj
          exact cubeBesovCircDepthSeminorm_nonneg Q s p u j)
  have hsum_le :
      Finset.sum (Finset.range (N + 1)) (fun j => cubeBesovCircDepthSeminorm Q s p u j) ≤
        Finset.sum (Finset.range (N + 1)) (fun j => A * r ^ j) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    calc
      cubeBesovCircDepthSeminorm Q s p u j
          ≤ cubeBesovScaleWeight (-s) Q * ((3 : ℝ) ^ (-s)) ^ j * cubeLpNorm Q p u := by
              exact cubeBesovCircDepthSeminorm_le_scaleWeight_neg_mul_geom_mul_cubeLpNorm
                Q s p u j hp hpTop hu
      _ = A * r ^ j := by
            dsimp [A, r]
            ring
  have hgeom :
      Finset.sum (Finset.range (N + 1)) (fun j => r ^ j) ≤ (1 - r)⁻¹ := by
    simpa only [Finset.range_eq_Ico, pow_zero, div_eq_mul_inv, one_mul] using
      (geom_sum_Ico_le_of_lt_one (x := r) (m := 0) (n := N + 1) hr_nonneg hr_lt_one)
  calc
    cubeBesovCircPartialNorm Q s p q N u
        ≤ Finset.sum (Finset.range (N + 1)) (fun j => cubeBesovCircDepthSeminorm Q s p u j) :=
          hpartial_le_sum
    _ ≤ Finset.sum (Finset.range (N + 1)) (fun j => A * r ^ j) := hsum_le
    _ = A * Finset.sum (Finset.range (N + 1)) (fun j => r ^ j) := by
          rw [Finset.mul_sum]
    _ ≤ A * (1 - r)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hgeom hA_nonneg
    _ = (cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
          rfl

theorem cubeBesovCircPartialNormTop_le_geometric_constant_of_memLp {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    cubeBesovCircPartialNormTop Q s p N u ≤
      (cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
  let r : ℝ := (3 : ℝ) ^ (-s)
  let A : ℝ := cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hr_le_one : r ≤ 1 := le_of_lt hr_lt_one
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) (cubeLpNorm_nonneg Q p u)
  have hInv_ge_one : 1 ≤ (1 - r)⁻¹ := by
    have hsub_pos : 0 < 1 - r := sub_pos.mpr hr_lt_one
    have hsub_le_one : 1 - r ≤ 1 := by linarith
    simpa [one_div] using (one_le_inv₀ hsub_pos).2 hsub_le_one
  unfold cubeBesovCircPartialNormTop
  refine Finset.sup'_le (s := Finset.range (N + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovCircDepthSeminorm Q s p u j) ?_
  intro j hj
  calc
    cubeBesovCircDepthSeminorm Q s p u j
        ≤ A * r ^ j := by
            calc
              cubeBesovCircDepthSeminorm Q s p u j
                  ≤ cubeBesovScaleWeight (-s) Q * ((3 : ℝ) ^ (-s)) ^ j * cubeLpNorm Q p u := by
                      exact cubeBesovCircDepthSeminorm_le_scaleWeight_neg_mul_geom_mul_cubeLpNorm
                        Q s p u j hp hpTop hu
              _ = A * r ^ j := by
                    dsimp [A, r]
                    ring
    _ ≤ A * 1 := by
          gcongr
          exact pow_le_one₀ hr_nonneg hr_le_one
    _ ≤ A * (1 - r)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hInv_ge_one hA_nonneg
    _ = (cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
          rfl

theorem cubeBesovCircNormEntry_le_geometric_constant_of_memLp {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hq : 1 ≤ q) :
    cubeBesovCircNormEntry Q s p q N u ≤
      (cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
  by_cases hqTop : q = ∞
  · simpa [cubeBesovCircNormEntry, hqTop] using
      cubeBesovCircPartialNormTop_le_geometric_constant_of_memLp
        (Q := Q) (s := s) (p := p) (N := N + 1) (u := u) hs hu hp hpTop
  · simpa [cubeBesovCircNormEntry, hqTop] using
      cubeBesovCircPartialNorm_le_geometric_constant_of_memLp
        (Q := Q) (s := s) (p := p) (q := q) (N := N + 1) (u := u)
        hs hu hp hpTop hq hqTop

theorem cubeBesovCircNormValueSet_bddAbove_of_memLp {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hq : 1 ≤ q) :
    BddAbove (cubeBesovCircNormValueSet Q s p q u) := by
  refine ⟨(cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u) * (1 - (3 : ℝ) ^ (-s))⁻¹, ?_⟩
  intro r hr
  rcases hr with ⟨N, rfl⟩
  exact cubeBesovCircNormEntry_le_geometric_constant_of_memLp
    Q s p q N u hs hu hp hpTop hq

/-- The full positive circ norm is controlled by the geometric `Lᵖ` bound used
for each finite entry. This is a direct `sSup` wrapper around
`cubeBesovCircNormEntry_le_geometric_constant_of_memLp`. -/
theorem cubeBesovCircNorm_le_geometric_constant_of_memLp {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hq : 1 ≤ q) :
    cubeBesovCircNorm Q s p q u ≤
      (cubeBesovScaleWeight (-s) Q * cubeLpNorm Q p u) *
        (1 - (3 : ℝ) ^ (-s))⁻¹ := by
  unfold cubeBesovCircNorm
  refine csSup_le (cubeBesovCircNormValueSet_nonempty Q s p q u) ?_
  intro r hr
  rcases hr with ⟨N, rfl⟩
  exact cubeBesovCircNormEntry_le_geometric_constant_of_memLp
    Q s p q N u hs hu hp hpTop hq

theorem CubeBesovDualMeanZeroTestGlobal.memLp {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : CubeBesovDualMeanZeroTestGlobal Q s p q g) :
    MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q) := by
  have hfluct :
      MeasureTheory.MemLp (cubeFluctuation Q g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure Q) :=
    hg.2.2 0 Q (by simp)
  convert hfluct using 1
  ext x
  simp [cubeFluctuation, hg.2.1]

theorem CubeBesovDualLocalMemLpGlobal.memLp {d : ℕ} {Q : TriadicCube d}
    {p : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : CubeBesovDualLocalMemLpGlobal Q p g) :
    MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q) := by
  have hfluct :
      MeasureTheory.MemLp (cubeFluctuation Q g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure Q) :=
    hg 0 Q (by simp)
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => cubeAverage Q g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (cubeAverage Q g)
  convert hfluct.add hconst using 1
  ext x
  simp [cubeFluctuation, sub_eq_add_neg, add_left_comm, add_comm]

theorem CubeBesovDualLocalMemLpGlobal.of_memLp_parent {d : ℕ} {Q : TriadicCube d}
    {p : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q)) :
    CubeBesovDualLocalMemLpGlobal Q p g := by
  intro j R hR
  have hgR :
      MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hg
  simpa [cubeFluctuation] using!
    hgR.sub (MeasureTheory.memLp_const (cubeAverage R g))

theorem CubeBesovDualFullTest.memLp {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {g : Vec d → ℝ} (hg : CubeBesovDualFullTest Q s p q g) :
    MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q) := by
  exact hg.2.memLp

theorem abs_cubeBesovPairing_le_max_mul_cubeBesovCircNorm_of_mean_zero_test {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u g : Vec d → ℝ)
    (hBddCirc : BddAbove (cubeBesovCircNormValueSet Q s p q u))
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q)
    (hg : CubeBesovDualMeanZeroTestGlobal Q s p q g) :
    |cubeBesovPairing Q u g| ≤
      max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u := by
  let B : ℝ := max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u
  have hconv :=
    tendsto_cubeBesovPairing_projection_left_of_memLp
      Q p u g hu hg.memLp hp hpTop hpConjTop
  have hconv_abs :
      Filter.Tendsto
        (fun n => |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g|)
        Filter.atTop (𝓝 |cubeBesovPairing Q u g|) := by
    simpa [Real.norm_eq_abs] using hconv.norm
  have hbound :
      ∀ n, |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g| ≤ B := by
    intro n
    have hpartial :
        |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g| ≤
          max 1 ((3 : ℝ) ^ s) * cubeBesovCircNormEntry Q s p q n u := by
      exact abs_cubeBesovPairing_projection_le_max_mul_cubeBesovCircNormEntry_of_dual_test
        (Q := Q) (s := s) (p := p) (q := q) (N := n) (u := u) (g := g)
        (integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) (hu.integrable hp)) hp hpTop
        hpConjTop hq (hg.to_dual_test n)
    calc
      |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g|
          ≤ max 1 ((3 : ℝ) ^ s) * cubeBesovCircNormEntry Q s p q n u := hpartial
      _ ≤ B := by
            exact mul_le_mul_of_nonneg_left
              (cubeBesovCircNormEntry_le_cubeBesovCircNorm
                (Q := Q) (s := s) (p := p) (q := q) (u := u) hBddCirc n)
              (le_trans (by norm_num) (le_max_left 1 ((3 : ℝ) ^ s)))
  have hlimit : |cubeBesovPairing Q u g| ≤ B := by
    exact le_of_tendsto hconv_abs (Filter.Eventually.of_forall hbound)
  simpa [B] using hlimit

theorem cubeBesovDualMeanZeroSeminormValueSet_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBddCirc : BddAbove (cubeBesovCircNormValueSet Q s p q u))
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    BddAbove (cubeBesovDualMeanZeroSeminormValueSet Q s p q u) := by
  refine ⟨max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u, ?_⟩
  intro r hr
  rcases hr with ⟨g, hg, rfl⟩
  exact abs_cubeBesovPairing_le_max_mul_cubeBesovCircNorm_of_mean_zero_test
    Q s p q u g hBddCirc hu hp hpTop hpConjTop hq hg

theorem cubeBesovDualMeanZeroSeminorm_le_max_mul_cubeBesovCircNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBddCirc : BddAbove (cubeBesovCircNormValueSet Q s p q u))
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    cubeBesovDualMeanZeroSeminorm Q s p q u ≤
      max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u := by
  have hpConj0 : cubeBesovConjExponent p ≠ 0 := cubeBesovConjExponent_ne_zero p
  unfold cubeBesovDualMeanZeroSeminorm
  refine csSup_le
    (cubeBesovDualMeanZeroSeminormValueSet_nonempty
      Q s p q u hpConj0 hpConjTop) ?_
  intro r hr
  rcases hr with ⟨g, hg, rfl⟩
  exact abs_cubeBesovPairing_le_max_mul_cubeBesovCircNorm_of_mean_zero_test
    Q s p q u g hBddCirc hu hp hpTop hpConjTop hq hg

theorem abs_cubeBesovPairing_le_max_mul_cubeBesovCircNorm_of_full_test {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u g : Vec d → ℝ)
    (hBddCirc : BddAbove (cubeBesovCircNormValueSet Q s p q u))
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q)
    (hg : CubeBesovDualFullTest Q s p q g) :
    |cubeBesovPairing Q u g| ≤
      max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u := by
  let B : ℝ := max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u
  have hconv :=
    tendsto_cubeBesovPairing_projection_left_of_memLp
      Q p u g hu hg.memLp hp hpTop hpConjTop
  have hconv_abs :
      Filter.Tendsto
        (fun n => |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g|)
        Filter.atTop (𝓝 |cubeBesovPairing Q u g|) := by
    simpa [Real.norm_eq_abs] using hconv.norm
  have hbound :
      ∀ n, |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g| ≤ B := by
    intro n
    have hpartial :
        |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g| ≤
          max 1 ((3 : ℝ) ^ s) * cubeBesovCircNormEntry Q s p q n u := by
      exact abs_cubeBesovPairing_projection_le_max_mul_cubeBesovCircNormEntry_of_dual_test
        (Q := Q) (s := s) (p := p) (q := q) (N := n) (u := u) (g := g)
        (integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) (hu.integrable hp)) hp hpTop
        hpConjTop hq (hg.to_dual_test n)
    calc
      |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g|
          ≤ max 1 ((3 : ℝ) ^ s) * cubeBesovCircNormEntry Q s p q n u := hpartial
      _ ≤ B := by
            exact mul_le_mul_of_nonneg_left
              (cubeBesovCircNormEntry_le_cubeBesovCircNorm
                (Q := Q) (s := s) (p := p) (q := q) (u := u) hBddCirc n)
              (le_trans (by norm_num) (le_max_left 1 ((3 : ℝ) ^ s)))
  have hlimit : |cubeBesovPairing Q u g| ≤ B := by
    exact le_of_tendsto hconv_abs (Filter.Eventually.of_forall hbound)
  simpa [B] using hlimit

theorem cubeBesovDualFullNorm_le_max_mul_cubeBesovCircNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBddCirc : BddAbove (cubeBesovCircNormValueSet Q s p q u))
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    cubeBesovDualFullNorm Q s p q u ≤
      max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u := by
  have hpConj0 : cubeBesovConjExponent p ≠ 0 := cubeBesovConjExponent_ne_zero p
  unfold cubeBesovDualFullNorm
  refine csSup_le
    (cubeBesovDualFullNormValueSet_nonempty
      Q s p q u hpConj0 hpConjTop) ?_
  intro r hr
  rcases hr with ⟨g, hg, rfl⟩
  exact abs_cubeBesovPairing_le_max_mul_cubeBesovCircNorm_of_full_test
    Q s p q u g hBddCirc hu hp hpTop hpConjTop hq hg

theorem max_one_three_rpow_le_three_rpow_nat_add (d : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    max 1 ((3 : ℝ) ^ s) ≤ (3 : ℝ) ^ ((d : ℝ) + s) := by
  have hs_one : 1 ≤ (3 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs
  rw [max_eq_right hs_one]
  calc
    (3 : ℝ) ^ s ≤ (3 : ℝ) ^ (d : ℝ) * (3 : ℝ) ^ s := by
      exact le_mul_of_one_le_left
        (Real.rpow_nonneg (by positivity) s)
        (Real.one_le_rpow (by norm_num) (by positivity : 0 ≤ (d : ℝ)))
    _ = (3 : ℝ) ^ ((d : ℝ) + s) := by
      symm
      rw [Real.rpow_add (by norm_num : 0 < (3 : ℝ))]

theorem cubeBesovCircNorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBddCirc : BddAbove (cubeBesovCircNormValueSet Q s p q u)) :
    0 ≤ cubeBesovCircNorm Q s p q u := by
  have hentry_nonneg : 0 ≤ cubeBesovCircNormEntry Q s p q 0 u := by
    by_cases hqTop : q = ∞
    · simpa [cubeBesovCircNormEntry, hqTop] using
        cubeBesovCircPartialNormTop_nonneg Q s p 1 u
    · simpa [cubeBesovCircNormEntry, hqTop] using
        cubeBesovCircPartialNorm_nonneg Q s p q 1 u
  exact le_trans hentry_nonneg
    (cubeBesovCircNormEntry_le_cubeBesovCircNorm
      (Q := Q) (s := s) (p := p) (q := q) (u := u) hBddCirc 0)

theorem cubeBesovDualMeanZeroSeminorm_le_note_constant_mul_cubeBesovCircNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    cubeBesovDualMeanZeroSeminorm Q s p q u ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s p q u := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hBddCirc := cubeBesovCircNormValueSet_bddAbove_of_memLp
    Q s p q u hs hu hp hpTop hq
  have hCircNonneg := cubeBesovCircNorm_nonneg Q s p q u hBddCirc
  calc
    cubeBesovDualMeanZeroSeminorm Q s p q u
        ≤ max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u := by
            exact cubeBesovDualMeanZeroSeminorm_le_max_mul_cubeBesovCircNorm
              Q s p q u hBddCirc hu hp hpTop hpConjTop hq
    _ ≤ (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s p q u := by
          exact mul_le_mul_of_nonneg_right
            (max_one_three_rpow_le_three_rpow_nat_add d s hs0) hCircNonneg

/-- The full negative Besov dual norm is controlled by the negative circ norm
alone.  This is the sharp average bookkeeping needed in the Caccioppoli
single-cube estimate: the depth-zero circ term already carries the
`cubeBesovScaleWeight (-s)` average contribution, so no extra positive Besov
average tail is needed. -/
theorem cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    cubeBesovDualFullNorm Q s p q u ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s p q u := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hBddCirc := cubeBesovCircNormValueSet_bddAbove_of_memLp
    Q s p q u hs hu hp hpTop hq
  have hCircNonneg := cubeBesovCircNorm_nonneg Q s p q u hBddCirc
  calc
    cubeBesovDualFullNorm Q s p q u
        ≤ max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u := by
            exact cubeBesovDualFullNorm_le_max_mul_cubeBesovCircNorm
              Q s p q u hBddCirc hu hp hpTop hpConjTop hq
    _ ≤ (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s p q u := by
          exact mul_le_mul_of_nonneg_right
            (max_one_three_rpow_le_three_rpow_nat_add d s hs0) hCircNonneg

theorem cubeBesovDualFullNorm_le_note_rhs {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    cubeBesovDualFullNorm Q s p q u ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s p q u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖ := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hBddCirc := cubeBesovCircNormValueSet_bddAbove_of_memLp
    Q s p q u hs hu hp hpTop hq
  have hbase :
      cubeBesovDualFullNorm Q s p q u ≤
        (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s p q u := by
    have hCircNonneg := cubeBesovCircNorm_nonneg Q s p q u hBddCirc
    calc
      cubeBesovDualFullNorm Q s p q u
          ≤ max 1 ((3 : ℝ) ^ s) * cubeBesovCircNorm Q s p q u := by
              exact cubeBesovDualFullNorm_le_max_mul_cubeBesovCircNorm
                Q s p q u hBddCirc hu hp hpTop hpConjTop hq
      _ ≤ (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovCircNorm Q s p q u := by
            exact mul_le_mul_of_nonneg_right
              (max_one_three_rpow_le_three_rpow_nat_add d s hs0) hCircNonneg
  exact hbase.trans (le_add_of_nonneg_right
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _)))

end Homogenization
