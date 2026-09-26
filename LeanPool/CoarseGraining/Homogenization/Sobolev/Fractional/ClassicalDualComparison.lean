/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.SobolevPublic
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliBridge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-!
# Classical fractional dual comparison

Scalar Euclidean Gagliardo tests with a scale-weighted normalized L² term
embed into the legacy partition Besov test space. All real-valued suprema
below are proved bounded for the L² fields to which the comparison applies.
-/

@[expose] public section

namespace Homogenization.ClassicalSobolev34

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The Euclidean difference quotient at the fixed order `3/4`. -/
def kernel {d : ℕ} (φ : Vec d → ℝ) : Vec d × Vec d → ℝ :=
  fun z => euclideanDist z.1 z.2 ^ (-((3 / 4 : ℝ) + (d : ℝ) / 2)) *
    (φ z.1 - φ z.2)

/-- Membership includes both measurability and finiteness certificates. -/
def memH34 {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) : Prop :=
  MemLp φ 2 (normalizedCubeMeasure Q) ∧
    MemLp (kernel φ) 2 (Gagliardo.gagliardoCubeMeasure Q)

/-- The Euclidean Gagliardo seminorm, normalized in its first integral. -/
def seminorm {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) : ℝ :=
  (eLpNorm (kernel φ) 2 (Gagliardo.gagliardoCubeMeasure Q)).toReal

/-- A full fractional norm which detects constants and has units `length⁻³ᐟ⁴`. -/
def testNorm {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) : ℝ :=
  seminorm Q φ + cubeScaleFactor Q ^ (-(3 / 4 : ℝ)) * cubeLpNorm Q 2 φ

/-- The unit ball of the full classical fractional test norm. -/
def isDualTest {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) : Prop :=
  memH34 Q φ ∧ testNorm Q φ ≤ 1

/-- Pairing magnitudes against classical unit tests. -/
def valueSet {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) : Set ℝ :=
  {r | ∃ φ, isDualTest Q φ ∧ r = |cubeBesovPairing Q f φ|}

/-- The full classical negative norm, on its proved finite `L²` locus. -/
def negativeNorm {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) : ℝ :=
  sSup (valueSet Q f)

/-- A dimension-only comparison coefficient. -/
def comparisonConstant (d : ℕ) : ℝ :=
  (3 : ℝ) ^ ((d : ℝ) / 2) * Book.Ch01.Legacy.wspVsBsppConstant d *
    (d : ℝ) ^ ((3 / 4 : ℝ) + (d : ℝ) / 2)

theorem comparisonConstant_pos {d : ℕ} [NeZero d] : 0 < comparisonConstant d := by
  unfold comparisonConstant
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Book.Ch01.Legacy.wspVsBsppConstant_pos d))
    (Real.rpow_pos_of_pos (by exact_mod_cast (NeZero.pos d)) _)

private theorem kernel_bound {d : ℕ} (hd : 2 ≤ d) (φ : Vec d → ℝ)
    (z : Vec d × Vec d) :
    ‖Gagliardo.gagliardoKernel (3 / 4 : ℝ) 2 φ z‖ ≤
      (d : ℝ) ^ ((3 / 4 : ℝ) + (d : ℝ) / 2) * ‖kernel φ z‖ := by
  let a : ℝ := (3 / 4 : ℝ) + (d : ℝ) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  by_cases hz : z.1 = z.2
  · simp [Gagliardo.gagliardoKernel, kernel, hz]
  have hdist : 0 < dist z.1 z.2 := dist_pos.mpr hz
  have heuc : 0 < euclideanDist z.1 z.2 :=
    lt_of_lt_of_le hdist (dist_le_euclideanDist _ _)
  have hpow : (euclideanDist z.1 z.2) ^ a ≤
      (d : ℝ) ^ a * (dist z.1 z.2) ^ a := by
    rw [← Real.mul_rpow hdpos.le hdist.le]
    exact Real.rpow_le_rpow (euclideanDist_nonneg _ _)
      (euclideanDist_le_dimension_mul_dist _ _) ha.le
  have hweight : (dist z.1 z.2) ^ (-a) ≤
      (d : ℝ) ^ a * (euclideanDist z.1 z.2) ^ (-a) := by
    rw [Real.rpow_neg hdist.le, Real.rpow_neg heuc.le]
    apply (le_mul_inv_iff₀ (Real.rpow_pos_of_pos heuc a)).mpr
    apply (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hdist a)).mpr
    simpa [mul_comm] using hpow
  have hnorm := mul_le_mul_of_nonneg_right hweight (norm_nonneg (φ z.1 - φ z.2))
  simp only [Gagliardo.gagliardoKernel, Gagliardo.kernelExponent,
    ENNReal.toReal_ofNat, smul_eq_mul, kernel, norm_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg hdist.le _),
    abs_of_nonneg (Real.rpow_nonneg heuc.le _)]
  simpa only [a, Real.norm_eq_abs, mul_assoc] using hnorm

private theorem supKernel_measurable {d : ℕ} {Q : TriadicCube d} {φ : Vec d → ℝ}
    (hφ : MemLp φ 2 (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (Gagliardo.gagliardoKernel (3 / 4 : ℝ) 2 φ)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  have hcube : AEStronglyMeasurable φ (cubeMeasure Q) := by
    refine ⟨hφ.1.mk _, hφ.1.stronglyMeasurable_mk, ?_⟩
    exact Gagliardo.ae_normalizedCubeMeasure_iff.mp hφ.1.ae_eq_mk
  have hfst := hφ.1.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst (ν := cubeMeasure Q))
  have hsnd := hcube.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_snd (μ := normalizedCubeMeasure Q))
  have hw : Measurable (fun z : Vec d × Vec d =>
      dist z.1 z.2 ^ (-Gagliardo.kernelExponent d (3 / 4 : ℝ) 2)) :=
    measurable_dist.pow measurable_const
  exact hw.aestronglyMeasurable.smul (hfst.sub hsnd)

private theorem supSeminorm_bound {d : ℕ} (hd : 2 ≤ d) {Q : TriadicCube d}
    {φ : Vec d → ℝ} (hφ : memH34 Q φ) :
    Gagliardo.MemWsp Q (3 / 4 : ℝ) 2 φ ∧
    Book.Ch01.Legacy.fractionalSobolevSeminorm Q (3 / 4 : ℝ) 2 φ ≤
      (d : ℝ) ^ ((3 / 4 : ℝ) + (d : ℝ) / 2) * seminorm Q φ := by
  let D : ℝ := (d : ℝ) ^ ((3 / 4 : ℝ) + (d : ℝ) / 2)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (μ := Gagliardo.gagliardoCubeMeasure Q)
    (Filter.Eventually.of_forall (kernel_bound hd φ)) (2 : ℝ≥0∞)
  have hfinite : ENNReal.ofReal D * eLpNorm (kernel φ) 2
      (Gagliardo.gagliardoCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hφ.2.2.ne
  have hmem : Gagliardo.MemWsp Q (3 / 4 : ℝ) 2 φ :=
    ⟨supKernel_measurable hφ.1, lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfinite)⟩
  refine ⟨hmem, ?_⟩
  have hr := ENNReal.toReal_mono hfinite hle
  simpa [Book.Ch01.Legacy.fractionalSobolevSeminorm,
    Gagliardo.cubeGagliardoSeminorm, Gagliardo.cubeGagliardoESeminorm,
    seminorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD, D] using hr

private theorem partialSeminorm_bound {d : ℕ} [NeZero d] {Q : TriadicCube d}
    {φ : Vec d → ℝ} (hφ : MemLp φ 2 (normalizedCubeMeasure Q))
    (hW : Gagliardo.MemWsp Q (3 / 4 : ℝ) 2 φ) (N : ℕ) :
    cubeBesovPartialSeminorm Q (3 / 4 : ℝ) 2 2 N φ ≤
      (3 : ℝ) ^ ((d : ℝ) / 2) * Book.Ch01.Legacy.wspVsBsppConstant d *
        Book.Ch01.Legacy.fractionalSobolevSeminorm Q (3 / 4 : ℝ) 2 φ := by
  obtain ⟨ψ, hψ, heq⟩ := hφ.1.aemeasurable
  have heqCube := Gagliardo.ae_normalizedCubeMeasure_iff.mp heq
  have hψW := (Gagliardo.memWsp_congr_ae heqCube).mp hW
  have hbound := Book.Ch01.Legacy.besovOverlapPartial_le_const_mul_gagliardo Q
    (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hψ (hφ.ae_eq heq) hψW N
  have hpart := Gagliardo.overlap_partialSeminorm_congr_ae
    (s := (3 / 4 : ℝ)) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (N := N) heqCube
  have hsemi := Gagliardo.cubeGagliardoESeminorm_congr_ae
    (s := (3 / 4 : ℝ)) (p := (2 : ℝ≥0∞)) heqCube
  have hbound' : cubeBesovOverlapPartialSeminorm Q (3 / 4 : ℝ) 2 2 N φ ≤
      Book.Ch01.Legacy.wspVsBsppConstant d *
        Book.Ch01.Legacy.fractionalSobolevSeminorm Q (3 / 4 : ℝ) 2 φ := by
    simpa [hpart, Book.Ch01.Legacy.fractionalSobolevSeminorm,
      Gagliardo.cubeGagliardoSeminorm, hsemi] using hbound
  have hdis := cubeBesovPartialSeminorm_le_three_rpow_mul_overlapPartialSeminorm
    Q (3 / 4 : ℝ) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) N φ
  calc
    _ ≤ (3 : ℝ) ^ ((d : ℝ) / 2) *
        cubeBesovOverlapPartialSeminorm Q (3 / 4 : ℝ) 2 2 N φ := by simpa using hdis
    _ ≤ _ := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbound'
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((d : ℝ) / 2))


private theorem conj_two : cubeBesovConjExponent 2 = 2 := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

private theorem one_le_comparisonConstant {d : ℕ} (hd : 2 ≤ d) :
    1 ≤ comparisonConstant d := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity))
      (Book.Ch01.Legacy.one_le_wspVsBsppConstant d)
  · exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ d by omega)) (by positivity)

private theorem partialTestNorm_bound {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {Q : TriadicCube d} {φ : Vec d → ℝ} (hφ : isDualTest Q φ) (N : ℕ) :
    cubeBesovDualTestNorm Q (3 / 4 : ℝ) 2 2 N φ ≤ comparisonConstant d := by
  obtain ⟨hW, hsup⟩ := supSeminorm_bound hd hφ.1
  have hpart := partialSeminorm_bound hφ.1.1 hW N
  have hA : 0 ≤ (3 : ℝ) ^ ((d : ℝ) / 2) * Book.Ch01.Legacy.wspVsBsppConstant d :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Book.Ch01.Legacy.wspVsBsppConstant_pos d).le
  have hsemi : cubeBesovPartialSeminorm Q (3 / 4 : ℝ) 2 2 N φ ≤
      comparisonConstant d * seminorm Q φ := by
    exact hpart.trans (by simpa [comparisonConstant, mul_assoc] using
      mul_le_mul_of_nonneg_left hsup hA)
  have hmean : ‖cubeAverage Q φ‖ ≤ cubeLpNorm Q 2 φ :=
    norm_cubeAverage_le_cubeLpNorm_two Q φ hφ.1.1
  have hweight : 0 ≤ cubeScaleFactor Q ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_nonneg (by unfold cubeScaleFactor; positivity) _
  have hmean' : cubeScaleFactor Q ^ (-(3 / 4 : ℝ)) * ‖cubeAverage Q φ‖ ≤
      comparisonConstant d *
        (cubeScaleFactor Q ^ (-(3 / 4 : ℝ)) * cubeLpNorm Q 2 φ) := by
    exact (mul_le_mul_of_nonneg_left hmean hweight).trans
      (le_mul_of_one_le_left (mul_nonneg hweight (cubeLpNorm_nonneg Q 2 φ))
        (one_le_comparisonConstant hd))
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top _ _ _ _ _ _ (by rw [conj_two]; norm_num),
    conj_two, cubeBesovPartialNorm]
  calc
    _ ≤ comparisonConstant d * seminorm Q φ + comparisonConstant d *
        (cubeScaleFactor Q ^ (-(3 / 4 : ℝ)) * cubeLpNorm Q 2 φ) :=
      add_le_add hsemi hmean'
    _ = comparisonConstant d * testNorm Q φ := by rw [testNorm, mul_add]
    _ ≤ comparisonConstant d := by
      simpa using mul_le_mul_of_nonneg_left hφ.2 (comparisonConstant_pos (d := d)).le

private theorem scaledTest {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {Q : TriadicCube d} {φ : Vec d → ℝ} (hφ : isDualTest Q φ) :
    CubeBesovDualFullTest Q (3 / 4 : ℝ) 2 2
      (fun x => (comparisonConstant d)⁻¹ * φ x) := by
  apply cubeBesovDualFullTest_two_two_of_uniform_bound Q (3 / 4 : ℝ) φ
    (comparisonConstant_pos (d := d)) (partialTestNorm_bound hd hφ)
  intro j R hR
  rw [conj_two]
  exact (memLp_on_descendant_of_memLp hR hφ.1.1).sub (memLp_const _)

/-- The classical unit ball gives bounded pairings with every L² field. -/
theorem pairing_le_mul_dualFullNorm {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (f : Vec d → ℝ) (hd : 2 ≤ d) (hf : MemLp f 2 (normalizedCubeMeasure Q))
    {φ : Vec d → ℝ} (hφ : isDualTest Q φ) :
    |cubeBesovPairing Q f φ| ≤
      comparisonConstant d * cubeBesovDualFullNorm Q (3 / 4 : ℝ) 2 2 f := by
  have hbound := abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp
    Q (3 / 4 : ℝ) 2 2 f (fun x => (comparisonConstant d)⁻¹ * φ x)
    (by norm_num) hf (by norm_num) (by norm_num) (by rw [conj_two]; norm_num)
    (by norm_num) (scaledTest hd hφ)
  rw [cubeBesovPairing_const_mul_right, abs_mul,
    abs_of_pos (inv_pos.mpr (comparisonConstant_pos (d := d)))] at hbound
  exact (inv_mul_le_iff₀ (comparisonConstant_pos (d := d))).mp hbound

/-- Zero is an admissible classical test. -/
theorem isDualTest_zero {d : ℕ} (Q : TriadicCube d) :
    isDualTest Q (fun _ => 0) := by
  have hk : kernel (fun _ : Vec d => (0 : ℝ)) = 0 := by
    funext z
    simp [kernel]
  refine ⟨⟨(memLp_const (0 : ℝ)), ?_⟩, ?_⟩
  · rw [hk]
    exact (memLp_const (0 : ℝ))
  · simp [testNorm, seminorm, hk, cubeLpNorm]

/-- The pairing set is nonempty independently of any regularity of the field. -/
theorem valueSet_nonempty {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    (valueSet Q f).Nonempty := by
  refine ⟨0, fun _ => 0, isDualTest_zero Q, ?_⟩
  simp [cubeBesovPairing, cubeAverage_const]

/-- On L² fields the real supremum cannot collapse through unboundedness. -/
theorem valueSet_bddAbove {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (f : Vec d → ℝ) (hd : 2 ≤ d) (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    BddAbove (valueSet Q f) := by
  refine ⟨comparisonConstant d * cubeBesovDualFullNorm Q (3 / 4 : ℝ) 2 2 f, ?_⟩
  rintro r ⟨φ, hφ, rfl⟩
  exact pairing_le_mul_dualFullNorm Q f hd hf hφ

/-- The full Euclidean classical negative norm is dominated by the legacy
partition dual, with a coefficient depending only on the dimension. -/
theorem negativeNorm_le_mul_dualFullNorm {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (f : Vec d → ℝ) (hd : 2 ≤ d) (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    negativeNorm Q f ≤
      comparisonConstant d * cubeBesovDualFullNorm Q (3 / 4 : ℝ) 2 2 f := by
  apply csSup_le (valueSet_nonempty Q f)
  rintro r ⟨φ, hφ, rfl⟩
  exact pairing_le_mul_dualFullNorm Q f hd hf hφ

/-- Each admissible pairing is bounded by the genuine finite classical dual. -/
theorem pairing_le_negativeNorm {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (f : Vec d → ℝ) (hd : 2 ≤ d) (hf : MemLp f 2 (normalizedCubeMeasure Q))
    {φ : Vec d → ℝ} (hφ : isDualTest Q φ) :
    |cubeBesovPairing Q f φ| ≤ negativeNorm Q f :=
  le_csSup (valueSet_bddAbove Q f hd hf) ⟨φ, hφ, rfl⟩

end
end Homogenization.ClassicalSobolev34
