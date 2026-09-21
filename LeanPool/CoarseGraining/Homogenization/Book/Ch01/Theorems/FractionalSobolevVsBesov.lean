/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.BesovLeGagliardo
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.GagliardoLeBesov
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CongruenceAE

/-!
# Legacy fractional Sobolev versus Besov seminorms (CG Lemma 1.3)

Legacy, restricted real-valued overlap-comparison lane.  On every triadic
cube, its volume-normalized fractional Sobolev (Gagliardo) seminorm and older
overlapping triadic Besov presentation `B^s_{p,p}` are equivalent, with a
constant depending only on the dimension — uniformly in `s ∈ (0,1]`,
`p ∈ [1,∞)`, and the cube scale.

Constant accounting (each factor uniform in `s, p`):

* upper bound (`B ≤ C·W`): overlap multiplicity `3^d` and the backwards
  geometric pair tail `≤ 2`, total `2·3^d` at power `p`;
* lower bound (`W ≤ C·B`): triangle split `2·2^p ≤ 4^p`, shell-versus-depth
  kernel slack `9^{sp+d} ≤ (9^{d+1})^p` (uses `s ≤ 1`), center count
  `3^d ≤ (3^d)^p`, shell reindexing `2 ≤ 2^p`; total `(2^3·3^{3d+2})^p`;
* both collapse to the single constant `wspVsBsppConstant d = 2^3·3^{3d+2}`
  after the `p`-th root, since `(X^p)^{1/p} = X` and `Y^{1/p} ≤ Y` for `Y ≥ 1`.

The Lean proof replaces the manuscript's partition-of-unity argument by a
discrete-annulus argument.  Within this restricted lane the comparison shape
is unchanged, but its Gagliardo kernel uses the ambient sup-distance, absorbed
into `C(d)`.  Its overlap Besov side is the older finite-truncation /
real-`sSup` presentation.  This is not the new exact Euclidean / `ENNReal`
manuscript API.

The packaged hypothesis `MemFractionalSobolev` (`MemLp` + `MemWsp`) is the
legacy analogue of `u ∈ W^{s,p}(□)` for this ambient-sup-distance kernel.  No
measurability of the representative is assumed in the packaged theorem (the
statement is a.e.-invariant, and a measurable representative is transported
through `CongruenceAE`).  The `BddAbove` side condition of the infinite-scale
Besov seminorm is *derived*, not assumed.
-/

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Legacy

/-- The legacy/restricted fractional Sobolev seminorm
`[u]_{W̲^{s,p}(□)}`, using the ambient sup-distance Gagliardo kernel. -/
noncomputable abbrev fractionalSobolevSeminorm {d : ℕ} (Q : Cube d) (s : ℝ)
    (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Gagliardo.cubeGagliardoSeminorm Q s p u

/-- The legacy/restricted overlapping Besov seminorm `[u]_{B̲^s_{p,p}(□)}`
in the finite-truncation / real-`sSup` presentation. -/
noncomputable abbrev positiveBesovOverlapSeminormDiagonal {d : ℕ} (Q : Cube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  cubeBesovOverlapSeminorm Q s p p u

/-- Legacy/restricted packaged membership: `L^p` on the cube with finite
ambient-sup-distance Gagliardo seminorm.  This is not the exact Euclidean /
`ENNReal` manuscript `u ∈ W^{s,p}(□_m)` API; no measurability of the
representative is assumed (it is recovered a.e. from `MemLp`). -/
def MemFractionalSobolev {d : ℕ} (Q : Cube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (normalizedCubeMeasure Q) ∧ Gagliardo.MemWsp Q s p u

theorem MemFractionalSobolev.memLp {d : ℕ} {Q : Cube d} {s : ℝ}
    {p : ℝ≥0∞} {u : Vec d → ℝ} (h : MemFractionalSobolev Q s p u) :
    MeasureTheory.MemLp u p (normalizedCubeMeasure Q) := h.1

theorem MemFractionalSobolev.memWsp {d : ℕ} {Q : Cube d} {s : ℝ}
    {p : ℝ≥0∞} {u : Vec d → ℝ} (h : MemFractionalSobolev Q s p u) :
    Gagliardo.MemWsp Q s p u := h.2

/-- The legacy/restricted overlap-comparison constant; it depends on the
dimension only and is fixed before every other quantifier. -/
noncomputable def wspVsBsppConstant (d : ℕ) : ℝ :=
  2 ^ 3 * 3 ^ (3 * d + 2)

theorem one_le_wspVsBsppConstant (d : ℕ) : 1 ≤ wspVsBsppConstant d := by
  have h3 : (1 : ℝ) ≤ 3 ^ (3 * d + 2) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 2 ^ 3 := by norm_num
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ 2 ^ 3 * 3 ^ (3 * d + 2) := mul_le_mul h2 h3 (by norm_num) (by positivity)

theorem wspVsBsppConstant_pos (d : ℕ) : 0 < wspVsBsppConstant d :=
  lt_of_lt_of_le one_pos (one_le_wspVsBsppConstant d)

/-- `toReal` of the L-direction `ℝ≥0∞` constant is the note constant. -/
theorem gagliardoBesovLowerConstant_toReal (d : ℕ) :
    (Gagliardo.gagliardoBesovLowerConstant d).toReal = wspVsBsppConstant d := by
  rw [Gagliardo.gagliardoBesovLowerConstant, wspVsBsppConstant]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow]

section MainTheorem

variable {d : ℕ} [NeZero d] (Q : Cube d) {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}

/-- Legacy upper bound: every finite-depth overlap-Besov partial seminorm is
controlled by the ambient-sup-distance Gagliardo seminorm. -/
theorem besovOverlapPartial_le_const_mul_gagliardo
    (hs : 0 < s) (hp : 1 ≤ p) (hpt : p ≠ ∞) (humeas : Measurable u)
    (hu : MemLp u p (normalizedCubeMeasure Q))
    (hW : Gagliardo.MemWsp Q s p u) (N : ℕ) :
    cubeBesovOverlapPartialSeminorm Q s p p N u ≤
      wspVsBsppConstant d * fractionalSobolevSeminorm Q s p u := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpr1 : (1 : ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hpt hp
  have hGE_ne : Gagliardo.cubeGagliardoESeminorm Q s p u ≠ ∞ :=
    hW.eSeminorm_lt_top.ne
  have hGdef : fractionalSobolevSeminorm Q s p u =
      (Gagliardo.cubeGagliardoESeminorm Q s p u).toReal := rfl
  have hGnonneg : 0 ≤ fractionalSobolevSeminorm Q s p u :=
    ENNReal.toReal_nonneg
  have hU := Gagliardo.ofReal_partialSeminorm_rpow_le_gagliardo Q hs.le hp hpt
    humeas hu N
  have hc_ne : (2 * 3 ^ d : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp))
  have hR_ne : (2 * 3 ^ d : ℝ≥0∞) *
      Gagliardo.cubeGagliardoESeminorm Q s p u ^ p.toReal ≠ ∞ :=
    ENNReal.mul_ne_top hc_ne (ENNReal.rpow_ne_top_of_nonneg hpr.le hGE_ne)
  have hc_toReal : ((2 * 3 ^ d : ℝ≥0∞)).toReal = (2 * 3 ^ d : ℝ) := by
    simp [ENNReal.toReal_mul, ENNReal.toReal_pow]
  have hreal : cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal ≤
      (2 * 3 ^ d : ℝ) * fractionalSobolevSeminorm Q s p u ^ p.toReal := by
    have h1 := (ENNReal.ofReal_le_iff_le_toReal hR_ne).1 hU
    have h2 : ((2 * 3 ^ d : ℝ≥0∞) *
        Gagliardo.cubeGagliardoESeminorm Q s p u ^ p.toReal).toReal =
        (2 * 3 ^ d : ℝ) * fractionalSobolevSeminorm Q s p u ^ p.toReal := by
      rw [ENNReal.toReal_mul, hc_toReal, hGdef, ENNReal.toReal_rpow]
    rw [← h2]
    exact h1
  -- take the `p`-th root
  have hpartial_nonneg : 0 ≤ cubeBesovOverlapPartialSeminorm Q s p p N u :=
    cubeBesovOverlapPartialSeminorm_nonneg Q s p p N u
  have hc0 : (1 : ℝ) ≤ 2 * 3 ^ d := by
    have h3 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    linarith
  have hroot : cubeBesovOverlapPartialSeminorm Q s p p N u ≤
      (2 * 3 ^ d : ℝ) ^ (1 / p.toReal) * fractionalSobolevSeminorm Q s p u := by
    have h2 : cubeBesovOverlapPartialSeminorm Q s p p N u =
        (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal) ^
          (1 / p.toReal) := by
      rw [one_div, Real.rpow_rpow_inv hpartial_nonneg hpr.ne']
    rw [h2]
    calc (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal) ^ (1 / p.toReal)
        ≤ ((2 * 3 ^ d : ℝ) *
            fractionalSobolevSeminorm Q s p u ^ p.toReal) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hpartial_nonneg _) hreal
            (by positivity)
      _ = (2 * 3 ^ d : ℝ) ^ (1 / p.toReal) *
            fractionalSobolevSeminorm Q s p u := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hGnonneg _),
            one_div, Real.rpow_rpow_inv hGnonneg hpr.ne']
  refine hroot.trans (mul_le_mul ?_ le_rfl hGnonneg
    (le_of_lt (wspVsBsppConstant_pos d)))
  have hexp : (2 * 3 ^ d : ℝ) ^ (1 / p.toReal) ≤ 2 * 3 ^ d := by
    have h1p : 1 / p.toReal ≤ 1 := by
      rw [div_le_one hpr]
      exact hpr1
    calc (2 * 3 ^ d : ℝ) ^ (1 / p.toReal) ≤ (2 * 3 ^ d : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hc0 h1p
      _ = 2 * 3 ^ d := Real.rpow_one _
  refine hexp.trans ?_
  rw [wspVsBsppConstant]
  have h3 : (3 : ℝ) ^ d ≤ 3 ^ (3 * d + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith [pow_nonneg (show (0:ℝ) ≤ 3 by norm_num) d]

/-- Legacy/restricted two-sided overlap comparison:
`C(d)⁻¹·[u]_{W̲^{s,p}} ≤ [u]_{B̲^s_{p,p}} ≤ C(d)·[u]_{W̲^{s,p}}` on every
triadic cube, with `C(d) = wspVsBsppConstant d` fixed before all other
quantifiers, uniformly in `s ∈ (0,1]`, `p ∈ [1,∞)`, and the cube. -/
theorem fractionalSobolevVsBesovSeminorms
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (humeas : Measurable u) (hu : MemLp u p (normalizedCubeMeasure Q))
    (hW : Gagliardo.MemWsp Q s p u) :
    (wspVsBsppConstant d)⁻¹ * fractionalSobolevSeminorm Q s p u ≤
        positiveBesovOverlapSeminormDiagonal Q s p u ∧
      positiveBesovOverlapSeminormDiagonal Q s p u ≤
        wspVsBsppConstant d * fractionalSobolevSeminorm Q s p u := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hGE_ne : Gagliardo.cubeGagliardoESeminorm Q s p u ≠ ∞ :=
    hW.eSeminorm_lt_top.ne
  have hGdef : fractionalSobolevSeminorm Q s p u =
      (Gagliardo.cubeGagliardoESeminorm Q s p u).toReal := rfl
  have hGnonneg : 0 ≤ fractionalSobolevSeminorm Q s p u :=
    ENNReal.toReal_nonneg
  have hBdd : BddAbove (cubeBesovOverlapSeminormValueSet Q s p p u) :=
    Gagliardo.besovOverlapSeminormValueSet_bddAbove_of_gagliardo Q hs.le hp hpt
      humeas hu hGE_ne
  have hpartial_le : ∀ N, cubeBesovOverlapPartialSeminorm Q s p p N u ≤
      positiveBesovOverlapSeminormDiagonal Q s p u := fun N =>
    cubeBesovOverlapPartialSeminorm_le_cubeBesovOverlapSeminorm_of_bddAbove
      Q s p p u hBdd N
  have hBnonneg : 0 ≤ positiveBesovOverlapSeminormDiagonal Q s p u :=
    (cubeBesovOverlapPartialSeminorm_nonneg Q s p p 0 u).trans (hpartial_le 0)
  constructor
  · -- lower bound: C⁻¹ · W ≤ B
    have hL := Gagliardo.gagliardo_rpow_le_iSup_partialSeminorm Q hs.le hs1 hp
      hpt humeas hu
    have hsup_le : (⨆ N : ℕ, ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal)) ≤
        ENNReal.ofReal (positiveBesovOverlapSeminormDiagonal Q s p u ^ p.toReal) := by
      refine iSup_le fun N => ENNReal.ofReal_le_ofReal ?_
      exact Real.rpow_le_rpow
        (cubeBesovOverlapPartialSeminorm_nonneg Q s p p N u)
        (hpartial_le N) hpr.le
    have hKE_ne : Gagliardo.gagliardoBesovLowerConstant d ≠ ∞ := by
      rw [Gagliardo.gagliardoBesovLowerConstant]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
        (ENNReal.pow_ne_top (by simp))
    have hKEpr_ne : (Gagliardo.gagliardoBesovLowerConstant d) ^ p.toReal ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hpr.le hKE_ne
    have hRHS_ne : (Gagliardo.gagliardoBesovLowerConstant d) ^ p.toReal *
        ENNReal.ofReal (positiveBesovOverlapSeminormDiagonal Q s p u ^ p.toReal)
          ≠ ∞ :=
      ENNReal.mul_ne_top hKEpr_ne ENNReal.ofReal_ne_top
    have hchain : Gagliardo.cubeGagliardoESeminorm Q s p u ^ p.toReal ≤
        (Gagliardo.gagliardoBesovLowerConstant d) ^ p.toReal *
          ENNReal.ofReal
            (positiveBesovOverlapSeminormDiagonal Q s p u ^ p.toReal) :=
      hL.trans (mul_le_mul_right hsup_le _)
    -- to the reals
    have hreal : fractionalSobolevSeminorm Q s p u ^ p.toReal ≤
        (wspVsBsppConstant d) ^ p.toReal *
          positiveBesovOverlapSeminormDiagonal Q s p u ^ p.toReal := by
      have h1 : fractionalSobolevSeminorm Q s p u ^ p.toReal =
          (Gagliardo.cubeGagliardoESeminorm Q s p u ^ p.toReal).toReal := by
        rw [hGdef, ENNReal.toReal_rpow]
      have h2 : ((Gagliardo.gagliardoBesovLowerConstant d) ^ p.toReal *
          ENNReal.ofReal
            (positiveBesovOverlapSeminormDiagonal Q s p u ^ p.toReal)).toReal =
          (wspVsBsppConstant d) ^ p.toReal *
            positiveBesovOverlapSeminormDiagonal Q s p u ^ p.toReal := by
        rw [ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (Real.rpow_nonneg hBnonneg _),
          ← ENNReal.toReal_rpow, gagliardoBesovLowerConstant_toReal]
      rw [h1, ← h2]
      exact ENNReal.toReal_mono hRHS_ne hchain
    -- take roots
    have hroot : fractionalSobolevSeminorm Q s p u ≤
        wspVsBsppConstant d * positiveBesovOverlapSeminormDiagonal Q s p u := by
      have h2 : fractionalSobolevSeminorm Q s p u =
          (fractionalSobolevSeminorm Q s p u ^ p.toReal) ^ (1 / p.toReal) := by
        rw [one_div, Real.rpow_rpow_inv hGnonneg hpr.ne']
      rw [h2]
      calc (fractionalSobolevSeminorm Q s p u ^ p.toReal) ^ (1 / p.toReal)
          ≤ ((wspVsBsppConstant d) ^ p.toReal *
              positiveBesovOverlapSeminormDiagonal Q s p u ^ p.toReal) ^
                (1 / p.toReal) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hGnonneg _) hreal
              (by positivity)
        _ = wspVsBsppConstant d * positiveBesovOverlapSeminormDiagonal Q s p u := by
            rw [Real.mul_rpow
              (Real.rpow_nonneg (le_of_lt (wspVsBsppConstant_pos d)) _)
              (Real.rpow_nonneg hBnonneg _), one_div,
              Real.rpow_rpow_inv (le_of_lt (wspVsBsppConstant_pos d)) hpr.ne',
              Real.rpow_rpow_inv hBnonneg hpr.ne']
    rw [inv_mul_le_iff₀ (wspVsBsppConstant_pos d)]
    exact hroot
  · -- upper bound: B ≤ C · W
    refine csSup_le (cubeBesovOverlapSeminormValueSet_nonempty Q s p p u) ?_
    rintro x ⟨N, rfl⟩
    exact besovOverlapPartial_le_const_mul_gagliardo Q hs hp hpt humeas hu hW N

/-- The legacy/restricted two-sided overlap comparison with its packaged
membership hypothesis.  No measurability hypothesis: the statement is
invariant under a.e.-modification, and a measurable representative is
extracted from `MemLp` and transported back through the congruence lemmas. -/
theorem fractionalSobolevVsBesovSeminorms_of_memFractionalSobolev
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hu : MemFractionalSobolev Q s p u) :
    (wspVsBsppConstant d)⁻¹ * fractionalSobolevSeminorm Q s p u ≤
        positiveBesovOverlapSeminormDiagonal Q s p u ∧
      positiveBesovOverlapSeminormDiagonal Q s p u ≤
        wspVsBsppConstant d * fractionalSobolevSeminorm Q s p u := by
  obtain ⟨g, hgmeas, haen⟩ := hu.memLp.aestronglyMeasurable.aemeasurable
  have hae : u =ᵐ[Homogenization.cubeMeasure Q] g :=
    Gagliardo.ae_normalizedCubeMeasure_iff.1 haen
  have hgLp : MeasureTheory.MemLp g p (normalizedCubeMeasure Q) :=
    hu.memLp.ae_eq haen
  have hgW : Gagliardo.MemWsp Q s p g :=
    (Gagliardo.memWsp_congr_ae hae).1 hu.memWsp
  have main := fractionalSobolevVsBesovSeminorms Q hs hs1 hp hpt hgmeas hgLp hgW
  have hWeq : fractionalSobolevSeminorm Q s p u =
      fractionalSobolevSeminorm Q s p g :=
    congrArg ENNReal.toReal (Gagliardo.cubeGagliardoESeminorm_congr_ae hae)
  have hBeq : positiveBesovOverlapSeminormDiagonal Q s p u =
      positiveBesovOverlapSeminormDiagonal Q s p g :=
    Gagliardo.cubeBesovOverlapSeminorm_congr_ae hae
  rw [hWeq, hBeq]
  exact main

end MainTheorem

end Legacy

end

end Ch01
end Book
end Homogenization
