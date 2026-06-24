/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.UpperBound.Recursive3Param.Value
import Mathlib.MeasureTheory.Integral.Prod

/-!
## Final bound for the 3-parameter recursive algorithm

This file completes the computation of `ClassicalAlgorithm.p recursive3ParamAlg` and derives the
numerical upper bound `p < 24118/100000`.
-/

namespace Distributed2Coloring

open MeasureTheory
open scoped unitInterval

namespace UpperBound
namespace Recursive3Param


open scoped ENNReal

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable abbrev μ : Measure Rand := (volume : Measure Rand)

lemma Iio_one_ae_eq_univ : (Set.Iio (1 : Rand) : Set Rand) =ᵐ[μ] (Set.univ : Set Rand) := by
  -- `Iio 1` and `univ` differ by a singleton, hence are a.e. equal.
  simp [μ]

/-- Outside the recursion square, `z0` reduces to `zBase`. -/
private lemma z0_eq_zBase {b c : Rand}
    (hsq : ¬ ((b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ))) :
    z0 b c = zBase b c := by
  classical
  unfold z0
  simp only [if_neg hsq]

/-- `zBase b c = t` when `b ≤ t ≤ c` (the base surface on the upper-right wedge with `b ≤ c`). -/
private lemma z0_eq_t_of_le_t_le {b c : Rand}
    (hsq : ¬ ((b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)))
    (hb : ¬ (b : ℝ) < t) (hc : (t : ℝ) ≤ c) : z0 b c = (t : ℝ) := by
  have hyt : (c : ℝ) ∈ Set.Ici (t : ℝ) := by simpa [Set.mem_Ici] using hc
  have hxt : ¬ (b : ℝ) ∈ Set.Iio (t : ℝ) := by simpa [Set.mem_Iio] using hb
  simp [z0_eq_zBase hsq, zBase, hyt, hxt]

/-- `zBase b c = 0` when `c < t ≤ b` (the lower-right "all-zero" wedge). -/
private lemma z0_eq_zero_of_lt_t_le {b c : Rand}
    (hsq : ¬ ((b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)))
    (hc : (c : ℝ) < t) (hb : (t : ℝ) ≤ b) : z0 b c = 0 := by
  have hyt : ¬ (c : ℝ) ∈ Set.Ici (t : ℝ) := by simpa [Set.mem_Ici] using not_le_of_gt hc
  have hxt : (b : ℝ) ∈ Set.Ici (t : ℝ) := by simpa [Set.mem_Ici] using hb
  simp [z0_eq_zBase hsq, zBase, hyt, hxt]

/-- `zBase b c = 1` when `b < t ≤ c` (the upper-left "all-one" wedge). -/
private lemma z0_eq_one_of_lt_t_le {b c : Rand}
    (hsq : ¬ ((b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)))
    (hb : (b : ℝ) < t) (hc : (t : ℝ) ≤ c) : z0 b c = 1 := by
  have hyt : (c : ℝ) ∈ Set.Ici (t : ℝ) := by simpa [Set.mem_Ici] using hc
  have hxt : (b : ℝ) ∈ Set.Iio (t : ℝ) := by simpa [Set.mem_Iio] using hb
  simp [z0_eq_zBase hsq, zBase, hyt, hxt]

/-- On the lower wedge `b, c < t` with `c < b`, the base surface equals `c`. -/
private lemma z0_eq_c_of_lt_t {b c : Rand}
    (hsq : ¬ ((b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)))
    (hc : (c : ℝ) < t) (hb : (b : ℝ) < t) (hcb : (c : ℝ) < b) : z0 b c = (c : ℝ) := by
  have hyt : ¬ (c : ℝ) ∈ Set.Ici (t : ℝ) := by simpa [Set.mem_Ici] using not_le_of_gt hc
  have hxt : ¬ (b : ℝ) ∈ Set.Ici (t : ℝ) := by simpa [Set.mem_Ici] using not_le_of_gt hb
  have hle : ¬ ((b : ℝ), (c : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := by
    simpa [Set.mem_setOf_eq] using not_le_of_gt hcb
  simp [z0_eq_zBase hsq, zBase, hyt, hxt, hle]

/-- On the lower wedge `b, c < t` with `b ≤ c`, the base surface equals `t`. -/
private lemma z0_eq_t_of_lt_t_le {b c : Rand}
    (hsq : ¬ ((b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)))
    (hc : (c : ℝ) < t) (hb : (b : ℝ) < t) (hbc : (b : ℝ) ≤ c) : z0 b c = (t : ℝ) := by
  have hyt : ¬ (c : ℝ) ∈ Set.Ici (t : ℝ) := by simpa [Set.mem_Ici] using not_le_of_gt hc
  have hxt : ¬ (b : ℝ) ∈ Set.Ici (t : ℝ) := by simpa [Set.mem_Ici] using not_le_of_gt hb
  have hle : ((b : ℝ), (c : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := by simpa [Set.mem_setOf_eq] using hbc
  simp [z0_eq_zBase hsq, zBase, hyt, hxt, hle]

/-- Inside the square, `c < t2 ≤ b`: the recursive surface equals `t1`. -/
private lemma z0_inSquare_eq_t1 {b c : Rand}
    (hsq : (b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ))
    (hc : (c : ℝ) < t2) (hb : (t2 : ℝ) ≤ b) : z0 b c = (t1 : ℝ) := by
  have hy : (c : ℝ) ∈ Set.Iio (t2 : ℝ) := hc
  have hx : (b : ℝ) ∈ Set.Ici (t2 : ℝ) := hb
  simp [z0, hsq, hy, hx]

/-- Inside the square, `t2 ≤ c` and `t2 ≤ b`: the recursive surface equals `t2`. -/
private lemma z0_inSquare_eq_t2_right {b c : Rand}
    (hsq : (b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ))
    (hc : (t2 : ℝ) ≤ c) (hb : (t2 : ℝ) ≤ b) : z0 b c = (t2 : ℝ) := by
  have hy : ¬ (c : ℝ) ∈ Set.Iio (t2 : ℝ) := by simp [Set.mem_Iio, not_lt.2 hc]
  have hx : ¬ (b : ℝ) ∈ Set.Iio (t2 : ℝ) := by simp [Set.mem_Iio, not_lt.2 hb]
  simp [z0, hsq, hy, hx]

/-- Inside the square, `c < t2`, `b < t2`, `c < b`: the recursive surface equals `c`. -/
private lemma z0_inSquare_eq_c {b c : Rand}
    (hsq : (b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ))
    (hc : (c : ℝ) < t2) (hb : (b : ℝ) < t2) (hcb : (c : ℝ) < b) : z0 b c = (c : ℝ) := by
  have hy : (c : ℝ) ∈ Set.Iio (t2 : ℝ) := hc
  have hx : ¬ (b : ℝ) ∈ Set.Ici (t2 : ℝ) := by simpa [Set.mem_Ici] using not_le_of_gt hb
  have hle : ¬ ((b : ℝ), (c : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := by
    simpa [Set.mem_setOf_eq] using not_le_of_gt hcb
  simp [z0, hsq, hy, hx, hle]

/-- Inside the square, `c < t2`, `b < t2`, `b ≤ c`: the recursive surface equals `t2`. -/
private lemma z0_inSquare_eq_t2_diag {b c : Rand}
    (hsq : (b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ))
    (hc : (c : ℝ) < t2) (hb : (b : ℝ) < t2) (hbc : (b : ℝ) ≤ c) : z0 b c = (t2 : ℝ) := by
  have hy : (c : ℝ) ∈ Set.Iio (t2 : ℝ) := hc
  have hx : ¬ (b : ℝ) ∈ Set.Ici (t2 : ℝ) := by simpa [Set.mem_Ici] using not_le_of_gt hb
  have hle : ((b : ℝ), (c : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := by simpa [Set.mem_setOf_eq] using hbc
  simp [z0, hsq, hy, hx, hle]

/-- Inside the square, `t2 ≤ c` and `b < t2`: the recursive surface equals `t`. -/
private lemma z0_inSquare_eq_t {b c : Rand}
    (hsq : (b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (c : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ))
    (hc : (t2 : ℝ) ≤ c) (hb : (b : ℝ) < t2) : z0 b c = (t : ℝ) := by
  have hy : ¬ (c : ℝ) ∈ Set.Iio (t2 : ℝ) := by simp [Set.mem_Iio, not_lt.2 hc]
  have hx : (b : ℝ) ∈ Set.Iio (t2 : ℝ) := hb
  simp [z0, hsq, hy, hx]

/-- `Iio b ∩ Iio a = Iio a` for `a ≤ b`. -/
private lemma Iio_inter_Iio_eq {a b : Rand} (hab : a ≤ b) :
    (Set.Iio b ∩ Set.Iio a : Set Rand) = Set.Iio a :=
  Set.inter_eq_right.2 (Set.Iio_subset_Iio hab)

/-- `Iio b \ Iio a = Ico a b` for `a ≤ b`. -/
private lemma Iio_diff_Iio_eq {a b : Rand} (_hab : a ≤ b) :
    (Set.Iio b \ Set.Iio a : Set Rand) = Set.Ico a b := by
  ext c
  simp only [Set.mem_sdiff, Set.mem_Iio, Set.mem_Ico, not_lt]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- `Ico a b ∩ Iio c = Ico a c` for `c ≤ b`. -/
private lemma Ico_inter_Iio_eq {a b c : Rand} (hcb : c ≤ b) :
    (Set.Ico a b ∩ Set.Iio c : Set Rand) = Set.Ico a c := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Iio]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, lt_of_lt_of_le h.2 hcb⟩, h.2⟩⟩

/-- `Ico a b \ Iio c = Ico c b` for `a ≤ c`. -/
private lemma Ico_diff_Iio_eq {a b c : Rand} (hac : a ≤ c) :
    (Set.Ico a b \ Set.Iio c : Set Rand) = Set.Ico c b := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_Iio, not_lt]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨le_trans hac h.1, h.2⟩, h.1⟩⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def constAboveT : ℝ≥0∞ :=
  ENNReal.ofReal (t : ℝ) * ENNReal.ofReal (t : ℝ) +
    ENNReal.ofReal (1 - (t : ℝ)) * ENNReal.ofReal (1 - (t : ℝ))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def gCt (c : Rand) : ℝ≥0∞ :=
  ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (t : ℝ) +
    ENNReal.ofReal (1 - (c : ℝ)) * ENNReal.ofReal (1 - (t : ℝ))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def constT1T : ℝ≥0∞ :=
  ENNReal.ofReal (t1 : ℝ) * ENNReal.ofReal (t : ℝ) +
    ENNReal.ofReal (1 - (t1 : ℝ)) * ENNReal.ofReal (1 - (t : ℝ))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def constT2T2 : ℝ≥0∞ :=
  ENNReal.ofReal (t2 : ℝ) * ENNReal.ofReal (t2 : ℝ) +
    ENNReal.ofReal (1 - (t2 : ℝ)) * ENNReal.ofReal (1 - (t2 : ℝ))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def gCt2 (c : Rand) : ℝ≥0∞ :=
  ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (t2 : ℝ) +
    ENNReal.ofReal (1 - (c : ℝ)) * ENNReal.ofReal (1 - (t2 : ℝ))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def gTB (b : Rand) : ℝ≥0∞ :=
  ENNReal.ofReal (t : ℝ) * ENNReal.ofReal (b : ℝ) +
    ENNReal.ofReal (1 - (t : ℝ)) * ENNReal.ofReal (1 - (b : ℝ))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def gT2B (b : Rand) : ℝ≥0∞ :=
  ENNReal.ofReal (t2 : ℝ) * ENNReal.ofReal (b : ℝ) +
    ENNReal.ofReal (1 - (t2 : ℝ)) * ENNReal.ofReal (1 - (b : ℝ))

/-- Generic linearization of an affine `ofReal`-product expression in one variable. -/
private lemma ofReal_affine_linear {x T : ℝ} (hx0 : 0 ≤ x) (h1x0 : 0 ≤ 1 - x)
    (hT0 : 0 ≤ T) (h1T0 : 0 ≤ 1 - T) (hA0 : 0 ≤ 2 * T - 1) :
    ENNReal.ofReal x * ENNReal.ofReal T + ENNReal.ofReal (1 - x) * ENNReal.ofReal (1 - T) =
      ENNReal.ofReal ((2 * T - 1) * x) + ENNReal.ofReal (1 - T) := by
  rw [← ENNReal.ofReal_mul hx0, ← ENNReal.ofReal_mul h1x0,
    ← ENNReal.ofReal_add (mul_nonneg hx0 hT0) (mul_nonneg h1x0 h1T0),
    ← ENNReal.ofReal_add (mul_nonneg hA0 hx0) h1T0]
  congr 1
  ring

lemma gCt_eq_linear (c : Rand) :
    gCt c =
      ENNReal.ofReal ((2 * (t : ℝ) - 1) * (c : ℝ)) + ENNReal.ofReal (1 - (t : ℝ)) := by
  rw [gCt, ofReal_affine_linear (x := (c : ℝ)) (T := (t : ℝ)) c.property.1
    (sub_nonneg.2 c.property.2) t.property.1 (sub_nonneg.2 (le_of_lt t_lt_one))
    (by simp only [t]; norm_num)]

lemma gCt2_eq_linear (c : Rand) :
    gCt2 c =
      ENNReal.ofReal ((2 * (t2 : ℝ) - 1) * (c : ℝ)) + ENNReal.ofReal (1 - (t2 : ℝ)) := by
  rw [gCt2, ofReal_affine_linear (x := (c : ℝ)) (T := (t2 : ℝ)) c.property.1
    (sub_nonneg.2 c.property.2) t2.property.1 (sub_nonneg.2 t2.property.2)
    (by simp only [t2]; norm_num)]

lemma gTB_eq_linear (b : Rand) :
    gTB b =
      ENNReal.ofReal ((2 * (t : ℝ) - 1) * (b : ℝ)) + ENNReal.ofReal (1 - (t : ℝ)) := by
  rw [gTB, mul_comm (ENNReal.ofReal (t : ℝ)), mul_comm (ENNReal.ofReal (1 - (t : ℝ))),
    ofReal_affine_linear (x := (b : ℝ)) (T := (t : ℝ)) b.property.1
    (sub_nonneg.2 b.property.2) t.property.1 (sub_nonneg.2 (le_of_lt t_lt_one))
    (by simp only [t]; norm_num)]

lemma gT2B_eq_linear (b : Rand) :
    gT2B b =
      ENNReal.ofReal ((2 * (t2 : ℝ) - 1) * (b : ℝ)) + ENNReal.ofReal (1 - (t2 : ℝ)) := by
  rw [gT2B, mul_comm (ENNReal.ofReal (t2 : ℝ)), mul_comm (ENNReal.ofReal (1 - (t2 : ℝ))),
    ofReal_affine_linear (x := (b : ℝ)) (T := (t2 : ℝ)) b.property.1
    (sub_nonneg.2 b.property.2) t2.property.1 (sub_nonneg.2 t2.property.2)
    (by simp only [t2]; norm_num)]

lemma innerBC_eq_constAboveT_of_t_lt_b {b c : Rand} (hb : t < b) (htc : t ≤ c)
    (hc1 : c ∈ (Set.Iio (1 : Rand) : Set Rand)) : innerBC b c = constAboveT := by
  have hc1' : (c : ℝ) < 1 := by simpa using hc1
  have hct : ¬ c < t := by exact not_lt.2 htc
  have haSlice : aSlice b c = Set.Iio t := by
    simp [aSlice_eq_of_t_lt_b (b := b) (c := c) hb, hct, hc1']
  have hz0 : z0 b c = (t : ℝ) :=
    z0_eq_t_of_le_t_le (fun h => (not_le_of_gt hb) h.1.2) (not_lt.2 hb.le) htc
  -- Now unfold `innerBC` and compute all measures.
  simp [innerBC, constAboveT, z0I, hz0, haSlice]

lemma innerBC_eq_zero_of_t_lt_b_of_c_lt_t {b c : Rand} (hb : t < b) (hc : c < t) :
    innerBC b c = 0 := by
  have haSlice : aSlice b c = Set.univ := by simp [aSlice_eq_of_t_lt_b (b := b) (c := c) hb, hc]
  have hz0 : z0 b c = 0 :=
    z0_eq_zero_of_lt_t_le (fun h => (not_le_of_gt hb) h.1.2) hc hb.le
  simp [innerBC, z0I, hz0, haSlice]

lemma innerBC_eq_gCt_of_t2_le_b_lt_t_of_c_lt_t1 {b c : Rand} (hb1 : t2 ≤ b) (hb2 : b < t)
    (hc : c < t1) : innerBC b c = gCt c := by
  have hc2 : c < t2 := lt_trans hc t1_lt_t2
  have haSlice : aSlice b c = Set.Iic t := by
    simp [aSlice_eq_of_t2_le_b_lt_t (b := b) (c := c) hb1 hb2, hc2]
  have hz0 : z0 b c = (c : ℝ) :=
    z0_eq_c_of_lt_t (fun h => (not_le_of_gt hc) h.2.1)
      (lt_trans hc (lt_trans t1_lt_t2 t2_lt_t)) hb2 (lt_of_lt_of_le (lt_trans hc t1_lt_t2) hb1)
  simp [innerBC, gCt, z0I, hz0, haSlice]

lemma innerBC_eq_constT1T_of_t2_le_b_lt_t_of_t1_le_c_of_c_lt_t2 {b c : Rand} (hb1 : t2 ≤ b)
    (hb2 : b < t) (hc1 : t1 ≤ c) (hc2 : c < t2) : innerBC b c = constT1T := by
  have haSlice : aSlice b c = Set.Iic t := by
    simp [aSlice_eq_of_t2_le_b_lt_t (b := b) (c := c) hb1 hb2, hc2]
  have hz0 : z0 b c = (t1 : ℝ) :=
    z0_inSquare_eq_t1 ⟨⟨le_trans t1_le_t2 hb1, hb2.le⟩, hc1, le_trans hc2.le t2_le_t⟩ hc2 hb1
  simp [innerBC, constT1T, z0I, hz0, haSlice]

lemma innerBC_eq_constT2T2_of_t2_le_b_lt_t_of_t2_le_c_of_c_lt_t {b c : Rand} (hb1 : t2 ≤ b)
    (hb2 : b < t) (hc1 : t2 ≤ c) (hc2 : c < t) : innerBC b c = constT2T2 := by
  have haSlice : aSlice b c = Set.Iio t2 := by
    have : ¬ c < t2 := not_lt.2 hc1
    simp [aSlice_eq_of_t2_le_b_lt_t (b := b) (c := c) hb1 hb2, this, hc2]
  have hz0 : z0 b c = (t2 : ℝ) :=
    z0_inSquare_eq_t2_right ⟨⟨le_trans t1_le_t2 hb1, hb2.le⟩, le_trans t1_le_t2 hc1, hc2.le⟩
      hc1 hb1
  simp [innerBC, constT2T2, z0I, hz0, haSlice]

/-!
### Pointwise formulas for the remaining `b`-ranges

For `b < t1` and for `t1 ≤ b < t2`, `innerBC b c` is still piecewise polynomial in `b,c`,
and can be integrated explicitly.
-/

lemma innerBC_eq_gCt_of_b_lt_t1_of_c_lt_b {b c : Rand} (hb : b < t1) (hc : c < b) :
    innerBC b c = gCt c := by
  have haSlice : aSlice b c = Set.Iio t := by simp [aSlice_eq_of_b_lt_t1 (b := b) (c := c) hb, hc]
  have hz0 : z0 b c = (c : ℝ) :=
    z0_eq_c_of_lt_t (fun h => (not_le_of_gt hb) h.1.1)
      (lt_trans (lt_trans hc hb) (lt_trans t1_lt_t2 t2_lt_t))
      (lt_trans hb (lt_trans t1_lt_t2 t2_lt_t)) hc
  simp [innerBC, gCt, z0I, hz0, haSlice]

lemma innerBC_eq_gTB_of_b_lt_t1_of_b_le_c_of_c_lt_t {b c : Rand} (hb : b < t1) (hc1 : b ≤ c)
    (hc2 : c < t) : innerBC b c = gTB b := by
  have hcb : ¬ c < b := not_lt_of_ge hc1
  have haSlice : aSlice b c = Set.Iic b := by
    simp [aSlice_eq_of_b_lt_t1 (b := b) (c := c) hb, hcb, hc2]
  have hz0 : z0 b c = (t : ℝ) :=
    z0_eq_t_of_lt_t_le (fun h => (not_le_of_gt hb) h.1.1) hc2
      (lt_trans hb (lt_trans t1_lt_t2 t2_lt_t)) hc1
  simp [innerBC, gTB, z0I, hz0, haSlice]

lemma innerBC_eq_zero_of_b_lt_t1_of_t_le_c {b c : Rand} (hb : b < t1) (hc : t ≤ c) :
    innerBC b c = 0 := by
  have hbt : (b : ℝ) < t := lt_trans hb (lt_trans t1_lt_t2 t2_lt_t)
  have hcb : ¬ c < b := not_lt_of_gt (lt_of_lt_of_le hbt hc)
  have hct : ¬ c < t := not_lt.2 hc
  have haSlice : aSlice b c = (∅ : Set Rand) := by
    simp [aSlice_eq_of_b_lt_t1 (b := b) (c := c) hb, hcb, hct]
  have hz0 : z0 b c = 1 :=
    z0_eq_one_of_lt_t_le (fun h => (not_le_of_gt hb) h.1.1) hbt hc
  simp [innerBC, z0I, hz0, haSlice]

lemma innerBC_eq_gCt_of_t1_le_b_lt_t2_of_c_lt_t1 {b c : Rand} (hb1 : t1 ≤ b) (hb2 : b < t2)
    (hc : c < t1) : innerBC b c = gCt c := by
  have haSlice : aSlice b c = Set.Iic t := by
    simp [aSlice_eq_of_t1_le_b_lt_t2 (b := b) (c := c) hb1 hb2, hc]
  have hz0 : z0 b c = (c : ℝ) :=
    z0_eq_c_of_lt_t (fun h => (not_le_of_gt hc) h.2.1)
      (lt_trans hc (lt_trans t1_lt_t2 t2_lt_t)) (lt_trans hb2 t2_lt_t)
      (lt_of_lt_of_le hc hb1)
  simp [innerBC, gCt, z0I, hz0, haSlice]

lemma innerBC_eq_gCt2_of_t1_le_b_lt_t2_of_t1_le_c_of_c_lt_b {b c : Rand} (hb1 : t1 ≤ b)
    (hb2 : b < t2) (hc1 : t1 ≤ c) (hc2 : c < b) : innerBC b c = gCt2 c := by
  have hc2' : (c : ℝ) < t2 := lt_trans hc2 hb2
  have haSlice : aSlice b c = Set.Iio t2 := by
    have : c < b := hc2
    simp [aSlice_eq_of_t1_le_b_lt_t2 (b := b) (c := c) hb1 hb2, hc1, this]
  have hz0 : z0 b c = (c : ℝ) :=
    z0_inSquare_eq_c ⟨⟨hb1, le_trans hb2.le t2_le_t⟩, hc1, le_trans hc2'.le t2_le_t⟩
      hc2' hb2 hc2
  simp [innerBC, gCt2, z0I, hz0, haSlice]

lemma innerBC_eq_gT2B_of_t1_le_b_lt_t2_of_b_le_c_of_c_lt_t2 {b c : Rand} (hb1 : t1 ≤ b)
    (hb2 : b < t2) (hc1 : b ≤ c) (hc2 : c < t2) : innerBC b c = gT2B b := by
  have hct1 : ¬ c < t1 := not_lt_of_ge (le_trans hb1 hc1)
  have haSlice : aSlice b c = Set.Iic b := by
    have : ¬ c < b := not_lt_of_ge hc1
    simp [aSlice_eq_of_t1_le_b_lt_t2 (b := b) (c := c) hb1 hb2, hct1, hc2, this]
  have hz0 : z0 b c = (t2 : ℝ) :=
    z0_inSquare_eq_t2_diag
      ⟨⟨hb1, le_trans hb2.le t2_le_t⟩, le_trans hb1 hc1, le_trans hc2.le t2_le_t⟩ hc2 hb2 hc1
  simp [innerBC, gT2B, z0I, hz0, haSlice]

lemma innerBC_eq_constT1T_of_t1_le_b_lt_t2_of_t2_le_c_of_c_lt_t {b c : Rand} (hb1 : t1 ≤ b)
    (hb2 : b < t2) (hc1 : t2 ≤ c) (hc2 : c < t) : innerBC b c = constT1T := by
  have hct1 : ¬ c < t1 := not_lt_of_ge (le_trans t1_le_t2 hc1)
  have hcb : ¬ c < b := by exact not_lt_of_gt (lt_of_lt_of_le hb2 hc1)
  have haSlice : aSlice b c = Set.Iio t1 := by
    have : ¬ c < t2 := not_lt.2 hc1
    simp [aSlice_eq_of_t1_le_b_lt_t2 (b := b) (c := c) hb1 hb2, hct1, hcb, this, hc2]
  have hz0 : z0 b c = (t : ℝ) :=
    z0_inSquare_eq_t ⟨⟨hb1, le_trans hb2.le t2_le_t⟩, le_trans t1_le_t2 hc1, hc2.le⟩ hc1 hb2
  simp [innerBC, constT1T, z0I, hz0, haSlice]
  ac_rfl

lemma innerBC_eq_zero_of_t1_le_b_lt_t2_of_t_lt_c {b c : Rand} (hb1 : t1 ≤ b) (hb2 : b < t2)
    (hc : t < c) : innerBC b c = 0 := by
  have hc2 : ¬ c < t2 := by exact not_lt_of_ge (le_trans t2_le_t (le_of_lt hc))
  have hct1 : ¬ c < t1 := by exact not_lt_of_ge (le_trans t1_le_t2 (le_trans t2_le_t (le_of_lt hc)))
  have hcb : ¬ c < b := by
    -- `b < t2 < t < c`.
    exact not_lt_of_gt (lt_trans (lt_trans hb2 t2_lt_t) hc)
  have haSlice : aSlice b c = (∅ : Set Rand) := by
    have : ¬ c < t := not_lt.2 (le_of_lt hc)
    simp [aSlice_eq_of_t1_le_b_lt_t2 (b := b) (c := c) hb1 hb2, hct1, hcb, hc2, this]
  have hz0 : z0 b c = 1 :=
    z0_eq_one_of_lt_t_le (fun h => (not_le_of_gt hc) h.2.2) (lt_trans hb2 t2_lt_t) hc.le
  simp [innerBC, z0I, hz0, haSlice]

/-!
### A `2D` triangle integral swap

We use Tonelli/Fubini to evaluate integrals over regions of the form `{(b,c) | c < b}` without
introducing subtractions at the `ℝ≥0∞` level.
-/

lemma lintegral_triangle_Iio (B : Rand) (f : Rand → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ b in Set.Iio B, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) =
      ∫⁻ c in Set.Iio B, f c * μ (Set.Ioo c B) ∂μ := by
  classical
  let F : Rand → Rand → ℝ≥0∞ := fun b c => if b < B ∧ c < b then f c else 0
  have hF : Measurable (Function.uncurry F) := by
    have hpred : MeasurableSet {p : Rand × Rand | p.1 < B ∧ p.2 < p.1} := by
      have h1 : MeasurableSet {p : Rand × Rand | p.1 < B} :=
        measurableSet_lt measurable_fst measurable_const
      have h2 : MeasurableSet {p : Rand × Rand | p.2 < p.1} :=
        measurableSet_lt measurable_snd measurable_fst
      have hEq :
          ({p : Rand × Rand | p.1 < B ∧ p.2 < p.1} :
              Set (Rand × Rand)) =
            {p : Rand × Rand | p.1 < B} ∩ {p : Rand × Rand | p.2 < p.1} := by
        ext p
        simp
      simpa [hEq] using h1.inter h2
    refine Measurable.ite (hp := hpred) ?_ measurable_const
    exact hf.comp (measurable_snd : Measurable fun p : Rand × Rand => p.2)
  have hswap :
      (∫⁻ b : Rand, ∫⁻ c : Rand, F b c ∂μ ∂μ) =
        ∫⁻ c : Rand, ∫⁻ b : Rand, F b c ∂μ ∂μ := by
    simpa [Function.uncurry] using
      (MeasureTheory.lintegral_lintegral_swap (μ := μ) (ν := μ) (f := F) hF.aemeasurable)
  have hL :
      (∫⁻ b in Set.Iio B, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) =
        ∫⁻ b : Rand, ∫⁻ c : Rand, F b c ∂μ ∂μ := by
    have hB : MeasurableSet (Set.Iio B : Set Rand) := by simp
    rw [← MeasureTheory.lintegral_indicator (μ := μ) hB (f := fun b => ∫⁻ c in Set.Iio b, f c ∂μ)]
    refine MeasureTheory.lintegral_congr fun b => ?_
    by_cases hb : b < B
    · have hIo : MeasurableSet (Set.Iio b : Set Rand) := by simp
      have :
        (∫⁻ c : Rand, F b c ∂μ) = ∫⁻ c in Set.Iio b, f c ∂μ := by
        -- rewrite `F b` as the indicator of `Iio b`.
        have hFc : (fun c : Rand => F b c) = (Set.Iio b).indicator f := by
          funext c
          by_cases hc : c < b <;> simp [F, hb, hc, Set.indicator, Set.mem_Iio]
        -- compute the `lintegral` of the indicator
        calc
          (∫⁻ c : Rand, F b c ∂μ) = ∫⁻ c : Rand, (Set.Iio b).indicator f c ∂μ := by simp [hFc]
          _ = ∫⁻ c in Set.Iio b, f c ∂μ := (MeasureTheory.lintegral_indicator (μ := μ) hIo f)
      have hbmem : b ∈ (Set.Iio B : Set Rand) := by simpa [Set.mem_Iio] using hb
      rw [this]
      simp [Set.indicator_of_mem hbmem]
    · have :
          (∫⁻ c : Rand, F b c ∂μ) = 0 := by
        have hFc : (fun c : Rand => F b c) = 0 := by
          funext c
          simp [F, hb]
        simp [hFc]
      have hbmem : b ∉ (Set.Iio B : Set Rand) := by simpa [Set.mem_Iio] using hb
      rw [this]
      simp [Set.indicator_of_notMem hbmem]
  have hR :
      (∫⁻ c : Rand, ∫⁻ b : Rand, F b c ∂μ ∂μ) =
        ∫⁻ c in Set.Iio B, f c * μ (Set.Ioo c B) ∂μ := by
    have hB : MeasurableSet (Set.Iio B : Set Rand) := by simp
    -- First, compute the inner `b`-integral pointwise in `c`.
    have hinner :
        (fun c : Rand => ∫⁻ b : Rand, F b c ∂μ) =
          (Set.Iio B).indicator (fun c => f c * μ (Set.Ioo c B)) := by
      funext c
      by_cases hcB : c < B
      · have hEq : (fun b : Rand => F b c) = (Set.Ioo c B).indicator (fun _ => f c) := by
          funext b
          by_cases hb : b < B <;> by_cases hcb : c < b <;>
            simp [F, hb, hcb, Set.indicator, Set.mem_Ioo]
        have hIoo : MeasurableSet (Set.Ioo c B : Set Rand) := by simp
        -- `lintegral` of an indicator of a constant function.
        simp [hEq, MeasureTheory.lintegral_indicator, hIoo, hcB]
      · have hEq : (fun b : Rand => F b c) = 0 := by
          funext b
          by_cases hb : b < B
          · have : ¬ c < b := not_lt_of_ge (le_trans (le_of_lt hb) (le_of_not_gt hcB))
            simp [F, hb, this]
          · simp [F, hb]
        -- Here `c ≥ B`, so the set `{b | b < B ∧ c < b}` is empty.
        have : (∫⁻ b : Rand, F b c ∂μ) = 0 := by
          rw [hEq]
          simpa using (MeasureTheory.lintegral_zero_fun (μ := μ) (α := Rand))
        simp [hcB, this]
    -- Use the pointwise formula and rewrite the outer integral as a set integral.
    have :
        (∫⁻ c : Rand, ∫⁻ b : Rand, F b c ∂μ ∂μ) =
          ∫⁻ c : Rand, (Set.Iio B).indicator (fun c => f c * μ (Set.Ioo c B)) c ∂μ := by
      refine MeasureTheory.lintegral_congr fun c => ?_
      simpa using congrArg (fun g => g c) hinner
    rw [this]
    exact
      (MeasureTheory.lintegral_indicator (μ := μ) (by simp)
        (f := fun c => f c * μ (Set.Ioo c B)))
  -- Put it together.
  calc
    (∫⁻ b in Set.Iio B, ∫⁻ c in Set.Iio b, f c ∂μ ∂μ) =
        ∫⁻ b : Rand, ∫⁻ c : Rand, F b c ∂μ ∂μ := hL
    _ = ∫⁻ c : Rand, ∫⁻ b : Rand, F b c ∂μ ∂μ := hswap
    _ = ∫⁻ c in Set.Iio B, f c * μ (Set.Ioo c B) ∂μ := hR

lemma lintegral_innerBC_Iio_one_of_t_lt_b {b : Rand} (hb : t < b) :
    (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
      constAboveT * (μ (Set.Ico t (1 : Rand))) := by
  classical
  have htmeas : MeasurableSet (Set.Iio t : Set Rand) := by measurability
  have hsplit :=
    (MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
      (A := (Set.Iio (1 : Rand) : Set Rand)) (B := (Set.Iio t : Set Rand)) htmeas)
  have hIio : ((Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t) = Set.Iio t :=
    Iio_inter_Iio_eq t_lt_one.le
  have hdiff : ((Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t) = Set.Ico t (1 : Rand) :=
    Iio_diff_Iio_eq t_lt_one.le
  have hzero :
      (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t, innerBC b c ∂μ) = 0 := by
    have :
        Set.EqOn (fun c : Rand => innerBC b c) 0 (Set.Iio t : Set Rand) := by
      intro c hc
      simpa using innerBC_eq_zero_of_t_lt_b_of_c_lt_t (b := b) (c := c) hb hc
    simpa [hIio] using (MeasureTheory.setLIntegral_eq_zero (μ := μ) htmeas this)
  have hconst :
      (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t, innerBC b c ∂μ) =
        constAboveT * μ (Set.Ico t (1 : Rand)) := by
    have hs : MeasurableSet (Set.Ico t (1 : Rand) : Set Rand) := by measurability
    have :
        Set.EqOn (fun c : Rand => innerBC b c) (fun _ => constAboveT)
          (Set.Ico t (1 : Rand) : Set Rand) := by
      intro c hc
      exact innerBC_eq_constAboveT_of_t_lt_b (b := b) (c := c) hb hc.1 hc.2
    calc
      (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t, innerBC b c ∂μ) =
          ∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ := by simp [hdiff]
      _ = ∫⁻ _c in Set.Ico t (1 : Rand), constAboveT ∂μ := by
            exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs this
      _ = constAboveT * μ (Set.Ico t (1 : Rand)) := by simp
  -- Use the splitting identity.
  have hsplit' :
      (∫⁻ c in Set.Iio t, innerBC b c ∂μ) +
          ∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ =
        ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ := by
    simpa [hIio, hdiff] using hsplit
  -- Replace terms.
  have hco :
      (∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ) =
        constAboveT * μ (Set.Ico t (1 : Rand)) := by
    simpa [hdiff] using hconst
  have hio : (∫⁻ c in Set.Iio t, innerBC b c ∂μ) = 0 := by
    -- restrict `hzero` to `Iio t` (since it equals `A ∩ B`)
    simpa [hIio] using hzero
  -- Solve.
  have :
      ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ =
        0 + constAboveT * μ (Set.Ico t (1 : Rand)) := by
    simpa [hio, hco] using hsplit'.symm
  simpa using this

lemma lintegral_b_above_t :
    (∫⁻ b in Set.Ico t (1 : Rand), ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
      constAboveT * (μ (Set.Ico t (1 : Rand))) * (μ (Set.Ico t (1 : Rand))) := by
  classical
  have hIoo : (Set.Ioo t (1 : Rand) : Set Rand) =ᵐ[μ] Set.Ico t (1 : Rand) := by
    simpa [μ] using
      (MeasureTheory.Ioo_ae_eq_Ico (μ := (μ : Measure Rand)) (a := t) (b := (1 : Rand)))
  -- Replace `Ico` by `Ioo` (they differ by endpoints of measure 0).
  have hcongr :
      (∫⁻ b in Set.Ico t (1 : Rand), ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        ∫⁻ b in Set.Ioo t (1 : Rand),
          ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ := by
    simpa using (MeasureTheory.setLIntegral_congr (μ := μ) (f := fun b =>
      ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) hIoo.symm)
  rw [hcongr]
  have hs : MeasurableSet (Set.Ioo t (1 : Rand) : Set Rand) := by measurability
  have hconst :
      Set.EqOn
        (fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
        (fun _ => constAboveT * μ (Set.Ico t (1 : Rand)))
        (Set.Ioo t (1 : Rand) : Set Rand) := by
    intro b hb
    have htb : t < b := hb.1
    simpa using (lintegral_innerBC_Iio_one_of_t_lt_b (b := b) htb)
  have :
      (∫⁻ b in Set.Ioo t (1 : Rand),
          ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        (∫⁻ _b in Set.Ioo t (1 : Rand), constAboveT * μ (Set.Ico t (1 : Rand)) ∂μ) := by
    exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs hconst
  rw [this]
  simp [mul_assoc]

private lemma lintegral_innerBC_Ico_t_one_eq_zero_of_t2_le_b_lt_t {b : Rand}
    (hb1 : t2 ≤ b) (hb2 : b < t) :
    (∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ) = 0 := by
  have hIoo : (Set.Ioo t (1 : Rand) : Set Rand) =ᵐ[μ] Set.Ico t (1 : Rand) := by
    simpa [μ] using
      (MeasureTheory.Ioo_ae_eq_Ico (μ := (μ : Measure Rand)) (a := t) (b := (1 : Rand)))
  have hIoo0 : (∫⁻ c in Set.Ioo t (1 : Rand), innerBC b c ∂μ) = 0 := by
    have hs : MeasurableSet (Set.Ioo t (1 : Rand) : Set Rand) := by simp
    have hEq :
        Set.EqOn (fun c : Rand => innerBC b c) 0 (Set.Ioo t (1 : Rand) : Set Rand) := by
      intro c hc
      have hc2 : ¬ c < t2 := by exact not_lt_of_ge (le_trans t2_le_t (le_of_lt hc.1))
      have haSlice : aSlice b c = (∅ : Set Rand) := by
        have : ¬ c < t := not_lt.2 (le_of_lt hc.1)
        simp [aSlice_eq_of_t2_le_b_lt_t (b := b) (c := c) hb1 hb2, hc2, this]
      have hz0 : z0 b c = 1 :=
        z0_eq_one_of_lt_t_le (fun h => (not_le_of_gt hc.1) h.2.2) hb2 hc.1.le
      simp [innerBC, z0I, hz0, haSlice]
    simpa using (MeasureTheory.setLIntegral_eq_zero (μ := μ) hs hEq)
  simpa using
    (MeasureTheory.setLIntegral_congr (μ := μ) (f := fun c => innerBC b c) hIoo.symm) ▸ hIoo0

lemma lintegral_b_t2_t :
    (∫⁻ b in Set.Ico t2 t, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
      μ (Set.Ico t2 t) *
        ((∫⁻ c in Set.Iio t1, gCt c ∂μ) +
          constT1T * μ (Set.Ico t1 t2) +
          constT2T2 * μ (Set.Ico t2 t)) := by
  classical
  have hbmeas : MeasurableSet (Set.Ico t2 t : Set Rand) := by simp
  -- On `b ∈ [t2,t)`, the inner integral depends only on `c` and can be written explicitly.
  have hinner :
      Set.EqOn
        (fun b : Rand => ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ)
        (fun _ =>
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) +
            constT1T * μ (Set.Ico t1 t2) +
            constT2T2 * μ (Set.Ico t2 t))
        (Set.Ico t2 t : Set Rand) := by
    intro b hb
    have hb1 : t2 ≤ b := hb.1
    have hb2 : b < t := hb.2
    -- Split `c ∈ Iio 1` into `c < t` and `t ≤ c < 1`. The second part is 0.
    have htmeas : MeasurableSet (Set.Iio t : Set Rand) := by simp
    have hsplit :=
      (MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
        (A := (Set.Iio (1 : Rand) : Set Rand)) (B := (Set.Iio t : Set Rand)) htmeas)
    have hAint : ((Set.Iio (1 : Rand) : Set Rand) ∩ Set.Iio t) = Set.Iio t :=
      Iio_inter_Iio_eq t_lt_one.le
    have hAdiff : ((Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t) = Set.Ico t (1 : Rand) :=
      Iio_diff_Iio_eq t_lt_one.le
    have hzero :
        (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand) \ Set.Iio t, innerBC b c ∂μ) = 0 := by
      have hIco0 : (∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ) = 0 := by
        exact lintegral_innerBC_Ico_t_one_eq_zero_of_t2_le_b_lt_t (b := b) hb1 hb2
      simpa [hAdiff] using hIco0
    -- Now compute the `c < t` part by splitting at `t1` and `t2`.
    have hsplit_t1 :=
      (MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
        (A := (Set.Iio t : Set Rand)) (B := (Set.Iio t1 : Set Rand))
        (by simp))
    have hIio_t1 : (Set.Iio t ∩ Set.Iio t1 : Set Rand) = Set.Iio t1 :=
      Iio_inter_Iio_eq (lt_trans t1_lt_t2 t2_lt_t).le
    have hIco_t1_t : (Set.Iio t \ Set.Iio t1 : Set Rand) = Set.Ico t1 t :=
      Iio_diff_Iio_eq (lt_trans t1_lt_t2 t2_lt_t).le
    have hsplit_t2 :=
      (MeasureTheory.lintegral_inter_add_sdiff (μ := μ) (f := fun c => innerBC b c)
        (A := (Set.Ico t1 t : Set Rand)) (B := (Set.Iio t2 : Set Rand))
        (by simp))
    have hIco_t1_t2 : (Set.Ico t1 t ∩ Set.Iio t2 : Set Rand) = Set.Ico t1 t2 :=
      Ico_inter_Iio_eq t2_lt_t.le
    have hIco_t2_t : (Set.Ico t1 t \ Set.Iio t2 : Set Rand) = Set.Ico t2 t :=
      Ico_diff_Iio_eq t1_le_t2
    -- Evaluate on each `c`-region.
    have h_on_t1 :
        (∫⁻ c in Set.Iio t1, innerBC b c ∂μ) = ∫⁻ c in Set.Iio t1, gCt c ∂μ := by
      have hs : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
      have :
          Set.EqOn (fun c : Rand => innerBC b c) (fun c => gCt c) (Set.Iio t1 : Set Rand) := by
        intro c hc
        exact innerBC_eq_gCt_of_t2_le_b_lt_t_of_c_lt_t1 (b := b) (c := c) hb1 hb2 hc
      exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs this
    have h_on_t1_t2 :
        (∫⁻ c in Set.Ico t1 t2, innerBC b c ∂μ) = constT1T * μ (Set.Ico t1 t2) := by
      have hs : MeasurableSet (Set.Ico t1 t2 : Set Rand) := by simp
      have :
          Set.EqOn
            (fun c : Rand => innerBC b c)
            (fun _ => constT1T)
            (Set.Ico t1 t2 : Set Rand) := by
        intro c hc
        exact innerBC_eq_constT1T_of_t2_le_b_lt_t_of_t1_le_c_of_c_lt_t2 (b := b) (c := c)
          hb1 hb2 hc.1 hc.2
      calc
        (∫⁻ c in Set.Ico t1 t2, innerBC b c ∂μ) =
            ∫⁻ _c in Set.Ico t1 t2, constT1T ∂μ := by
              exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs this
        _ = constT1T * μ (Set.Ico t1 t2) := by simp
    have h_on_t2_t :
        (∫⁻ c in Set.Ico t2 t, innerBC b c ∂μ) = constT2T2 * μ (Set.Ico t2 t) := by
      have hs : MeasurableSet (Set.Ico t2 t : Set Rand) := by simp
      have :
          Set.EqOn
            (fun c : Rand => innerBC b c)
            (fun _ => constT2T2)
            (Set.Ico t2 t : Set Rand) := by
        intro c hc
        exact innerBC_eq_constT2T2_of_t2_le_b_lt_t_of_t2_le_c_of_c_lt_t (b := b) (c := c)
          hb1 hb2 hc.1 hc.2
      calc
        (∫⁻ c in Set.Ico t2 t, innerBC b c ∂μ) =
            ∫⁻ _c in Set.Ico t2 t, constT2T2 ∂μ := by
              exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs this
        _ = constT2T2 * μ (Set.Ico t2 t) := by simp
    -- Assemble the `c < t` integral from `hsplit_t1` and `hsplit_t2`.
    have h_t :
        (∫⁻ c in Set.Iio t, innerBC b c ∂μ) =
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) +
            constT1T * μ (Set.Ico t1 t2) +
            constT2T2 * μ (Set.Ico t2 t) := by
      -- First split at `t1`.
      have h1 : (∫⁻ c in Set.Iio t1, innerBC b c ∂μ) + ∫⁻ c in Set.Ico t1 t, innerBC b c ∂μ =
          ∫⁻ c in Set.Iio t, innerBC b c ∂μ := by
        simpa [hIio_t1, hIco_t1_t] using hsplit_t1
      -- Then split `Ico t1 t` at `t2`.
      have h2 : (∫⁻ c in Set.Ico t1 t2, innerBC b c ∂μ) + ∫⁻ c in Set.Ico t2 t, innerBC b c ∂μ =
          ∫⁻ c in Set.Ico t1 t, innerBC b c ∂μ := by
        simpa [hIco_t1_t2, hIco_t2_t] using hsplit_t2
      -- Substitute computed pieces.
      calc
        (∫⁻ c in Set.Iio t, innerBC b c ∂μ) =
            (∫⁻ c in Set.Iio t1, innerBC b c ∂μ) + ∫⁻ c in Set.Ico t1 t, innerBC b c ∂μ := by
              simpa [add_comm, add_left_comm, add_assoc] using h1.symm
        _ =
            (∫⁻ c in Set.Iio t1, innerBC b c ∂μ) +
              ((∫⁻ c in Set.Ico t1 t2, innerBC b c ∂μ) +
                ∫⁻ c in Set.Ico t2 t, innerBC b c ∂μ) := by
              simp [h2]
        _ =
            (∫⁻ c in Set.Iio t1, gCt c ∂μ) + constT1T * μ (Set.Ico t1 t2) +
              constT2T2 * μ (Set.Ico t2 t) := by
              -- `simp` computes each term, and `ac_rfl` rearranges addition/multiplication.
              simp [h_on_t1, h_on_t1_t2, h_on_t2_t]
              ac_rfl
    -- Now conclude the full `Iio 1` integral.
    have hA :
        (∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ) =
          (∫⁻ c in Set.Iio t, innerBC b c ∂μ) + 0 := by
      have hAB :
          (∫⁻ c in Set.Iio t, innerBC b c ∂μ) +
              ∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ =
            ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ := by
        simpa [hAint, hAdiff] using hsplit
      -- The `Ico t 1` part is zero.
      have hIco0 : (∫⁻ c in Set.Ico t (1 : Rand), innerBC b c ∂μ) = 0 := by
        -- rewrite the set and use `hzero`
        simpa [hAdiff] using hzero
      simpa [hIco0, add_comm] using hAB.symm
    simp [hA, h_t]
  -- Finally, integrate over `b ∈ [t2,t)` (constant function).
  have hs : MeasurableSet (Set.Ico t2 t : Set Rand) := by simp
  have :
      (∫⁻ b in Set.Ico t2 t,
          ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
        ∫⁻ _b in Set.Ico t2 t,
          (∫⁻ c in Set.Iio t1, gCt c ∂μ) +
            constT1T * μ (Set.Ico t1 t2) +
            constT2T2 * μ (Set.Ico t2 t) ∂μ := by
    exact MeasureTheory.setLIntegral_congr_fun (μ := μ) hs hinner
  rw [this]
  simp
  ac_rfl

/-- Merge a product-sum of `ofReal`s into a single `ofReal`. -/
private lemma ofReal_prodSum {x y : ℝ} (hx0 : 0 ≤ x) (h1x0 : 0 ≤ 1 - x)
    (hy0 : 0 ≤ y) (h1y0 : 0 ≤ 1 - y) :
    ENNReal.ofReal x * ENNReal.ofReal y + ENNReal.ofReal (1 - x) * ENNReal.ofReal (1 - y) =
      ENNReal.ofReal (x * y + (1 - x) * (1 - y)) := by
  rw [← ENNReal.ofReal_mul hx0, ← ENNReal.ofReal_mul h1x0,
    ← ENNReal.ofReal_add (mul_nonneg hx0 hy0) (mul_nonneg h1x0 h1y0)]

/-- Exact value of the constant `constAboveT = t^2 + (1-t)^2`. -/
lemma constAboveT_eq : constAboveT = ENNReal.ofReal (17 / 32 : ℝ) := by
  rw [constAboveT, ofReal_prodSum t.property.1 (sub_nonneg.2 (le_of_lt t_lt_one))
    t.property.1 (sub_nonneg.2 (le_of_lt t_lt_one))]
  norm_num [t]

/-- Exact value of the constant `constT1T = t1*t + (1-t1)*(1-t)`. -/
lemma constT1T_eq : constT1T = ENNReal.ofReal (15 / 32 : ℝ) := by
  rw [constT1T, ofReal_prodSum t1.property.1 (sub_nonneg.2 t1.property.2)
    t.property.1 (sub_nonneg.2 (le_of_lt t_lt_one))]
  norm_num [t1, t]

/-- Exact value of the constant `constT2T2 = t2^2 + (1-t2)^2`. -/
lemma constT2T2_eq : constT2T2 = ENNReal.ofReal (257 / 512 : ℝ) := by
  rw [constT2T2, ofReal_prodSum t2.property.1 (sub_nonneg.2 t2.property.2)
    t2.property.1 (sub_nonneg.2 t2.property.2)]
  norm_num [t2]

lemma lintegral_gCt_Iio_t1 :
    (∫⁻ c in Set.Iio t1, gCt c ∂μ) = ENNReal.ofReal (81 / 512 : ℝ) := by
  have ha0 : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have hb0 : 0 ≤ (3 / 8 : ℝ) := by norm_num
  have hs : MeasurableSet (Set.Iio t1 : Set Rand) := by simp
  have ht : (2 * (t : ℝ) - 1) = (1 / 4 : ℝ) := by norm_num [t]
  have hconst : (1 - (t : ℝ)) = (3 / 8 : ℝ) := by norm_num [t]
  have hEq :
      Set.EqOn (fun c : Rand => gCt c)
        (fun c : Rand =>
          ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (c : ℝ) + ENNReal.ofReal (3 / 8 : ℝ))
        (Set.Iio t1 : Set Rand) := by
    intro c _hc
    -- `gCt` is affine in `c` at our concrete dyadic `t = 5/8`.
    have hc : gCt c = ENNReal.ofReal ((1 / 4 : ℝ) * (c : ℝ)) + ENNReal.ofReal (3 / 8 : ℝ) := by
      simpa [ht, hconst] using (gCt_eq_linear c)
    -- rewrite `ofReal ((1/4) * c)` as `ofReal (1/4) * ofReal c`
    simpa [ENNReal.ofReal_mul ha0, mul_assoc] using hc
  have hcongr :
      (∫⁻ c in Set.Iio t1, gCt c ∂μ) =
        ∫⁻ c in Set.Iio t1,
          (ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (c : ℝ) +
            ENNReal.ofReal (3 / 8 : ℝ)) ∂μ := MeasureTheory.setLIntegral_congr_fun (μ := μ) hs hEq
  rw [hcongr]
  -- Split the integral into affine and constant parts.
  have hmeas1 : Measurable fun c : Rand => ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (c : ℝ) := by
    measurability
  rw [MeasureTheory.lintegral_add_left (μ := μ.restrict (Set.Iio t1)) hmeas1]
  -- Pull out the constant `ofReal (1/4)`.
  have hmeas_id : Measurable fun c : Rand => ENNReal.ofReal (c : ℝ) := by measurability
  rw [MeasureTheory.lintegral_const_mul
    (μ := μ.restrict (Set.Iio t1))
    (r := ENNReal.ofReal (1 / 4 : ℝ))
    (f := fun c : Rand => ENNReal.ofReal (c : ℝ)) hmeas_id]
  -- Compute both remaining set integrals.
  have h_id :
      (∫⁻ c in Set.Iio t1, ENNReal.ofReal (c : ℝ) ∂μ) =
        ENNReal.ofReal (((t1 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / 2) := by
    simpa [μ] using (setLIntegral_ofReal_id_Iio (b := t1))
  have ht1 : μ (Set.Iio t1) = ENNReal.ofReal (3 / 8 : ℝ) := by simp [μ, t1]
  -- Now finish by straightforward arithmetic.
  rw [h_id]
  have hconstInt :
      (∫⁻ _a in Set.Iio t1, ENNReal.ofReal (3 / 8 : ℝ) ∂μ) =
        ENNReal.ofReal (3 / 8 : ℝ) * μ (Set.Iio t1) := by
    simp [MeasureTheory.lintegral_const]
  rw [hconstInt, ht1]
  -- Rewrite the products and sum as a single `ofReal`, then do real arithmetic.
  have hnonneg1 : 0 ≤ (1 / 4 : ℝ) * (((t1 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / 2) := by
    have ht1sq : 0 ≤ ((t1 : ℝ) ^ 2) := sq_nonneg _
    have : 0 ≤ (((t1 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / 2) := by nlinarith
    exact mul_nonneg (by norm_num) this
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4), ← ENNReal.ofReal_mul hb0,
    ← ENNReal.ofReal_add hnonneg1 (mul_nonneg hb0 hb0)]
  simp only [t1]
  norm_num

/-- Evaluate the `b ≥ t` region as an explicit rational value. -/
lemma lintegral_b_above_t_value :
    (∫⁻ b in Set.Ico t (1 : Rand), ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
      ENNReal.ofReal (153 / 2048 : ℝ) := by
  have h17 : 0 ≤ (17 / 32 : ℝ) := by norm_num
  have h3 : 0 ≤ (3 / 8 : ℝ) := by norm_num
  rw [lintegral_b_above_t]
  rw [constAboveT_eq]
  have hμ : μ (Set.Ico t (1 : Rand)) = ENNReal.ofReal (3 / 8 : ℝ) := by norm_num [μ, t]
  -- Fold the product into a single `ofReal`.
  rw [hμ, ← ENNReal.ofReal_mul h17, ← ENNReal.ofReal_mul (mul_nonneg h17 h3)]
  norm_num

lemma lintegral_b_t2_t_value :
    (∫⁻ b in Set.Ico t2 t, ∫⁻ c in (Set.Iio (1 : Rand) : Set Rand), innerBC b c ∂μ ∂μ) =
      ENNReal.ofReal (13689 / 524288 : ℝ) := by
  have h3 : 0 ≤ (3 / 32 : ℝ) := by norm_num
  have h81 : 0 ≤ (81 / 512 : ℝ) := by norm_num
  have h15 : 0 ≤ (15 / 32 : ℝ) := by norm_num
  have h257 : 0 ≤ (257 / 512 : ℝ) := by norm_num
  rw [lintegral_b_t2_t]
  -- Replace each term by its explicit value.
  have hμt2t : μ (Set.Ico t2 t) = ENNReal.ofReal (3 / 32 : ℝ) := by norm_num [μ, t2, t]
  have hμt1t2 : μ (Set.Ico t1 t2) = ENNReal.ofReal (5 / 32 : ℝ) := by norm_num [μ, t1, t2]
  rw [hμt2t, lintegral_gCt_Iio_t1, constT1T_eq, constT2T2_eq, hμt1t2]
  -- Fold all products/sums into a single `ofReal`, then evaluate.
  rw [← ENNReal.ofReal_mul h15, ← ENNReal.ofReal_mul h257,
    ← ENNReal.ofReal_add h81 (mul_nonneg h15 (by norm_num)),
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg h257 h3),
    ← ENNReal.ofReal_mul h3]
  norm_num

end Recursive3Param
end UpperBound

end Distributed2Coloring
