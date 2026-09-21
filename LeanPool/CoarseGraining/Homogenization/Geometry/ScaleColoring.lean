/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeColoring

/-! # Scale Coloring -/

namespace Homogenization

/-- The Chapter 4 scale-dependent coloring period
`r_k = 1 + \lceil 3^{-k} \rceil`. -/
noncomputable def scaleColorPeriod (k : ℤ) : ℕ :=
  1 + Nat.ceil ((3 : ℝ) ^ (-k))

/-- The scale-dependent triadic colors attached to cubes at scale `k`. -/
abbrev ScaleColor (d : ℕ) (k : ℤ) := Fin d → Fin (scaleColorPeriod k)

lemma scaleColorPeriod_pos (k : ℤ) : 0 < scaleColorPeriod k := by
  simp [scaleColorPeriod]

lemma scaleColorPeriod_int_pos (k : ℤ) : 0 < (scaleColorPeriod k : ℤ) := by
  exact_mod_cast scaleColorPeriod_pos k

lemma scaleColorPeriod_int_ne_zero (k : ℤ) : (scaleColorPeriod k : ℤ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (scaleColorPeriod_pos k))

private theorem cubeScaleFactor_pos {d : ℕ} (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

/-- The scale-dependent color of a triadic cube, given by its coordinatewise
residue class modulo `r_k`. -/
noncomputable def cubeScaleColor {d : ℕ} (k : ℤ) (Q : TriadicCube d) : ScaleColor d k := fun i =>
  ⟨Int.toNat (Q.index i % (scaleColorPeriod k : ℤ)), by
    have hnonneg : 0 ≤ Q.index i % (scaleColorPeriod k : ℤ) :=
      Int.emod_nonneg _ (scaleColorPeriod_int_ne_zero k)
    have hlt : Q.index i % (scaleColorPeriod k : ℤ) < (scaleColorPeriod k : ℤ) :=
      Int.emod_lt_of_pos _ (scaleColorPeriod_int_pos k)
    rw [Int.toNat_lt hnonneg]
    exact hlt⟩

/-- The descendants of `Q` at scale `k` with prescribed scale-dependent color
`c`. -/
noncomputable def descendantsAtScaleScaleColorClass {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (c : ScaleColor d k) :
    Finset (TriadicCube d) :=
  (descendantsAtScale Q k).filter fun R => cubeScaleColor k R = c

@[simp] theorem cubeScaleColor_val {d : ℕ} (k : ℤ) (Q : TriadicCube d) (i : Fin d) :
    (cubeScaleColor k Q i : ℕ) = Int.toNat (Q.index i % (scaleColorPeriod k : ℤ)) :=
  rfl

theorem cubeScaleColor_eq_iff_modEq {d : ℕ} {k : ℤ} {R S : TriadicCube d} :
    cubeScaleColor k R = cubeScaleColor k S ↔
      ∀ i, R.index i ≡ S.index i [ZMOD (scaleColorPeriod k : ℤ)] := by
  constructor
  · intro h i
    change R.index i % (scaleColorPeriod k : ℤ) = S.index i % (scaleColorPeriod k : ℤ)
    have hval :
        Int.toNat (R.index i % (scaleColorPeriod k : ℤ)) =
          Int.toNat (S.index i % (scaleColorPeriod k : ℤ)) := by
      simpa [cubeScaleColor] using
        congrArg Fin.val (congrArg (fun c : ScaleColor d k => c i) h)
    have hcast :
        (((Int.toNat (R.index i % (scaleColorPeriod k : ℤ)) : ℕ) : ℤ)) =
          Int.toNat (S.index i % (scaleColorPeriod k : ℤ)) := by
      exact_mod_cast hval
    have hR_nonneg : 0 ≤ R.index i % (scaleColorPeriod k : ℤ) :=
      Int.emod_nonneg _ (scaleColorPeriod_int_ne_zero k)
    have hS_nonneg : 0 ≤ S.index i % (scaleColorPeriod k : ℤ) :=
      Int.emod_nonneg _ (scaleColorPeriod_int_ne_zero k)
    simpa [Int.ModEq, Int.toNat_of_nonneg hR_nonneg, Int.toNat_of_nonneg hS_nonneg] using hcast
  · intro h
    funext i
    apply Fin.ext
    have hmod : R.index i % (scaleColorPeriod k : ℤ) = S.index i % (scaleColorPeriod k : ℤ) := by
      simpa [Int.ModEq] using h i
    have hR_nonneg : 0 ≤ R.index i % (scaleColorPeriod k : ℤ) :=
      Int.emod_nonneg _ (scaleColorPeriod_int_ne_zero k)
    have hS_nonneg : 0 ≤ S.index i % (scaleColorPeriod k : ℤ) :=
      Int.emod_nonneg _ (scaleColorPeriod_int_ne_zero k)
    simpa [cubeScaleColor, Int.toNat_of_nonneg hR_nonneg, Int.toNat_of_nonneg hS_nonneg] using
      congrArg Int.toNat hmod

@[simp] theorem mem_descendantsAtScaleScaleColorClass_iff {d : ℕ} {Q R : TriadicCube d}
    {k : ℤ} {c : ScaleColor d k} :
    R ∈ descendantsAtScaleScaleColorClass Q k c ↔
      R ∈ descendantsAtScale Q k ∧ cubeScaleColor k R = c := by
  simp [descendantsAtScaleScaleColorClass]

theorem mem_descendantsAtScaleScaleColorClass_self {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hR : R ∈ descendantsAtScale Q k) :
    R ∈ descendantsAtScaleScaleColorClass Q k (cubeScaleColor k R) := by
  simp [descendantsAtScaleScaleColorClass, hR]

@[simp] theorem card_scaleColor (d : ℕ) (k : ℤ) :
    Fintype.card (ScaleColor d k) = scaleColorPeriod k ^ d := by
  simp [ScaleColor]

theorem card_image_cubeScaleColor_descendantsAtScale_le {d : ℕ} (Q : TriadicCube d) (k : ℤ) :
    ((descendantsAtScale Q k).image (cubeScaleColor k)).card ≤ scaleColorPeriod k ^ d := by
  have hsubset :
      (descendantsAtScale Q k).image (cubeScaleColor k) ⊆ (Finset.univ : Finset (ScaleColor d k)) := by
    intro c hc
    simp
  simpa [card_scaleColor] using Finset.card_le_card hsubset

theorem descendantsAtScale_eq_biUnion_scaleColorClass {d : ℕ} (Q : TriadicCube d) (k : ℤ) :
    (Finset.univ : Finset (ScaleColor d k)).biUnion (descendantsAtScaleScaleColorClass Q k) =
      descendantsAtScale Q k := by
  ext R
  constructor
  · intro hR
    rcases Finset.mem_biUnion.mp hR with ⟨c, -, hRc⟩
    exact (mem_descendantsAtScaleScaleColorClass_iff.mp hRc).1
  · intro hR
    exact Finset.mem_biUnion.mpr
      ⟨cubeScaleColor k R, by simp, mem_descendantsAtScaleScaleColorClass_self hR⟩

theorem descendantsAtScale_eq_biUnion_image_cubeScaleColor {d : ℕ} (Q : TriadicCube d) (k : ℤ) :
    ((descendantsAtScale Q k).image (cubeScaleColor k)).biUnion
        (descendantsAtScaleScaleColorClass Q k) =
      descendantsAtScale Q k := by
  ext R
  constructor
  · intro hR
    rcases Finset.mem_biUnion.mp hR with ⟨c, -, hRc⟩
    exact (mem_descendantsAtScaleScaleColorClass_iff.mp hRc).1
  · intro hR
    exact Finset.mem_biUnion.mpr
      ⟨cubeScaleColor k R, Finset.mem_image.mpr ⟨R, hR, rfl⟩,
        mem_descendantsAtScaleScaleColorClass_self hR⟩

theorem disjoint_descendantsAtScaleScaleColorClass_of_ne {d : ℕ} (Q : TriadicCube d) (k : ℤ)
    {c₁ c₂ : ScaleColor d k} (hneq : c₁ ≠ c₂) :
    Disjoint (descendantsAtScaleScaleColorClass Q k c₁)
      (descendantsAtScaleScaleColorClass Q k c₂) := by
  rw [Finset.disjoint_left]
  intro R hR₁ hR₂
  have hc₁ : cubeScaleColor k R = c₁ := (mem_descendantsAtScaleScaleColorClass_iff.mp hR₁).2
  have hc₂ : cubeScaleColor k R = c₂ := (mem_descendantsAtScaleScaleColorClass_iff.mp hR₂).2
  exact hneq (hc₁.symm.trans hc₂)

theorem card_descendantsAtScale_eq_sum_card_scaleColorClass_image {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) :
    (descendantsAtScale Q k).card =
      ((descendantsAtScale Q k).image (cubeScaleColor k)).sum
        (fun c => (descendantsAtScaleScaleColorClass Q k c).card) := by
  classical
  calc
    (descendantsAtScale Q k).card =
        ((((descendantsAtScale Q k).image (cubeScaleColor k)).biUnion
          (descendantsAtScaleScaleColorClass Q k)).card) := by
            rw [descendantsAtScale_eq_biUnion_image_cubeScaleColor Q k]
    _ = ((descendantsAtScale Q k).image (cubeScaleColor k)).sum
          (fun c => (descendantsAtScaleScaleColorClass Q k c).card) := by
            exact Finset.card_biUnion (by
              intro c hc c' hc' hne
              exact disjoint_descendantsAtScaleScaleColorClass_of_ne Q k hne)

private theorem index_add_scaleColorPeriod_le_of_cubeScaleColor_eq_of_lt {d : ℕ}
    {k : ℤ} {R S : TriadicCube d} {i : Fin d}
    (hcolor : cubeScaleColor k R = cubeScaleColor k S) (hlt : R.index i < S.index i) :
    R.index i + scaleColorPeriod k ≤ S.index i := by
  have hmod :
      R.index i ≡ S.index i [ZMOD (scaleColorPeriod k : ℤ)] :=
    (cubeScaleColor_eq_iff_modEq.mp hcolor) i
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨n, hn⟩
  have hperiod_pos : 0 < (scaleColorPeriod k : ℤ) := scaleColorPeriod_int_pos k
  have hdiff_pos : 0 < (scaleColorPeriod k : ℤ) * n := by
    rw [← hn]
    exact sub_pos.mpr hlt
  have hn_pos : 0 < n := by
    nlinarith
  have hperiod_le : (scaleColorPeriod k : ℤ) ≤ (scaleColorPeriod k : ℤ) * n := by
    nlinarith
  nlinarith [hn, hperiod_le]

lemma one_le_scaleColorPeriod_pred_mul_zpow (k : ℤ) :
    1 ≤ (((scaleColorPeriod k : ℝ) - 1) * (3 : ℝ) ^ k) := by
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ k := by positivity
  have hceil_ge : (3 : ℝ) ^ (-k) ≤ (Nat.ceil ((3 : ℝ) ^ (-k)) : ℝ) :=
    Nat.le_ceil ((3 : ℝ) ^ (-k))
  have hmul := mul_le_mul_of_nonneg_right hceil_ge hpow_nonneg
  calc
    1 = (3 : ℝ) ^ (-k) * (3 : ℝ) ^ k := by
          rw [← zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
          simp
    _ ≤ (Nat.ceil ((3 : ℝ) ^ (-k)) : ℝ) * (3 : ℝ) ^ k := hmul
    _ = (((scaleColorPeriod k : ℝ) - 1) * (3 : ℝ) ^ k) := by
          simp [scaleColorPeriod]

lemma scaleColorPeriod_le_three_mul_one_add_zpow_neg (k : ℤ) :
    (scaleColorPeriod k : ℝ) ≤ 3 * (1 + (3 : ℝ) ^ (-k)) := by
  have hnonneg : 0 ≤ (3 : ℝ) ^ (-k) := by positivity
  have hceil_le : (Nat.ceil ((3 : ℝ) ^ (-k)) : ℝ) ≤ (3 : ℝ) ^ (-k) + 1 :=
    (Nat.ceil_lt_add_one hnonneg).le
  calc
    (scaleColorPeriod k : ℝ) = 1 + (Nat.ceil ((3 : ℝ) ^ (-k)) : ℝ) := by
          simp [scaleColorPeriod]
    _ ≤ 2 + (3 : ℝ) ^ (-k) := by linarith
    _ ≤ 3 * (1 + (3 : ℝ) ^ (-k)) := by nlinarith

theorem one_le_dist_of_ne_of_mem_descendantsAtScaleScaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    (hR : R ∈ descendantsAtScaleScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleScaleColorClass Q k c) (hneq : R ≠ S)
    {x y : Vec d} (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet S) :
    1 ≤ dist x y := by
  have hcolor : cubeScaleColor k R = cubeScaleColor k S := by
    calc
      cubeScaleColor k R = c := (mem_descendantsAtScaleScaleColorClass_iff.mp hR).2
      _ = cubeScaleColor k S := ((mem_descendantsAtScaleScaleColorClass_iff.mp hS).2).symm
  have hindex_ne : ∃ i, R.index i ≠ S.index i := by
    by_contra h
    push Not at h
    apply hneq
    cases R with
    | mk scaleR indexR =>
        cases S with
        | mk scaleS indexS =>
            simp at h ⊢
            refine ⟨?_, funext h⟩
            have hscaleR : scaleR = k := by
              simpa using
                scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1
            have hscaleS : scaleS = k := by
              simpa using
                scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleScaleColorClass_iff.mp hS).1
            exact hscaleR.trans hscaleS.symm
  rcases hindex_ne with ⟨i, hi⟩
  have hscale :
      cubeScaleFactor S = cubeScaleFactor R := by
    calc
      cubeScaleFactor S = (3 : ℝ) ^ k := by
        rw [cubeScaleFactor,
          scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleScaleColorClass_iff.mp hS).1]
      _ = cubeScaleFactor R := by
        rw [cubeScaleFactor,
          scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1]
  have hscale_nonneg : 0 ≤ cubeScaleFactor R := le_of_lt (cubeScaleFactor_pos R)
  have hperiod_scale :
      1 ≤ (((scaleColorPeriod k : ℝ) - 1) * cubeScaleFactor R) := by
    rw [cubeScaleFactor,
      scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1]
    simpa using one_le_scaleColorPeriod_pred_mul_zpow k
  have hxR := hx i
  have hyS := hy i
  rw [hscale] at hyS
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hgap : R.index i + scaleColorPeriod k ≤ S.index i :=
      index_add_scaleColorPeriod_le_of_cubeScaleColor_eq_of_lt hcolor hlt
    have hgap_real : ((R.index i : ℝ) + scaleColorPeriod k : ℝ) ≤ (S.index i : ℝ) := by
      exact_mod_cast hgap
    have hcoord :
        (((scaleColorPeriod k : ℝ) - 1) * cubeScaleFactor R) ≤ ‖(y - x) i‖ := by
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg]
      · nlinarith [hyS.1, hxR.2, hgap_real, hscale_nonneg]
      · nlinarith [hyS.1, hxR.2, hgap_real, hscale_nonneg]
    have hnorm : 1 ≤ ‖y - x‖ := by
      exact le_trans hperiod_scale (le_trans hcoord (norm_le_pi_norm (y - x) i))
    simpa [dist_eq_norm, norm_sub_rev] using hnorm
  · have hgap : S.index i + scaleColorPeriod k ≤ R.index i :=
      index_add_scaleColorPeriod_le_of_cubeScaleColor_eq_of_lt hcolor.symm hgt
    have hgap_real : ((S.index i : ℝ) + scaleColorPeriod k : ℝ) ≤ (R.index i : ℝ) := by
      exact_mod_cast hgap
    have hcoord :
        (((scaleColorPeriod k : ℝ) - 1) * cubeScaleFactor R) ≤ ‖(x - y) i‖ := by
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg]
      · nlinarith [hxR.1, hyS.2, hgap_real, hscale_nonneg]
      · nlinarith [hxR.1, hyS.2, hgap_real, hscale_nonneg]
    have hnorm : 1 ≤ ‖x - y‖ := by
      exact le_trans hperiod_scale (le_trans hcoord (norm_le_pi_norm (x - y) i))
    simpa [dist_eq_norm] using hnorm

theorem pairwiseDisjoint_descendantsAtScaleScaleColorClass {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (c : ScaleColor d k) :
    (descendantsAtScaleScaleColorClass Q k c : Set (TriadicCube d)).PairwiseDisjoint cubeSet := by
  intro R hR S hS hneq
  exact disjoint_cubeSet_of_ne_of_mem_descendantsAtScale
    (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1
    (mem_descendantsAtScaleScaleColorClass_iff.mp hS).1 hneq

end Homogenization
