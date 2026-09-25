/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition

/-! # Cube Coloring -/

@[expose] public section

namespace Homogenization

/-- A triadic color is a choice of residue class modulo `3` in each coordinate. -/
abbrev CubeColor (d : ℕ) := Fin d → Fin 3

/-- The color of a triadic cube, given by the coordinatewise residue class of its lattice index
modulo `3`. -/
def cubeColor {d : ℕ} (Q : TriadicCube d) : CubeColor d := fun i =>
  ⟨Int.toNat (Q.index i % 3), by
    have hnonneg : 0 ≤ Q.index i % 3 := Int.emod_nonneg _ (by norm_num)
    have hlt : Q.index i % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    rw [Int.toNat_lt hnonneg]
    exact hlt⟩

/-- The descendants of `Q` at scale `k` with the prescribed triadic color `c`. -/
def descendantsAtScaleColorClass {d : ℕ} (Q : TriadicCube d) (k : ℤ) (c : CubeColor d) :
    Finset (TriadicCube d) :=
  (descendantsAtScale Q k).filter fun R => cubeColor R = c

@[simp] theorem cubeColor_val {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    (cubeColor Q i : ℕ) = Int.toNat (Q.index i % 3) :=
  rfl

theorem cubeColor_eq_iff_modEq {d : ℕ} {R S : TriadicCube d} :
    cubeColor R = cubeColor S ↔ ∀ i, R.index i ≡ S.index i [ZMOD 3] := by
  constructor
  · intro h i
    change R.index i % 3 = S.index i % 3
    have hval : Int.toNat (R.index i % 3) = Int.toNat (S.index i % 3) := by
      simpa [cubeColor] using
        congrArg Fin.val (congrArg (fun c : CubeColor d => c i) h)
    have hcast : (((Int.toNat (R.index i % 3) : ℕ) : ℤ)) = Int.toNat (S.index i % 3) := by
      exact_mod_cast hval
    have hR_nonneg : 0 ≤ R.index i % 3 := Int.emod_nonneg _ (by norm_num)
    have hS_nonneg : 0 ≤ S.index i % 3 := Int.emod_nonneg _ (by norm_num)
    simpa [Int.toNat_of_nonneg hR_nonneg, Int.toNat_of_nonneg hS_nonneg] using hcast
  · intro h
    funext i
    apply Fin.ext
    have hmod : R.index i % 3 = S.index i % 3 := by
      simpa [Int.ModEq] using h i
    have hR_nonneg : 0 ≤ R.index i % 3 := Int.emod_nonneg _ (by norm_num)
    have hS_nonneg : 0 ≤ S.index i % 3 := Int.emod_nonneg _ (by norm_num)
    simpa [cubeColor, Int.toNat_of_nonneg hR_nonneg, Int.toNat_of_nonneg hS_nonneg] using
      congrArg Int.toNat hmod

@[simp] theorem mem_descendantsAtScaleColorClass_iff {d : ℕ} {Q R : TriadicCube d}
    {k : ℤ} {c : CubeColor d} :
    R ∈ descendantsAtScaleColorClass Q k c ↔ R ∈ descendantsAtScale Q k ∧ cubeColor R = c := by
  simp [descendantsAtScaleColorClass]

theorem mem_descendantsAtScaleColorClass_self {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hR : R ∈ descendantsAtScale Q k) :
    R ∈ descendantsAtScaleColorClass Q k (cubeColor R) := by
  simp [descendantsAtScaleColorClass, hR]

@[simp] theorem card_cubeColor (d : ℕ) : Fintype.card (CubeColor d) = 3 ^ d := by
  simp [CubeColor]

theorem card_image_cubeColor_descendantsAtScale_le {d : ℕ} (Q : TriadicCube d) (k : ℤ) :
    ((descendantsAtScale Q k).image cubeColor).card ≤ 3 ^ d := by
  have hsubset :
      (descendantsAtScale Q k).image cubeColor ⊆ (Finset.univ : Finset (CubeColor d)) := by
    intro c hc
    simp
  simpa [card_cubeColor] using Finset.card_le_card hsubset

theorem descendantsAtScale_eq_biUnion_colorClass {d : ℕ} (Q : TriadicCube d) (k : ℤ) :
    (Finset.univ : Finset (CubeColor d)).biUnion (descendantsAtScaleColorClass Q k) =
      descendantsAtScale Q k := by
  ext R
  constructor
  · intro hR
    rcases Finset.mem_biUnion.mp hR with ⟨c, -, hRc⟩
    exact (mem_descendantsAtScaleColorClass_iff.mp hRc).1
  · intro hR
    exact Finset.mem_biUnion.mpr
      ⟨cubeColor R, by simp, mem_descendantsAtScaleColorClass_self hR⟩

theorem descendantsAtScale_eq_biUnion_image_cubeColor {d : ℕ} (Q : TriadicCube d) (k : ℤ) :
    ((descendantsAtScale Q k).image cubeColor).biUnion (descendantsAtScaleColorClass Q k) =
      descendantsAtScale Q k := by
  ext R
  constructor
  · intro hR
    rcases Finset.mem_biUnion.mp hR with ⟨c, -, hRc⟩
    exact (mem_descendantsAtScaleColorClass_iff.mp hRc).1
  · intro hR
    exact Finset.mem_biUnion.mpr
      ⟨cubeColor R, Finset.mem_image.mpr ⟨R, hR, rfl⟩, mem_descendantsAtScaleColorClass_self hR⟩

theorem disjoint_descendantsAtScaleColorClass_of_ne {d : ℕ} (Q : TriadicCube d) (k : ℤ)
    {c₁ c₂ : CubeColor d} (hneq : c₁ ≠ c₂) :
    Disjoint (descendantsAtScaleColorClass Q k c₁) (descendantsAtScaleColorClass Q k c₂) := by
  rw [Finset.disjoint_left]
  intro R hR₁ hR₂
  have hc₁ : cubeColor R = c₁ := (mem_descendantsAtScaleColorClass_iff.mp hR₁).2
  have hc₂ : cubeColor R = c₂ := (mem_descendantsAtScaleColorClass_iff.mp hR₂).2
  exact hneq (hc₁.symm.trans hc₂)

theorem card_descendantsAtScale_eq_sum_card_colorClass_image {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) :
    (descendantsAtScale Q k).card =
      ((descendantsAtScale Q k).image cubeColor).sum
        (fun c => (descendantsAtScaleColorClass Q k c).card) := by
  classical
  calc
    (descendantsAtScale Q k).card =
        (((descendantsAtScale Q k).image cubeColor).biUnion (descendantsAtScaleColorClass Q k)).card := by
          rw [descendantsAtScale_eq_biUnion_image_cubeColor Q k]
    _ = ((descendantsAtScale Q k).image cubeColor).sum
          (fun c => (descendantsAtScaleColorClass Q k c).card) := by
          exact Finset.card_biUnion (by
            intro c hc c' hc' hne
            exact disjoint_descendantsAtScaleColorClass_of_ne Q k hne)

theorem scale_le_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hR : R ∈ descendantsAtScale Q k) :
    k ≤ Q.scale := by
  by_contra hk
  exact (not_mem_descendantsAtScale_of_lt (lt_of_not_ge hk)) hR

theorem scale_eq_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hR : R ∈ descendantsAtScale Q k) :
    R.scale = k := by
  have hk : k ≤ Q.scale := scale_le_of_mem_descendantsAtScale hR
  have hdepth := scale_eq_sub_of_mem_descendantsAtScale hk hR
  have hnonneg : 0 ≤ Q.scale - k := sub_nonneg.mpr hk
  calc
    R.scale = Q.scale - (Int.toNat (Q.scale - k) : ℕ) := hdepth
    _ = Q.scale - (Q.scale - k) := by rw [Int.toNat_of_nonneg hnonneg]
    _ = k := sub_sub_cancel _ _

private theorem cubeScaleFactor_pos {d : ℕ} (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

private theorem index_add_three_le_of_cubeColor_eq_of_lt {d : ℕ} {R S : TriadicCube d}
    {i : Fin d} (hcolor : cubeColor R = cubeColor S) (hlt : R.index i < S.index i) :
    R.index i + 3 ≤ S.index i := by
  have hmod : R.index i ≡ S.index i [ZMOD 3] := (cubeColor_eq_iff_modEq.mp hcolor) i
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨n, hn⟩
  omega

theorem disjoint_cubeSet_of_scale_eq_of_ne {d : ℕ} {R S : TriadicCube d}
    (hscale : R.scale = S.scale) (hneq : R ≠ S) :
    Disjoint (cubeSet R) (cubeSet S) := by
  rw [Set.disjoint_left]
  intro x hxR hxS
  have hindex_ne : ∃ i, R.index i ≠ S.index i := by
    by_contra h
    push Not at h
    apply hneq
    cases R with
    | mk scaleR indexR =>
        cases S with
        | mk scaleS indexS =>
            simp at hscale ⊢
            exact ⟨hscale, funext h⟩
  rcases hindex_ne with ⟨i, hi⟩
  have hfactor : cubeScaleFactor S = cubeScaleFactor R := by
    simp [cubeScaleFactor, hscale]
  have hfactor_nonneg : 0 ≤ cubeScaleFactor R := le_of_lt (cubeScaleFactor_pos R)
  have hxRi := hxR i
  have hxSi := hxS i
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hidx' : (R.index i : ℝ) + 1 ≤ S.index i := by
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    have hsep :
        (((R.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor R) ≤
          (((S.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor S) := by
      rw [hfactor]
      have hcoeff : (R.index i : ℝ) + (1 / 2 : ℝ) ≤ (S.index i : ℝ) - (1 / 2 : ℝ) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hcoeff hfactor_nonneg
    exact not_lt_of_ge (le_trans hsep (by simpa [hfactor] using hxSi.1)) hxRi.2
  · have hidx' : (S.index i : ℝ) + 1 ≤ R.index i := by
      exact_mod_cast (Int.add_one_le_iff.mpr hgt)
    have hsep :
        (((S.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor S) ≤
          (((R.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor R) := by
      rw [hfactor]
      have hcoeff : (S.index i : ℝ) + (1 / 2 : ℝ) ≤ (R.index i : ℝ) - (1 / 2 : ℝ) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hcoeff hfactor_nonneg
    exact not_lt_of_ge (le_trans hsep hxRi.1) (by simpa [hfactor] using hxSi.2)

theorem disjoint_cubeSet_of_ne_of_mem_descendantsAtScale {d : ℕ} {Q R S : TriadicCube d}
    {k : ℤ} (hR : R ∈ descendantsAtScale Q k) (hS : S ∈ descendantsAtScale Q k) (hneq : R ≠ S) :
    Disjoint (cubeSet R) (cubeSet S) := by
  refine disjoint_cubeSet_of_scale_eq_of_ne ?_ hneq
  rw [scale_eq_of_mem_descendantsAtScale hR, scale_eq_of_mem_descendantsAtScale hS]

theorem disjoint_cubeSet_of_ne_of_mem_descendantsAtScaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : CubeColor d}
    (hR : R ∈ descendantsAtScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleColorClass Q k c) (hneq : R ≠ S) :
    Disjoint (cubeSet R) (cubeSet S) := by
  exact disjoint_cubeSet_of_ne_of_mem_descendantsAtScale
    (mem_descendantsAtScaleColorClass_iff.mp hR).1
    (mem_descendantsAtScaleColorClass_iff.mp hS).1 hneq

theorem cubeScaleFactor_le_dist_of_ne_of_mem_descendantsAtScaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : CubeColor d}
    (hR : R ∈ descendantsAtScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleColorClass Q k c) (hneq : R ≠ S)
    {x y : Vec d} (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet S) :
    cubeScaleFactor R ≤ dist x y := by
  have hcolor : cubeColor R = cubeColor S := by
    calc
      cubeColor R = c := (mem_descendantsAtScaleColorClass_iff.mp hR).2
      _ = cubeColor S := ((mem_descendantsAtScaleColorClass_iff.mp hS).2).symm
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
                scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleColorClass_iff.mp hR).1
            have hscaleS : scaleS = k := by
              simpa using
                scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleColorClass_iff.mp hS).1
            exact hscaleR.trans hscaleS.symm
  rcases hindex_ne with ⟨i, hi⟩
  have hscale :
      cubeScaleFactor S = cubeScaleFactor R := by
    calc
      cubeScaleFactor S = (3 : ℝ) ^ k := by
        rw [cubeScaleFactor,
          scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleColorClass_iff.mp hS).1]
      _ = cubeScaleFactor R := by
        rw [cubeScaleFactor,
          scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleColorClass_iff.mp hR).1]
  have hscale_nonneg : 0 ≤ cubeScaleFactor R := le_of_lt (cubeScaleFactor_pos R)
  have hxR := hx i
  have hyS := hy i
  rw [hscale] at hyS
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hgap : R.index i + 3 ≤ S.index i :=
      index_add_three_le_of_cubeColor_eq_of_lt hcolor hlt
    have hgap_real : ((R.index i : ℝ) + 3 : ℝ) ≤ (S.index i : ℝ) := by
      exact_mod_cast hgap
    have hcoord : cubeScaleFactor R ≤ ‖(y - x) i‖ := by
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg]
      · nlinarith [hyS.1, hxR.2, hgap_real, hscale_nonneg]
      · nlinarith [hyS.1, hxR.2, hgap_real, hscale_nonneg]
    have hnorm : cubeScaleFactor R ≤ ‖y - x‖ := by
      exact le_trans hcoord (norm_le_pi_norm (y - x) i)
    simpa [dist_eq_norm, norm_sub_rev] using hnorm
  · have hgap : S.index i + 3 ≤ R.index i :=
      index_add_three_le_of_cubeColor_eq_of_lt hcolor.symm hgt
    have hgap_real : ((S.index i : ℝ) + 3 : ℝ) ≤ (R.index i : ℝ) := by
      exact_mod_cast hgap
    have hcoord : cubeScaleFactor R ≤ ‖(x - y) i‖ := by
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg]
      · nlinarith [hxR.1, hyS.2, hgap_real, hscale_nonneg]
      · nlinarith [hxR.1, hyS.2, hgap_real, hscale_nonneg]
    have hnorm : cubeScaleFactor R ≤ ‖x - y‖ := by
      exact le_trans hcoord (norm_le_pi_norm (x - y) i)
    simpa [dist_eq_norm] using hnorm

theorem one_le_dist_of_ne_of_mem_descendantsAtScaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : CubeColor d} (hk : 0 ≤ k)
    (hR : R ∈ descendantsAtScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleColorClass Q k c) (hneq : R ≠ S)
    {x y : Vec d} (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet S) :
    1 ≤ dist x y := by
  have hscale_nonneg : 1 ≤ cubeScaleFactor R := by
    rw [cubeScaleFactor,
      scale_eq_of_mem_descendantsAtScale (mem_descendantsAtScaleColorClass_iff.mp hR).1]
    exact one_le_zpow₀ (show (1 : ℝ) ≤ 3 by norm_num) hk
  exact hscale_nonneg.trans
    (cubeScaleFactor_le_dist_of_ne_of_mem_descendantsAtScaleColorClass hR hS hneq hx hy)

theorem pairwiseDisjoint_descendantsAtScaleColorClass {d : ℕ} (Q : TriadicCube d) (k : ℤ)
    (c : CubeColor d) :
    (descendantsAtScaleColorClass Q k c : Set (TriadicCube d)).PairwiseDisjoint cubeSet := by
  intro R hR S hS hneq
  exact disjoint_cubeSet_of_ne_of_mem_descendantsAtScaleColorClass hR hS hneq

end Homogenization
