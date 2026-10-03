/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZDecomposition

/-!
# Existence of the dyadic Calderón--Zygmund decomposition

This module turns the maximal-cube estimates into the consumer-facing
decomposition structure.  The good and bad parts are integrated directly over
the disjoint cube family.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Foundation.Euclidean

private theorem dyadicGoodPart_eq_average_on_cube
    {F : Vec3 → ℝ} {D : Set DyadicIndex}
    (hD : D.Pairwise (Function.onFun Disjoint dyadicCubeSet))
    {Q : DyadicIndex} (hQ : Q ∈ D) {x : Vec3}
    (hx : x ∈ dyadicCubeSet Q) :
    dyadicGoodPart F D x = dyadicAverage F Q := by
  let hxmem : dyadicCubeMember D x := ⟨Q, hQ, hx⟩
  have hchoose := Classical.choose_spec hxmem
  have heq : Classical.choose hxmem = Q := by
    by_contra hne
    exact (Set.disjoint_left.1 (hD hchoose.1 hQ hne)) hchoose.2 hx
  simp only [dyadicGoodPart, dite_eq_left hxmem]
  rw [heq]

private theorem dyadicGoodPart_l1_le
    {F : Vec3 → ℝ} (hF : Integrable F) {D : Set DyadicIndex}
    (hD : D.Pairwise (Function.onFun Disjoint dyadicCubeSet)) :
    (∫⁻ x, ENNReal.ofReal |dyadicGoodPart F D x|) ≤ dyadicL1Norm F := by
  let U : Set Vec3 := ⋃ Q : {Q // Q ∈ D}, dyadicCubeSet Q.1
  have hUmeas : MeasurableSet U := by
    apply MeasurableSet.iUnion
    intro Q
    exact dyadicCube_measurable Q.1.scale Q.1.corner
  have hUdisjoint : Pairwise (Function.onFun Disjoint
      (fun Q : {Q // Q ∈ D} => dyadicCubeSet Q.1)) := by
    intro Q R hQR
    exact hD Q.2 R.2 (Subtype.coe_ne_coe.mpr hQR)
  have hU_good :
      (∫⁻ x in U, ENNReal.ofReal |dyadicGoodPart F D x|) ≤
        ∫⁻ x in U, ENNReal.ofReal |F x| := by
    calc
      (∫⁻ x in U, ENNReal.ofReal |dyadicGoodPart F D x|) =
          tsum (fun Q : {Q // Q ∈ D} =>
            ∫⁻ x in dyadicCubeSet Q.1,
              ENNReal.ofReal |dyadicGoodPart F D x|) := by
        dsimp [U]
        apply lintegral_iUnion
        · intro Q
          exact dyadicCube_measurable Q.1.scale Q.1.corner
        · exact hUdisjoint
      _ = tsum (fun Q : {Q // Q ∈ D} =>
          ENNReal.ofReal |dyadicAverage F Q.1| *
            volume (dyadicCubeSet Q.1)) := by
        apply tsum_congr
        intro Q
        calc
          (∫⁻ x in dyadicCubeSet Q.1,
              ENNReal.ofReal |dyadicGoodPart F D x|) =
              ∫⁻ x in dyadicCubeSet Q.1,
                ENNReal.ofReal |dyadicAverage F Q.1| := by
            apply setLIntegral_congr_fun
              (dyadicCube_measurable Q.1.scale Q.1.corner)
            intro x hx
            change ENNReal.ofReal |dyadicGoodPart F D x| =
              ENNReal.ofReal |dyadicAverage F Q.1|
            rw [dyadicGoodPart_eq_average_on_cube hD Q.2 hx]
          _ = ENNReal.ofReal |dyadicAverage F Q.1| *
              volume (dyadicCubeSet Q.1) := by
            exact setLIntegral_const _ _
      _ ≤ tsum (fun Q : {Q // Q ∈ D} =>
          ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) := by
        apply ENNReal.tsum_le_tsum
        intro Q
        have hI : IntegrableOn (fun x => |F x|)
            (dyadicCubeSet Q.1) volume := hF.norm.integrableOn
        have hnonneg : 0 ≤ᵐ[volume.restrict (dyadicCubeSet Q.1)]
            (fun x => |F x|) := ae_of_all _ (fun x => abs_nonneg _)
        have havg := ofReal_setAverage hI hnonneg
        have habs := abs_dyadicAverage_le_dyadicAbsAverage (F := F) Q.1
        have hle : ENNReal.ofReal |dyadicAverage F Q.1| ≤
            ENNReal.ofReal (⨍ x in dyadicCubeSet Q.1, |F x|) := by
          exact ENNReal.ofReal_le_ofReal habs
        rw [havg] at hle
        have hvol0 : volume (dyadicCubeSet Q.1) ≠ 0 := by
          change volume (dyadicCube Q.1.scale Q.1.corner) ≠ 0
          rw [volume_dyadicCube_eq_pow]
          positivity
        have hvoltop : volume (dyadicCubeSet Q.1) ≠ ∞ := by
          change volume (dyadicCube Q.1.scale Q.1.corner) ≠ ∞
          rw [volume_dyadicCube_eq_pow]
          exact ENNReal.ofReal_ne_top
        have hconst :=
          (ENNReal.le_div_iff_mul_le (Or.inl hvol0) (Or.inl hvoltop)).mp hle
        simpa only [mul_comm] using hconst
      _ = ∫⁻ x in U, ENNReal.ofReal |F x| := by
        symm
        dsimp [U]
        apply lintegral_iUnion
        · intro Q
          exact dyadicCube_measurable Q.1.scale Q.1.corner
        · exact hUdisjoint
  have hU_compl :
      (∫⁻ x in Uᶜ, ENNReal.ofReal |dyadicGoodPart F D x|) =
        ∫⁻ x in Uᶜ, ENNReal.ofReal |F x| := by
    apply setLIntegral_congr_fun hUmeas.compl
    intro x hx
    have hxmem : ¬dyadicCubeMember D x := by
      intro hxmem
      obtain ⟨Q, hQ, hxQ⟩ := hxmem
      exact hx (mem_iUnion.2 ⟨⟨Q, hQ⟩, hxQ⟩)
    have heq := dyadicGoodPart_eq_of_not_mem (F := F) hxmem
    simp only [heq]
  calc
    (∫⁻ x, ENNReal.ofReal |dyadicGoodPart F D x|) =
        (∫⁻ x in U, ENNReal.ofReal |dyadicGoodPart F D x|) +
          ∫⁻ x in Uᶜ, ENNReal.ofReal |dyadicGoodPart F D x| := by
      symm
      exact lintegral_add_compl _ hUmeas
    _ ≤ (∫⁻ x in U, ENNReal.ofReal |F x|) +
          ∫⁻ x in Uᶜ, ENNReal.ofReal |F x| := by
      exact add_le_add hU_good (le_of_eq hU_compl)
    _ = dyadicL1Norm F := by
      dsimp [dyadicL1Norm]
      exact lintegral_add_compl _ hUmeas

private theorem dyadicBadPart_l1_sum_le
    {F : Vec3 → ℝ} (hF : Integrable F) {D : Set DyadicIndex}
    (hD : D.Pairwise (Function.onFun Disjoint dyadicCubeSet)) :
    (tsum (fun Q : {Q // Q ∈ D} =>
      ∫⁻ x in dyadicCubeSet Q.1,
        ENNReal.ofReal |dyadicBadPart F Q.1 x|)) ≤
      2 * dyadicL1Norm F := by
  let U : Set Vec3 := ⋃ Q : {Q // Q ∈ D}, dyadicCubeSet Q.1
  have hUdisjoint : Pairwise (Function.onFun Disjoint
      (fun Q : {Q // Q ∈ D} => dyadicCubeSet Q.1)) := by
    intro Q R hQR
    exact hD Q.2 R.2 (Subtype.coe_ne_coe.mpr hQR)
  have hbad (Q : {Q // Q ∈ D}) :
      (∫⁻ x in dyadicCubeSet Q.1,
        ENNReal.ofReal |dyadicBadPart F Q.1 x|) ≤
        2 * (∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) := by
    have hrewrite :
        (∫⁻ x in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 x|) =
          ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |F x - dyadicAverage F Q.1| := by
      apply setLIntegral_congr_fun
        (dyadicCube_measurable Q.1.scale Q.1.corner)
      intro x hx
      change ENNReal.ofReal (|(dyadicCubeSet Q.1).indicator
        (fun x => F x - dyadicAverage F Q.1) x|) =
        ENNReal.ofReal |F x - dyadicAverage F Q.1|
      have hx' : x ∈ dyadicCubeSet Q.1 := hx
      rw [Set.indicator_of_mem hx']
    have hI : IntegrableOn (fun x => |F x|)
        (dyadicCubeSet Q.1) volume := hF.norm.integrableOn
    have hnonneg : 0 ≤ᵐ[volume.restrict (dyadicCubeSet Q.1)]
        (fun x => |F x|) := ae_of_all _ (fun x => abs_nonneg _)
    have havg := ofReal_setAverage hI hnonneg
    have habs := abs_dyadicAverage_le_dyadicAbsAverage (F := F) Q.1
    have hconst :
        ENNReal.ofReal |dyadicAverage F Q.1| * volume (dyadicCubeSet Q.1) ≤
          ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x| := by
      have hle : ENNReal.ofReal |dyadicAverage F Q.1| ≤
          ENNReal.ofReal (⨍ x in dyadicCubeSet Q.1, |F x|) :=
        ENNReal.ofReal_le_ofReal habs
      rw [havg] at hle
      have hvol0 : volume (dyadicCubeSet Q.1) ≠ 0 := by
        change volume (dyadicCube Q.1.scale Q.1.corner) ≠ 0
        rw [volume_dyadicCube_eq_pow]
        positivity
      have hvoltop : volume (dyadicCubeSet Q.1) ≠ ∞ := by
        change volume (dyadicCube Q.1.scale Q.1.corner) ≠ ∞
        rw [volume_dyadicCube_eq_pow]
        exact ENNReal.ofReal_ne_top
      exact (ENNReal.le_div_iff_mul_le
        (Or.inl hvol0) (Or.inl hvoltop)).mp hle
    rw [hrewrite]
    calc
      (∫⁻ x in dyadicCubeSet Q.1,
          ENNReal.ofReal |F x - dyadicAverage F Q.1|) ≤
          ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal (|F x| + |dyadicAverage F Q.1|) := by
        apply lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal (abs_sub _ _)
      _ = (∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) +
          ENNReal.ofReal |dyadicAverage F Q.1| *
            volume (dyadicCubeSet Q.1) := by
        calc
          (∫⁻ x in dyadicCubeSet Q.1,
              ENNReal.ofReal (|F x| + |dyadicAverage F Q.1|)) =
              ∫⁻ x in dyadicCubeSet Q.1,
                (ENNReal.ofReal |F x| +
                  ENNReal.ofReal |dyadicAverage F Q.1|) := by
            apply setLIntegral_congr_fun
              (dyadicCube_measurable Q.1.scale Q.1.corner)
            intro x hx
            change ENNReal.ofReal (|F x| + |dyadicAverage F Q.1|) =
              ENNReal.ofReal |F x| + ENNReal.ofReal |dyadicAverage F Q.1|
            rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          _ = (∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) +
              ENNReal.ofReal |dyadicAverage F Q.1| *
                volume (dyadicCubeSet Q.1) := by
            rw [lintegral_add_right
              (fun x => ENNReal.ofReal |F x|)
              (μ := volume.restrict (dyadicCubeSet Q.1)) measurable_const,
              setLIntegral_const]
      _ ≤ (∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) +
          (∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) := by
        simpa [add_comm] using
          (add_le_add_left hconst
            (∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|))
      _ = 2 * (∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|) := by
        ring
  have hsumF :
      (tsum (fun Q : {Q // Q ∈ D} =>
          ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|)) ≤
        dyadicL1Norm F := by
    calc
      (tsum (fun Q : {Q // Q ∈ D} =>
          ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|)) =
          ∫⁻ x in U, ENNReal.ofReal |F x| := by
        symm
        dsimp [U]
        apply lintegral_iUnion
        · intro Q
          exact dyadicCube_measurable Q.1.scale Q.1.corner
        · exact hUdisjoint
      _ ≤ dyadicL1Norm F := by
        dsimp [dyadicL1Norm]
        gcongr
        exact MeasureTheory.Measure.restrict_le_self
  calc
    (tsum (fun Q : {Q // Q ∈ D} =>
        ∫⁻ x in dyadicCubeSet Q.1,
        ENNReal.ofReal |dyadicBadPart F Q.1 x|)) ≤
        tsum (fun Q : {Q // Q ∈ D} =>
          2 * (∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|)) :=
      ENNReal.tsum_le_tsum (fun Q => hbad Q)
    _ = 2 * (tsum (fun Q : {Q // Q ∈ D} =>
        ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |F x|)) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ 2 * dyadicL1Norm F := by gcongr

private theorem dyadicBadPart_mean_zero
    {F : Vec3 → ℝ} (hF : Integrable F) (Q : DyadicIndex) :
    ∫ x in dyadicCubeSet Q, dyadicBadPart F Q x = 0 := by
  have hvoltop : volume (dyadicCubeSet Q) ≠ ∞ := by
    change volume (dyadicCube Q.scale Q.corner) ≠ ∞
    rw [volume_dyadicCube_eq_pow]
    exact ENNReal.ofReal_ne_top
  rw [dyadicBadPart]
  change ∫ x in dyadicCube Q.scale Q.corner,
      (dyadicCube Q.scale Q.corner).indicator
        (fun x => F x - dyadicAverage F Q) x = 0
  rw [setIntegral_indicator (dyadicCube_measurable Q.scale Q.corner)]
  simp only [inter_self]
  change ∫ x in dyadicCubeSet Q, F x - dyadicAverage F Q = 0
  have hzero := setIntegral_setAverage_sub hvoltop hF.integrableOn
  calc
    (∫ x in dyadicCubeSet Q, F x - dyadicAverage F Q) =
        -(∫ x in dyadicCubeSet Q,
          (⨍ a in dyadicCubeSet Q, F a) - F x) := by
      rw [← integral_neg]
      congr 1
      funext x
      simp [dyadicAverage]
    _ = 0 := by rw [hzero, neg_zero]

theorem exists_calderonZygmund_decomposition
    {F : Vec3 → ℝ} {height : ℝ} (hF : Integrable F)
    (hheight : 0 < height) :
    ∃ D : CZDecomposition F height,
      D.cubes = dyadicMaximalCubes F height := by
  let D : Set DyadicIndex := dyadicMaximalCubes F height
  have hspec := dyadicMaximalCubes_spec hF hheight
  dsimp only at hspec
  obtain ⟨hcount, hpair, hgt, hle, hparent, hvol, hoff, hgood⟩ := hspec
  refine ⟨
    { height_pos := hheight
      integrable := hF
      cubes := D
      cubes_countable := hcount
      cubes_pairwise_disjoint := hpair
      cube_average_gt := hgt
      cube_average_le := hle
      parent_average_le := hparent
      cube_volume_sum_le := hvol
      off_cubes_le_ae := hoff
      good_part_bound_ae := hgood
      good_part_l1_le := dyadicGoodPart_l1_le hF hpair
      bad_part_mean_zero := fun Q _ => dyadicBadPart_mean_zero hF Q
      bad_part_l1_sum_le := dyadicBadPart_l1_sum_le hF hpair }, rfl⟩

end CKN.Foundation.Euclidean
