/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondOperator
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondBadPart
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationLpChar
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationRestricted

/-!
# Riesz Second Weak Assembly

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

def czGood {level : ℝ} (F : Vec3 → ℝ) (D : CZDecomposition F level) : Vec3 → ℝ :=
  dyadicGoodPart F D.cubes

def czBad {level : ℝ} (F : Vec3 → ℝ) (D : CZDecomposition F level)
    (Q : {Q // Q ∈ D.cubes}) : Vec3 → ℝ :=
  dyadicBadPart F Q.1

theorem dyadic_good_part_memLp_two
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) :
    MemLp (dyadicGoodPart F D.cubes) (2 : ℝ≥0∞) volume := by
  let U : Set Vec3 := ⋃ Q : {Q // Q ∈ D.cubes}, dyadicCubeSet Q.1
  have hU : MeasurableSet U := by
    dsimp [U]
    apply MeasurableSet.iUnion
    intro Q
    exact dyadicCube_measurable Q.1.scale Q.1.corner
  have hsum : AEMeasurable (fun x : Vec3 =>
      ∑' Q : {Q // Q ∈ D.cubes},
        (dyadicCubeSet Q.1).indicator (fun _ => dyadicAverage F Q.1) x) := by
    apply AEMeasurable.tsum
    intro Q
    exact (measurable_const : Measurable (fun _ : Vec3 => dyadicAverage F Q.1)).aemeasurable.indicator
      (dyadicCube_measurable Q.1.scale Q.1.corner)
  have hrep : AEMeasurable (fun x : Vec3 =>
      U.indicator (fun x => ∑' Q : {Q // Q ∈ D.cubes},
        (dyadicCubeSet Q.1).indicator (fun _ => dyadicAverage F Q.1) x) x +
      Uᶜ.indicator F x) := by
    exact (hsum.indicator hU).add
      (hF₂.aestronglyMeasurable.indicator hU.compl).aemeasurable
  have hgeq : (fun x => dyadicGoodPart F D.cubes x) =ᵐ[volume]
      (fun x => U.indicator (fun x => ∑' Q : {Q // Q ∈ D.cubes},
        (dyadicCubeSet Q.1).indicator (fun _ => dyadicAverage F Q.1) x) x +
      Uᶜ.indicator F x) := by
    apply ae_of_all
    intro x
    by_cases hxU : x ∈ U
    · obtain ⟨Q, hQx⟩ := mem_iUnion.1 hxU
      have hxmem : dyadicCubeMember D.cubes x := ⟨Q.1, Q.2, hQx⟩
      have hchoose : Classical.choose hxmem = Q.1 := by
        by_contra hne
        exact (Set.disjoint_left.1
          (D.cubes_pairwise_disjoint (Classical.choose_spec hxmem).1
            Q.2 hne)) (Classical.choose_spec hxmem).2 hQx
      have hgood : dyadicGoodPart F D.cubes x = dyadicAverage F Q.1 := by
        simp only [dyadicGoodPart, dite_eq_left hxmem]
        rw [hchoose]
      have hzero : ∀ R : {R // R ∈ D.cubes},
          x ∉ dyadicCubeSet R.1 →
            (dyadicCubeSet R.1).indicator
              (fun _ => dyadicAverage F R.1) x = 0 := by
        intro R hR
        exact Set.indicator_of_notMem hR _
      have huniq : ∀ R : {R // R ∈ D.cubes}, R ≠ Q →
          x ∉ dyadicCubeSet R.1 := by
        intro R hRQ hxR
        exact (Set.disjoint_left.1
          (D.cubes_pairwise_disjoint R.2 Q.2
            (Subtype.coe_ne_coe.mpr hRQ))) hxR hQx
      have hsum : ∑' R : {R // R ∈ D.cubes},
          (dyadicCubeSet R.1).indicator
            (fun _ => dyadicAverage F R.1) x = dyadicAverage F Q.1 := by
        rw [tsum_eq_single Q]
        · exact Set.indicator_of_mem hQx _
        · intro R hRQ
          exact hzero R (huniq R hRQ)
      have hnot : x ∉ Uᶜ := by
        exact not_not_intro hxU
      simp only [Set.indicator_of_mem hxU, Set.indicator_of_notMem hnot]
      simp
      rw [hgood, hsum]
    · have hxmem : ¬dyadicCubeMember D.cubes x := by
        intro hxmem
        obtain ⟨Q, hQ, hQx⟩ := hxmem
        exact hxU (mem_iUnion.2 ⟨⟨Q, hQ⟩, hQx⟩)
      have hzero : ∀ R : {R // R ∈ D.cubes},
          (dyadicCubeSet R.1).indicator
            (fun _ => dyadicAverage F R.1) x = 0 := by
        intro R
        apply Set.indicator_of_notMem
        intro hxR
        exact hxmem ⟨R.1, R.2, hxR⟩
      have hsum : ∑' R : {R // R ∈ D.cubes},
          (dyadicCubeSet R.1).indicator
            (fun _ => dyadicAverage F R.1) x = 0 := by
        have hz : (fun R : {R // R ∈ D.cubes} =>
            (dyadicCubeSet R.1).indicator
              (fun _ => dyadicAverage F R.1) x) = fun _ => 0 := by
          funext R
          exact hzero R
        rw [hz]
        simp
      have hmemU : x ∈ Uᶜ := hxU
      simp only [dyadicGoodPart, dite_eq_right hxmem,
        Set.indicator_of_notMem hxU, Set.indicator_of_mem hmemU]
      simp
  have hgmem : MemLp (fun x => U.indicator (fun x => ∑' Q : {Q // Q ∈ D.cubes},
        (dyadicCubeSet Q.1).indicator (fun _ => dyadicAverage F Q.1) x) x +
      Uᶜ.indicator F x) (2 : ℝ≥0∞) volume := by
    have hFtop : dyadicL1Norm F < ∞ := by
      dsimp [dyadicL1Norm]
      have hne := (lintegral_ofReal_ne_top_iff_integrable
        D.integrable.norm.aestronglyMeasurable
        (ae_of_all _ (fun x => abs_nonneg (F x)))).2 D.integrable.norm
      exact lt_top_iff_ne_top.mpr hne
    have hgmeas : AEStronglyMeasurable (dyadicGoodPart F D.cubes) volume :=
      (hrep.congr hgeq.symm).aestronglyMeasurable
    have hgtop : (∫⁻ x, ENNReal.ofReal
        |dyadicGoodPart F D.cubes x|) < ∞ := by
      exact D.good_part_l1_le.trans_lt hFtop
    have hgl1norm : Integrable
        (fun x => ‖dyadicGoodPart F D.cubes x‖) volume :=
      (lintegral_ofReal_ne_top_iff_integrable
        hgmeas.norm
        (ae_of_all _ (fun x => abs_nonneg (dyadicGoodPart F D.cubes x)))).1
        (ne_of_lt hgtop)
    have hgl1 : Integrable (dyadicGoodPart F D.cubes) volume := by
      refine ⟨hgmeas, ?_⟩
      simpa only [hasFiniteIntegral_iff_norm, Real.norm_eq_abs, abs_abs] using
        hgl1norm.hasFiniteIntegral
    have hgsq : Integrable
        (fun x => (dyadicGoodPart F D.cubes x) ^ (2 : ℕ)) volume := by
      refine Integrable.mono' (hgl1.norm.mul_const (8 * level)) ?_ ?_
      · exact hgmeas.pow 2
      · filter_upwards [D.good_part_bound] with x hx
        simp only [Real.norm_eq_abs]
        rw [abs_pow]
        simpa only [pow_two] using
          (mul_le_mul_of_nonneg_left hx
            (abs_nonneg (dyadicGoodPart F D.cubes x)))
    have hg₂ : MemLp (dyadicGoodPart F D.cubes) (2 : ℝ≥0∞) volume :=
      (memLp_two_iff_integrable_sq hgmeas).2 hgsq
    exact hg₂.ae_eq hgeq
  exact (memLp_congr_ae hgeq).2 hgmem

theorem dyadic_good_part_energy
    {F : Vec3 → ℝ} {level A : ℝ} (D : CZDecomposition F level)
    (hF : Integrable F) (hF₂ : MemLp F (2 : ℝ≥0∞) volume) (hA : 0 ≤ A)
    (hAeq : dyadicL1Norm F = ENNReal.ofReal A) :
    ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤ 8 * level * A := by
  have hg₂ := dyadic_good_part_memLp_two D hF₂
  have hgsq := hg₂.integrable_sq
  have hgl1 : Integrable (dyadicGoodPart F D.cubes) volume := by
    have hgm : AEStronglyMeasurable (dyadicGoodPart F D.cubes) volume :=
      hg₂.aestronglyMeasurable
    have htop : (∫⁻ x, ENNReal.ofReal
        |dyadicGoodPart F D.cubes x|) < ∞ :=
      D.good_part_l1_le.trans_lt (by
        dsimp [dyadicL1Norm]
        have hne := (lintegral_ofReal_ne_top_iff_integrable
          hF.norm.aestronglyMeasurable
          (ae_of_all _ (fun x => abs_nonneg (F x)))).2 hF.norm
        exact lt_top_iff_ne_top.mpr hne)
    have hnorm : Integrable
        (fun x => ‖dyadicGoodPart F D.cubes x‖) volume :=
      (lintegral_ofReal_ne_top_iff_integrable hgm.norm
        (ae_of_all _ (fun x => abs_nonneg (dyadicGoodPart F D.cubes x)))).1
        (ne_of_lt htop)
    refine ⟨hgm, ?_⟩
    simpa only [hasFiniteIntegral_iff_norm, Real.norm_eq_abs, abs_abs] using
      hnorm.hasFiniteIntegral
  have hmajor : Integrable
      (fun x => (8 * level) * |dyadicGoodPart F D.cubes x|) volume :=
    hgl1.norm.const_mul (8 * level)
  have hpoint : ∀ᵐ x ∂volume,
      (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤
        (8 * level) * |dyadicGoodPart F D.cubes x| := by
    filter_upwards [D.good_part_bound] with x hx
    calc
      (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) =
          |dyadicGoodPart F D.cubes x| ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ (8 * level) * |dyadicGoodPart F D.cubes x| := by
        simpa only [pow_two] using
          (mul_le_mul_of_nonneg_right hx (abs_nonneg _))
  have hInt := integral_mono_ae hgsq hmajor hpoint
  have hgoodof : ENNReal.ofReal (∫ x,
      |dyadicGoodPart F D.cubes x|) =
      ∫⁻ x, ENNReal.ofReal |dyadicGoodPart F D.cubes x| := by
    simpa only [Real.norm_eq_abs] using
      ofReal_integral_eq_lintegral_ofReal hgl1.norm
        (ae_of_all _ (fun x => abs_nonneg (dyadicGoodPart F D.cubes x)))
  have hreal : ∫ x, |dyadicGoodPart F D.cubes x| ≤ A := by
    apply (ENNReal.ofReal_le_ofReal_iff hA).mp
    rw [hgoodof, ← hAeq]
    exact D.good_part_l1_le
  calc
    ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤
        ∫ x, (8 * level) * |dyadicGoodPart F D.cubes x| := hInt
    _ = 8 * level * (∫ x, |dyadicGoodPart F D.cubes x|) := by
      rw [integral_const_mul]
    _ ≤ 8 * level * A := by
      exact mul_le_mul_of_nonneg_left hreal
        (mul_nonneg (by norm_num) D.height_pos.le)

theorem dyadic_bad_part_memLp_two
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume)
    (Q : {Q // Q ∈ D.cubes}) :
    MemLp (dyadicBadPart F Q.1) (2 : ℝ≥0∞) volume := by
  have hmeas : MeasurableSet (dyadicCubeSet Q.1) :=
    dyadicCube_measurable Q.1.scale Q.1.corner
  have hvol : volume (dyadicCubeSet Q.1) ≠ ∞ := by
    change volume (dyadicCube Q.1.scale Q.1.corner) ≠ ∞
    rw [volume_dyadicCube_eq_pow]
    exact ENNReal.ofReal_ne_top
  have hF' := hF₂.indicator hmeas
  have hc := memLp_indicator_const (2 : ℝ≥0∞) hmeas
    (dyadicAverage F Q.1) (Or.inr hvol)
  have hsub := hF'.sub hc
  convert hsub using 1
  funext x
  by_cases hx : x ∈ dyadicCubeSet Q.1
  · simp [dyadicBadPart, Set.indicator_of_mem hx]
  · simp [dyadicBadPart, Set.indicator, hx]

theorem dyadic_good_bad_decomposition_ae
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level) :
    F =ᵐ[volume] (fun x => dyadicGoodPart F D.cubes x +
      ∑' Q : {Q // Q ∈ D.cubes}, dyadicBadPart F Q.1 x) := by
  apply ae_of_all
  intro x
  change F x = dyadicGoodPart F D.cubes x +
    ∑' Q : {Q // Q ∈ D.cubes}, dyadicBadPart F Q.1 x
  by_cases hxmem : dyadicCubeMember D.cubes x
  · obtain ⟨Q, hQ, hQx⟩ := hxmem
    have hmem : dyadicCubeMember D.cubes x := ⟨Q, hQ, hQx⟩
    let Q' : {Q // Q ∈ D.cubes} := ⟨Q, hQ⟩
    have hchoose : Classical.choose hmem = Q := by
      by_contra hne
      exact (Set.disjoint_left.1
        (D.cubes_pairwise_disjoint (Classical.choose_spec hmem).1
          hQ hne)) (Classical.choose_spec hmem).2 hQx
    have hgood : dyadicGoodPart F D.cubes x = dyadicAverage F Q := by
      simp only [dyadicGoodPart, dite_eq_left hmem]
      rw [hchoose]
    have hzero : ∀ R : {R // R ∈ D.cubes}, R ≠ Q' →
        dyadicBadPart F R.1 x = 0 := by
      intro R hRQ
      have hnot : x ∉ dyadicCubeSet R.1 := by
        intro hxR
        exact (Set.disjoint_left.1
          (D.cubes_pairwise_disjoint R.2 Q'.2
            (Subtype.coe_ne_coe.mpr hRQ))) hxR hQx
      exact Set.indicator_of_notMem hnot _
    have hsum : ∑' R : {R // R ∈ D.cubes},
        dyadicBadPart F R.1 x = dyadicBadPart F Q x := by
      rw [tsum_eq_single Q']
      · intro R hRQ
        exact hzero R hRQ
    have hbad : dyadicBadPart F Q x = F x - dyadicAverage F Q := by
      rw [dyadicBadPart, Set.indicator_of_mem hQx]
    rw [hgood, hsum, hbad]
    ring
  · have hzero : ∀ R : {R // R ∈ D.cubes},
        dyadicBadPart F R.1 x = 0 := by
      intro R
      apply Set.indicator_of_notMem
      intro hxR
      exact hxmem ⟨R.1, R.2, hxR⟩
    have hsum : ∑' R : {R // R ∈ D.cubes},
        dyadicBadPart F R.1 x = 0 := by
      have hz : (fun R : {R // R ∈ D.cubes} =>
          dyadicBadPart F R.1 x) = fun _ => 0 := by
        funext R
        exact hzero R
      rw [hz]
      simp
    have hgood : dyadicGoodPart F D.cubes x = F x := by
      simp only [dyadicGoodPart, dite_eq_right hxmem]
    rw [hgood, hsum]
    simp

theorem dyadic_bad_sum_memLp_two
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) :
    MemLp (fun x => F x - dyadicGoodPart F D.cubes x)
      (2 : ℝ≥0∞) volume := by
  exact hF₂.sub (dyadic_good_part_memLp_two D hF₂)

theorem rieszSecond_good_output_l2
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (hL2 : RieszSecondL2Input i j) (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) :
    MemLp (rieszSecondL2MeasurableOperator hL2
      (MemLp.toLp (dyadicGoodPart F D.cubes)
        (dyadic_good_part_memLp_two D hF₂))) (2 : ℝ≥0∞) volume ∧
      (∫ x, (rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp (dyadicGoodPart F D.cubes)
          (dyadic_good_part_memLp_two D hF₂)) x) ^ (2 : ℕ)) ≤
        ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) := by
  let g : Vec3 → ℝ := dyadicGoodPart F D.cubes
  have hg₂ : MemLp g (2 : ℝ≥0∞) volume := dyadic_good_part_memLp_two D hF₂
  let u : rieszSecondL2 := MemLp.toLp g hg₂
  have hmem_ext : MemLp
      ((rieszSecondL2Extension hL2 u : rieszSecondL2) : Vec3 → ℝ)
      (2 : ℝ≥0∞) volume := Lp.memLp _
  have hmem_op : MemLp (rieszSecondL2MeasurableOperator hL2 u)
      (2 : ℝ≥0∞) volume :=
    hmem_ext.ae_eq (rieszSecondL2MeasurableOperator_ae_eq_extension hL2 u).symm
  have hsq_ext := hmem_ext.integrable_sq
  have hsq_op := hmem_op.integrable_sq
  have hbound := rieszSecondL2MeasurableOperator_l2_bound hL2 u
  have hbound' : (∫⁻ x, ENNReal.ofReal
      ((rieszSecondL2MeasurableOperator hL2 u x) ^ (2 : ℕ))) ≤
      ∫⁻ x, ENNReal.ofReal (g x ^ (2 : ℕ)) := by
    calc
      (∫⁻ x, ENNReal.ofReal
          ((rieszSecondL2MeasurableOperator hL2 u x) ^ (2 : ℕ))) =
          ∫⁻ x, absE (rieszSecondL2MeasurableOperator hL2 u) x ^ (2 : ℕ) := by
        apply lintegral_congr
        intro x
        simp only [absE]
        rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
      _ ≤ ∫⁻ x, absE (u : Vec3 → ℝ) x ^ (2 : ℕ) := hbound
      _ = ∫⁻ x, ENNReal.ofReal (g x ^ (2 : ℕ)) := by
        apply lintegral_congr_ae
        filter_upwards [hg₂.coeFn_toLp] with x hx
        simp only [absE]
        rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, hx, sq_abs]
  have hreal : ∫ x,
      (rieszSecondL2MeasurableOperator hL2 u x) ^ (2 : ℕ) ≤
      ∫ x, g x ^ (2 : ℕ) := by
    have hleft := ofReal_integral_eq_lintegral_ofReal hsq_op
      (ae_of_all _ (fun x => sq_nonneg _))
    apply (ENNReal.ofReal_le_ofReal_iff
      (integral_nonneg (fun x => sq_nonneg _))).mp
    rw [hleft]
    have hrightg := ofReal_integral_eq_lintegral_ofReal hg₂.integrable_sq
      (ae_of_all _ (fun x => sq_nonneg _))
    rw [hrightg]
    exact hbound'
  simpa only [g, u] using And.intro hmem_op hreal

def rieszSecondPressureKernel (i j : Fin 3) : Vec3 → ℝ :=
  fun z => -rieszSecondKernel i j z

theorem rieszSecond_bad_part_interface_of_cube
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (D : CZDecomposition F level)
    (hdata : ∀ Q : {Q // Q ∈ D.cubes},
      IntegrableOn (dyadicBadPart F Q.1) (dyadicCubeSet Q.1) volume ∧
      (∀ x ∈ (rieszSecondCubeStar Q.1)ᶜ,
        IntegrableOn (fun y => rieszSecondKernel i j (x - y) *
          dyadicBadPart F Q.1 y) (dyadicCubeSet Q.1) volume) ∧
      AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(rieszSecondKernel i j (z.1 - z.2) -
          rieszSecondKernel i j (z.1 - dyadicCubeCenter Q.1.scale Q.1.corner)) *
            dyadicBadPart F Q.1 z.2|)
        ((volume.restrict (rieszSecondCubeStar Q.1)ᶜ).prod
          (volume.restrict (dyadicCubeSet Q.1))) ∧
      AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(rieszSecondKernel i j (z.2 - z.1) -
          rieszSecondKernel i j (z.2 - dyadicCubeCenter Q.1.scale Q.1.corner)) *
            dyadicBadPart F Q.1 z.1|)
        ((volume.restrict (dyadicCubeSet Q.1)).prod
          (volume.restrict (rieszSecondCubeStar Q.1)ᶜ))) :
    ∀ Q : {Q // Q ∈ D.cubes}, ∃ Tbad : Vec3 → ℝ,
      AEMeasurable (fun x => ENNReal.ofReal |Tbad x|)
        (volume.restrict
          (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ) ∧
      IntegrableOn Tbad (rieszSecondCubeStar Q.1)ᶜ volume ∧
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |Tbad x|) ≤
        ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
          ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 x| := by
  intro Q
  obtain ⟨hb, hterm, hjoint, hjointSwap⟩ := hdata Q
  obtain ⟨Tbad, hmeas, hIntegrable, hbound⟩ :=
    rieszSecond_bad_cube_hormander (Q := Q.1)
      (b := dyadicBadPart F Q.1) i j (D.bad_part_mean Q.2)
      hb hterm hjoint hjointSwap
  have hsubset : (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ ⊆
      (rieszSecondCubeStar Q.1)ᶜ := by
    intro x hx hxQ
    exact hx (mem_iUnion.2 ⟨Q, hxQ⟩)
  have hmeas' := hmeas.mono_measure
    (Measure.restrict_mono hsubset le_rfl)
  refine ⟨Tbad, hmeas', hIntegrable, hbound⟩

lemma measurableSet_rieszSecondCubeStar_assembly (Q : DyadicIndex) :
    MeasurableSet (rieszSecondCubeStar Q) := by
  have hc : Continuous (fun x : Vec3 =>
      vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner)) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact (isClosed_Iic.preimage hc).measurableSet

lemma dyadicL1Norm_lt_top_of_integrable {F : Vec3 → ℝ}
    (hF : Integrable F volume) : dyadicL1Norm F < ∞ := by
  dsimp [dyadicL1Norm]
  have hne := (lintegral_ofReal_ne_top_iff_integrable
    hF.norm.aestronglyMeasurable
    (ae_of_all _ (fun x => abs_nonneg (F x)))).2 hF.norm
  exact lt_top_iff_ne_top.mpr hne

def rieszSecondL2_cz_certificate_of_interfaces
    {i j : Fin 3} {F : Vec3 → ℝ} {level : ℝ}
    (hL2 : RieszSecondL2Input i j) (hF : Integrable F volume)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) (hlevel : 0 < level)
    (hcountable : ∀ D : CZDecomposition F level, ∃ Tbad :
        {Q // Q ∈ D.cubes} → Vec3 → ℝ,
      (∀ᵐ x ∂(volume.restrict
        (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
        (rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x -
          rieszSecondL2MeasurableOperator hL2
            (MemLp.toLp (dyadicGoodPart F D.cubes)
              (dyadic_good_part_memLp_two D hF₂)) x) =
          ∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x) ∧
      (∀ Q : {Q // Q ∈ D.cubes},
        AEMeasurable (fun x => ENNReal.ofReal |Tbad Q x|)
          (volume.restrict
            (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ)) ∧
      (∀ Q : {Q // Q ∈ D.cubes},
        (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
          ENNReal.ofReal |Tbad Q x|) ≤
          ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
            ∫⁻ x in dyadicCubeSet Q.1,
              ENNReal.ofReal |dyadicBadPart F Q.1 x|)) :
    RieszSecondL2CZCertificate hL2 F hF₂ level := by
  let A : ℝ := (dyadicL1Norm F).toReal
  have hnormtop : dyadicL1Norm F < ∞ := dyadicL1Norm_lt_top_of_integrable hF
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hAeq : dyadicL1Norm F = ENNReal.ofReal A := by
    dsimp [A]
    exact (ENNReal.ofReal_toReal hnormtop.ne).symm
  let G : CZDecomposition F level → Vec3 → ℝ := fun D x =>
    rieszSecondL2MeasurableOperator hL2
      (MemLp.toLp (dyadicGoodPart F D.cubes)
        (dyadic_good_part_memLp_two D hF₂)) x
  let B : CZDecomposition F level → Vec3 → ℝ := fun D x =>
    rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x - G D x
  have hgood : ∀ (D : CZDecomposition F level),
      ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤
      8 * level * A := by
    intro D
    exact dyadic_good_part_energy D hF hF₂ hA hAeq
  have hG : ∀ D, Integrable (fun x => G D x ^ (2 : ℕ)) volume ∧
      (∫ x, G D x ^ (2 : ℕ)) ≤
        (1 : ℝ) ^ 2 * ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) := by
    intro D
    obtain ⟨hm, hbound⟩ := rieszSecond_good_output_l2 hL2 D hF₂
    exact ⟨hm.integrable_sq, by simpa [G] using hbound⟩
  have hdecomp : ∀ D x,
      rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x =
        G D x + B D x := by
    intro D x
    simp only [B]
    ring
  have hTmem : MemLp
      (rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂))
      (2 : ℝ≥0∞) volume := by
    have hm : MemLp
        ((rieszSecondL2Extension hL2 (MemLp.toLp F hF₂) : rieszSecondL2) :
          Vec3 → ℝ) (2 : ℝ≥0∞) volume := Lp.memLp _
    exact hm.ae_eq
      (rieszSecondL2MeasurableOperator_ae_eq_extension hL2 _).symm
  have hBmem : ∀ D, MemLp (B D) (2 : ℝ≥0∞) volume := by
    intro D
    exact hTmem.sub ((rieszSecond_good_output_l2 hL2 D hF₂).1.ae_eq
      (by rfl))
  have hBmeas : ∀ D, Measurable (B D) := by
    intro D
    exact (rieszSecondL2MeasurableOperator_measurable hL2 _).sub
      (rieszSecondL2MeasurableOperator_measurable hL2 _)
  have hbad : ∀ D, ∃ Tbad : {Q // Q ∈ D.cubes} → Vec3 → ℝ,
      Integrable (B D) volume ∧
      (∀ᵐ x ∂(volume.restrict
          (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
        ENNReal.ofReal |B D x| ≤
          ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x|) ∧
      (∀ Q : {Q // Q ∈ D.cubes},
        AEMeasurable (fun x => ENNReal.ofReal |Tbad Q x|)
          (volume.restrict
            (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ)) ∧
      (∀ Q : {Q // Q ∈ D.cubes},
        (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
          ENNReal.ofReal |Tbad Q x|) ≤
          ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
            ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 x|) := by
    intro D
    let U : Set Vec3 := ⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1
    obtain ⟨Tbad, hcountable_eq, hmeas, hbridge⟩ := hcountable D
    have hU : MeasurableSet U := by
      dsimp [U]
      apply MeasurableSet.iUnion
      intro Q
      exact measurableSet_rieszSecondCubeStar_assembly Q.1
    have hpoint : ∀ᵐ x ∂(volume.restrict Uᶜ),
        ENNReal.ofReal |B D x| ≤
          ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x| := by
      filter_upwards [hcountable_eq] with x hx
      rw [show B D x =
          rieszSecondL2MeasurableOperator hL2 (MemLp.toLp F hF₂) x - G D x by
            rfl, hx]
      calc
        ENNReal.ofReal |∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x| =
            ‖∑' Q : {Q // Q ∈ D.cubes}, Tbad Q x‖ₑ := by
              simp only [Real.enorm_eq_ofReal_abs]
        _ ≤ ∑' Q : {Q // Q ∈ D.cubes}, ‖Tbad Q x‖ₑ :=
          enorm_tsum_le_tsum_enorm
        _ = ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x| := by
          apply tsum_congr
          intro Q
          simp only [Real.enorm_eq_ofReal_abs]
    have hBoutside := rieszSecond_bad_part_exterior_bound D
      hpoint hmeas hbridge
    have hUvol : volume U < ∞ := by
      have hsum := rieszSecondCubeStar_volume_sum D
      have hquot : dyadicL1Norm F / ENNReal.ofReal level < ∞ := by
        exact ENNReal.div_lt_top hnormtop.ne
          (ENNReal.ofReal_pos.mpr hlevel).ne'
      have hright : ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (dyadicL1Norm F / ENNReal.ofReal level) < ∞ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hquot
      exact lt_of_le_of_lt (by
        calc
          volume U ≤ ∑' Q : {Q // Q ∈ D.cubes},
              volume (rieszSecondCubeStar Q.1) := by
            dsimp [U]
            exact measure_iUnion_le
              (s := fun Q : {Q // Q ∈ D.cubes} => rieszSecondCubeStar Q.1)
          _ ≤ ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
              (dyadicL1Norm F / ENNReal.ofReal level) := hsum) hright
    have hBin : IntegrableOn (B D) U volume := by
      have hBin' := integrableOn_Lp_of_measure_ne_top
        (MemLp.toLp (B D) (hBmem D)) (by norm_num) hUvol.ne
      exact hBin'.congr_fun_ae
        (ae_restrict_of_ae (MemLp.coeFn_toLp (hBmem D)))
    have hfinite : (∫⁻ x in Uᶜ, ENNReal.ofReal |B D x|) < ∞ := by
      have hright : ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
          (2 * dyadicL1Norm F) < ∞ := by
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top (by norm_num) hnormtop)
      exact lt_of_le_of_lt hBoutside hright
    have hBout : IntegrableOn (B D) Uᶜ volume := by
      change Integrable (B D) (volume.restrict Uᶜ)
      have hnorm := (lintegral_ofReal_ne_top_iff_integrable
        (f := fun x => |B D x|) (μ := volume.restrict Uᶜ)
        ((hBmeas D).aestronglyMeasurable.mono_measure Measure.restrict_le_self).norm
        (ae_of_all _ (fun x => abs_nonneg (B D x)))).1 hfinite.ne
      exact (integrable_norm_iff
        ((hBmeas D).aestronglyMeasurable.mono_measure Measure.restrict_le_self)).1
        (by simpa only [Real.norm_eq_abs] using hnorm)
    have hBint : Integrable (B D) volume := by
      rw [← integrableOn_univ]
      simpa only [union_compl_self] using hBin.union hBout
    refine ⟨Tbad, hBint, ?_, ?_, ?_⟩
    · simpa [U] using hpoint
    · intro Q
      simpa [U] using hmeas Q
    · intro Q
      exact hbridge Q
  refine ⟨A, hA, hAeq, G, B, hdecomp, hgood, hG, hbad⟩

theorem rieszSecondL2_strong_type_of_restricted_inputs
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    {A₁ p : ℝ}
    (hTsub : ∀ f g, Measurable f → Integrable f volume → MemLp f 2 volume →
      Measurable g → MemLp g 2 volume → ∀ x,
        |rieszSecondL2RawOperator hL2 (f + g) x| ≤
          |rieszSecondL2RawOperator hL2 f x| +
            |rieszSecondL2RawOperator hL2 g x|)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) /
            ENNReal.ofReal l)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    {f : Vec3 → ℝ} (hf : Measurable f)
    (hfp : MemLp f (ENNReal.ofReal p) volume)
    (hf₂ : MemLp f (2 : ℝ≥0∞) volume) :
    ∫⁻ x, absE (rieszSecondL2RawOperator hL2 f) x ^ p ≤
      ENNReal.ofReal (p * (2 ^ p *
        (A₁ / (p - 1) + (1 : ℝ) ^ 2 / (2 - p)))) *
        ∫⁻ x, absE f x ^ p := by
  have hTmeas : ∀ g, Measurable g → MemLp g 2 volume →
      Measurable (rieszSecondL2RawOperator hL2 g) := by
    intro g hg hg₂
    exact rieszSecondL2RawOperator_measurable hL2 hg₂
  have hstrong : ∀ g, Measurable g → MemLp g 2 volume →
      ∫⁻ x, absE (rieszSecondL2RawOperator hL2 g) x ^ 2 ≤
        ENNReal.ofReal ((1 : ℝ) ^ 2) * ∫⁻ x, absE g x ^ 2 := by
    intro g hg hg₂
    have hae := rieszSecondL2RawOperator_ae_eq hL2 hg₂
    have hinput : ∫⁻ x, absE
        (MemLp.toLp g hg₂ : Vec3 → ℝ) x ^ (2 : ℕ) =
        ∫⁻ x, absE g x ^ (2 : ℕ) := by
      apply lintegral_congr_ae
      filter_upwards [hg₂.coeFn_toLp] with x hx
      simp only [absE, hx]
    calc
      ∫⁻ x, absE (rieszSecondL2RawOperator hL2 g) x ^ 2 =
          ∫⁻ x, absE (rieszSecondL2MeasurableOperator hL2
            (MemLp.toLp g hg₂)) x ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [hae] with x hx
        simp [absE, hx]
      _ ≤ ∫⁻ x, absE (MemLp.toLp g hg₂ : Vec3 → ℝ) x ^ 2 :=
        rieszSecondL2MeasurableOperator_l2_bound hL2 _
      _ = ∫⁻ x, absE g x ^ 2 := hinput
      _ = ENNReal.ofReal ((1 : ℝ) ^ 2) * ∫⁻ x, absE g x ^ 2 := by norm_num
  exact interpolation_weak11_strong22_of_l2_classes
    hTsub hTmeas hWeak11 hstrong hA₁ hp1 hp2 hf hfp hf₂

end CKN.Foundation.Euclidean
