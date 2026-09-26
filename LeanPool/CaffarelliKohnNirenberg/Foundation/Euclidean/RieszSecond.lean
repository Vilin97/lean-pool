/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HessianL2
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZDecomposition
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZDecompositionExistence
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Hormander
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Riesz Second

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean
private lemma measure_abs_gt_le_integral_sq {f : Vec3 → ℝ}
    (hf : Integrable (fun x => f x ^ (2 : ℕ)) volume)
    {a : ℝ} (ha : 0 < a) :
    volume {x | a < |f x|} ≤
      ENNReal.ofReal (∫ x, f x ^ (2 : ℕ)) /
        ENNReal.ofReal (a ^ (2 : ℕ)) := by
  have hsqae : AEMeasurable (fun x => ENNReal.ofReal (f x ^ (2 : ℕ))) volume := by
    exact AEMeasurable.ennreal_ofReal hf.aestronglyMeasurable.aemeasurable
  have hε : ENNReal.ofReal (a ^ (2 : ℕ)) ≠ 0 := by
    exact ne_of_gt ((ENNReal.ofReal_pos).2 (by positivity))
  have hεtop : ENNReal.ofReal (a ^ (2 : ℕ)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hmark := meas_ge_le_lintegral_div hsqae hε hεtop
  have hsub : {x | a < |f x|} ⊆
      {x | ENNReal.ofReal (a ^ (2 : ℕ)) ≤
        ENNReal.ofReal (f x ^ (2 : ℕ))} := by
    intro x hx
    change a < |f x| at hx
    change ENNReal.ofReal (a ^ (2 : ℕ)) ≤ ENNReal.ofReal (f x ^ (2 : ℕ))
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
    nlinarith only [hx, ha, abs_nonneg (f x), sq_abs (f x)]
  have hmeas := measure_mono (μ := (volume : Measure Vec3)) hsub
  calc
    volume {x | a < |f x|} ≤
        volume {x | ENNReal.ofReal (a ^ (2 : ℕ)) ≤
          ENNReal.ofReal (f x ^ (2 : ℕ))} := hmeas
    _ ≤ (∫⁻ x, ENNReal.ofReal (f x ^ (2 : ℕ))) /
        ENNReal.ofReal (a ^ (2 : ℕ)) := hmark
    _ = ENNReal.ofReal (∫ x, f x ^ (2 : ℕ)) /
        ENNReal.ofReal (a ^ (2 : ℕ)) := by
      have hnonneg : 0 ≤ᵐ[volume] (fun x => f x ^ (2 : ℕ)) :=
        ae_of_all _ (fun x => sq_nonneg (f x))
      rw [← ofReal_integral_eq_lintegral_ofReal hf hnonneg]
private lemma measure_abs_gt_le_integral {f : Vec3 → ℝ}
    (hf : Integrable f volume) {a : ℝ} (ha : 0 < a) :
    volume {x | a < |f x|} ≤
      (∫⁻ x, ENNReal.ofReal |f x|) / ENNReal.ofReal a := by
  have hfae : AEMeasurable (fun x => ENNReal.ofReal |f x|) volume := by
    exact AEMeasurable.ennreal_ofReal hf.norm.aestronglyMeasurable.aemeasurable
  have hε : ENNReal.ofReal a ≠ 0 := by
    exact ne_of_gt ((ENNReal.ofReal_pos).2 ha)
  have hεtop : ENNReal.ofReal a ≠ ∞ := ENNReal.ofReal_ne_top
  have hmark := meas_ge_le_lintegral_div hfae hε hεtop
  have hsub : {x | a < |f x|} ⊆
      {x | ENNReal.ofReal a ≤ ENNReal.ofReal |f x|} := by
    intro x hx
    change a < |f x| at hx
    change ENNReal.ofReal a ≤ ENNReal.ofReal |f x|
    exact ENNReal.ofReal_le_ofReal hx.le
  calc
    volume {x | a < |f x|} ≤
        volume {x | ENNReal.ofReal a ≤ ENNReal.ofReal |f x|} :=
      measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal |f x|) / ENNReal.ofReal a := hmark
private lemma translate_setLIntegral {E : Set Vec3} (hE : MeasurableSet E)
    {f : Vec3 → ℝ≥0∞} (hf : Measurable f) (c : Vec3) :
    (∫⁻ x in E, f (x - c)) =
      ∫⁻ z in {z | z + c ∈ E}, f z := by
  let g : Vec3 → ℝ≥0∞ := {z | z + c ∈ E}.indicator f
  have hg : Measurable g := by
    exact hf.indicator (measurableSet_preimage (measurable_add_const c) hE)
  calc
    (∫⁻ x in E, f (x - c)) = ∫⁻ x, E.indicator (fun x => f (x - c)) x := by
      rw [lintegral_indicator hE]
    _ = ∫⁻ x, g (x - c) := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ E
      · have hmem : x - c ∈ {z | z + c ∈ E} := by
          simpa [sub_add_cancel] using hx
        simp [g, Set.indicator, hx, hmem]
      · have hxc : x - c ∉ {z | z + c ∈ E} := by
          intro h
          exact hx (by simpa [sub_add_cancel] using h)
        simp [g, Set.indicator, hx, hxc]
    _ = ∫⁻ z, g z :=
      (measurePreserving_sub_right (volume : Measure Vec3) c).lintegral_comp hg
    _ = ∫⁻ z in {z | z + c ∈ E}, f z := by
      symm
      rw [lintegral_indicator]
      exact measurableSet_preimage (measurable_add_const c) hE
private lemma vec3EuclideanNorm_le_sqrt_three_mul_norm (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    have hv : vec3EuclideanNorm v ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
      unfold vec3EuclideanNorm
      exact Real.sq_sqrt (Finset.sum_nonneg (fun i _hi => sq_nonneg _))
    rw [hv, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ∑ i : Fin 3, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2
/-- The Euclidean `2√3` enlargement of a dyadic cube, with the cube's
    sup-radius `dyadicScale Q.scale / 2`. -/
@[expose]
def rieszSecondCubeStar (Q : DyadicIndex) : Set Vec3 :=
  {x | vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner) ≤
    2 * Real.sqrt 3 * (dyadicScale Q.scale / 2)}

private lemma measurableSet_rieszSecondCubeStar (Q : DyadicIndex) :
    MeasurableSet (rieszSecondCubeStar Q) := by
  have hc : Continuous (fun x : Vec3 =>
      vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner)) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact (isClosed_Iic.preimage hc).measurableSet

private lemma dyadicCube_subset_rieszSecondCubeStar (Q : DyadicIndex) :
    dyadicCubeSet Q ⊆ rieszSecondCubeStar Q := by
  intro x hx
  have hs : 0 < dyadicScale Q.scale := dyadicScale_pos Q.scale
  have hsup : ‖x - dyadicCubeCenter Q.scale Q.corner‖ ≤ dyadicScale Q.scale / 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    have hx' := (mem_dyadicCube.mp hx) i
    change |x i - dyadicCubeCenter Q.scale Q.corner i| ≤ dyadicScale Q.scale / 2
    dsimp [dyadicCubeCenter]
    rw [abs_le]
    constructor <;> nlinarith only [hx'.1, hx'.2, hs]
  have heuc := vec3EuclideanNorm_le_sqrt_three_mul_norm
    (x - dyadicCubeCenter Q.scale Q.corner)
  change vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner) ≤
    2 * Real.sqrt 3 * (dyadicScale Q.scale / 2)
  calc
    vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner) ≤
        Real.sqrt 3 * ‖x - dyadicCubeCenter Q.scale Q.corner‖ := heuc
    _ ≤ Real.sqrt 3 * (dyadicScale Q.scale / 2) := by
      gcongr
    _ ≤ 2 * Real.sqrt 3 * (dyadicScale Q.scale / 2) := by
      nlinarith only [mul_nonneg (Real.sqrt_nonneg 3) (le_of_lt hs)]

/-- The enlarged cube has the explicit volume comparison needed in the bad
    region estimate. -/
theorem rieszSecondCubeStar_volume (Q : DyadicIndex) :
    volume (rieszSecondCubeStar Q) ≤
      ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
        volume (dyadicCubeSet Q) := by
  let c : Vec3 := dyadicCubeCenter Q.scale Q.corner
  let s : ℝ := dyadicScale Q.scale / 2
  have hs : 0 < s := div_pos (dyadicScale_pos Q.scale) (by norm_num)
  have hsub : rieszSecondCubeStar Q ⊆ vec3Ball c (4 * Real.sqrt 3 * s) := by
    intro x hx
    rw [mem_vec3Ball]
    change vec3EuclideanNorm (x - c) ≤ 2 * Real.sqrt 3 * s at hx
    dsimp [c, s] at hx ⊢
    have hr : 0 < 2 * Real.sqrt 3 * (dyadicScale Q.scale / 2) := by positivity
    nlinarith only [hx, hr]
  calc
    volume (rieszSecondCubeStar Q) ≤ volume (vec3Ball c (4 * Real.sqrt 3 * s)) :=
      measure_mono hsub
    _ = ENNReal.ofReal (4 * Real.sqrt 3 * s) ^ 3 *
        ENNReal.ofReal (Real.pi * 4 / 3) := volume_vec3Ball_eq _ _
    _ = ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
        volume (dyadicCubeSet Q) := by
      change ENNReal.ofReal (4 * Real.sqrt 3 * s) ^ 3 *
          ENNReal.ofReal (Real.pi * 4 / 3) =
        ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          volume (dyadicCube Q.scale Q.corner)
      rw [volume_dyadicCube]
      rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 4 * Real.sqrt 3 * s) 3,
        ← ENNReal.ofReal_pow (dyadicScale_pos Q.scale).le 3,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.sqrt 3 * s) ^ 3),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 32 * Real.pi * Real.sqrt 3)]
      congr 1
      dsimp [s]
      ring_nf
      have hsqrt : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
        calc
          (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
          _ = 3 * Real.sqrt 3 := by
            rw [show (Real.sqrt 3) ^ 2 = 3 by norm_num]
      rw [hsqrt]
      ring
theorem rieszSecondCubeStar_volume_sum {F : Vec3 → ℝ} {height : ℝ}
    (D : CZDecomposition F height) :
    (∑' Q : {Q // Q ∈ D.cubes},
      volume (rieszSecondCubeStar Q.1)) ≤
      ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
        (dyadicL1Norm F / ENNReal.ofReal height) := by
  calc
    (∑' Q : {Q // Q ∈ D.cubes}, volume (rieszSecondCubeStar Q.1)) ≤
        ∑' Q : {Q // Q ∈ D.cubes},
          ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
            volume (dyadicCubeSet Q.1) := by
      apply ENNReal.tsum_le_tsum
      intro Q
      exact rieszSecondCubeStar_volume Q.1
    _ = ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
        (∑' Q : {Q // Q ∈ D.cubes}, volume (dyadicCubeSet Q.1)) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
        (dyadicL1Norm F / ENNReal.ofReal height) := by
      gcongr
      exact D.cube_volume_sum_le
/- The enlarged cubes and the exterior `L¹` estimate combine before any
   pointwise representation of the bad output is chosen. -/
theorem rieszSecond_bad_output_measure {F : Vec3 → ℝ} {height level : ℝ}
    (D : CZDecomposition F height) (hlevel : 0 < level)
    {B : Vec3 → ℝ} (hB : Integrable B)
    {C_H : ℝ≥0∞}
    (hBoutside :
      (∫⁻ x in (⋃ Q : {Q // Q ∈ D.cubes},
          rieszSecondCubeStar Q.1)ᶜ, ENNReal.ofReal |B x|) ≤
        C_H * (2 * dyadicL1Norm F)) :
    volume {x | level < |B x|} ≤
      ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (dyadicL1Norm F / ENNReal.ofReal height) +
        (C_H * (2 * dyadicL1Norm F)) / ENNReal.ofReal level := by
  let U : Set Vec3 := ⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1
  have hU : MeasurableSet U := by
    dsimp [U]
    apply MeasurableSet.iUnion
    intro Q
    exact measurableSet_rieszSecondCubeStar Q.1
  have hUvol : volume U ≤
      ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
        (dyadicL1Norm F / ENNReal.ofReal height) := by
    calc
      volume U ≤ ∑' Q : {Q // Q ∈ D.cubes},
          volume (rieszSecondCubeStar Q.1) := by
        dsimp [U]
        exact measure_iUnion_le
          (s := fun Q : {Q // Q ∈ D.cubes} => rieszSecondCubeStar Q.1)
      _ ≤ ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (dyadicL1Norm F / ENNReal.ofReal height) :=
        rieszSecondCubeStar_volume_sum D
  have hmark_meas : AEMeasurable
      (fun x => ENNReal.ofReal |B x|) (volume.restrict Uᶜ) := by
    exact (AEMeasurable.ennreal_ofReal
      hB.norm.aestronglyMeasurable.aemeasurable).mono_measure
      Measure.restrict_le_self
  have hε : ENNReal.ofReal level ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos).2 hlevel)
  have hεtop : ENNReal.ofReal level ≠ ∞ := ENNReal.ofReal_ne_top
  have hmark := meas_ge_le_lintegral_div hmark_meas hε hεtop
  have houtside : volume ({x | level < |B x|} ∩ Uᶜ) ≤
      (C_H * (2 * dyadicL1Norm F)) / ENNReal.ofReal level := by
    have hsub : {x | level < |B x|} ∩ Uᶜ ⊆
        {x | ENNReal.ofReal level ≤ ENNReal.ofReal |B x|} ∩ Uᶜ := by
      intro x hx
      exact ⟨ENNReal.ofReal_le_ofReal hx.1.le, hx.2⟩
    have hmeas := measure_mono (μ := (volume : Measure Vec3)) hsub
    calc
      volume ({x | level < |B x|} ∩ Uᶜ) ≤
          volume ({x | ENNReal.ofReal level ≤ ENNReal.ofReal |B x|} ∩ Uᶜ) := hmeas
      _ = (volume.restrict Uᶜ)
          {x | ENNReal.ofReal level ≤ ENNReal.ofReal |B x|} := by
        rw [Measure.restrict_apply' hU.compl]
      _ ≤ (∫⁻ x in Uᶜ, ENNReal.ofReal |B x|) /
          ENNReal.ofReal level := by
        simpa using hmark
      _ ≤ (C_H * (2 * dyadicL1Norm F)) / ENNReal.ofReal level := by
        gcongr
  have hsubset : {x | level < |B x|} ⊆
      U ∪ ({x | level < |B x|} ∩ Uᶜ) := by
    intro x hx
    by_cases hxu : x ∈ U
    · exact Or.inl hxu
    · exact Or.inr ⟨hx, hxu⟩
  calc
    volume {x | level < |B x|} ≤
        volume U + volume ({x | level < |B x|} ∩ Uᶜ) := by
      exact (measure_mono hsubset).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (dyadicL1Norm F / ENNReal.ofReal height) +
        (C_H * (2 * dyadicL1Norm F)) / ENNReal.ofReal level :=
      add_le_add hUvol houtside
private lemma rieszSecond_hormander_exterior
    {K : Vec3 → ℝ} {C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hKmeas : Measurable K)
    (hdiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ K x)
    (hgrad : ∀ x, x ≠ 0 →
      ‖fderiv ℝ K x‖ ≤ C₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)))
    {Q : DyadicIndex} {y : Vec3} (hy : y ∈ dyadicCubeSet Q) :
    ∫⁻ x in (rieszSecondCubeStar Q)ᶜ,
        ENNReal.ofReal |K (x - y) -
          K (x - dyadicCubeCenter Q.scale Q.corner)| ≤
      ENNReal.ofReal (64 * Real.pi * C₂) := by
  let c : Vec3 := dyadicCubeCenter Q.scale Q.corner
  let s : ℝ := dyadicScale Q.scale / 2
  let r : ℝ := 2 * Real.sqrt 3 * s
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (dyadicScale_pos Q.scale) (by norm_num)
  have hyc : vec3EuclideanNorm (y - c) ≤ Real.sqrt 3 * s := by
    dsimp [c, s]
    have hsup : ‖y - dyadicCubeCenter Q.scale Q.corner‖ ≤ dyadicScale Q.scale / 2 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      have hy' := (mem_dyadicCube.mp hy) i
      change |y i - dyadicCubeCenter Q.scale Q.corner i| ≤ dyadicScale Q.scale / 2
      dsimp [dyadicCubeCenter]
      rw [abs_le]
      constructor <;> nlinarith only [hy'.1, hy'.2, dyadicScale_pos Q.scale]
    exact (vec3EuclideanNorm_le_sqrt_three_mul_norm _).trans
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 3))
  have h2hy : 2 * vec3EuclideanNorm (y - c) ≤ r := by
    dsimp [r]
    nlinarith only [hyc, Real.sqrt_nonneg 3, hs]
  have hE : MeasurableSet (rieszSecondCubeStar Q)ᶜ :=
    (measurableSet_rieszSecondCubeStar Q).compl
  have hf : Measurable (fun z : Vec3 =>
      ENNReal.ofReal |K (z - (y - c)) - K z|) := by
    apply Measurable.ennreal_ofReal
    exact (hKmeas.comp (measurable_id.sub measurable_const)).sub hKmeas |>.norm
  have hshift := translate_setLIntegral hE hf c
      (f := fun z : Vec3 => ENNReal.ofReal |K (z - (y - c)) - K z|)
  have hset : {z : Vec3 | z + c ∈ (rieszSecondCubeStar Q)ᶜ} =
      {z : Vec3 | r < vec3EuclideanNorm z} := by
    ext z
    simp [rieszSecondCubeStar, r, s, c, add_sub_cancel_right]
  have hfun : (fun x : Vec3 =>
      ENNReal.ofReal |K ((x - c) - (y - c)) - K (x - c)|) =
      (fun x : Vec3 => ENNReal.ofReal |K (x - y) - K (x - c)|) := by
    funext x
    congr 3
    abel_nf
  have hleft : (∫⁻ x in (rieszSecondCubeStar Q)ᶜ,
      ENNReal.ofReal |K (x - y) - K (x - c)|) =
      ∫⁻ x in (rieszSecondCubeStar Q)ᶜ,
        ENNReal.ofReal |K ((x - c) - (y - c)) - K (x - c)| := by
    apply lintegral_congr
    intro x
    exact (congrFun hfun x).symm
  rw [hleft, hshift, hset]
  have hsub : {z : Vec3 | r < vec3EuclideanNorm z} ⊆
      {z : Vec3 | 2 * vec3EuclideanNorm (y - c) < vec3EuclideanNorm z} := by
    intro z hz
    dsimp [r] at hz
    exact lt_of_le_of_lt h2hy hz
  calc
    ∫⁻ z in {z : Vec3 | r < vec3EuclideanNorm z},
        ENNReal.ofReal |K (z - (y - c)) - K z| ≤
        ∫⁻ z in {z : Vec3 |
          2 * vec3EuclideanNorm (y - c) < vec3EuclideanNorm z},
          ENNReal.ofReal |K (z - (y - c)) - K z| := lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal (64 * Real.pi * C₂) := by
      by_cases hzero : y - c = 0
      · simp [hzero]
      · exact hormander_integral_bound hC₂ hdiff hgrad hzero
theorem rieszSecond_bad_cube_bridge
    {K b : Vec3 → ℝ} {Q : DyadicIndex} {C_H : ℝ≥0∞}
    (hC_H : C_H ≠ ∞)
    (hmean : ∫ y in dyadicCubeSet Q, b y = 0)
    (hb : IntegrableOn b (dyadicCubeSet Q) volume)
    (hterm : ∀ x ∈ (rieszSecondCubeStar Q)ᶜ,
      IntegrableOn (fun y => K (x - y) * b y) (dyadicCubeSet Q) volume)
    (hjoint : AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(K (z.1 - z.2) -
          K (z.1 - dyadicCubeCenter Q.scale Q.corner)) * b z.2|
        ) ((volume.restrict (rieszSecondCubeStar Q)ᶜ).prod
          (volume.restrict (dyadicCubeSet Q))))
    (hjointSwap : AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(K (z.2 - z.1) -
          K (z.2 - dyadicCubeCenter Q.scale Q.corner)) * b z.1|
        ) ((volume.restrict (dyadicCubeSet Q)).prod
          (volume.restrict (rieszSecondCubeStar Q)ᶜ)))
    (hExt : ∀ y ∈ dyadicCubeSet Q,
      ∫⁻ x in (rieszSecondCubeStar Q)ᶜ,
        ENNReal.ofReal |K (x - y) -
          K (x - dyadicCubeCenter Q.scale Q.corner)| ≤ C_H) :
    ∫⁻ x in (rieszSecondCubeStar Q)ᶜ,
        ENNReal.ofReal |∫ y in dyadicCubeSet Q, K (x - y) * b y| ≤
      C_H * ∫⁻ y in dyadicCubeSet Q, ENNReal.ofReal |b y| := by
  let c : Vec3 := dyadicCubeCenter Q.scale Q.corner
  let E : Set Vec3 := (rieszSecondCubeStar Q)ᶜ
  let S : Set Vec3 := dyadicCubeSet Q
  let f : Vec3 × Vec3 → ℝ≥0∞ := fun z =>
    ENNReal.ofReal |(K (z.1 - z.2) - K (z.1 - c)) * b z.2|
  let fs : Vec3 × Vec3 → ℝ≥0∞ := fun z =>
    ENNReal.ofReal |(K (z.2 - z.1) - K (z.2 - c)) * b z.1|
  have hEmeas : MeasurableSet E :=
    (measurableSet_rieszSecondCubeStar Q).compl
  have hfinner : AEMeasurable (fun x => ∫⁻ y, f (x, y)
      ∂(volume.restrict S)) (volume.restrict E) := by
    exact hjoint.lintegral_prod_right (ν := volume.restrict S)
  have hfswap : AEMeasurable fs
      ((volume.restrict S).prod (volume.restrict E)) := by
    simpa [fs, c, E, S] using hjointSwap
  have hprod := lintegral_prod f hjoint
  have hprods := lintegral_prod fs hfswap
  have hswap := (Measure.measurePreserving_swap
      (μ := volume.restrict E) (ν := volume.restrict S)).lintegral_comp_emb
        MeasurableEquiv.prodComm.measurableEmbedding fs
  have htonelli :
      (∫⁻ x in E, ∫⁻ y in S, f (x, y)) =
        ∫⁻ y in S, ∫⁻ x in E, f (x, y) := by
    calc
      (∫⁻ x in E, ∫⁻ y in S, f (x, y)) =
          ∫⁻ z, f z ∂((volume.restrict E).prod (volume.restrict S)) :=
        hprod.symm
      _ = ∫⁻ z, fs (Prod.swap z) ∂
          ((volume.restrict E).prod (volume.restrict S)) := by
        apply lintegral_congr
        intro z
        simp [f, fs, c]
      _ = ∫⁻ z, fs z ∂((volume.restrict S).prod (volume.restrict E)) := hswap
      _ = (∫⁻ y in S, ∫⁻ x in E, fs (y, x)) := hprods
      _ = ∫⁻ y in S, ∫⁻ x in E, f (x, y) := by
        apply lintegral_congr
        intro y
        apply lintegral_congr
        intro x
        simp [f, fs, c]
  have hpoint : ∀ᵐ x ∂(volume.restrict E),
      ENNReal.ofReal |∫ y in S, K (x - y) * b y| ≤
        ∫⁻ y in S, f (x, y) := by
    filter_upwards [ae_restrict_mem hEmeas] with x hx
    have hterm' : Integrable (fun y => K (x - y) * b y)
        (volume.restrict S) := hterm x hx
    have hb' : Integrable b (volume.restrict S) := hb
    have hconst : Integrable (fun y => K (x - c) * b y)
        (volume.restrict S) := hb'.const_mul (K (x - c))
    have hdiff : Integrable (fun y =>
        (K (x - y) - K (x - c)) * b y) (volume.restrict S) := by
      have hsub := hterm'.sub hconst
      convert hsub using 1
      funext y
      simp only [Pi.sub_apply]
      ring
    have hzero : ∫ y in S, K (x - c) * b y = 0 := by
      rw [integral_const_mul]
      rw [show (∫ y in S, b y) = 0 by simpa [S] using hmean, mul_zero]
    have hidentity : ∫ y in S, K (x - y) * b y =
        ∫ y in S, (K (x - y) - K (x - c)) * b y := by
      calc
        ∫ y in S, K (x - y) * b y =
            ∫ y in S, (K (x - y) * b y - K (x - c) * b y) := by
          rw [integral_sub hterm' hconst, hzero]
          simp
        _ = ∫ y in S, (K (x - y) - K (x - c)) * b y := by
          apply integral_congr_ae
          filter_upwards [] with y
          ring
    rw [hidentity]
    have hnorm := norm_integral_le_integral_norm
      (μ := volume.restrict S)
      (fun y => (K (x - y) - K (x - c)) * b y)
    have hof := ENNReal.ofReal_le_ofReal hnorm
    rw [Real.norm_eq_abs] at hof
    rw [ofReal_integral_eq_lintegral_ofReal hdiff.norm
      (ae_of_all _ (fun y => abs_nonneg _))] at hof
    simpa [f, c, E, S, ENNReal.ofReal_mul (abs_nonneg _)] using hof
  have houter := lintegral_mono_ae hpoint
  calc
    ∫⁻ x in E, ENNReal.ofReal |∫ y in S, K (x - y) * b y| ≤
        ∫⁻ x in E, ∫⁻ y in S, f (x, y) := houter
    _ = ∫⁻ y in S, ∫⁻ x in E, f (x, y) := htonelli
    _ ≤ ∫⁻ y in S, C_H * ENNReal.ofReal |b y| := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (dyadicCube_measurable Q.scale Q.corner)]
        with y hy
      have hxy : ∫⁻ x in E,
          ENNReal.ofReal |K (x - y) - K (x - c)| ≤ C_H := by
        simpa [E, c] using hExt y (by simpa [S] using hy)
      calc
        (∫⁻ x in E, f (x, y)) =
            ENNReal.ofReal |b y| * ∫⁻ x in E,
              ENNReal.ofReal |K (x - y) - K (x - c)| := by
          calc
            ∫⁻ x in E, f (x, y) =
                ∫⁻ x in E, ENNReal.ofReal |b y| *
                  ENNReal.ofReal |K (x - y) - K (x - c)| := by
              apply lintegral_congr
              intro x
              simp [f, c, abs_mul, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
            _ = ENNReal.ofReal |b y| * ∫⁻ x in E,
                  ENNReal.ofReal |K (x - y) - K (x - c)| := by
              rw [lintegral_const_mul']
              exact ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal |b y| * C_H := by
          calc
            ENNReal.ofReal |b y| *
                ∫⁻ x in E, ENNReal.ofReal |K (x - y) - K (x - c)| =
                (∫⁻ x in E, ENNReal.ofReal |K (x - y) - K (x - c)|) *
                  ENNReal.ofReal |b y| := by rw [mul_comm]
            _ ≤ C_H * ENNReal.ofReal |b y| := mul_le_mul_left hxy _
            _ = ENNReal.ofReal |b y| * C_H := by rw [mul_comm]
        _ = C_H * ENNReal.ofReal |b y| := by ac_rfl
    _ = C_H * ∫⁻ y in S, ENNReal.ofReal |b y| := by
      rw [lintegral_const_mul']
      exact hC_H

theorem rieszSecond_bad_cube_bridge_of_kernel
    {K b : Vec3 → ℝ} {Q : DyadicIndex} {C₂ : ℝ}
    (hC₂ : 0 ≤ C₂) (hKmeas : Measurable K)
    (hdiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ K x)
    (hgrad : ∀ x, x ≠ 0 →
      ‖fderiv ℝ K x‖ ≤ C₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)))
    (hmean : ∫ y in dyadicCubeSet Q, b y = 0)
    (hb : IntegrableOn b (dyadicCubeSet Q) volume)
    (hterm : ∀ x ∈ (rieszSecondCubeStar Q)ᶜ,
      IntegrableOn (fun y => K (x - y) * b y) (dyadicCubeSet Q) volume)
    (hjoint : AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(K (z.1 - z.2) -
          K (z.1 - dyadicCubeCenter Q.scale Q.corner)) * b z.2|
        ) ((volume.restrict (rieszSecondCubeStar Q)ᶜ).prod
          (volume.restrict (dyadicCubeSet Q))))
    (hjointSwap : AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(K (z.2 - z.1) -
          K (z.2 - dyadicCubeCenter Q.scale Q.corner)) * b z.1|
        ) ((volume.restrict (dyadicCubeSet Q)).prod
          (volume.restrict (rieszSecondCubeStar Q)ᶜ))) :
    ∫⁻ x in (rieszSecondCubeStar Q)ᶜ,
        ENNReal.ofReal |∫ y in dyadicCubeSet Q, K (x - y) * b y| ≤
      ENNReal.ofReal (64 * Real.pi * C₂) *
        ∫⁻ y in dyadicCubeSet Q, ENNReal.ofReal |b y| := by
  apply rieszSecond_bad_cube_bridge ENNReal.ofReal_ne_top hmean hb hterm
    hjoint hjointSwap
  intro y hy
  exact rieszSecond_hormander_exterior hC₂ hKmeas hdiff hgrad hy

/-- The good part estimate after the (L^2) operator bound and Chebyshev. -/
theorem rieszSecond_good_part_chebyshev {F : Vec3 → ℝ} {height level C A : ℝ}
    (D : CZDecomposition F height) (hheight : 0 < height) (hlevel : 0 < level)
    (hA : 0 ≤ A)
    (henergy : ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤ 8 * height * A)
    {T : Vec3 → ℝ → ℝ}
    (hT : Integrable (fun x => T x (dyadicGoodPart F D.cubes x) ^ (2 : ℕ)) volume)
    (hL2 : ∫ x, T x (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤
      C ^ 2 * ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ)) :
    volume {x | level < |T x (dyadicGoodPart F D.cubes x)|} ≤
      ENNReal.ofReal (8 * C ^ 2 * height / level ^ 2) * ENNReal.ofReal A := by
  have hmark := measure_abs_gt_le_integral_sq hT hlevel
  have hnum : ∫ x, T x (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤
      8 * C ^ 2 * height * A := by
    calc
      ∫ x, T x (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤
          C ^ 2 * ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) := hL2
      _ ≤ C ^ 2 * (8 * height * A) := by
        gcongr
      _ = 8 * C ^ 2 * height * A := by ring
  calc
    volume {x | level < |T x (dyadicGoodPart F D.cubes x)|} ≤
        ENNReal.ofReal (∫ x, T x (dyadicGoodPart F D.cubes x) ^ (2 : ℕ)) /
          ENNReal.ofReal (level ^ (2 : ℕ)) := hmark
    _ ≤ ENNReal.ofReal (8 * C ^ 2 * height * A) /
          ENNReal.ofReal (level ^ (2 : ℕ)) := by
      gcongr
    _ = ENNReal.ofReal (8 * C ^ 2 * height / level ^ 2) *
          ENNReal.ofReal A := by
      rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (sq_pos_of_pos hlevel)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [show (8 * C ^ 2 * height * A) * (level ^ 2)⁻¹ =
          (8 * C ^ 2 * height / level ^ 2) * A by
            field_simp]

/-- The summed bad-part estimate supplied by the Hörmander integral bound. -/
theorem rieszSecond_hormander_kernel_condition {K : Vec3 → ℝ} {C₂ : ℝ}
    (hC₂ : 0 ≤ C₂)
    (hdiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ K x)
    (hgrad : ∀ x, x ≠ 0 →
      ‖fderiv ℝ K x‖ ≤ C₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)))
    {y : Vec3} (hy : y ≠ 0) :
    ∫⁻ x in {x | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x},
        ENNReal.ofReal |K (x - y) - K x| ≤
      ENNReal.ofReal (64 * Real.pi * C₂) := by
  exact hormander_integral_bound hC₂ hdiff hgrad hy

theorem rieszSecond_hormander_sum_bound {F : Vec3 → ℝ} {height : ℝ}
    (D : CZDecomposition F height) {T : (Vec3 → ℝ) → Vec3 → ℝ}
    {C_H : ℝ≥0∞}
    (hH : ∀ Q : {Q // Q ∈ D.cubes},
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |T (dyadicBadPart F Q.1) x|) ≤
        C_H * ∫⁻ x in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 x|) :
    (∑' Q : {Q // Q ∈ D.cubes},
      ∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |T (dyadicBadPart F Q.1) x|) ≤
      C_H * (2 * dyadicL1Norm F) := by
  calc
    (∑' Q : {Q // Q ∈ D.cubes},
      ∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |T (dyadicBadPart F Q.1) x|) ≤
        ∑' Q : {Q // Q ∈ D.cubes},
          C_H * ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 x| := by
      apply ENNReal.tsum_le_tsum
      intro Q
      exact hH Q
    _ = C_H * (∑' Q : {Q // Q ∈ D.cubes},
          ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 x|) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ C_H * (2 * dyadicL1Norm F) := by
      gcongr
      exact D.bad_part_l1_sum_le

/- The geometric/Fubini part of the bad estimate is supplied by the caller;
   this wrapper supplies the quantitative kernel input uniformly to every
   cube. -/
theorem rieszSecond_hormander_sum_bound_of_kernel
    {F : Vec3 → ℝ} {height : ℝ} (D : CZDecomposition F height)
    {T : (Vec3 → ℝ) → Vec3 → ℝ} {K : Vec3 → ℝ} {C₂ : ℝ}
    (hC₂ : 0 ≤ C₂)
    (hdiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ K x)
    (hgrad : ∀ x, x ≠ 0 →
      ‖fderiv ℝ K x‖ ≤ C₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)))
    (hH : ∀ Q : {Q // Q ∈ D.cubes},
      (∀ y, y ≠ 0 →
        ∫⁻ x in {x | 2 * vec3EuclideanNorm y < vec3EuclideanNorm x},
          ENNReal.ofReal |K (x-y) - K x| ≤
            ENNReal.ofReal (64 * Real.pi * C₂)) →
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |T (dyadicBadPart F Q.1) x|) ≤
        ENNReal.ofReal (64 * Real.pi * C₂) *
          ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 x|) :
    (∑' Q : {Q // Q ∈ D.cubes},
      ∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |T (dyadicBadPart F Q.1) x|) ≤
      ENNReal.ofReal (64 * Real.pi * C₂) * (2 * dyadicL1Norm F) := by
  apply rieszSecond_hormander_sum_bound D
  intro Q
  exact hH Q (fun y hy =>
    rieszSecond_hormander_kernel_condition hC₂ hdiff hgrad hy)

/- The certificate-level assembly of the bad output.  The pointwise `tsum`
   hypothesis is the sole linearity/interchange interface for a concrete
   convolution operator; each summand is discharged by the per-cube bridge
   above, and the certificate supplies the final `L¹` sum. -/
theorem rieszSecond_bad_part_exterior_bound
    {F : Vec3 → ℝ} {height : ℝ} (D : CZDecomposition F height)
    {B : Vec3 → ℝ} {Tbad : {Q // Q ∈ D.cubes} → Vec3 → ℝ}
    {C_H : ℝ≥0∞}
    (hpoint : ∀ᵐ x ∂(volume.restrict
        (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
      ENNReal.ofReal |B x| ≤
        ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x|)
    (hmeas : ∀ Q : {Q // Q ∈ D.cubes},
      AEMeasurable (fun x => ENNReal.ofReal |Tbad Q x|)
        (volume.restrict
          (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ))
    (hbridge : ∀ Q : {Q // Q ∈ D.cubes},
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |Tbad Q x|) ≤
        C_H * ∫⁻ x in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 x|) :
    (∫⁻ x in (⋃ Q : {Q // Q ∈ D.cubes},
        rieszSecondCubeStar Q.1)ᶜ, ENNReal.ofReal |B x|) ≤
      C_H * (2 * dyadicL1Norm F) := by
  let U : Set Vec3 := ⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1
  have hU : MeasurableSet U := by
    dsimp [U]
    apply MeasurableSet.iUnion
    intro Q
    exact measurableSet_rieszSecondCubeStar Q.1
  have hsum : (∑' Q : {Q // Q ∈ D.cubes},
      ∫⁻ x in Uᶜ, ENNReal.ofReal |Tbad Q x|) ≤
      C_H * (2 * dyadicL1Norm F) := by
    calc
      (∑' Q : {Q // Q ∈ D.cubes},
          ∫⁻ x in Uᶜ, ENNReal.ofReal |Tbad Q x|) ≤
          ∑' Q : {Q // Q ∈ D.cubes},
            ∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
              ENNReal.ofReal |Tbad Q x| := by
        apply ENNReal.tsum_le_tsum
        intro Q
        have hsub : Uᶜ ⊆ (rieszSecondCubeStar Q.1)ᶜ := by
          intro x hx hxQ
          exact hx (mem_iUnion.2 ⟨Q, hxQ⟩)
        exact lintegral_mono_set hsub
      _ ≤ ∑' Q : {Q // Q ∈ D.cubes}, C_H *
          ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 x| := by
        apply ENNReal.tsum_le_tsum
        intro Q
        exact hbridge Q
      _ = C_H * (∑' Q : {Q // Q ∈ D.cubes},
          ∫⁻ x in dyadicCubeSet Q.1,
            ENNReal.ofReal |dyadicBadPart F Q.1 x|) := by
        rw [ENNReal.tsum_mul_left]
      _ ≤ C_H * (2 * dyadicL1Norm F) := by
        gcongr
        exact D.bad_part_l1_sum_le
  calc
    (∫⁻ x in Uᶜ, ENNReal.ofReal |B x|) ≤
        ∫⁻ x in Uᶜ,
          ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x| :=
      lintegral_mono_ae hpoint
    _ = ∑' Q : {Q // Q ∈ D.cubes},
        ∫⁻ x in Uᶜ, ENNReal.ofReal |Tbad Q x| := by
      rw [lintegral_tsum hmeas]
    _ ≤ C_H * (2 * dyadicL1Norm F) := hsum

/- The complete weak-type assembly.  The decomposition itself is obtained
   internally from the established existence theorem.  `hL2` is deliberately an
   explicit interface: it is the global operator estimate supplied by the
   separate cutoff-limit argument. -/
theorem rieszSecond_weak_type_unconditional
    {F : Vec3 → ℝ} {level C₂ A : ℝ} {C_H : ℝ≥0∞}
    (hF : Integrable F) (hlevel : 0 < level)
    (hA : 0 ≤ A) (hAeq : dyadicL1Norm F = ENNReal.ofReal A)
    {T : Vec3 → ℝ} {G B : CZDecomposition F level → Vec3 → ℝ}
    (hdecomp : ∀ D : CZDecomposition F level, ∀ x,
      T x = G D x + B D x)
    (henergy : ∀ D : CZDecomposition F level,
      ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤ 8 * level * A)
    (hL2 : ∀ D : CZDecomposition F level,
      Integrable (fun x => G D x ^ (2 : ℕ)) volume ∧
      (∫ x, G D x ^ (2 : ℕ)) ≤ C₂ ^ 2 *
        ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ))
    (hbad : ∀ D : CZDecomposition F level,
      ∃ Tbad : {Q // Q ∈ D.cubes} → Vec3 → ℝ,
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
            C_H * ∫⁻ x in dyadicCubeSet Q.1,
              ENNReal.ofReal |dyadicBadPart F Q.1 x|)) :
    volume {x | level < |T x|} ≤
      ENNReal.ofReal (8 * C₂ ^ 2 * level / (level / 2) ^ 2) *
          ENNReal.ofReal A +
        ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (ENNReal.ofReal A / ENNReal.ofReal level) +
        (C_H * (2 * ENNReal.ofReal A)) / ENNReal.ofReal (level / 2) := by
  obtain ⟨D, _⟩ := exists_calderonZygmund_decomposition hF hlevel
  obtain ⟨hGint, hG_L2⟩ := hL2 D
  have hgood := rieszSecond_good_part_chebyshev D hlevel
    (by positivity : 0 < level / 2) hA (henergy D)
    (T := fun x _ => G D x)
    (by simpa only [Function.comp_apply] using hGint)
    (by simpa only [Function.comp_apply] using hG_L2)
  obtain ⟨Tbad, hBint, hpoint, hmeas, hbridge⟩ := hbad D
  have hBoutside := rieszSecond_bad_part_exterior_bound D hpoint hmeas hbridge
  have hbad' := rieszSecond_bad_output_measure D
    (by positivity : 0 < level / 2) hBint hBoutside
  have hbad'' : volume {x | level / 2 < |B D x|} ≤
      ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (ENNReal.ofReal A / ENNReal.ofReal level) +
        (C_H * (2 * ENNReal.ofReal A)) / ENNReal.ofReal (level / 2) := by
    simpa [hAeq] using hbad'
  have hsub : {x | level < |T x|} ⊆
      {x | level / 2 < |G D x|} ∪ {x | level / 2 < |B D x|} := by
    intro x hx
    by_contra hnot
    have hG : |G D x| ≤ level / 2 := le_of_not_gt (by
      intro hG'
      exact hnot (Or.inl hG'))
    have hB : |B D x| ≤ level / 2 := le_of_not_gt (by
      intro hB'
      exact hnot (Or.inr hB'))
    have htri : |G D x + B D x| ≤ |G D x| + |B D x| :=
      abs_add_le _ _
    change level < |T x| at hx
    rw [hdecomp D x] at hx
    linarith only [hx, htri, hG, hB, hlevel]
  calc
    volume {x | level < |T x|} ≤
        volume ({x | level / 2 < |G D x|} ∪
          {x | level / 2 < |B D x|}) := measure_mono hsub
    _ ≤ volume {x | level / 2 < |G D x|} +
        volume {x | level / 2 < |B D x|} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (8 * C₂ ^ 2 * level / (level / 2) ^ 2) *
          ENNReal.ofReal A +
        (ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (ENNReal.ofReal A / ENNReal.ofReal level) +
          (C_H * (2 * ENNReal.ofReal A)) / ENNReal.ofReal (level / 2)) :=
      add_le_add hgood hbad''
    _ = ENNReal.ofReal (8 * C₂ ^ 2 * level / (level / 2) ^ 2) *
          ENNReal.ofReal A +
        ENNReal.ofReal (32 * Real.pi * Real.sqrt 3) *
          (ENNReal.ofReal A / ENNReal.ofReal level) +
        (C_H * (2 * ENNReal.ofReal A)) / ENNReal.ofReal (level / 2) := by
      ac_rfl

end CKN.Foundation.Euclidean
