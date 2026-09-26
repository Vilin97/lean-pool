/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientProduct
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyData
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.HolderTripleProducts

/-!
# Pressure Gradient Source Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-- The product-rule source obtained after inserting a spatial cutoff into the
quadratic tensor.  The field `dη j` is the j-th spatial derivative of the
cutoff; its analytic derivative estimate is passed at the use site. -/
@[expose]
def pressureDivergenceCutoffSource
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (f : Vec3 → Vec3) : Vec3 → Vec3 :=
  fun x i => ∑ j, (η x * Du x i j * u x j + dη j x * u x i * u x j) - η x * f x i

private theorem eLpNorm_three_half_to_six_fifths
    {μ : Measure Vec3} {f : Vec3 → ℝ} (hf : AEStronglyMeasurable f μ)
    (_ : μ Set.univ < ⊤) :
    eLpNorm f (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ *
        μ Set.univ ^ (1 / (6 / 5 : ℝ) - 1 / (3 / 2 : ℝ)) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (f := f) (p := ENNReal.ofReal (6 / 5 : ℝ))
    (q := ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num) hf
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using h

private theorem eLpNorm_force_q_to_six_fifths
    {μ : Measure Vec3} {f : Vec3 → ℝ} {q : ℝ}
    (hf : AEStronglyMeasurable f μ) (hq : 5 / 2 < q) :
    eLpNorm f (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm f (ENNReal.ofReal q) μ *
        μ Set.univ ^ (5 / 6 - 1 / q) := by
  have hqpos : 0 < q := by linarith only [hq]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (f := f) (p := ENNReal.ofReal (6 / 5 : ℝ))
    (q := ENNReal.ofReal q) (by
      exact ENNReal.ofReal_le_ofReal (by linarith only [hq] : (6 / 5 : ℝ) ≤ q)) hf
  rw [ENNReal.toReal_ofReal hqpos.le] at h
  convert h using 1
  · norm_num

private theorem eLpNorm_abs_eq
    {μ : Measure Vec3} {f : Vec3 → ℝ} (hf : AEStronglyMeasurable f μ)
    {p : ℝ≥0∞} :
    eLpNorm (fun x => |f x|) p μ = eLpNorm f p μ := by
  exact eLpNorm_congr_norm_ae (hf.norm) hf (Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_abs])

private theorem vec3_norm_le_sum_abs (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i, |v i| := by
  rw [vec3EuclideanNorm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) ≤
      (|v 0| + (|v 1| + |v 2|)) ^ 2
    nlinarith only [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]

private theorem space_norm_le_vec3_euclidean (v : Vec3) :
    ‖v‖ ≤ vec3EuclideanNorm v := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i : Fin 3 => ‖v i‖₊) ≤
      ⟨vec3EuclideanNorm v, vec3EuclideanNorm_nonneg v⟩ := by
    apply Finset.sup_le
    intro i hi
    change |v i| ≤ vec3EuclideanNorm v
    unfold vec3EuclideanNorm
    exact Real.abs_le_sqrt (Finset.single_le_sum
      (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
  exact_mod_cast hnn

/-! A cutoff does not change the product exponents.  The two cutoff bounds
are kept as separate parameters so that the spatial derivative contribution
can be instantiated with `C₁₀ / ρ`. -/

theorem pressure_divergence_cutoff_source_slice_component_le
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {f : Vec3 → Vec3}
    {i : Fin 3} {q Cη Cdη : ℝ} {KU KD KF : ℝ≥0∞}
    (hq : 5 / 2 < q) (hμ : (volume.restrict B) Set.univ < ⊤)
    (hCη : 0 ≤ Cη) (hCdη : 0 ≤ Cdη)
    (hη : AEStronglyMeasurable η (volume.restrict B))
    (hηbound : ∀ᵐ x ∂(volume.restrict B), |η x| ≤ Cη)
    (hdη : ∀ j : Fin 3,
      AEStronglyMeasurable (dη j) (volume.restrict B))
    (hdηbound : ∀ j : Fin 3,
      ∀ᵐ x ∂(volume.restrict B), |dη j x| ≤ Cdη)
    (hU : ∀ j : Fin 3,
      eLpNorm (fun x => u x j) (ENNReal.ofReal (3 : ℝ))
        (volume.restrict B) ≤ KU)
    (hD : ∀ j : Fin 3,
      eLpNorm (fun x => Du x i j) (ENNReal.ofReal (2 : ℝ))
        (volume.restrict B) ≤ KD)
    (hF : eLpNorm (fun x => f x i) (ENNReal.ofReal q)
      (volume.restrict B) ≤ KF)
    (hUmeas : ∀ j : Fin 3,
      AEStronglyMeasurable (fun x => u x j) (volume.restrict B))
    (hDmeas : ∀ j : Fin 3,
      AEStronglyMeasurable (fun x => Du x i j) (volume.restrict B))
    (hFmeas : AEStronglyMeasurable (fun x => f x i)
      (volume.restrict B)) :
    eLpNorm (fun x => pressureDivergenceCutoffSource η dη u Du f x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
      3 * (ENNReal.ofReal Cη * KD * KU +
        ENNReal.ofReal Cdη *
          (KU * KU * (volume.restrict B) Set.univ ^ (1 / 6 : ℝ))) +
        ENNReal.ofReal Cη *
          (KF * (volume.restrict B) Set.univ ^ (5 / 6 - 1 / q)) := by
  let μ := volume.restrict B
  let HA : ℝ≥0∞ := ENNReal.ofReal Cη * KD * KU
  let HB : ℝ≥0∞ := ENNReal.ofReal Cdη *
    (KU * KU * μ Set.univ ^ (1 / 6 : ℝ))
  let HC : ℝ≥0∞ := ENNReal.ofReal Cη *
    (KF * μ Set.univ ^ (5 / 6 - 1 / q))
  have hprod (j : Fin 3) :
      eLpNorm (fun x => Du x i j * u x j)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ KD * KU := by
    exact (CKN.Foundation.Measure.eLpNorm_mul_le_two_three (μ := μ) (hDmeas j) (hUmeas j)).trans
      (mul_le_mul (hD j) (hU j) (by positivity) (by positivity))
  have hA (j : Fin 3) :
      eLpNorm (fun x => η x * Du x i j * u x j)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ HA := by
    have h := CKN.Foundation.Measure.eLpNorm_mul_le_ofReal_mul (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ)) hη
      ((hDmeas j).mul (hUmeas j)) hCη hηbound
    have h' := h.trans (mul_le_mul_of_nonneg_left (hprod j) (by positivity))
    simpa [HA, mul_assoc, mul_comm, mul_left_comm] using h'
  have huu32 (j : Fin 3) :
      eLpNorm (fun x => u x i * u x j)
        (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ KU * KU := by
    exact (CKN.Foundation.Measure.eLpNorm_mul_le_three_three (μ := μ) (hUmeas i) (hUmeas j)).trans
      (mul_le_mul (hU i) (hU j) (by positivity) (by positivity))
  have huu (j : Fin 3) :
      eLpNorm (fun x => u x i * u x j)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
        KU * KU * μ Set.univ ^ (1 / 6 : ℝ) := by
    have h := eLpNorm_three_half_to_six_fifths
      (μ := μ) (hUmeas i |>.mul (hUmeas j)) hμ
    have h' := h.trans (mul_le_mul_of_nonneg_right (huu32 j) (by positivity))
    convert h' using 1
    · norm_num
  have hB (j : Fin 3) :
      eLpNorm (fun x => dη j x * u x i * u x j)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ HB := by
    have h := CKN.Foundation.Measure.eLpNorm_mul_le_ofReal_mul (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (hdη j)
      ((hUmeas i).mul (hUmeas j)) hCdη (hdηbound j)
    have h' := h.trans (mul_le_mul_of_nonneg_left (huu j) (by positivity))
    simpa [HB, mul_assoc, mul_comm, mul_left_comm] using h'
  have hforce :
      eLpNorm (fun x => f x i) (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
        KF * μ Set.univ ^ (5 / 6 - 1 / q) := by
    exact eLpNorm_force_q_to_six_fifths hFmeas hq |>.trans
      (mul_le_mul_of_nonneg_right hF (by positivity))
  have hC : eLpNorm (fun x => η x * f x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ HC := by
    have h := CKN.Foundation.Measure.eLpNorm_mul_le_ofReal_mul (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ)) hη hFmeas hCη hηbound
    have h' := h.trans (mul_le_mul_of_nonneg_left hforce (by positivity))
    simpa [HC, mul_assoc, mul_comm, mul_left_comm] using h'
  let T : Fin 3 → Vec3 → ℝ := fun j x =>
    η x * Du x i j * u x j + dη j x * u x i * u x j
  have hTmeas : ∀ j : Fin 3, AEStronglyMeasurable (T j) μ := by
    intro j
    change AEStronglyMeasurable (fun x =>
      η x * Du x i j * u x j + dη j x * u x i * u x j)
      (volume.restrict B)
    have h0 :=
      (hη.mul ((hDmeas j).mul (hUmeas j))).add
        ((hdη j).mul ((hUmeas i).mul (hUmeas j)))
    have heq : η * ((fun x => Du x i j) * (fun x => u x j)) +
        (dη j) * ((fun x => u x i) * (fun x => u x j)) =
        (fun x => η x * Du x i j * u x j + dη j x * u x i * u x j) := by
      funext x
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    rw [heq] at h0
    exact h0
  have hT : ∀ j : Fin 3,
      eLpNorm (T j) (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ HA + HB := by
    intro j
    have h := eLpNorm_add_le (μ := μ) (p := ENNReal.ofReal (6 / 5 : ℝ))
      (f := fun x => η x * Du x i j * u x j)
      (g := fun x => dη j x * u x i * u x j) (by norm_num)
    have h' := h.trans (add_le_add (hA j) (hB j))
    change eLpNorm (fun x =>
      η x * Du x i j * u x j + dη j x * u x i * u x j)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ HA + HB
    have heq : (fun x => η x * Du x i j * u x j) +
        (fun x => dη j x * u x i * u x j) = (fun x =>
          η x * Du x i j * u x j + dη j x * u x i * u x j) := by
      funext x
      rfl
    rw [heq] at h'
    exact h'
  have hsum0 := eLpNorm_add_le (μ := μ)
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (f := T 0)
    (g := fun x => T 1 x + T 2 x) (by norm_num)
  have hsum1 := eLpNorm_add_le (μ := μ)
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (f := T 1) (g := T 2) (by norm_num)
  have hsum : eLpNorm (fun x => ∑ j, T j x)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ 3 * (HA + HB) := by
    have h1 := hsum1.trans (add_le_add (hT 1) (hT 2))
    have h0 := hsum0.trans (add_le_add (hT 0) h1)
    have heq : (fun x => ∑ j, T j x) =
        (fun x => T 0 x + (T 1 x + T 2 x)) := by
      funext x
      simp [Fin.sum_univ_succ]
    rw [heq]
    convert h0 using 1
    · ring
  have hsource := eLpNorm_sub_le (μ := μ)
    (f := fun x => ∑ j, T j x) (g := fun x => η x * f x i)
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (by norm_num)
  have hbound := hsource.trans (add_le_add hsum hC)
  change eLpNorm ((fun x => ∑ j, T j x) -
      (fun x => η x * f x i)) (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ _
  simpa only [HA, HB, HC, μ] using hbound

theorem pressure_divergence_cutoff_source_slice_le
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {f : Vec3 → Vec3}
    {q Cη Cdη : ℝ} {KU KD KF : ℝ≥0∞}
    (hq : 5 / 2 < q) (hμ : (volume.restrict B) Set.univ < ⊤)
    (hCη : 0 ≤ Cη) (hCdη : 0 ≤ Cdη)
    (hη : AEStronglyMeasurable η (volume.restrict B))
    (hηbound : ∀ᵐ x ∂(volume.restrict B), |η x| ≤ Cη)
    (hdη : ∀ j : Fin 3,
      AEStronglyMeasurable (dη j) (volume.restrict B))
    (hdηbound : ∀ j : Fin 3,
      ∀ᵐ x ∂(volume.restrict B), |dη j x| ≤ Cdη)
    (hU : ∀ j : Fin 3,
      eLpNorm (fun x => u x j) (ENNReal.ofReal (3 : ℝ))
        (volume.restrict B) ≤ KU)
    (hD : ∀ i j : Fin 3,
      eLpNorm (fun x => Du x i j) (ENNReal.ofReal (2 : ℝ))
        (volume.restrict B) ≤ KD)
    (hF : ∀ i : Fin 3,
      eLpNorm (fun x => f x i) (ENNReal.ofReal q)
        (volume.restrict B) ≤ KF)
    (hUmeas : ∀ j : Fin 3,
      AEStronglyMeasurable (fun x => u x j) (volume.restrict B))
    (hDmeas : ∀ i j : Fin 3,
      AEStronglyMeasurable (fun x => Du x i j) (volume.restrict B))
    (hFmeas : ∀ i : Fin 3,
      AEStronglyMeasurable (fun x => f x i) (volume.restrict B)) :
    eLpNorm (fun x => pressureDivergenceCutoffSource η dη u Du f x)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
      3 * (3 * (ENNReal.ofReal Cη * KD * KU +
        ENNReal.ofReal Cdη *
          (KU * KU * (volume.restrict B) Set.univ ^ (1 / 6 : ℝ))) +
        ENNReal.ofReal Cη *
          (KF * (volume.restrict B) Set.univ ^ (5 / 6 - 1 / q))) := by
  let μ := volume.restrict B
  let M : ℝ≥0∞ := 3 * (ENNReal.ofReal Cη * KD * KU +
    ENNReal.ofReal Cdη *
      (KU * KU * μ Set.univ ^ (1 / 6 : ℝ))) +
    ENNReal.ofReal Cη * (KF * μ Set.univ ^ (5 / 6 - 1 / q))
  have hcomp : ∀ i : Fin 3,
      eLpNorm (fun x => pressureDivergenceCutoffSource η dη u Du f x i)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ M := by
    intro i
    simpa only [M] using pressure_divergence_cutoff_source_slice_component_le
      hq hμ hCη hCdη hη hηbound (hdη) (hdηbound) hU (hD i) (hF i)
        hUmeas (hDmeas i) (hFmeas i)
  have hsourceAEMeas : AEMeasurable
      (fun x => pressureDivergenceCutoffSource η dη u Du f x)
      μ := by
    rw [aemeasurable_pi_iff]
    intro i
    have hsum0 := Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun j _ => ((hη.mul ((hDmeas i j).mul (hUmeas j))).add
        ((hdη j).mul ((hUmeas i).mul (hUmeas j)))).aemeasurable)
    have hsum : AEMeasurable (fun x => ∑ j,
        (η x * Du x i j * u x j + dη j x * u x i * u x j)) μ := by
      have heq0 : (∑ j, (η * ((fun x => Du x i j) * (fun x => u x j)) +
          (dη j) * ((fun x => u x i) * (fun x => u x j)))) =
          (fun x => ∑ j, (η x * Du x i j * u x j +
            dη j x * u x i * u x j)) := by
        funext x
        simp only [Finset.sum_apply, Pi.add_apply, Pi.mul_apply]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq0] at hsum0
      exact hsum0
    have h0 := hsum.sub (hη.aemeasurable.mul (hFmeas i).aemeasurable)
    have heq : ((fun x => ∑ j, (η x * Du x i j * u x j +
        dη j x * u x i * u x j)) - η * (fun x => f x i)) =
        (fun x => pressureDivergenceCutoffSource η dη u Du f x i) := by
      funext x
      simp [pressureDivergenceCutoffSource]
    rw [heq] at h0
    exact h0
  have hsourceMeas := hsourceAEMeas.aestronglyMeasurable
  have hsourceCompMeas : ∀ i : Fin 3,
      AEStronglyMeasurable
        (fun x => pressureDivergenceCutoffSource η dη u Du f x i) μ := by
    intro i
    exact (aemeasurable_pi_iff.mp hsourceAEMeas i).aestronglyMeasurable
  have hmono : eLpNorm (fun x => pressureDivergenceCutoffSource η dη u Du f x)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm (fun x => ∑ i,
        |pressureDivergenceCutoffSource η dη u Du f x i|)
        (ENNReal.ofReal (6 / 5 : ℝ)) μ := by
    let a : Vec3 → ℝ := fun x => ∑ i,
      |pressureDivergenceCutoffSource η dη u Du f x i|
    apply eLpNorm_mono_enorm_ae hsourceMeas
    filter_upwards [] with x
    have hnonneg : 0 ≤ a x := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hpoint : ‖pressureDivergenceCutoffSource η dη u Du f x‖ ≤ a x := by
      calc
        ‖pressureDivergenceCutoffSource η dη u Du f x‖ ≤
            vec3EuclideanNorm (pressureDivergenceCutoffSource η dη u Du f x) :=
          space_norm_le_vec3_euclidean _
        _ ≤ a x := by exact vec3_norm_le_sum_abs _
    change ‖pressureDivergenceCutoffSource η dη u Du f x‖ₑ ≤ ‖a x‖ₑ
    rw [← ofReal_norm, Real.enorm_eq_ofReal hnonneg]
    exact ENNReal.ofReal_le_ofReal hpoint
  have hsumBound : eLpNorm (fun x => ∑ i,
      |pressureDivergenceCutoffSource η dη u Du f x i|)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ 3 * M := by
    have ha0 := eLpNorm_add_le (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ))
      (f := fun x => |pressureDivergenceCutoffSource η dη u Du f x 0|)
      (g := fun x => |pressureDivergenceCutoffSource η dη u Du f x 1| +
        |pressureDivergenceCutoffSource η dη u Du f x 2|) (by norm_num)
    have ha1 := eLpNorm_add_le (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ))
      (f := fun x => |pressureDivergenceCutoffSource η dη u Du f x 1|)
      (g := fun x => |pressureDivergenceCutoffSource η dη u Du f x 2|)
      (by norm_num)
    have he0 := eLpNorm_abs_eq (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (hsourceCompMeas 0)
    have he1 := eLpNorm_abs_eq (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (hsourceCompMeas 1)
    have he2 := eLpNorm_abs_eq (μ := μ)
      (p := ENNReal.ofReal (6 / 5 : ℝ)) (hsourceCompMeas 2)
    have ha1' := ha1.trans (add_le_add he1.le he2.le)
    have ha0' := ha0.trans (add_le_add he0.le ha1')
    have hsum := ha0'.trans (add_le_add (hcomp 0)
      (add_le_add (hcomp 1) (hcomp 2)))
    have hsumfun : (fun x => ∑ i,
        |pressureDivergenceCutoffSource η dη u Du f x i|) = (fun x =>
          |pressureDivergenceCutoffSource η dη u Du f x 0| +
            (|pressureDivergenceCutoffSource η dη u Du f x 1| +
              |pressureDivergenceCutoffSource η dη u Du f x 2|)) := by
      funext x
      simp [Fin.sum_univ_succ]
    rw [hsumfun]
    have hfun : (fun x => |pressureDivergenceCutoffSource η dη u Du f x 0|) +
        (fun x => |pressureDivergenceCutoffSource η dη u Du f x 1| +
          |pressureDivergenceCutoffSource η dη u Du f x 2|) = (fun x =>
            |pressureDivergenceCutoffSource η dη u Du f x 0| +
              (|pressureDivergenceCutoffSource η dη u Du f x 1| +
                |pressureDivergenceCutoffSource η dη u Du f x 2|)) := by
      rfl
    rw [hfun] at hsum
    convert hsum using 1
    · ring
  change eLpNorm (fun x => pressureDivergenceCutoffSource η dη u Du f x)
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤ _
  simpa only [M, μ] using hmono.trans hsumBound

end CKN.Core.Step4
