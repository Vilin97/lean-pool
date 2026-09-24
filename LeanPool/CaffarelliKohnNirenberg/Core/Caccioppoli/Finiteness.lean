/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationBall
public import LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationCylinder
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.FinitenessComponentBounds

/-!
# Finiteness

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology
noncomputable section

namespace CKN
private theorem caccioppoli_spatial_l3_bound_fixed
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) {u : Vec3 → Vec3}
    {C₆ : ℝ≥0∞}
    (hC₆ : ∀ (v : H1Function (euclideanBall x₀ r)),
      lpNormOn 3 (euclideanBall x₀ r) v.toFun ^ (3 : ℝ) ≤
        C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^ (3 / 2 : ℝ) *
            lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3 / 2 : ℝ) +
          C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
            lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3 : ℝ))
    (hu : ∀ _i : Fin 3, H1Function (euclideanBall x₀ r))
    (hcomp : ∀ i : Fin 3, (hu i).toFun = fun x => u x i) :
    (∫⁻ x in vec3Ball x₀ r,
      ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ)) ≤
      3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          (∑ i : Fin 3, weakGradientLpNormOn 2 (euclideanBall x₀ r) (hu i).grad) ^
            (3 / 2 : ℝ) *
          (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ r) (hu i).toFun) ^
            (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
          (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ r) (hu i).toFun) ^ (3 : ℝ) := by
  let B : Set Vec3 := euclideanBall x₀ r
  let L : ℝ≥0∞ := ∑ i : Fin 3, lpNormOn 2 B (hu i).toFun
  let G : ℝ≥0∞ := ∑ i : Fin 3, weakGradientLpNormOn 2 B (hu i).grad
  have hball : vec3Ball x₀ r = B := by
    ext x
    change vec3EuclideanNorm (x - x₀) < r ↔ x ∈ euclideanBall x₀ r
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).symm
  have hmeas : ∀ i : Fin 3,
      AEStronglyMeasurable (fun x => u x i) (volume.restrict B) := by
    intro i
    rw [← hcomp i]
    exact (hu i).memL2.aestronglyMeasurable
  have hvec := lintegral_vec3EuclideanNorm_rpow_le_sum
    (s := B) (u := u) (p := (3 : ℝ)) (by norm_num)
      (fun i => (hmeas i).aemeasurable)
  rw [hball]
  have hcomp_eq : ∀ i : Fin 3,
      (∫⁻ x in B, ENNReal.ofReal |u x i| ^ (3 : ℝ)) =
        lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) := by
    intro i
    have hi : AEStronglyMeasurable (fun x => u x i) (volume.restrict B) := hmeas i
    calc
      (∫⁻ x in B, ENNReal.ofReal |u x i| ^ (3 : ℝ)) =
          eLpNorm (fun x => u x i) (3 : ℝ≥0∞) (volume.restrict B) ^ (3 : ℕ) :=
        (caccioppoli_eLpNorm_cube_eq_lintegral_abs_cube hi).symm
      _ = lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) := by
        simpa only [lpNormOn] using
          congrArg (fun f : Vec3 → ℝ =>
            eLpNorm f (3 : ℝ≥0∞) (volume.restrict B) ^ (3 : ℕ)) (hcomp i).symm
  have hterm : ∀ i : Fin 3,
      lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) ≤
        C₆ * (weakGradientLpNormOn 2 B (hu i).grad) ^ (3 / 2 : ℝ) *
            (lpNormOn 2 B (hu i).toFun) ^ (3 / 2 : ℝ) +
          C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
            (lpNormOn 2 B (hu i).toFun) ^ (3 : ℝ) := by
    intro i
    simpa [B] using hC₆ (hu i)
  have hLi : ∀ i : Fin 3, lpNormOn 2 B (hu i).toFun ≤ L := by
    intro i
    simpa only [L] using
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
        (f := fun j : Fin 3 => lpNormOn 2 B (hu j).toFun) :
        lpNormOn 2 B (hu i).toFun ≤ ∑ j : Fin 3, lpNormOn 2 B (hu j).toFun)
  have hGi : ∀ i : Fin 3,
      weakGradientLpNormOn 2 B (hu i).grad ≤ G := by
    intro i
    simpa only [G] using
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
        (f := fun j : Fin 3 => weakGradientLpNormOn 2 B (hu j).grad) :
        weakGradientLpNormOn 2 B (hu i).grad ≤
          ∑ j : Fin 3, weakGradientLpNormOn 2 B (hu j).grad)
  have hsum : ∑ i : Fin 3, lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) ≤
      3 * C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) +
        3 * C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) := by
    calc
      _ ≤ ∑ i : Fin 3,
          (C₆ * (weakGradientLpNormOn 2 B (hu i).grad) ^ (3 / 2 : ℝ) *
              (lpNormOn 2 B (hu i).toFun) ^ (3 / 2 : ℝ) +
            C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
              (lpNormOn 2 B (hu i).toFun) ^ (3 : ℝ)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ ≤ 3 * C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) +
          3 * C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) := by
        have hfirst : ∀ i : Fin 3,
            C₆ * (weakGradientLpNormOn 2 B (hu i).grad) ^ (3 / 2 : ℝ) *
                (lpNormOn 2 B (hu i).toFun) ^ (3 / 2 : ℝ) ≤
              C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) := by
          intro i
          gcongr
          · exact hGi i
          · exact hLi i
        have hsecond : ∀ i : Fin 3,
            C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
                (lpNormOn 2 B (hu i).toFun) ^ (3 : ℝ) ≤
              C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) := by
          intro i
          exact mul_le_mul_of_nonneg_left
            (ENNReal.rpow_le_rpow (hLi i) (by norm_num)) (by positivity)
        rw [Finset.sum_add_distrib]
        calc
          _ ≤ ∑ i : Fin 3, C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) +
              ∑ i : Fin 3, C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) :=
            add_le_add (Finset.sum_le_sum (fun i _ => hfirst i))
              (Finset.sum_le_sum (fun i _ => hsecond i))
          _ = _ := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
  calc
    ∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt 3) *
          ∑ i : Fin 3, ∫⁻ x in B, ‖u x i‖ₑ ^ (3 : ℝ) := by
      simpa only [show max 0 ((3 : ℝ) / 2 - 1) = (3 : ℝ) / 2 - 1 by norm_num,
        show (3 : ℝ) ^ ((3 : ℝ) / 2 - 1) = Real.sqrt 3 by
          rw [show (3 : ℝ) / 2 - 1 = (1 / 2 : ℝ) by norm_num,
            ← Real.sqrt_eq_rpow]] using hvec
    _ = ENNReal.ofReal (Real.sqrt 3) *
          ∑ i : Fin 3, ∫⁻ x in B, ENNReal.ofReal |u x i| ^ (3 : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply lintegral_congr
      intro x
      rw [Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    _ ≤ ENNReal.ofReal (Real.sqrt 3) *
          (3 * C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) +
            3 * C₆ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ)) := by
      gcongr
      simpa only [hcomp_eq] using hsum
    _ = _ := by
      dsimp [L, G, B]
      ring
private theorem caccioppoli_l3_finite_of_slice_bound
    {x₀ : Vec3} {t₀ ρ : ℝ} {F : ParabolicPoint → ℝ≥0∞}
    {A G : ℝ → ℝ≥0∞} {K R A₀ G₂ V : ℝ≥0∞}
    (hF : AEMeasurable F
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hA : AEMeasurable A
      (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)))
    (hG : AEMeasurable G
      (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)))
    (hKtop : K ≠ ∞) (hRtop : R ≠ ∞) (hA₀top : A₀ ≠ ∞) (hG₂top : G₂ ≠ ∞)
    (hVtop : V ≠ ∞)
    (hA₀ : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀), A s ≤ A₀)
    (hG₂ : (∫⁻ s in Ioc (t₀ - ρ ^ 2) t₀, G s ^ (2 : ℝ)) ≤ G₂)
    (hV : volume (Ioc (t₀ - ρ ^ 2) t₀) ≤ V)
    (hpoint : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      (∫⁻ y in vec3Ball x₀ ρ, F (y, s)) ≤
        K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) +
          K * R * A s ^ (3 : ℝ)) :
    (∫⁻ z in parabolicCylinder x₀ t₀ ρ, F z) ≠ ∞ := by
  have htime := time_interpolation_ball_l3 (R := R) hA hG hKtop hA₀top hA₀ hG₂ hV
  have hright :
      K * A₀ ^ (3 / 2 : ℝ) * G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) +
        K * R * V * A₀ ^ (3 : ℝ) ≠ ∞ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKtop
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA₀top))
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hG₂top))
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVtop)
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKtop hRtop)
        hVtop) (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA₀top)
  have hprod : AEMeasurable F
      ((volume.restrict (vec3Ball x₀ ρ)).prod
        (volume.restrict (Ioc (t₀ - ρ ^ 2) t₀))) := by
    rw [Measure.prod_restrict]
    exact hF
  have hFubini := lintegral_parabolicCylinder hF
  rw [hFubini]
  apply ne_of_lt (lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hright))
  exact le_trans (lintegral_mono_ae hpoint) htime
private theorem caccioppoli_velocity_slice_bound
    {Ω' : Set Vec3} {x₀ : Vec3} {ρ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {C₆ : ℝ≥0∞}
    (hρ : 0 < ρ)
    (hC₆ : ∀ (v : H1Function (euclideanBall x₀ ρ)),
      lpNormOn 3 (euclideanBall x₀ ρ) v.toFun ^ (3 : ℕ) ≤
        C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ ρ) v.grad ^ (3 / 2 : ℝ) *
            lpNormOn 2 (euclideanBall x₀ ρ) v.toFun ^ (3 / 2 : ℝ) +
          C₆ * ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) *
            lpNormOn 2 (euclideanBall x₀ ρ) v.toFun ^ (3 : ℕ))
    (hB : vec3Ball x₀ ρ ⊆ Ω') {s : ℝ}
    (hs : (MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
      (∀ i : Fin 3, HasWeakGradientOn Ω'
        (fun x => u (x, s) i) (fun x => Du (x, s) i))) :
    (∫⁻ y in vec3Ball x₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      (27 * 3 * ENNReal.ofReal (Real.sqrt 3) * C₆) *
          (∫⁻ y in vec3Ball x₀ ρ,
            ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ^
              (3 / 4 : ℝ) *
          (∫⁻ y in vec3Ball x₀ ρ,
            ENNReal.ofReal (spatialGradientSq u Du (y, s))) ^
              (3 / 4 : ℝ) +
        (27 * 3 * ENNReal.ofReal (Real.sqrt 3) * C₆) *
          ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) *
          (∫⁻ y in vec3Ball x₀ ρ,
            ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ^
              (3 / 2 : ℝ) := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  let E : ℝ≥0∞ := ∫⁻ y in B,
    ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)
  let A : ℝ≥0∞ := E ^ (1 / 2 : ℝ)
  let D : ℝ≥0∞ := ∫⁻ y in B, ENNReal.ofReal (spatialGradientSq u Du (y, s))
  let G : ℝ≥0∞ := D ^ (1 / 2 : ℝ)
  let μ : Measure Vec3 := volume.restrict B
  have huB : MemLp (fun x : Vec3 => u (x, s)) 2 μ := by
    exact hs.1.1.mono_measure (Measure.restrict_mono_set volume hB)
  have hDB : MemLp (fun x : Vec3 => Du (x, s)) 2 μ := by
    exact hs.1.2.mono_measure (Measure.restrict_mono_set volume hB)
  have huMeas : AEStronglyMeasurable (fun x : Vec3 => u (x, s)) μ :=
    huB.aestronglyMeasurable
  have hDMeas : AEStronglyMeasurable (fun x : Vec3 => Du (x, s)) μ :=
    hDB.aestronglyMeasurable
  have hL : ∀ i : Fin 3,
      lpNormOn 2 B (fun x => u (x, s) i) ≤ A := by
    intro i
    exact caccioppoli_l2_component_bound ((huB.eval i).aemeasurable) huMeas
  have hG : ∀ i : Fin 3,
      weakGradientLpNormOn 2 B (fun x => Du (x, s) i) ≤ G := by
    intro i
    simpa [spatialGradientSq, D, G, B] using
      (caccioppoli_gradient_component_bound hDMeas (i := i))
  have hballE : euclideanBall x₀ ρ ⊆ Ω' := by
    intro x hx
    apply hB
    have hx' : vec3EuclideanNorm (x - x₀) < ρ := by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
        using (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1 hx
    exact hx'
  have hballEq : B = euclideanBall x₀ ρ := by
    ext x
    change vec3EuclideanNorm (x - x₀) < ρ ↔ x ∈ euclideanBall x₀ ρ
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).symm
  let huH1 : ∀ i : Fin 3, H1Function (euclideanBall x₀ ρ) := fun i =>
    let hopen : IsOpen (euclideanBall x₀ ρ) := by
      change IsOpen {x : Vec3 | euclideanSqDist x x₀ < ρ ^ 2}
      exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
    { toFun := fun x => u (x, s) i
      grad := fun x => Du (x, s) i
      memL2 := (MemLp.eval hs.1.1 i).mono_measure
        (Measure.restrict_mono_set volume hballE)
      gradMemL2 := fun j => (MemLp.eval (MemLp.eval hs.1.2 i) j).mono_measure
        (Measure.restrict_mono_set volume hballE)
      hasWeakGradient := (hs.2 i).restrict hopen hballE }
  have hcomp : ∀ i : Fin 3,
      (huH1 i).toFun = fun x => (fun y => u (y, s)) x i := by
    intro i
    rfl
  have hC₆' : ∀ (v : H1Function (euclideanBall x₀ ρ)),
      lpNormOn 3 (euclideanBall x₀ ρ) v.toFun ^ (3 : ℝ) ≤
        C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ ρ) v.grad ^ (3 / 2 : ℝ) *
            lpNormOn 2 (euclideanBall x₀ ρ) v.toFun ^ (3 / 2 : ℝ) +
          C₆ * ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) *
            lpNormOn 2 (euclideanBall x₀ ρ) v.toFun ^ (3 : ℝ) := by
    intro v
    convert hC₆ v using 1
    all_goals norm_num [ENNReal.rpow_natCast]
  have hsp := caccioppoli_spatial_l3_bound_fixed hρ hC₆' huH1 hcomp
  have hsumL : ∑ i : Fin 3, lpNormOn 2 B (huH1 i).toFun ≤ 3 * A := by
    calc
      _ ≤ ∑ _i : Fin 3, A := Finset.sum_le_sum (fun i _ => by
        simpa [huH1] using hL i)
      _ = 3 * A := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsumG : ∑ i : Fin 3,
      weakGradientLpNormOn 2 B (huH1 i).grad ≤ 3 * G := by
    calc
      _ ≤ ∑ _i : Fin 3, G := Finset.sum_le_sum (fun i _ => by
        simpa [huH1] using hG i)
      _ = 3 * G := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsumL' : ∑ i : Fin 3,
      lpNormOn 2 (euclideanBall x₀ ρ) (huH1 i).toFun ≤ 3 * A := by
    simpa [hballEq] using hsumL
  have hsumG' : ∑ i : Fin 3,
      weakGradientLpNormOn 2 (euclideanBall x₀ ρ) (huH1 i).grad ≤ 3 * G := by
    simpa [hballEq] using hsumG
  have hsp' : (∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          (3 * G) ^ (3 / 2 : ℝ) * (3 * A) ^ (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) * (3 * A) ^ (3 : ℝ) := by
    calc
      _ ≤ 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          (∑ i : Fin 3, weakGradientLpNormOn 2 (euclideanBall x₀ ρ)
            (huH1 i).grad) ^
            (3 / 2 : ℝ) *
          (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ ρ)
            (huH1 i).toFun) ^ (3 / 2 : ℝ) +
          3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
            ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) *
            (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ ρ)
              (huH1 i).toFun) ^ (3 : ℝ) := by
        simpa [huH1] using hsp
      _ ≤ _ := by gcongr
  have hmain : (∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      (27 * 3 * ENNReal.ofReal (Real.sqrt 3) * C₆) *
          A ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ) +
        (27 * 3 * ENNReal.ofReal (Real.sqrt 3) * C₆) *
          ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) * A ^ (3 : ℝ) := by
    calc
      _ ≤ 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          (3 * G) ^ (3 / 2 : ℝ) * (3 * A) ^ (3 / 2 : ℝ) +
          3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
            ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) * (3 * A) ^ (3 : ℝ) := hsp'
      _ = _ := by
        have hGmul : (3 * G) ^ (3 / 2 : ℝ) =
            (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        have hAmul : (3 * A) ^ (3 / 2 : ℝ) =
            (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        have hA3mul : (3 * A) ^ (3 : ℝ) =
            (3 : ℝ≥0∞) ^ (3 : ℝ) * A ^ (3 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [hGmul, hAmul, hA3mul]
        have hthree : (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
            (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) = (3 : ℝ≥0∞) ^ (3 : ℝ) := by
          rw [← ENNReal.rpow_add]
          all_goals norm_num
        have hfirst :
            3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
                ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ)) *
                ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ)) =
              (27 * 3 * ENNReal.ofReal (Real.sqrt 3) * C₆) *
                A ^ (3 / 2 : ℝ) * G ^ (3 / 2 : ℝ) := by
          calc
            _ = 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
                ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
                  (3 : ℝ≥0∞) ^ (3 / 2 : ℝ)) *
                (G ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ)) := by ring
            _ = _ := by rw [hthree]; norm_num; ring
        have hsecond :
            3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
                ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) *
                ((3 : ℝ≥0∞) ^ (3 : ℝ) * A ^ (3 : ℝ)) =
              (27 * 3 * ENNReal.ofReal (Real.sqrt 3) * C₆) *
                ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) * A ^ (3 : ℝ) := by
          norm_num
          ring
        rw [hfirst, hsecond]
  have hA32 : A ^ (3 / 2 : ℝ) = E ^ (3 / 4 : ℝ) := by
    dsimp [A]
    rw [← ENNReal.rpow_mul]
    norm_num
  have hA3 : A ^ (3 : ℝ) = E ^ (3 / 2 : ℝ) := by
    dsimp [A]
    rw [← ENNReal.rpow_mul]
    norm_num
  have hG32 : G ^ (3 / 2 : ℝ) = D ^ (3 / 4 : ℝ) := by
    dsimp [G]
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hA32, hA3, hG32] at hmain
  simpa [E, D, B] using hmain
private theorem caccioppoli_velocity_ae_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J)
    (hcyl : parabolicCylinder x₀ t₀ ρ ⊆ spaceTimeSet Ω' J) :
    AEMeasurable
        (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
        (volume.restrict (parabolicCylinder x₀ t₀ ρ)) ∧
      ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
        (MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
          MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
        (∀ i : Fin 3, HasWeakGradientOn Ω' (fun x => u (x, s) i)
          (fun x => Du (x, s) i)) := by
  let _ : MeasurableSpace ParabolicPoint := Prod.instMeasurableSpace
  let B : Set Vec3 := vec3Ball x₀ ρ
  let T : Set ℝ := Ioc (t₀ - ρ ^ 2) t₀
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  have hB : B ⊆ Ω' := by
    intro y hy
    have hz : (y, t₀) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨sub_lt_self t₀ hρ2, le_rfl⟩⟩
    exact (hcyl hz).1
  have hT : T ⊆ J := by
    intro s hs
    have hx : x₀ ∈ B := by
      dsimp [B]
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hz : (x₀, s) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs⟩
    exact (hcyl hz).2
  have hu0 : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hF : AEMeasurable
      (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    have hm : AEMeasurable (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)))
        (volume.restrict (spaceTimeSet Ω' J)) :=
      (ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hu0
        |>.aemeasurable
    exact (hm.pow_const (3 : ℝ)).mono_measure
      (Measure.restrict_mono hcyl le_rfl)
  have hslice := slice_memLp_ae_of_sws hsol hbox
  have hgrad : ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
      HasWeakGradientOn Ω' (fun x => u (x, s) i)
        (fun x => Du (x, s) i) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.2.2.2.2.2
  have hgradAll : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x => u (x, s) i)
        (fun x => Du (x, s) i) := by
    rw [ae_all_iff]
    intro i
    exact hgrad i
  refine ⟨hF, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hT hslice,
    ae_restrict_of_ae_restrict_of_subset hT hgradAll] with s hs hg
  exact ⟨hs, hg⟩
private theorem caccioppoli_velocity_energy_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    timeSliceEnergyEssSup x₀ t₀ ρ (fun w => vec3EuclideanNorm (u w)) ≠ ∞ :=
  sws_timeSliceEnergyEssSup_ne_top (h := hsol) (z := (x₀, t₀)) (r := ρ) hρ hsub
private theorem caccioppoli_velocity_gradient_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ z in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (spatialGradientSq u Du z)) ≠ ∞ :=
  ne_of_lt (sws_gradient_integral_lt_top
    (h := hsol) (z := (x₀, t₀)) (r := ρ) hρ hsub)
private theorem caccioppoli_velocity_gradient_measurable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ}
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J)
    (hcyl : parabolicCylinder x₀ t₀ ρ ⊆ spaceTimeSet Ω' J) :
    AEMeasurable
      (fun z => ENNReal.ofReal (spatialGradientSq u Du z))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
  have hDu0 : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.1
  have hsum : Continuous (fun v : Fin 3 → Vec3 =>
      ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by
    fun_prop
  have hcont : Continuous (fun v : Fin 3 → Vec3 =>
      ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ))) :=
    ENNReal.continuous_ofReal.comp hsum
  have hm := (hcont.comp_aestronglyMeasurable hDu0).aemeasurable
  simpa only [spatialGradientSq] using
    hm.mono_measure (Measure.restrict_mono hcyl le_rfl)
private theorem caccioppoli_velocity_integral_ne_top_local
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J)
    (hcyl : parabolicCylinder x₀ t₀ ρ ⊆ spaceTimeSet Ω' J)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞ := by
  let _ : MeasurableSpace ParabolicPoint := Prod.instMeasurableSpace
  let B : Set Vec3 := vec3Ball x₀ ρ
  let T : Set ℝ := Ioc (t₀ - ρ ^ 2) t₀
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  have hB : B ⊆ Ω' := by
    intro y hy
    have hz : (y, t₀) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨sub_lt_self t₀ hρ2, le_rfl⟩⟩
    exact (hcyl hz).1
  have hT : T ⊆ J := by
    intro s hs
    have hx : x₀ ∈ B := by
      dsimp [B]
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hz : (x₀, s) ∈ parabolicCylinder x₀ t₀ ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs⟩
    exact (hcyl hz).2
  have hDu0 : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.1
  obtain ⟨hF, hgood⟩ := caccioppoli_velocity_ae_data
    hsol hρ hbox hcyl
  obtain ⟨C₆, hC₆top, hC₆⟩ := interpolationBall_three_finite
  let E : ℝ → ℝ≥0∞ := fun s => ∫⁻ y in B,
    ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)
  let D : ℝ → ℝ≥0∞ := fun s => ∫⁻ y in B,
    ENNReal.ofReal (spatialGradientSq u Du (y, s))
  let A : ℝ → ℝ≥0∞ := fun s => E s ^ (1 / 2 : ℝ)
  let G : ℝ → ℝ≥0∞ := fun s => D s ^ (1 / 2 : ℝ)
  have hu0 : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hUu := hu0
  have hUd := hDu0
  have hEprod : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    have hnorm : AEStronglyMeasurable (fun z => vec3EuclideanNorm (u z))
        (volume.restrict (spaceTimeSet Ω' J)) := by
      unfold vec3EuclideanNorm
      fun_prop
    have hbase : AEMeasurable
        (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)))
        (volume.restrict (spaceTimeSet Ω' J)) :=
      (ENNReal.continuous_ofReal.comp (by
        unfold vec3EuclideanNorm
        fun_prop)).comp_aestronglyMeasurable hUu |>.aemeasurable
    exact (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hbase).mono_measure
      (Measure.restrict_mono_set volume (prod_mono hB le_rfl))
  have hDprod : AEMeasurable
      (fun z => ENNReal.ofReal (spatialGradientSq u Du z))
      ((volume.restrict B).prod (volume.restrict J)) := by
    have hDwide : AEStronglyMeasurable Du
        ((volume.restrict Ω').prod (volume.restrict J)) := by
      rw [Measure.prod_restrict Ω' J]
      exact hDu0
    have hsum : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by
      fun_prop
    have hcont : Continuous (fun v : Fin 3 → Vec3 =>
        ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ))) :=
      ENNReal.continuous_ofReal.comp hsum
    have hm := (hcont.comp_aestronglyMeasurable hDwide).aemeasurable
    simpa only [spatialGradientSq] using
      hm.mono_measure (Measure.prod_mono
        (Measure.restrict_mono_set volume hB) le_rfl)
  have hA : AEMeasurable A (volume.restrict T) := by
    have h := (hEprod.lintegral_prod_left').pow_const (1 / 2 : ℝ)
    exact (h.mono_measure (Measure.restrict_mono_set volume hT)).congr
      (Filter.Eventually.of_forall (fun s => rfl))
  have hG : AEMeasurable G (volume.restrict T) := by
    have h := (hDprod.lintegral_prod_left').pow_const (1 / 2 : ℝ)
    exact (h.mono_measure (Measure.restrict_mono_set volume hT)).congr
      (Filter.Eventually.of_forall (fun s => rfl))
  have hEtopRaw := caccioppoli_velocity_energy_top hsol hρ hsub
  have hDtop := caccioppoli_velocity_gradient_top hsol hρ hsub
  have hEtop : (essSup E (volume.restrict T)) ≠ ∞ := by
    have hEeq : E = (fun s => timeSliceBallEnergy x₀ ρ s
        (fun w => vec3EuclideanNorm (u w))) := by
      funext s
      dsimp [E, timeSliceBallEnergy]
      apply lintegral_congr
      intro y
      rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
    rw [hEeq]
    simpa [T, timeSliceEnergyEssSup] using hEtopRaw
  let A₀ : ℝ≥0∞ := (essSup E (volume.restrict T)) ^ (1 / 2 : ℝ)
  have hA₀top : A₀ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEtop
  have hA₀bound : ∀ᵐ s ∂volume.restrict T, A s ≤ A₀ := by
    filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict T) (fun s => E s)] with s hs
    exact ENNReal.rpow_le_rpow hs (by norm_num)
  let G₂ : ℝ≥0∞ := ∫⁻ z in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (spatialGradientSq u Du z)
  have hD_cyl := caccioppoli_velocity_gradient_measurable
    hsol hbox hcyl
  have hG₂top : G₂ ≠ ∞ := by simpa [G₂] using hDtop
  have hG₂ : (∫⁻ s in T, G s ^ (2 : ℝ)) ≤ G₂ := by
    have hpow : ∀ s, G s ^ (2 : ℝ) = D s := by
      intro s
      dsimp [G]
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [show (∫⁻ s in T, G s ^ (2 : ℝ)) = ∫⁻ s in T, D s by
      apply lintegral_congr
      intro s
      exact hpow s]
    calc
      _ = ∫⁻ z in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (spatialGradientSq u Du z) := by
        simpa only [D, B, T] using (lintegral_parabolicCylinder hD_cyl).symm
      _ ≤ G₂ := le_rfl
  let V : ℝ≥0∞ := volume T
  have hVtop : V ≠ ∞ := by
    dsimp [V]
    exact measure_Ioc_lt_top.ne
  have hpoint : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
        (27 * 3 * ENNReal.ofReal (Real.sqrt 3) * C₆) *
            A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) +
          (27 * 3 * ENNReal.ofReal (Real.sqrt 3) * C₆) *
            ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) * A s ^ (3 : ℝ) := by
    filter_upwards [hgood] with s hs
    have hA32 : A s ^ (3 / 2 : ℝ) = E s ^ (3 / 4 : ℝ) := by
      dsimp [A]
      rw [← ENNReal.rpow_mul]
      norm_num
    have hA3 : A s ^ (3 : ℝ) = E s ^ (3 / 2 : ℝ) := by
      dsimp [A]
      rw [← ENNReal.rpow_mul]
      norm_num
    have hG32 : G s ^ (3 / 2 : ℝ) = D s ^ (3 / 4 : ℝ) := by
      dsimp [G]
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [hA32, hA3, hG32]
    simpa [E, D, B] using
      caccioppoli_velocity_slice_bound (x₀ := x₀) (ρ := ρ) hρ
        (hC₆ (x₀ := x₀) (r := ρ) hρ) hB hs
  apply caccioppoli_l3_finite_of_slice_bound hF hA hG
    (by finiteness) (by finiteness) hA₀top hG₂top hVtop
    hA₀bound hG₂ (le_rfl) hpoint
theorem caccioppoli_velocity_integral_ne_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞ := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  exact caccioppoli_velocity_integral_ne_top_local hsol hρ hbox hcyl hsub
end CKN
