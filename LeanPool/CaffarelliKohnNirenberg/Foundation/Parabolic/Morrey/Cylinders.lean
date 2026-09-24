/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Slice
public import LeanPool.CaffarelliKohnNirenberg.Setting.VectorNormAggregation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# Cylinders

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

private theorem morreyScale_two {p q r : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hr : 0 < r) :
    (ENNReal.ofReal r) ^ (-(5 * (1 / p - 1 / q))) =
      (2 : ℝ≥0∞) ^ (5 * (1 / p - 1 / q)) *
        (ENNReal.ofReal (2 * r)) ^ (-(5 * (1 / p - 1 / q))) := by
  let d : ℝ := 5 * (1 / p - 1 / q)
  have hdiff : 0 ≤ 1 / p - 1 / q :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq)
  have hd : 0 ≤ d := by
    exact mul_nonneg (by norm_num) hdiff
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2r : ENNReal.ofReal (2 * r) = (2 : ℝ≥0∞) * ENNReal.ofReal r := by
    rw [ENNReal.ofReal_mul (by positivity)]
    norm_num
  change (ENNReal.ofReal r) ^ (-d) =
    (2 : ℝ≥0∞) ^ d * (ENNReal.ofReal (2 * r)) ^ (-d)
  rw [h2r, ENNReal.rpow_neg, ENNReal.rpow_neg,
    ENNReal.mul_rpow_of_nonneg _ _ hd]
  have h2 : (2 : ℝ≥0∞) ^ d ≠ 0 := by positivity
  have h2top : (2 : ℝ≥0∞) ^ d ≠ ⊤ := by finiteness
  calc
    (ENNReal.ofReal r ^ d)⁻¹ =
        (ENNReal.ofReal r ^ d)⁻¹ * 1 := by rw [mul_one]
    _ = (ENNReal.ofReal r ^ d)⁻¹ *
        (2 ^ d * (2 ^ d)⁻¹) := by rw [ENNReal.mul_inv_cancel h2 h2top]
    _ = 2 ^ d * ((2 ^ d)⁻¹ * (ENNReal.ofReal r ^ d)⁻¹) := by ac_rfl
    _ = 2 ^ d * (2 ^ d * ENNReal.ofReal r ^ d)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl h2) (Or.inl h2top)]

private theorem morreyBallCell_le_doubledCylinder {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) {g : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) :
    morreyBallCell p q g z r ≤
      (2 : ℝ≥0∞) ^ (5 * (1 / p - 1 / q)) *
        morreyCell p q g (z.1, z.2 + 2 * r ^ 2) (2 * r) := by
  have hroot := ballPowerIntegral_le_cylinderPowerIntegral
    (p := p) (x := z.1) (t := z.2) (R := r) (le_of_lt hp) hr g
  have hroot' := ENNReal.rpow_le_rpow hroot (one_div_nonneg.mpr hp.le)
  have hscale := morreyScale_two hp hpq hr
  have hexp : -(5 * (1 - p / q) / p) =
      -(5 * (1 / p - 1 / q)) := by
    have hq : 0 < q := lt_of_lt_of_le hp hpq
    field_simp [hp.ne', hq.ne']
  rw [show morreyBallCell p q g z r =
      (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (ballPowerIntegral p g z r) ^ (1 / p) by rfl,
    morreyCell_eq p q g (z.1, z.2 + 2 * r ^ 2) (2 * r)]
  rw [hexp]
  calc
    (ENNReal.ofReal r) ^ (-(5 * (1 / p - 1 / q))) *
        (ballPowerIntegral p g z r) ^ (1 / p) ≤
      (ENNReal.ofReal r) ^ (-(5 * (1 / p - 1 / q))) *
        (cylinderPowerIntegral p g (z.1, z.2 + 2 * r ^ 2) (2 * r)) ^
          (1 / p) := mul_le_mul_of_nonneg_left hroot' (by positivity)
    _ = (2 : ℝ≥0∞) ^ (5 * (1 / p - 1 / q)) *
        ((ENNReal.ofReal (2 * r)) ^
          (-(5 * (1 / p - 1 / q))) *
          (cylinderPowerIntegral p g (z.1, z.2 + 2 * r ^ 2) (2 * r)) ^
            (1 / p)) := by
      rw [hscale]
      ac_rfl

theorem morreyNorm_le_morreyBallNorm_of_range {p q : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (g : ParabolicPoint → ℝ) :
    morreyNorm p q g ≤ morreyBallNorm p q g := by
  exact morreyNorm_le_morreyBallNorm (le_trans zero_le_one hp) hpq g

theorem morreyBallNorm_le_two_rpow_mul_morreyNorm {p q : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (g : ParabolicPoint → ℝ) :
    morreyBallNorm p q g ≤
      (2 : ℝ≥0∞) ^ (5 * (1 / p - 1 / q)) * morreyNorm p q g := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  unfold morreyBallNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  have hcell := morreyBallCell_le_doubledCylinder (g := g) (z := z)
    (r := r.1) hp0 hpq r.2
  let z' : ParabolicPoint := (z.1, z.2 + 2 * r.1 ^ 2)
  have hnorm : morreyCell p q g z' (2 * r.1) ≤ morreyNorm p q g := by
    exact le_iSup_of_le z'
      (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p q g z' s.1)
        ⟨2 * r.1, mul_pos (by norm_num) r.2⟩)
  simpa [z'] using hcell.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))

theorem morrey_cylinder_ball_bridge {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    {g : ParabolicPoint → ℝ} (_ : AEMeasurable g volume) :
    morreyNorm p q g ≤ morreyBallNorm p q g ∧
      morreyBallNorm p q g ≤
        (2 : ℝ≥0∞) ^ (5 * (1 / p - 1 / q)) * morreyNorm p q g := by
  exact ⟨morreyNorm_le_morreyBallNorm_of_range hp hpq g,
    morreyBallNorm_le_two_rpow_mul_morreyNorm hp hpq g⟩

theorem morreyVecMem_iff_cylinder_lt_top {P τ : ℝ} (hP : 1 ≤ P) (hPτ : P ≤ τ)
    (S : Set ParabolicPoint) (u : ParabolicPoint → Vec3) :
    morreyVecMem P τ S u ↔
      ∀ i : Fin 3,
        morreyNorm P τ (S.indicator (fun z => u z i)) < ⊤ := by
  constructor
  · intro h i
    exact (morreyNorm_le_morreyBallNorm_of_range hP hPτ _).trans_lt (h i)
  · intro h i
    have hdiff : 0 ≤ 1 / P - 1 / τ :=
      sub_nonneg.mpr (one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hP) hPτ)
    have hbridge := morreyBallNorm_le_two_rpow_mul_morreyNorm hP hPτ
      (S.indicator (fun z => u z i))
    exact hbridge.trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg
        (mul_nonneg (by norm_num) hdiff) (by norm_num)) (h i))

theorem morreyVecMem_iff_ball_lt_top {P τ : ℝ}
    (S : Set ParabolicPoint) (u : ParabolicPoint → Vec3) :
    morreyVecMem P τ S u ↔
      ∀ i : Fin 3,
        morreyBallNorm P τ (S.indicator (fun z => u z i)) < ⊤ := by
  rfl

end CKN.Foundation.Parabolic.Morrey

namespace CKN

private theorem vec3Ball_eq_euclideanBall_cyl {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    vec3Ball x₀ r = euclideanBall x₀ r := by
  ext x
  change vec3EuclideanNorm (x - x₀) < r ↔ x ∈ euclideanBall x₀ r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
    using (mem_euclideanBall_iff_vecEuclideanNorm_lt (d := 3) hr).symm

private theorem eLpNorm_cube_eq_lintegral_abs_cube_cyl
    {s : Set Vec3} {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s)) :
    eLpNorm f (3 : ℝ≥0∞) (volume.restrict s) ^ (3 : ℕ) =
      ∫⁻ x in s, ENNReal.ofReal |f x| ^ (3 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (3 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top hf,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs]

private theorem h1_vec3_l3_cyl
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) {u : Vec3 → Vec3}
    (hu : ∀ _i : Fin 3, H1Function (euclideanBall x₀ (2 * r)))
    (hcomp : ∀ i : Fin 3, (hu i).toFun = fun x => u x i) :
    ∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ) ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) *
        ∑ i : Fin 3,
          lpNormOn 3 (euclideanBall x₀ r) (hu i).toFun ^ (3 : ℕ) := by
  rw [vec3Ball_eq_euclideanBall_cyl hr]
  have hmeas : ∀ i : Fin 3,
      AEMeasurable (fun x => u x i)
        (volume.restrict (euclideanBall x₀ r)) := by
    intro i
    rw [← hcomp i]
    exact (hu i).memL2.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono_set volume (by
        intro x hx
        have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
          (x₀ := x₀) (by positivity)).1 hx
        have hrr : r ≤ 2 * r := by nlinarith only [hr]
        exact (mem_euclideanBall_iff_vecEuclideanNorm_lt
          (x₀ := x₀) (by positivity)).2 (lt_of_lt_of_le hx' hrr)))
  have hvec := lintegral_vec3EuclideanNorm_rpow_le_sum
    (s := euclideanBall x₀ r) (u := u) (p := (3 : ℝ)) (by norm_num) hmeas
  calc
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) *
        ∑ i : Fin 3, ∫⁻ x in euclideanBall x₀ r,
          ‖u x i‖ₑ ^ (3 : ℝ) := by
      simpa only [show max 0 ((3 : ℝ) / 2 - 1) = (3 : ℝ) / 2 - 1 by norm_num]
        using hvec
    _ = ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) *
        ∑ i : Fin 3, lpNormOn 3 (euclideanBall x₀ r) (hu i).toFun ^ (3 : ℕ) := by
      apply congrArg (fun a => ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * a)
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ∫⁻ x in euclideanBall x₀ r, ‖u x i‖ₑ ^ (3 : ℝ) =
            ∫⁻ x in euclideanBall x₀ r, ENNReal.ofReal |u x i| ^ (3 : ℝ) := by
              apply lintegral_congr
              intro x
              rw [Real.enorm_eq_ofReal_abs,
                ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (u x i)) (by norm_num)]
        _ = eLpNorm (fun x => u x i) (3 : ℝ≥0∞)
              (volume.restrict (euclideanBall x₀ r)) ^ (3 : ℕ) := by
              symm
              apply eLpNorm_cube_eq_lintegral_abs_cube_cyl
              rw [← hcomp i]
              exact (hu i).memL2.aestronglyMeasurable.mono_measure
                (Measure.restrict_mono_set volume (by
                  intro x hx
                  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
                    (x₀ := x₀) (by positivity)).1 hx
                  have hrr : r ≤ 2 * r := by nlinarith only [hr]
                  exact (mem_euclideanBall_iff_vecEuclideanNorm_lt
                    (x₀ := x₀) (by positivity)).2 (lt_of_lt_of_le hx' hrr)))
        _ = lpNormOn 3 (euclideanBall x₀ r) (hu i).toFun ^ (3 : ℕ) := by
              rw [hcomp i]
              rfl

private theorem time_rpow_bound_cyl
    {T : Set ℝ} {A G : ℝ → ℝ≥0∞} {A₀ B G₂ V : ℝ≥0∞}
    (_ : AEMeasurable A (volume.restrict T))
    (hG : AEMeasurable G (volume.restrict T))
    (hA₀top : A₀ ≠ ⊤)
    (hA₀ : ∀ᵐ s ∂volume.restrict T, A s ≤ A₀)
    (hG₂ : (∫⁻ s in T, G s ^ (2 : ℝ)) ≤ G₂)
    (hV : volume T ≤ V) :
    (∫⁻ s in T, A s ^ (3 / 2 : ℝ) * (G s + B) ^ (3 / 2 : ℝ)) ≤
      A₀ ^ (3 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) + V * B ^ (3 / 2 : ℝ)) := by
  have hGmeas : AEMeasurable (fun s => G s ^ (3 / 2 : ℝ))
      (volume.restrict T) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hG
  have hone : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞))
      (volume.restrict T) := aemeasurable_const
  have hpq : (4 / 3 : ℝ).HolderConjugate (4 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict T) hpq hGmeas hone
  have hGpow : (∫⁻ s in T, G s ^ (3 / 2 : ℝ)) ≤
      G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) := by
    calc
      _ = ∫⁻ s in T, (G s ^ (3 / 2 : ℝ)) * 1 := by
        apply lintegral_congr
        intro s
        rw [mul_one]
      _ ≤ (∫⁻ s in T, (G s ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ)) ^
            (1 / (4 / 3 : ℝ)) * (∫⁻ s in T, (1 : ℝ≥0∞) ^ (4 : ℝ)) ^
              (1 / (4 : ℝ)) := hholder
      _ = (∫⁻ s in T, G s ^ (2 : ℝ)) ^ (3 / 4 : ℝ) *
          (volume T) ^ (1 / 4 : ℝ) := by
        rw [show 1 / (4 / 3 : ℝ) = (3 / 4 : ℝ) by norm_num]
        congr 1
        · apply congrArg (fun z : ℝ≥0∞ => z ^ (3 / 4 : ℝ))
          apply lintegral_congr
          intro s
          rw [← ENNReal.rpow_mul]
          norm_num
        · simp
      _ ≤ _ := by gcongr
  have hpoint : ∀ᵐ s ∂volume.restrict T,
      A s ^ (3 / 2 : ℝ) * (G s + B) ^ (3 / 2 : ℝ) ≤
        A₀ ^ (3 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (G s ^ (3 / 2 : ℝ) + B ^ (3 / 2 : ℝ)) := by
    filter_upwards [hA₀] with s hs
    calc
      _ ≤ A₀ ^ (3 / 2 : ℝ) * (G s + B) ^ (3 / 2 : ℝ) := by gcongr
      _ ≤ A₀ ^ (3 / 2 : ℝ) * ((2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (G s ^ (3 / 2 : ℝ) + B ^ (3 / 2 : ℝ))) := by
        have hpow := ENNReal.rpow_add_le_mul_rpow_add_rpow
          (p := (3 / 2 : ℝ)) (G s) B (by norm_num)
        have hpow' : (G s + B) ^ (3 / 2 : ℝ) ≤
            (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
              (G s ^ (3 / 2 : ℝ) + B ^ (3 / 2 : ℝ)) := by
          simpa only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] using hpow
        exact mul_le_mul_of_nonneg_left hpow' (by positivity)
      _ = _ := by ac_rfl
  calc
    _ ≤ ∫⁻ s in T, A₀ ^ (3 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (G s ^ (3 / 2 : ℝ) + B ^ (3 / 2 : ℝ)) := lintegral_mono_ae hpoint
    _ = A₀ ^ (3 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ((∫⁻ s in T, G s ^ (3 / 2 : ℝ)) + (volume T) * B ^ (3 / 2 : ℝ)) := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA₀top) (by finiteness)),
        lintegral_add_left' hGmeas, lintegral_const]
      simp [mul_assoc, mul_comm]
    _ ≤ _ := by gcongr

private theorem sup_sq_le_euclidean_sq_cyl (v : Vec3) :
    ‖v‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) := by
  have hnorm : ‖v‖ ≤ vec3EuclideanNorm v := by
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
  calc
    ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
      rw [show ‖v‖ₑ = ENNReal.ofReal ‖v‖ from (ofReal_norm v).symm,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg v)]
    _ ≤ ENNReal.ofReal (vec3EuclideanNorm v ^ 2) := by
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg v) hnorm 2)
    _ = ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg v) (by norm_num)]
      norm_num [Real.rpow_natCast]

private theorem component_sq_le_spatialGradientSq_cyl
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (z : ParabolicPoint) (i : Fin 3) :
    ‖Du z i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (spatialGradientSq u Du z) := by
  have hnorm : ‖Du z i‖ ^ 2 ≤ spatialGradientSq u Du z := by
    have hsup : (Finset.univ.sup (fun j : Fin 3 => ‖Du z i j‖₊) : ℝ≥0) ≤
        ⟨Real.sqrt (spatialGradientSq u Du z), by positivity⟩ := by
      apply Finset.sup_le
      intro j hj
      change ‖Du z i j‖ ≤ Real.sqrt (spatialGradientSq u Du z)
      exact (Real.le_sqrt (by positivity) (by
        unfold spatialGradientSq
        positivity)).2 (by
        unfold spatialGradientSq
        have hterm : (Du z i j) ^ 2 ≤ ∑ k : Fin 3, ∑ l : Fin 3, (Du z k l) ^ 2 := by
          calc
            _ ≤ ∑ l : Fin 3, (Du z i l) ^ 2 :=
              Finset.single_le_sum (fun l _ => sq_nonneg (Du z i l))
                (Finset.mem_univ j)
            _ ≤ _ := Finset.single_le_sum
              (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (Du z k l)))
              (Finset.mem_univ i)
        simpa [Real.norm_eq_abs, sq_abs] using hterm)
    rw [Pi.norm_def]
    change (↑(Finset.univ.sup (fun j : Fin 3 => ‖Du z i j‖₊) : ℝ≥0) : ℝ) ^ 2 ≤
      spatialGradientSq u Du z
    have hsup' : (↑(Finset.univ.sup (fun j : Fin 3 => ‖Du z i j‖₊) : ℝ≥0) : ℝ) ≤
        Real.sqrt (spatialGradientSq u Du z) := by exact_mod_cast hsup
    calc
      _ ≤ Real.sqrt (spatialGradientSq u Du z) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsup' 2
      _ = _ := Real.sq_sqrt (by unfold spatialGradientSq; positivity)
  calc
    ‖Du z i‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖Du z i‖ ^ 2) := by
      rw [show ‖Du z i‖ₑ = ENNReal.ofReal ‖Du z i‖ from (ofReal_norm _).symm,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg (Du z i))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hnorm

/-- Quantitative cylinder `L³` control obtained from the vector H¹ interpolation
estimate.  The larger cylinder supplies the time-slice energy and gradient
bounds; this is the analytic certificate used by the Step 2 Morrey argument. -/
theorem step2_cylinder_l3_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x : Vec3} {t r : ℝ} (hr : 0 < r)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J)
    (hcyl : parabolicCylinder x t (2 * r) ⊆ spaceTimeSet Ω' J)
    {Abar Gbar : ℝ≥0∞}
    (hAbar : Abar < ⊤)
    (hAbound : (essSup (fun s => ∫⁻ y in vec3Ball x (2 * r),
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
        (volume.restrict (Set.Ioc (t - r ^ 2) t))) ^ (1 / 2 : ℝ) ≤ Abar)
    (hGbound : (∫⁻ w in parabolicCylinder x t (2 * r),
        ENNReal.ofReal (spatialGradientSq u Du w)) ≤ Gbar) :
    (∫⁻ w in parabolicCylinder x t r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
      (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
        localSobolevConstant ^ (3 / 2 : ℝ) * Abar ^ (3 / 2 : ℝ) *
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (Gbar ^ (3 / 4 : ℝ) * ENNReal.ofReal (r ^ 2) ^ (1 / 4 : ℝ) +
          ENNReal.ofReal (r ^ 2) *
            ((Real.toNNReal (32 / r) : ℝ≥0∞) * Abar) ^ (3 / 2 : ℝ)) := by
  let outer : Set Vec3 := euclideanBall x (2 * r)
  let inner : Set Vec3 := vec3Ball x r
  let T : Set ℝ := Set.Ioc (t - r ^ 2) t
  let A : ℝ → ℝ≥0∞ := fun s =>
    (∫⁻ y in outer, ‖u (y, s)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  let G : ℝ → ℝ≥0∞ := fun s =>
    (∫⁻ y in outer, ENNReal.ofReal (spatialGradientSq u Du (y, s))) ^
      (1 / 2 : ℝ)
  have houter : outer ⊆ Ω' := by
    intro y hy
    have hy2 : y ∈ vec3Ball x (2 * r) := by
      change y ∈ euclideanBall x (2 * r) at hy
      rw [vec3Ball_eq_euclideanBall_cyl (x₀ := x) (r := 2 * r) (by positivity)]
      exact hy
    have hmem : (y, t) ∈ spaceTimeSet Ω' J := hcyl (by
      change ((y, t) : ParabolicPoint) ∈ parabolicCylinder x t (2 * r)
      exact ⟨vec3Ball_mono (by nlinarith only [hr]) hy2,
        ⟨by nlinarith only [sq_pos_of_pos hr], le_rfl⟩⟩)
    exact hmem.1
  have hIocJ : T ⊆ J := by
    intro s hs
    have hmem : (x, s) ∈ spaceTimeSet Ω' J := hcyl (by
      change ((x, s) : ParabolicPoint) ∈ parabolicCylinder x t (2 * r)
      exact ⟨by simp [vec3EuclideanNorm_zero, hr],
        ⟨by nlinarith only [hs.1, hr], hs.2⟩⟩)
    exact hmem.2
  have houter_meas : MeasurableSet outer := by
    change MeasurableSet {y : Vec3 | euclideanSqDist y x < (2 * r) ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x).continuous
      continuous_const).measurableSet
  have hprod_u : AEMeasurable (fun z => ‖u z‖ₑ ^ (2 : ℝ))
      ((volume.restrict outer).prod (volume.restrict J)) := by
    have hU := (hsol.2.2.2.2.2.1 Ω' J hbox).1
    have hUprod : AEMeasurable (fun z => ‖u z‖ₑ ^ (2 : ℝ))
        ((volume.restrict Ω').prod (volume.restrict J)) := by
      rw [Measure.prod_restrict Ω' J]
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hU.enorm
    exact hUprod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume houter) le_rfl)
  have hprod_D : AEMeasurable (fun z : Vec3 × ℝ =>
      ENNReal.ofReal (spatialGradientSq u Du z))
      ((volume.restrict outer).prod (volume.restrict J)) := by
    have hD := (hsol.2.2.2.2.2.1 Ω' J hbox).2.1
    have hDprod : AEStronglyMeasurable Du
        ((volume.restrict Ω').prod (volume.restrict J)) := by
      rw [Measure.prod_restrict Ω' J]
      exact hD
    have hcont : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by fun_prop
    have hm := (ENNReal.continuous_ofReal.comp hcont).comp_aestronglyMeasurable hDprod
    exact hm.aemeasurable.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume houter) le_rfl)
  have hAmeas : AEMeasurable A (volume.restrict J) :=
    (hprod_u.lintegral_prod_left').pow_const (1 / 2 : ℝ)
  have hGmeas : AEMeasurable G (volume.restrict J) :=
    (hprod_D.lintegral_prod_left').pow_const (1 / 2 : ℝ)
  have hgood : ∀ᵐ s ∂volume.restrict T,
      (MemLp (fun y => u (y, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun y => Du (y, s)) 2 (volume.restrict Ω')) ∧
      (∀ i : Fin 3, HasWeakGradientOn Ω' (fun y => u (y, s) i)
        (fun y => Du (y, s) i)) := by
    have hslices := slice_memLp_ae_of_sws hsol hbox
    have hgrad : ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun y => u (y, s) i) (fun y => Du (y, s) i) :=
      (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.2.2.2.2.2
    have hgrad_all : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
        HasWeakGradientOn Ω' (fun y => u (y, s) i) (fun y => Du (y, s) i) := by
      rw [ae_all_iff]
      intro i
      exact hgrad i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hIocJ hslices,
      ae_restrict_of_ae_restrict_of_subset hIocJ hgrad_all] with s hs hg
    exact ⟨hs, hg⟩
  have hpoint : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ y in inner, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
        localSobolevConstant ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ) *
        (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * A s) ^ (3 / 2 : ℝ) := by
    filter_upwards [hgood] with s hs
    have hopen : IsOpen (euclideanBall x (2 * r)) := by
      change IsOpen {y : Vec3 | euclideanSqDist y x < (2 * r) ^ 2}
      exact isOpen_lt (contDiff_euclideanSqDist_left x).continuous continuous_const
    let H : ∀ i : Fin 3, H1Function (euclideanBall x (2 * r)) := fun i =>
      { toFun := fun y => u (y, s) i
        grad := fun y => Du (y, s) i
        memL2 := (MemLp.eval hs.1.1 i).mono_measure
          (Measure.restrict_mono_set volume houter)
        gradMemL2 := fun j => (MemLp.eval (MemLp.eval hs.1.2 i) j).mono_measure
          (Measure.restrict_mono_set volume houter)
        hasWeakGradient := (hs.2 i).restrict hopen houter }
    have hcomp : ∀ i : Fin 3, (H i).toFun = fun y => u (y, s) i := by
      intro i
      rfl
    have hvec := h1_vec3_l3_cyl hr (u := fun y => u (y, s)) H hcomp
    have hAi : ∀ i : Fin 3, lpNormOn 2 (euclideanBall x (2 * r))
        (H i).toFun ≤ A s := by
      intro i
      rw [hcomp i]
      calc
        _ ≤ eLpNorm (fun y => u (y, s)) 2
            (volume.restrict (euclideanBall x (2 * r))) := by
          apply eLpNorm_mono_ae
            ((MemLp.eval hs.1.1 i).mono_measure
              (Measure.restrict_mono_set volume houter)).aestronglyMeasurable
          filter_upwards [] with y
          exact norm_le_pi_norm (u (y, s)) i
        _ = A s := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
            (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top
            (hs.1.1.mono_measure
              (Measure.restrict_mono_set volume houter)).aestronglyMeasurable]
          rfl
    have hGi : ∀ i : Fin 3, weakGradientLpNormOn 2
        (euclideanBall x (2 * r)) (H i).grad ≤ G s := by
      intro i
      change eLpNorm (fun y => Du (y, s) i) 2 _ ≤ _
      have hGpoint : ∀ y : Vec3,
          ‖Du (y, s) i‖ₑ ^ (2 : ℝ) ≤
            ENNReal.ofReal (spatialGradientSq u Du (y, s)) := by
        intro y
        exact component_sq_le_spatialGradientSq_cyl (y, s) i
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top
        ((MemLp.eval hs.1.2 i).mono_measure
          (Measure.restrict_mono_set volume houter)).aestronglyMeasurable]
      norm_num
      have hlin : (∫⁻ y in euclideanBall x (2 * r),
          ‖Du (y, s) i‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ y in euclideanBall x (2 * r),
            ENNReal.ofReal (spatialGradientSq u Du (y, s)) := by
        apply lintegral_mono (μ := volume.restrict (euclideanBall x (2 * r)))
        intro y
        exact hGpoint y
      have hpow := ENNReal.rpow_le_rpow hlin
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      simpa [Real.rpow_natCast, G, outer] using hpow
    have hterm : ∀ i : Fin 3, lpNormOn 3 (euclideanBall x r)
        (H i).toFun ^ (3 : ℕ) ≤ localSobolevConstant ^ (3 / 2 : ℝ) *
          A s ^ (3 / 2 : ℝ) * (G s +
            (Real.toNNReal (32 / r) : ℝ≥0∞) * A s) ^ (3 / 2 : ℝ) := by
      intro i
      have hi := h1InterpolationBallCubed hr (H i)
      have hAiPow := ENNReal.rpow_le_rpow (hAi i)
        (by norm_num : (0 : ℝ) ≤ 3 / 2)
      have hsum : weakGradientLpNormOn 2 (euclideanBall x (2 * r)) (H i).grad +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            lpNormOn 2 (euclideanBall x (2 * r)) (H i).toFun ≤
          G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * A s :=
        add_le_add (hGi i)
        (mul_le_mul_of_nonneg_left (hAi i) (by positivity))
      have hsumPow := ENNReal.rpow_le_rpow hsum
        (by norm_num : (0 : ℝ) ≤ 3 / 2)
      calc
        _ ≤ localSobolevConstant ^ (3 / 2 : ℝ) *
            lpNormOn 2 (euclideanBall x (2 * r)) (H i).toFun ^ (3 / 2 : ℝ) *
            (weakGradientLpNormOn 2 (euclideanBall x (2 * r)) (H i).grad +
              (Real.toNNReal (32 / r) : ℝ≥0∞) *
                lpNormOn 2 (euclideanBall x (2 * r)) (H i).toFun) ^
              (3 / 2 : ℝ) := hi
        _ ≤ localSobolevConstant ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ) *
            (weakGradientLpNormOn 2 (euclideanBall x (2 * r)) (H i).grad +
              (Real.toNNReal (32 / r) : ℝ≥0∞) *
                lpNormOn 2 (euclideanBall x (2 * r)) (H i).toFun) ^
              (3 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hAiPow (by positivity)) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hsumPow (by positivity)
    calc
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) *
          ∑ i : Fin 3, (localSobolevConstant ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ) *
            (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * A s) ^ (3 / 2 : ℝ)) := by
        exact (hvec.trans (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => hterm i)) (by positivity)))
      _ = _ := by simp only [Finset.sum_const, Finset.card_fin]; ring_nf
  have hA0 : ∀ᵐ s ∂volume.restrict T,
      A s ≤ (essSup (fun s => ∫⁻ y in vec3Ball x (2 * r),
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
        (volume.restrict T)) ^ (1 / 2 : ℝ) := by
    have hess := ENNReal.ae_le_essSup (μ := volume.restrict T)
      (fun s => ∫⁻ y in vec3Ball x (2 * r),
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
    filter_upwards [hess] with s hs
    change (∫⁻ y in outer, ‖u (y, s)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ _
    have houter_eq : outer = vec3Ball x (2 * r) := by
      dsimp [outer]
      exact (vec3Ball_eq_euclideanBall_cyl (x₀ := x) (r := 2 * r)
        (by positivity)).symm
    rw [houter_eq]
    apply ENNReal.rpow_le_rpow
    · exact (lintegral_mono (μ := volume.restrict (vec3Ball x (2 * r)))
        (fun y => sup_sq_le_euclidean_sq_cyl (u (y, s)))).trans hs
    · norm_num
  have hGsq : ∀ s, G s ^ (2 : ℝ) = ∫⁻ y in outer,
      ENNReal.ofReal (spatialGradientSq u Du (y, s)) := by
    intro s
    dsimp [G]
    rw [← ENNReal.rpow_mul]
    norm_num
  have hrect_sub : outer ×ˢ T ⊆ parabolicCylinder x t (2 * r) := by
    intro z hz
    rcases hz with ⟨hy, hs⟩
    have hy' : z.1 ∈ vec3Ball x (2 * r) := by
      rw [vec3Ball_eq_euclideanBall_cyl (x₀ := x) (r := 2 * r) (by positivity)]
      simpa [outer] using hy
    change vec3EuclideanNorm (z.1 - x) < 2 * r ∧
      ((t - (2 * r) ^ 2 < z.2) ∧ z.2 ≤ t)
    exact ⟨by simpa [mem_vec3Ball] using hy',
      ⟨by nlinarith only [hs.1, hr], hs.2⟩⟩
  have hG2 : (∫⁻ s in T, G s ^ (2 : ℝ)) ≤
      ∫⁻ w in parabolicCylinder x t (2 * r),
        ENNReal.ofReal (spatialGradientSq u Du w) := by
    calc
      _ = ∫⁻ s in T, ∫⁻ y in outer,
          ENNReal.ofReal (spatialGradientSq u Du (y, s)) := by
        apply lintegral_congr
        intro s
        exact hGsq s
      _ = ∫⁻ z in outer ×ˢ T,
          ENNReal.ofReal (spatialGradientSq u Du z) :=
        (CKN.Foundation.Parabolic.Integration.prod_lintegral_swap_cyl (hprod_D.mono_measure (Measure.prod_mono
          le_rfl (Measure.restrict_mono hIocJ le_rfl)))).symm
      _ ≤ _ := lintegral_mono_set hrect_sub
  have hV : volume T ≤ ENNReal.ofReal (r ^ 2) := by
    rw [Real.volume_Ioc]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring_nf))
  have hAmeasT := hAmeas.mono_measure (Measure.restrict_mono hIocJ le_rfl)
  have hGmeasT := hGmeas.mono_measure (Measure.restrict_mono hIocJ le_rfl)
  have hpoint' : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ y in inner, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
        localSobolevConstant ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ) *
        (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * Abar) ^ (3 / 2 : ℝ) := by
    filter_upwards [hpoint, hA0] with s hs hAs
    have hAs' : A s ≤ Abar := hAs.trans hAbound
    have hsum : G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * A s ≤
        G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * Abar :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hAs' (by positivity))
    have hpow := ENNReal.rpow_le_rpow hsum (by norm_num : (0 : ℝ) ≤ 3 / 2)
    calc
      _ ≤ (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
          localSobolevConstant ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ) *
          (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * A s) ^ (3 / 2 : ℝ) := hs
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have htime := time_rpow_bound_cyl
    (B := (Real.toNNReal (32 / r) : ℝ≥0∞) * Abar)
    hAmeasT hGmeasT hAbar.ne
    (hA0.mono fun s hs => hs.trans hAbound) (hG2.trans hGbound) hV
  have hinner_sub : inner ×ˢ T ⊆ spaceTimeSet Ω' J := by
    intro z hz
    exact hcyl (parabolicCylinder_mono (by positivity) (by nlinarith only [hr]) hz)
  have hFinner : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
      ((volume.restrict inner).prod (volume.restrict T)) := by
    have hu := (hsol.2.2.2.2.2.1 Ω' J hbox).1
    have hveccont : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
      unfold vec3EuclideanNorm
      fun_prop
    have hcont : Continuous (fun v : Vec3 =>
        ENNReal.ofReal (vec3EuclideanNorm v) ^ (3 : ℝ)) := by
      exact (ENNReal.continuous_rpow_const (y := (3 : ℝ))).comp
        (ENNReal.continuous_ofReal.comp hveccont)
    have hm := (hcont.comp_aestronglyMeasurable hu).aemeasurable
    rw [Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    exact hm.mono_measure (Measure.restrict_mono_set volume hinner_sub)
  have hinner_eq : (∫⁻ w in parabolicCylinder x t r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
      ∫⁻ s in T, ∫⁻ y in inner,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ) := by
    change (∫⁻ z, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)
      ∂(volume.restrict (inner ×ˢ T))) = _
    exact CKN.Foundation.Parabolic.Integration.prod_lintegral_swap_cyl hFinner
  rw [hinner_eq]
  calc
    _ ≤ ∫⁻ s in T, (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
        localSobolevConstant ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ) *
          (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * Abar) ^ (3 / 2 : ℝ) :=
      lintegral_mono_ae hpoint'
    _ = ((ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
          localSobolevConstant ^ (3 / 2 : ℝ)) *
        (∫⁻ s in T, A s ^ (3 / 2 : ℝ) *
          (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * Abar) ^ (3 / 2 : ℝ)) := by
      let C : ℝ≥0∞ := (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
        localSobolevConstant ^ (3 / 2 : ℝ)
      have hC : C ≠ ⊤ := by
        dsimp [C]
        apply ENNReal.mul_ne_top
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
            (by unfold localSobolevConstant; finiteness)
      calc
        _ = ∫⁻ s in T, C * (A s ^ (3 / 2 : ℝ) *
            (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * Abar) ^ (3 / 2 : ℝ)) := by
          apply lintegral_congr
          intro s
          dsimp [C]
          ring_nf
        _ = C * (∫⁻ s in T, A s ^ (3 / 2 : ℝ) *
            (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * Abar) ^ (3 / 2 : ℝ)) :=
          lintegral_const_mul' _ _ hC
        _ = _ := by rfl
    _ ≤ _ := by
      let C : ℝ≥0∞ := (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
        localSobolevConstant ^ (3 / 2 : ℝ)
      change C * (∫⁻ s in T, A s ^ (3 / 2 : ℝ) *
        (G s + (Real.toNNReal (32 / r) : ℝ≥0∞) * Abar) ^ (3 / 2 : ℝ)) ≤ _
      exact mul_le_mul_of_nonneg_left htime (by positivity)
    _ = _ := by
      ring_nf

/-! The metric-ball-to-cylinder inclusion used to recenter a small Morrey ball. -/
theorem step2_shifted_ball_cylinder
    {z z' : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hz' : z' ∈ Metric.ball z ρ) :
    Metric.ball z ρ ⊆ parabolicCylinder z'.1 (z'.2 + (2 * ρ) ^ 2) (4 * ρ) := by
  have hball : Metric.ball z ρ ⊆ Metric.ball z' (2 * ρ) := by
    intro y hy
    rw [mem_ball] at hy hz' ⊢
    have htri : dist y z' ≤ dist y z + dist z z' := dist_triangle y z z'
    have hzz' : dist z z' < ρ := by simpa [dist_comm] using hz'
    nlinarith only [htri, hy, hzz', hρ]
  exact hball.trans (by
    have hh := metricBall_subset_parabolicCylinder_doubled
      (z := z') (r := 2 * ρ) (by positivity)
    convert hh using 1
    ring_nf)

/-! Closure of a positive cylinder is contained in its closed parabolic ball. -/
theorem step2_closure_cylinder_subset_closedBall
    {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    closure (parabolicCylinder x t r) ⊆
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace (x, t) r := by
  rw [closure_parabolicCylinder hr]
  intro z hz
  change dist z ((x, t) : ParabolicPoint) ≤ r
  rw [dist_eq_parabolicDist z ((x, t) : ParabolicPoint)]
  change max (vec3EuclideanNorm (z.1 - x)) (Real.sqrt |z.2 - t|) ≤ r
  have htime : |z.2 - t| ≤ r ^ 2 := by
    rw [abs_le]
    constructor <;> linarith only [hz.2.1, hz.2.2, sq_nonneg r]
  have hsqrt : Real.sqrt |z.2 - t| ≤ r := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by simpa [sq] using htime⟩
  exact max_le hz.1 hsqrt

/-! Parabolic distance from a point to its forward time-shifted copy. -/
theorem step2_shifted_center_dist {w : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    @dist ParabolicPoint (@PseudoMetricSpace.toDist ParabolicPoint
      parabolicMetricSpace.toPseudoMetricSpace)
      ((w.1, w.2 + r ^ 2) : ParabolicPoint) w = r := by
  calc
    @dist ParabolicPoint (@PseudoMetricSpace.toDist ParabolicPoint
        parabolicMetricSpace.toPseudoMetricSpace)
        ((w.1, w.2 + r ^ 2) : ParabolicPoint) w =
        parabolicDist ((w.1, w.2 + r ^ 2) : ParabolicPoint) w :=
      dist_eq_parabolicDist _ _
    _ = r := by
      have hzero : vec3EuclideanNorm (0 : Vec3) ≤ r := by
        simp [vec3EuclideanNorm_zero, hr.le]
      simp [parabolicDist, max_eq_right hzero,
        abs_of_nonneg (sq_nonneg r), Real.sqrt_sq (le_of_lt hr)]
