/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ExtSobolevBallSupported
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# The time-Sobolev estimate on Euclidean balls

Clause (iv) of the external Sobolev input is used here in the Euclidean-ball
form.  The paper's equation (1446--1453) states, for `q = 10/3`,

`∫_{B_r} |v|^(10/3) ≤ C₆ ((∫_{B_r} |∇v|²)(∫_{B_r} |v|²)^(2/3)
  + r^(-2)(∫_{B_r} |v|²)^(5/3))`.

The text at lines 4649--4671 integrates this same-ball estimate in time to
obtain the `L∞_t L²_x ∩ L²_t H¹_x` to `L^(10/3)` embedding.  This theorem
formalizes that time estimate on Euclidean balls.  Clauses (i)--(iii) of the
external input are independent and are not changed here.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

theorem euclideanBall_eq_vec3Ball_timeSobolev
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private theorem eLpNorm_two_sq_eq_lintegral
    {α E : Type*} [MeasurableSpace α] [MeasurableSpace E]
    [NormedAddCommGroup E] [BorelSpace E] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (2 : ℝ≥0∞) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  norm_num

noncomputable def zeroH1Whole : H1Function (Set.univ : Set Vec3) where
  toFun := fun _ => 0
  grad := fun _ => 0
  memL2 := by
    change MemLp (fun _ : Vec3 => (0 : ℝ)) 2 (volume.restrict Set.univ)
    simp
  gradMemL2 := by
    intro i
    change MemLp (fun _ : Vec3 => (0 : ℝ)) 2 (volume.restrict Set.univ)
    simp
  hasWeakGradient := by
    intro i
    have h := HasWeakGradientOn.of_contDiff (U := (Set.univ : Set Vec3))
      (f := fun _ : Vec3 => (0 : ℝ)) (contDiff_const (𝕜 := ℝ))
    simpa [HasWeakGradientOn] using h i

noncomputable def timeSobolevSlice
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    (g : Vec3 × ℝ → ℝ) (Dg : Vec3 × ℝ → Vec3) :
    ℝ → H1Function (euclideanBall x₀ r) := by
  classical
  let hball := euclideanBall_eq_vec3Ball_timeSobolev (x₀ := x₀) hr
  let zero := zeroH1Whole.restrict (isOpen_euclideanBall x₀ r) (Set.subset_univ _)
  exact fun s =>
    if hs : ∃ v : H1Function (vec3Ball x₀ r),
        (fun x => g (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
        (fun x => Dg (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad then
      (Classical.choose hs).restrict (isOpen_euclideanBall x₀ r) (by rw [← hball])
    else zero

private theorem timeSobolevSlice_representation_at
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    {g : Vec3 × ℝ → ℝ} {Dg : Vec3 × ℝ → Vec3}
    (s : ℝ)
    (hs : ∃ v : H1Function (vec3Ball x₀ r),
      (fun x => g (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
      (fun x => Dg (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad) :
    (fun x => g (x, s)) =ᵐ[volume.restrict (euclideanBall x₀ r)]
        (timeSobolevSlice x₀ r hr g Dg s).toFun ∧
    (fun x => Dg (x, s)) =ᵐ[volume.restrict (euclideanBall x₀ r)]
        (timeSobolevSlice x₀ r hr g Dg s).grad := by
  have hball := euclideanBall_eq_vec3Ball_timeSobolev (x₀ := x₀) hr
  constructor
  · simpa [timeSobolevSlice, hs, H1Function.restrict_toFun, hball] using
      (Classical.choose_spec hs).1
  · simpa [timeSobolevSlice, hs, H1Function.restrict_grad, hball] using
      (Classical.choose_spec hs).2

private theorem timeSobolevSlice_representation
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) {J : Set ℝ}
    {g : Vec3 × ℝ → ℝ} {Dg : Vec3 × ℝ → Vec3}
    (hgood : ∀ᵐ s ∂(volume.restrict J),
      ∃ v : H1Function (vec3Ball x₀ r),
        (fun x => g (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
        (fun x => Dg (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad) :
    let u := timeSobolevSlice x₀ r hr g Dg
    (∀ᵐ s ∂(volume.restrict J),
      (fun x => g (x, s)) =ᵐ[volume.restrict (euclideanBall x₀ r)] (u s).toFun) ∧
    (∀ᵐ s ∂(volume.restrict J),
      (fun x => Dg (x, s)) =ᵐ[volume.restrict (euclideanBall x₀ r)] (u s).grad) := by
  dsimp
  constructor
  · filter_upwards [hgood] with s hs
    exact (timeSobolevSlice_representation_at x₀ r hr
      (g := g) (Dg := Dg) s hs).1
  · filter_upwards [hgood] with s hs
    exact (timeSobolevSlice_representation_at x₀ r hr
      (g := g) (Dg := Dg) s hs).2

private theorem timeSobolevSlice_norm_eq
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    {g : Vec3 × ℝ → ℝ} {Dg : Vec3 × ℝ → Vec3}
    (s : ℝ)
    (hs : ∃ v : H1Function (vec3Ball x₀ r),
      (fun x => g (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
      (fun x => Dg (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad) :
    lpNormOn 2 (euclideanBall x₀ r)
        (timeSobolevSlice x₀ r hr g Dg s).toFun =
      eLpNorm (fun x => g (x, s)) 2 (volume.restrict (vec3Ball x₀ r)) := by
  have hrep := (timeSobolevSlice_representation_at x₀ r hr
    (g := g) (Dg := Dg) s hs).1
  calc
    eLpNorm (timeSobolevSlice x₀ r hr g Dg s).toFun 2
        (volume.restrict (euclideanBall x₀ r)) =
        eLpNorm (fun x => g (x, s)) 2 (volume.restrict (euclideanBall x₀ r)) :=
      (eLpNorm_congr_ae hrep).symm
    _ = eLpNorm (fun x => g (x, s)) 2 (volume.restrict (vec3Ball x₀ r)) := by
      rw [euclideanBall_eq_vec3Ball_timeSobolev (x₀ := x₀) (r := r) hr]

private theorem timeSobolevSlice_mass_eq
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    {g : Vec3 × ℝ → ℝ} {Dg : Vec3 × ℝ → Vec3}
    (s : ℝ)
    (hs : ∃ v : H1Function (vec3Ball x₀ r),
      (fun x => g (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
      (fun x => Dg (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad) :
    (∫⁻ x in euclideanBall x₀ r, ‖g (x, s)‖ₑ ^ (2 : ℝ)) =
      lpNormOn 2 (euclideanBall x₀ r)
        (timeSobolevSlice x₀ r hr g Dg s).toFun ^ (2 : ℝ) := by
  have hsrep := (timeSobolevSlice_representation_at x₀ r hr
    (g := g) (Dg := Dg) s hs).1
  have hIntEq : (∫⁻ x in euclideanBall x₀ r, ‖g (x, s)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x in euclideanBall x₀ r,
        ‖(timeSobolevSlice x₀ r hr g Dg s).toFun x‖ₑ ^ (2 : ℝ) := by
    apply lintegral_congr_ae
    filter_upwards [hsrep] with x hx
    rw [hx]
  rw [hIntEq]
  exact (eLpNorm_two_sq_eq_lintegral
    ((timeSobolevSlice x₀ r hr g Dg s).memL2.aestronglyMeasurable)).symm

private theorem timeSobolevSlice_gradient_eq
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    {g : Vec3 × ℝ → ℝ} {Dg : Vec3 × ℝ → Vec3}
    (s : ℝ)
    (hs : ∃ v : H1Function (vec3Ball x₀ r),
      (fun x => g (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
      (fun x => Dg (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad) :
    weakGradientLpNormOn 2 (euclideanBall x₀ r)
        (timeSobolevSlice x₀ r hr g Dg s).grad ^ (2 : ℝ) =
      ∫⁻ x in euclideanBall x₀ r, ‖Dg (x, s)‖ₑ ^ (2 : ℝ) := by
  have hrep := (timeSobolevSlice_representation_at x₀ r hr
    (g := g) (Dg := Dg) s hs).2
  have hgradMem : MemLp (timeSobolevSlice x₀ r hr g Dg s).grad 2
      (volume.restrict (euclideanBall x₀ r)) :=
    (memLp_pi_iff).2 (timeSobolevSlice x₀ r hr g Dg s).gradMemL2
  have hgradMeas := hgradMem.aestronglyMeasurable
  have hIntEq : (∫⁻ x in euclideanBall x₀ r,
      ‖Dg (x, s)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x in euclideanBall x₀ r,
        ‖(timeSobolevSlice x₀ r hr g Dg s).grad x‖ₑ ^ (2 : ℝ) := by
    apply lintegral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx]
  unfold weakGradientLpNormOn
  rw [eLpNorm_two_sq_eq_lintegral hgradMeas, hIntEq]

/-- The Euclidean-ball form of clause (iv) of the external Sobolev
input, with one absolute constant. -/
theorem ball_time_sobolev :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x₀ : Vec3) (r : ℝ), 0 < r →
      ∀ J : Set ℝ, OrdConnected J →
      ∀ g : Vec3 × ℝ → ℝ, ∀ Dg : Vec3 × ℝ → Vec3,
      let U := vec3Ball x₀ r
      AEStronglyMeasurable g (volume.restrict (U ×ˢ J)) →
      AEStronglyMeasurable Dg (volume.restrict (U ×ˢ J)) →
      (∀ᵐ s ∂volume.restrict J, ∃ v : H1Function U,
        (fun x => g (x,s)) =ᵐ[volume.restrict U] v.toFun ∧
        (fun x => Dg (x,s)) =ᵐ[volume.restrict U] v.grad) →
      MemLp g 2 (volume.restrict (U ×ˢ J)) →
      MemLp Dg 2 (volume.restrict (U ×ˢ J)) →
      let A := essSup
        (fun s => eLpNorm (fun x => g (x,s)) 2 (volume.restrict U))
        (volume.restrict J)
      A < ⊤ →
      MemLp g (ENNReal.ofReal (10/3 : ℝ)) (volume.restrict (U ×ˢ J)) ∧
      eLpNorm g (ENNReal.ofReal (10/3 : ℝ))
          (volume.restrict (U ×ˢ J)) ^ (10/3 : ℝ) ≤
        ENNReal.ofReal C *
          (A ^ (4/3 : ℝ) *
            eLpNorm (fun z => vec3EuclideanNorm (Dg z)) 2
              (volume.restrict (U ×ˢ J)) ^ (2 : ℝ) +
           ENNReal.ofReal (r ^ (-2 : ℝ)) *
             A ^ (10/3 : ℝ) * volume J) := by
  obtain ⟨K, hKtop, hKinterp⟩ := interpolationBall_finite
  let C : ℝ := K.toReal + 1
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCeq : ENNReal.ofReal C = K + 1 := by
    dsimp [C]
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num)]
    rw [ENNReal.ofReal_toReal hKtop]
    norm_num
  have hKle : K ≤ ENNReal.ofReal C := by
    rw [hCeq]
    exact le_add_of_nonneg_right (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro x₀ r hr J hJ g Dg U hg hDg hslice hg₂ hDg₂ A hA
  let E : Set Vec3 := euclideanBall x₀ r
  let ν : Measure ℝ := volume.restrict J
  let μ : Measure Vec3 := volume.restrict U
  let u : ℝ → H1Function E := timeSobolevSlice x₀ r hr g Dg
  let M : ℝ → ℝ≥0∞ := fun s => eLpNorm (fun x => g (x, s)) 2 μ
  let D : ℝ → ℝ≥0∞ := fun s => weakGradientLpNormOn 2 E (u s).grad ^ (2 : ℝ)
  let M₂ : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in E, ‖g (x, s)‖ₑ ^ (2 : ℝ)
  let D₂ : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in E, ‖Dg (x, s)‖ₑ ^ (2 : ℝ)
  let Q : ℝ≥0∞ := (ENNReal.ofReal r) ^ (-(2 : ℝ))
  let q : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  have hBall : E = U := by
    dsimp [E, U]
    exact euclideanBall_eq_vec3Ball_timeSobolev (x₀ := x₀) (r := r) hr
  have hprod : volume.restrict (U ×ˢ J) =
      (volume.restrict E).prod (volume.restrict J) := by
    calc
      volume.restrict (U ×ˢ J) =
          (volume.restrict U).prod (volume.restrict J) := by
        rw [show (volume : Measure (Vec3 × ℝ)) =
          (volume : Measure Vec3).prod (volume : Measure ℝ) from
            Measure.volume_eq_prod Vec3 ℝ]
        exact (Measure.prod_restrict U J).symm
      _ = (volume.restrict E).prod (volume.restrict J) := by rw [← hBall]
  have hgProd : AEStronglyMeasurable g
      ((volume.restrict E).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hg
  have hDgProd : AEStronglyMeasurable Dg
      ((volume.restrict E).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hDg
  have hgLpProd : MemLp g 2 ((volume.restrict E).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hg₂
  have hDgLpProd : MemLp Dg 2 ((volume.restrict E).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hDg₂
  have hgood : ∀ᵐ s ∂ν,
      ∃ v : H1Function (vec3Ball x₀ r),
        (fun x => g (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
        (fun x => Dg (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad := by
    simpa [ν, U] using hslice
  have hrep := timeSobolevSlice_representation x₀ r hr (J := J)
    (g := g) (Dg := Dg) hgood
  have hrepG : ∀ᵐ s ∂ν,
      (fun x => g (x, s)) =ᵐ[volume.restrict E] (u s).toFun := by
    simpa [u, ν] using hrep.1
  have hrepD : ∀ᵐ s ∂ν,
      (fun x => Dg (x, s)) =ᵐ[volume.restrict E] (u s).grad := by
    simpa [u, ν] using hrep.2
  have hG₂fun : AEMeasurable
      (fun z : Vec3 × ℝ => ‖g z‖ₑ ^ (2 : ℝ))
      ((volume.restrict E).prod (volume.restrict J)) :=
    hgProd.enorm.pow_const (2 : ℝ)
  have hD₂fun : AEMeasurable
      (fun z : Vec3 × ℝ => ‖Dg z‖ₑ ^ (2 : ℝ))
      ((volume.restrict E).prod (volume.restrict J)) :=
    hDgProd.enorm.pow_const (2 : ℝ)
  have hM₂meas : AEMeasurable M₂ ν := by
    exact hG₂fun.lintegral_prod_left'
  have hD₂meas : AEMeasurable D₂ ν := by
    exact hD₂fun.lintegral_prod_left'
  have hDae : ∀ᵐ s ∂ν, D s = D₂ s := by
    filter_upwards [hgood] with s hs
    exact timeSobolevSlice_gradient_eq x₀ r hr s hs
  have hDae' : ∀ᵐ s ∂ν, D₂ s = D s := hDae.mono (fun _ hs => hs.symm)
  have hDmeas : AEMeasurable D ν := hD₂meas.congr hDae'
  have hDtotal : (∫⁻ s, D s ∂ν) =
      ∫⁻ z in E ×ˢ J, ‖Dg z‖ₑ ^ (2 : ℝ) := by
    calc
      _ = ∫⁻ s, D₂ s ∂ν := lintegral_congr_ae hDae
      _ = ∫⁻ z in E ×ˢ J, ‖Dg z‖ₑ ^ (2 : ℝ) :=
        (prod_lintegral_swap_cyl hD₂fun).symm
  have hM₂total : (∫⁻ s, M₂ s ∂ν) =
      ∫⁻ z in E ×ˢ J, ‖g z‖ₑ ^ (2 : ℝ) :=
    (prod_lintegral_swap_cyl hG₂fun).symm
  have hGint : (∫⁻ z in E ×ˢ J, ‖g z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have hprodE : volume.restrict (E ×ˢ J) =
        (volume.restrict E).prod (volume.restrict J) := by
      rw [show (volume : Measure (Vec3 × ℝ)) =
        (volume : Measure Vec3).prod (volume : Measure ℝ) from
          Measure.volume_eq_prod Vec3 ℝ]
      exact (Measure.prod_restrict E J).symm
    have hfinite := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hgProd).mp hgLpProd.eLpNorm_lt_top
    simpa [hprodE, ENNReal.toReal_ofNat] using hfinite
  have hDgint : (∫⁻ z in E ×ˢ J, ‖Dg z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have hprodE : volume.restrict (E ×ˢ J) =
        (volume.restrict E).prod (volume.restrict J) := by
      rw [show (volume : Measure (Vec3 × ℝ)) =
        (volume : Measure Vec3).prod (volume : Measure ℝ) from
          Measure.volume_eq_prod Vec3 ℝ]
      exact (Measure.prod_restrict E J).symm
    have hfinite := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hDgLpProd.aestronglyMeasurable).mp hDgLpProd.eLpNorm_lt_top
    simpa [hprodE, ENNReal.toReal_ofNat] using hfinite
  have hDtotalFinite : (∫⁻ s, D s ∂ν) < ⊤ := by
    rw [hDtotal]
    exact hDgint
  have hM₂totalFinite : (∫⁻ s, M₂ s ∂ν) < ⊤ := by
    rw [hM₂total]
    exact hGint
  have hAess : ∀ᵐ s ∂ν, M s ≤ A := by
    exact ENNReal.ae_le_essSup (μ := ν) (fun s => M s)
  have hUbound : ∀ᵐ s ∂ν, lpNormOn 2 E (u s).toFun ≤ A := by
    filter_upwards [hgood, hAess] with s hs hMs
    rw [timeSobolevSlice_norm_eq x₀ r hr s hs]
    exact hMs
  have hgradMass : ∀ᵐ s ∂ν, M₂ s = lpNormOn 2 E (u s).toFun ^ (2 : ℝ) := by
    filter_upwards [hgood] with s hs
    exact timeSobolevSlice_mass_eq x₀ r hr s hs
  have hspatial : ∀ {x₀ : Vec3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) ≤
          K * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^ (2 : ℕ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (4 / 3 : ℝ) +
            K * (ENNReal.ofReal r) ^ (-(2 : ℝ)) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) := by
    intro x₀ r hr v
    have h := hKinterp (10 / 3) (by norm_num) (by norm_num) hr v
    change lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) ≤
        K * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
            (2 * (3 * ((10 / 3 : ℝ) - 2) / 4)) *
          lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
            ((10 / 3 : ℝ) - 2 * (3 * ((10 / 3 : ℝ) - 2) / 4)) +
        K * (ENNReal.ofReal r) ^ (-(2 * (3 * ((10 / 3 : ℝ) - 2) / 4))) *
          lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) at h
    norm_num at h
    exact h
  have hQ : Q = ENNReal.ofReal (r ^ (-(2 : ℝ))) := by
    dsimp [Q]
    rw [← ENNReal.ofReal_rpow_of_pos hr]
  have hRadius : ENNReal.ofReal r ^ (-(2 : ℝ)) =
      ENNReal.ofReal (r ^ (-(2 : ℝ))) := by
    rw [← ENNReal.ofReal_rpow_of_pos hr]
  have hQtop : Q ≠ ⊤ := by
    rw [hQ]
    exact ENNReal.ofReal_ne_top
  have hqfun : AEMeasurable
      (fun z : Vec3 × ℝ => ‖g z‖ₑ ^ (10 / 3 : ℝ))
      ((volume.restrict E).prod (volume.restrict J)) := by
    exact hgProd.enorm.pow_const (10 / 3 : ℝ)
  have hqtime := extSobolevBall_productIntegral_eq_timeSlices
    (x₀ := x₀) (r := r) (J := J) (g := g) (u := u) hqfun hrepG
  have hpointTime : ∀ᵐ s ∂ν,
      lpNormOn q E (u s).toFun ^ (10 / 3 : ℝ) ≤
        K * A ^ (4 / 3 : ℝ) * D s + K * Q * A ^ (10 / 3 : ℝ) := by
    filter_upwards [hUbound] with s hs
    have hsp := hspatial (x₀ := x₀) (r := r) hr (u s)
    have hpow₁ : lpNormOn 2 E (u s).toFun ^ (4 / 3 : ℝ) ≤ A ^ (4 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow hs (by norm_num)
    have hpow₂ : lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) ≤ A ^ (10 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow hs (by norm_num)
    have hfirst : K * weakGradientLpNormOn 2 E (u s).grad ^ (2 : ℕ) *
        lpNormOn 2 E (u s).toFun ^ (4 / 3 : ℝ) ≤
          K * A ^ (4 / 3 : ℝ) * D s := by
      calc
        _ ≤ K * weakGradientLpNormOn 2 E (u s).grad ^ (2 : ℕ) *
              A ^ (4 / 3 : ℝ) := by gcongr
        _ = K * A ^ (4 / 3 : ℝ) * D s := by
          simp [D, mul_assoc, mul_left_comm, mul_comm]
    have hsecond : K * ENNReal.ofReal r ^ (-(2 : ℝ)) *
        lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) ≤
          K * Q * A ^ (10 / 3 : ℝ) := by
      calc
        _ = K * ENNReal.ofReal (r ^ (-(2 : ℝ))) *
              lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) := by rw [hRadius]
        _ ≤ K * ENNReal.ofReal (r ^ (-(2 : ℝ))) * A ^ (10 / 3 : ℝ) := by
          gcongr
        _ = K * Q * A ^ (10 / 3 : ℝ) := by rw [hQ]
    calc
      _ = lpNormOn (ENNReal.ofReal (10 / 3 : ℝ))
          (euclideanBall x₀ r) (u s).toFun ^ (10 / 3 : ℝ) := by simp [q, E]
      _ ≤ K * A ^ (4 / 3 : ℝ) * D s + K * Q * A ^ (10 / 3 : ℝ) := by
        calc
          _ ≤ K * weakGradientLpNormOn 2 E (u s).grad ^ (2 : ℕ) *
                lpNormOn 2 E (u s).toFun ^ (4 / 3 : ℝ) +
              K * ENNReal.ofReal r ^ (-(2 : ℝ)) *
                lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) := by
            simpa [E] using hsp
          _ ≤ _ := add_le_add hfirst hsecond
  have hpointFinite : ∀ᵐ s ∂ν,
      lpNormOn q E (u s).toFun ^ (10 / 3 : ℝ) ≤
        K * A ^ (4 / 3 : ℝ) * D s + K * Q * A ^ (4 / 3 : ℝ) * M₂ s := by
    filter_upwards [hUbound, hgradMass] with s hs hmass
    have hsp := hspatial (x₀ := x₀) (r := r) hr (u s)
    have hpow : lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) =
        lpNormOn 2 E (u s).toFun ^ (4 / 3 : ℝ) *
          lpNormOn 2 E (u s).toFun ^ (2 : ℝ) := by
      rw [show (10 / 3 : ℝ) = 4 / 3 + 2 by norm_num,
        ENNReal.rpow_add_of_nonneg (x := lpNormOn 2 E (u s).toFun)
          (y := (4 / 3 : ℝ)) (z := (2 : ℝ)) (by norm_num) (by norm_num)]
    have hpowBound : lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) ≤
        A ^ (4 / 3 : ℝ) * M₂ s := by
      rw [hpow, hmass]
      exact mul_le_mul_of_nonneg_right
        (ENNReal.rpow_le_rpow hs (by norm_num)) (by positivity)
    have hsp := hspatial (x₀ := x₀) (r := r) hr (u s)
    have hfirst : K * weakGradientLpNormOn 2 E (u s).grad ^ (2 : ℕ) *
        lpNormOn 2 E (u s).toFun ^ (4 / 3 : ℝ) ≤ K * A ^ (4 / 3 : ℝ) * D s := by
      calc
        _ ≤ K * weakGradientLpNormOn 2 E (u s).grad ^ (2 : ℕ) * A ^ (4 / 3 : ℝ) := by
          gcongr
        _ = K * A ^ (4 / 3 : ℝ) * D s := by
          simp [D, mul_assoc, mul_left_comm, mul_comm]
    have hsecond : K * ENNReal.ofReal r ^ (-(2 : ℝ)) *
        lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) ≤
          K * Q * A ^ (4 / 3 : ℝ) * M₂ s := by
      calc
        _ = K * ENNReal.ofReal (r ^ (-(2 : ℝ))) *
              lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) := by rw [hRadius]
        _ ≤ K * ENNReal.ofReal (r ^ (-(2 : ℝ))) *
              (A ^ (4 / 3 : ℝ) * M₂ s) := by gcongr
        _ = K * Q * A ^ (4 / 3 : ℝ) * M₂ s := by rw [hQ]; ac_rfl
    calc
      _ = lpNormOn (ENNReal.ofReal (10 / 3 : ℝ))
          (euclideanBall x₀ r) (u s).toFun ^ (10 / 3 : ℝ) := by simp [q, E]
      _ ≤ K * A ^ (4 / 3 : ℝ) * D s + K * Q * A ^ (4 / 3 : ℝ) * M₂ s := by
        calc
          _ ≤ K * weakGradientLpNormOn 2 E (u s).grad ^ (2 : ℕ) *
                lpNormOn 2 E (u s).toFun ^ (4 / 3 : ℝ) +
              K * ENNReal.ofReal r ^ (-(2 : ℝ)) *
                lpNormOn 2 E (u s).toFun ^ (10 / 3 : ℝ) := by
            simpa [E] using hsp
          _ ≤ _ := add_le_add hfirst hsecond
  have hRhsFinite :
      (∫⁻ s, K * A ^ (4 / 3 : ℝ) * D s +
        K * Q * A ^ (4 / 3 : ℝ) * M₂ s ∂ν) < ⊤ := by
    have hfirstMeas : AEMeasurable (fun s =>
        (K * A ^ (4 / 3 : ℝ)) * D s) ν := hDmeas.const_mul _
    have hsecondMeas : AEMeasurable (fun s =>
        (K * Q * A ^ (4 / 3 : ℝ)) * M₂ s) ν := hM₂meas.const_mul _
    have hKfin : K * A ^ (4 / 3 : ℝ) ≠ ⊤ := by
      exact ENNReal.mul_ne_top hKtop
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_of_lt hA))
    have hKQfin : K * Q * A ^ (4 / 3 : ℝ) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hKtop hQtop)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_of_lt hA))
    have hfirst : (∫⁻ s, K * A ^ (4 / 3 : ℝ) * D s ∂ν) < ⊤ := by
      rw [show (fun s => K * A ^ (4 / 3 : ℝ) * D s) =
        fun s => (K * A ^ (4 / 3 : ℝ)) * D s by funext s; ring,
        lintegral_const_mul'' _ hDmeas]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hKfin) hDtotalFinite
    have hsecond : (∫⁻ s, K * Q * A ^ (4 / 3 : ℝ) * M₂ s ∂ν) < ⊤ := by
      rw [show (fun s => K * Q * A ^ (4 / 3 : ℝ) * M₂ s) =
        fun s => (K * Q * A ^ (4 / 3 : ℝ)) * M₂ s by funext s; ring,
        lintegral_const_mul'' _ hM₂meas]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hKQfin) hM₂totalFinite
    rw [lintegral_add_left' hfirstMeas]
    exact ENNReal.add_lt_top.mpr ⟨hfirst, hsecond⟩
  have hqIntegralFinite :
      (∫⁻ z in E ×ˢ J, ‖g z‖ₑ ^ (10 / 3 : ℝ)) < ⊤ := by
    rw [hqtime]
    exact (lintegral_mono_ae hpointFinite).trans_lt hRhsFinite
  have hqMeasTarget : AEStronglyMeasurable g
      (volume.restrict (U ×ˢ J)) := hg
  have hqIntegralFiniteTarget :
      (∫⁻ z, ‖g z‖ₑ ^ (ENNReal.ofReal (10 / 3 : ℝ)).toReal
        ∂(volume.restrict (U ×ˢ J))) < ⊤ := by
    simpa [U, E, hBall,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3)] using hqIntegralFinite
  have hmemq : MemLp g q (volume.restrict (U ×ˢ J)) := by
    rw [memLp_iff]
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by dsimp [q]; norm_num) (by dsimp [q]; norm_num) hqMeasTarget).2
      hqIntegralFiniteTarget
  have hDcompare :
      (∫⁻ z in E ×ˢ J, ‖Dg z‖ₑ ^ (2 : ℝ)) ≤
        eLpNorm (fun z => vec3EuclideanNorm (Dg z)) 2
          (volume.restrict (U ×ˢ J)) ^ (2 : ℝ) := by
    have hEmeas : AEStronglyMeasurable
        (fun z : Vec3 × ℝ => vec3EuclideanNorm (Dg z))
        (volume.restrict (U ×ˢ J)) :=
      (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hDg)
    have hEid := eLpNorm_two_sq_eq_lintegral hEmeas
    have hProductSet : E ×ˢ J = U ×ˢ J := by rw [hBall]
    calc
      (∫⁻ z in E ×ˢ J, ‖Dg z‖ₑ ^ (2 : ℝ)) =
          ∫⁻ z in U ×ˢ J, ‖Dg z‖ₑ ^ (2 : ℝ) := by rw [hProductSet]
      _ ≤ ∫⁻ z in U ×ˢ J, ‖vec3EuclideanNorm (Dg z)‖ₑ ^ (2 : ℝ) := by
        apply lintegral_mono
        intro z
        have hnorm : ‖Dg z‖ₑ ≤ ‖vec3EuclideanNorm (Dg z)‖ₑ := by
          calc
            ‖Dg z‖ₑ = ENNReal.ofReal ‖Dg z‖ := by rw [← ofReal_norm]
            _ ≤ ENNReal.ofReal (vec3EuclideanNorm (Dg z)) :=
              ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm (Dg z))
            _ = ‖vec3EuclideanNorm (Dg z)‖ₑ :=
              (Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg (Dg z))).symm
        exact ENNReal.rpow_le_rpow hnorm (by norm_num)
      _ = eLpNorm (fun z => vec3EuclideanNorm (Dg z)) 2
            (volume.restrict (U ×ˢ J)) ^ (2 : ℝ) := hEid.symm
  have hIntegralBound :
      eLpNorm g q (volume.restrict (U ×ˢ J)) ^ (10 / 3 : ℝ) ≤
        ENNReal.ofReal C *
          (A ^ (4 / 3 : ℝ) *
            eLpNorm (fun z => vec3EuclideanNorm (Dg z)) 2
              (volume.restrict (U ×ˢ J)) ^ (2 : ℝ) +
          ENNReal.ofReal (r ^ (-2 : ℝ)) * A ^ (10 / 3 : ℝ) * volume J) := by
    have htargetId' : eLpNorm g q (volume.restrict (U ×ˢ J)) ^ (10 / 3 : ℝ) =
        ∫⁻ z in U ×ˢ J, ‖g z‖ₑ ^ (10 / 3 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by dsimp [q]; norm_num) (by dsimp [q]; norm_num) hqMeasTarget,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3),
        ← ENNReal.rpow_mul]
      norm_num
    rw [htargetId']
    have hBoundOnProduct :
        (∫⁻ z in E ×ˢ J, ‖g z‖ₑ ^ (10 / 3 : ℝ)) ≤
          K * A ^ (4 / 3 : ℝ) * (∫⁻ s, D s ∂ν) +
            K * Q * A ^ (10 / 3 : ℝ) * volume J := by
      rw [hqtime]
      have hfirstMeas : AEMeasurable (fun s =>
          (K * A ^ (4 / 3 : ℝ)) * D s) ν := hDmeas.const_mul _
      have hsum :
          (∫⁻ s, K * D s * A ^ (4 / 3 : ℝ) +
            K * Q * A ^ (10 / 3 : ℝ) ∂ν) =
          K * A ^ (4 / 3 : ℝ) * (∫⁻ s, D s ∂ν) +
            K * Q * A ^ (10 / 3 : ℝ) * volume J := by
        calc
          _ = ∫⁻ s, (K * A ^ (4 / 3 : ℝ)) * D s +
                K * Q * A ^ (10 / 3 : ℝ) ∂ν := by
            congr 1
            funext s
            ring
          _ = _ := by
            rw [lintegral_add_left' hfirstMeas]
            rw [lintegral_const_mul'' _ hDmeas]
            simp only [lintegral_const]
            simp [ν, volume.restrict_apply_univ]
      have hpointTime' : ∀ᵐ s ∂ν,
          lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) E (u s).toFun ^ (10 / 3 : ℝ) ≤
            K * A ^ (4 / 3 : ℝ) * D s + K * Q * A ^ (10 / 3 : ℝ) := by
        simpa [q] using hpointTime
      calc
        _ ≤ ∫⁻ s, K * D s * A ^ (4 / 3 : ℝ) +
              K * Q * A ^ (10 / 3 : ℝ) ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [hpointTime'] with s hs
          calc
            _ ≤ K * A ^ (4 / 3 : ℝ) * D s + K * Q * A ^ (10 / 3 : ℝ) := hs
            _ = _ := by congr 1; ac_rfl
        _ = _ := hsum
    have hProductSet : E ×ˢ J = U ×ˢ J := by rw [hBall]
    calc
      _ = ∫⁻ z in E ×ˢ J, ‖g z‖ₑ ^ (10 / 3 : ℝ) := by
        rw [← hProductSet]
      _ ≤ K * A ^ (4 / 3 : ℝ) * (∫⁻ s, D s ∂ν) +
            K * Q * A ^ (10 / 3 : ℝ) * volume J := hBoundOnProduct
      _ ≤ K * A ^ (4 / 3 : ℝ) *
            eLpNorm (fun z => vec3EuclideanNorm (Dg z)) 2
              (volume.restrict (U ×ˢ J)) ^ (2 : ℝ) +
          K * Q * A ^ (10 / 3 : ℝ) * volume J := by
        have hDtime : (∫⁻ s, D s ∂ν) ≤
            eLpNorm (fun z => vec3EuclideanNorm (Dg z)) 2
              (volume.restrict (U ×ˢ J)) ^ (2 : ℝ) := by
          rw [hDtotal]
          exact hDcompare
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hDtime (by positivity)
        · exact le_rfl
      _ ≤ _ := by
        rw [hQ]
        let S : ℝ≥0∞ :=
          A ^ (4 / 3 : ℝ) *
              eLpNorm (fun z => vec3EuclideanNorm (Dg z)) 2
                (volume.restrict (U ×ˢ J)) ^ (2 : ℝ) +
            ENNReal.ofReal (r ^ (-2 : ℝ)) * A ^ (10 / 3 : ℝ) * volume J
        calc
          _ = K * S := by dsimp [S]; ring
          _ ≤ ENNReal.ofReal C * S :=
            mul_le_mul_of_nonneg_right hKle (by dsimp [S]; positivity)
  exact ⟨hmemq, hIntegralBound⟩

end CKN

end
