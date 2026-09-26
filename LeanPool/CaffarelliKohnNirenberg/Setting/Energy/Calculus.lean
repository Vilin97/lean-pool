/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.PointwiseEnergy

/-!
# Calculus

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

lemma spaceTimeTestFunction_mul_smooth
    {Ω : Set Vec3} {I : Set ℝ}
    {ψ χ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    (fun z => ψ z * χ z) ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  rcases hψ with ⟨hψ_diff, hψ_compact, hψ_support⟩
  refine ⟨hψ_diff.mul hχ, hψ_compact.mul_right (f' := χ), ?_⟩
  exact (tsupport_mul_subset_left (f := ψ) (g := χ)).trans hψ_support

lemma spatialPartial_contDiff
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial ψ i z) := by
  let F : (Vec3 × ℝ) → Vec3 → ℝ := fun z x => ψ (x, z.2)
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Vec3 × ℝ) × Vec3 => (q.2, q.1.2)) := by
    exact contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) := by
    convert hψ.comp hmap using 1
    funext q
    rfl
  have hderiv := hF.fderiv_apply
    (contDiff_fst (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
    (contDiff_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (c := basisVec i))
    (by simp)
  simpa only [F, spatialPartial, Function.uncurry] using hderiv

lemma spatialPartial_mul_time
    {ψ : Vec3 × ℝ → ℝ} {χ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun w => ψ w * χ w.2) i z =
      spatialPartial ψ i z * χ z.2 := by
  unfold spatialPartial
  have hψd : DifferentiableAt ℝ (fun x : Vec3 => ψ (x, z.2)) z.1 := by
    exact (hψ.contDiffAt.differentiableAt (by simp)).comp z.1
      ((contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2).contDiffAt.differentiableAt
        (by simp))
  have hχd : DifferentiableAt ℝ (fun _ : Vec3 => χ z.2) z.1 :=
    differentiableAt_const (c := χ z.2)
  change (fderiv ℝ ((fun x : Vec3 => ψ (x, z.2)) *
      (fun _ : Vec3 => χ z.2)) z.1) (basisVec i) = _
  rw [fderiv_mul hψd hχd]
  have hconst : fderiv ℝ (fun _ : Vec3 => χ z.2) z.1 = 0 := by
    change fderiv ℝ (Function.const Vec3 (χ z.2)) z.1 = 0
    rw [fderiv_const]
    simp only [Pi.zero_apply]
  rw [hconst]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    _root_.zero_apply, zero_mul, mul_comm, zero_add]

lemma timePartial_mul_time
    {ψ : Vec3 × ℝ → ℝ} {χ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (z : Vec3 × ℝ) :
    timePartial (fun w => ψ w * χ w.2) z =
      timePartial ψ z * χ z.2 + ψ z * deriv χ z.2 := by
  unfold timePartial
  have hψd : DifferentiableAt ℝ (fun s : ℝ => ψ (z.1, s)) z.2 := by
    exact (hψ.contDiffAt.differentiableAt (by simp)).comp z.2
      ((contDiff_prodMk_right (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.1).contDiffAt.differentiableAt
        (by simp))
  have hχd : DifferentiableAt ℝ χ z.2 := hχ.contDiffAt.differentiableAt (by simp)
  change (fderiv ℝ ((fun s : ℝ => ψ (z.1, s)) * χ) z.2) 1 = _
  rw [fderiv_mul hψd hχd]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, deriv]
  ring

lemma spatialSecondPartial_mul_time
    {ψ : Vec3 × ℝ → ℝ} {χ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    spatialSecondPartial (fun w => ψ w * χ w.2) i j z =
      spatialSecondPartial ψ i j z * χ z.2 := by
  unfold spatialSecondPartial
  change spatialPartial
      (fun w : Vec3 × ℝ => spatialPartial
        (fun v : Vec3 × ℝ => ψ v * χ v.2) i w) j z = _
  have hinner :
      (fun w : Vec3 × ℝ => spatialPartial
        (fun v : Vec3 × ℝ => ψ v * χ v.2) i w) =
        (fun w : Vec3 × ℝ => spatialPartial ψ i w * χ w.2) := by
    funext w
    exact spatialPartial_mul_time hψ i w
  rw [hinner]
  exact spatialPartial_mul_time (spatialPartial_contDiff hψ i) j z

lemma localEnergyRhs_mul_time
    {u : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ}
    {f : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    {χ : ℝ → ℝ} {z : Vec3 × ℝ}
  (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
  (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    localEnergyRhs u p f (fun w => ψ w * χ w.2) z =
      localEnergyRhs u p f ψ z * χ z.2
        + (vec3EuclideanNorm (u z)) ^ 2 * ψ z * deriv χ z.2 := by
  have htime :
      timePartialProd (fun w => ψ w * χ w.2) z =
        timePartialProd ψ z * χ z.2 + ψ z * deriv χ z.2 := by
    unfold timePartialProd
    exact timePartial_mul_time hψ hχ z
  have hsecond : ∀ i : Fin 3,
      spatialSecondPartialProd (fun w => ψ w * χ w.2) i i z =
        spatialSecondPartialProd ψ i i z * χ z.2 := by
    intro i
    unfold spatialSecondPartialProd
    exact spatialSecondPartial_mul_time hψ i i z
  have hspatial : ∀ i : Fin 3,
      spatialPartialProd (fun w => ψ w * χ w.2) i z =
        spatialPartialProd ψ i z * χ z.2 := by
    intro i
    unfold spatialPartialProd
    exact spatialPartial_mul_time hψ i z
  simp only [localEnergyRhs, htime]
  simp_rw [hsecond, hspatial]
  have hsecond_sum :
      (∑ i, spatialSecondPartialProd ψ i i z * χ z.2) =
        (∑ i, spatialSecondPartialProd ψ i i z) * χ z.2 := by
    rw [Finset.sum_mul]
  have hspatial_sum :
      (∑ i, u z i * (spatialPartialProd ψ i z * χ z.2)) =
        (∑ i, u z i * spatialPartialProd ψ i z) * χ z.2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsecond_sum]
  simp_rw [hspatial_sum]
  ring

end CKN
