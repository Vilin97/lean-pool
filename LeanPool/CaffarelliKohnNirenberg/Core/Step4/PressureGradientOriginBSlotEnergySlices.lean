/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq

/-! # Collar slice masses from the unit data of `thm:A`

The three slice quantities that control the localized pressure source of
`eq:pressure-gradient-decomposition` on a collar `Q(z, ρ)` are the cube of the velocity
slice norm, the square of the gradient slice norm and the `q`-th power of the
force slice norm.  This file identifies each of their time masses with a
space-time integral over the collar and bounds it by the unit data of `thm:A`
or by the collar Dirichlet integral.

No estimate here uses velocity or gradient Morrey data.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- The time mass of the powers of a vector slice norm is the space-time power
integral of its norm on the product box. -/
theorem vector_time_slice_norm_power_eq {V : Type*} [NormedAddCommGroup V]
    {P : ℝ} (hP : 0 < P) {G : Vec3 × ℝ → V} {E : Set Vec3} {J : Set ℝ}
    (hG : AEStronglyMeasurable G (volume.restrict (E ×ˢ J))) :
    (∫⁻ s in J, eLpNorm (fun y => G (y, s)) (ENNReal.ofReal P)
      (volume.restrict E) ^ P) =
      ∫⁻ w in E ×ˢ J, ENNReal.ofReal ‖G w‖ ^ P := by
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (E ×ˢ J) =
      (volume.restrict E).prod (volume.restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  have hGp : AEStronglyMeasurable G ((volume.restrict E).prod (volume.restrict J)) := by
    rw [hprod] at hG
    exact hG
  have hslice : ∀ᵐ s ∂volume.restrict J,
      AEStronglyMeasurable (fun y => G (y, s)) (volume.restrict E) := hGp.prodMk_right
  have hcongr : (∫⁻ s in J, eLpNorm (fun y => G (y, s)) (ENNReal.ofReal P)
      (volume.restrict E) ^ P) =
      ∫⁻ s in J, eLpNorm (fun y => ‖G (y, s)‖) (ENNReal.ofReal P)
        (volume.restrict E) ^ P := by
    refine (lintegral_congr_ae ?_).symm
    filter_upwards [hslice] with s hs
    rw [eLpNorm_norm _ hs]
  rw [hcongr, origin_time_slice_norm_power_eq hP hG.norm.aemeasurable]
  exact lintegral_congr fun w => by rw [abs_of_nonneg (norm_nonneg _)]

/-- Vector slice norms are measurable in time on a product box. -/
theorem vector_time_slice_norm_aemeasurable {V : Type*} [NormedAddCommGroup V]
    {P : ℝ} (hP : 0 < P) {G : Vec3 × ℝ → V} {E : Set Vec3} {J : Set ℝ}
    (hG : AEStronglyMeasurable G (volume.restrict (E ×ˢ J))) :
    AEMeasurable (fun s => eLpNorm (fun y => G (y, s)) (ENNReal.ofReal P)
      (volume.restrict E)) (volume.restrict J) := by
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (E ×ˢ J) =
      (volume.restrict E).prod (volume.restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  have hGp : AEStronglyMeasurable G ((volume.restrict E).prod (volume.restrict J)) := by
    rw [hprod] at hG
    exact hG
  have hslice : ∀ᵐ s ∂volume.restrict J,
      AEStronglyMeasurable (fun y => G (y, s)) (volume.restrict E) := hGp.prodMk_right
  have hbase := origin_time_slice_norm_aemeasurable hP hG.norm.aemeasurable
    (E := E) (J := J)
  refine hbase.congr ?_
  filter_upwards [hslice] with s hs
  rw [eLpNorm_norm _ hs]

/-- The cube mass of the velocity slice norms on a collar is at most the unit
data of `thm:A`. -/
theorem collar_velocity_slice_cube_mass_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {q ε : ℝ} {E : Set Vec3} {J : Set ℝ}
    (hsub : E ×ˢ J ⊆ parabolicCylinder (0 : Vec3) 0 1)
    (hu : AEStronglyMeasurable u (volume.restrict (E ×ˢ J)))
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    (∫⁻ s in J, eLpNorm (fun y => u (y, s)) (ENNReal.ofReal (3 : ℝ))
      (volume.restrict E) ^ (3 : ℝ)) ≤ ENNReal.ofReal ε := by
  rw [vector_time_slice_norm_power_eq (by norm_num) hu]
  calc (∫⁻ w in E ×ˢ J, ENNReal.ofReal ‖u w‖ ^ (3 : ℝ))
      ≤ ∫⁻ w in E ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) :=
        lintegral_mono fun w => ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm (u w))) (by norm_num)
    _ ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := lintegral_mono_set hsub
    _ ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q :=
        lintegral_mono fun w => le_add_right le_self_add
    _ ≤ _ := hsize

/-- The square mass of the gradient slice norms on a collar is at most the
collar Dirichlet integral. -/
theorem collar_gradient_slice_square_mass_le
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {E : Set Vec3} {J : Set ℝ}
    (hDu : AEStronglyMeasurable Du (volume.restrict (E ×ˢ J))) :
    (∫⁻ s in J, eLpNorm (fun y => Du (y, s)) (ENNReal.ofReal (2 : ℝ))
      (volume.restrict E) ^ (2 : ℝ)) ≤
      ∫⁻ w in E ×ˢ J, ENNReal.ofReal (spatialGradientSq u Du w) := by
  rw [vector_time_slice_norm_power_eq (by norm_num) hDu]
  refine lintegral_mono fun w => ?_
  have hsq : ‖Du w‖ ^ (2 : ℕ) ≤ spatialGradientSq u Du w := by
    have hmax : ∃ i : Fin 3, ‖Du w‖ = ‖Du w i‖ := by
      obtain ⟨i, hi⟩ := Finite.exists_max (fun i : Fin 3 => ‖Du w i‖)
      refine ⟨i, le_antisymm ?_ (norm_le_pi_norm (Du w) i)⟩
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg (Du w i))).mpr hi
    obtain ⟨i, hi⟩ := hmax
    have hmaxj : ∃ j : Fin 3, ‖Du w i‖ = |Du w i j| := by
      obtain ⟨j, hj⟩ := Finite.exists_max (fun j : Fin 3 => ‖Du w i j‖)
      refine ⟨j, le_antisymm ?_ ?_⟩
      · exact (pi_norm_le_iff_of_nonneg (norm_nonneg (Du w i j))).mpr hj
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm (Du w i) j
    obtain ⟨j, hj⟩ := hmaxj
    have hterm : (Du w i j) ^ (2 : ℕ) ≤ spatialGradientSq u Du w := by
      unfold spatialGradientSq
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun a : Fin 3 => ∑ b : Fin 3, (Du w a b) ^ (2 : ℕ))
        (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun b : Fin 3 => (Du w i b) ^ (2 : ℕ))
        (fun b _ => sq_nonneg _) (Finset.mem_univ j)
    calc ‖Du w‖ ^ (2 : ℕ) = |Du w i j| ^ (2 : ℕ) := by rw [hi, hj]
      _ = (Du w i j) ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ _ := hterm
  calc ENNReal.ofReal ‖Du w‖ ^ (2 : ℝ)
      = ENNReal.ofReal (‖Du w‖ ^ (2 : ℕ)) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _),
          show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsq

/-- The `q`-th power mass of the force slice norms on a collar is at most the
unit data of `thm:A`. -/
theorem collar_force_slice_power_mass_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {q ε : ℝ} (hq : 0 < q)
    {E : Set Vec3} {J : Set ℝ}
    (hsub : E ×ˢ J ⊆ parabolicCylinder (0 : Vec3) 0 1)
    (hf : AEStronglyMeasurable f (volume.restrict (E ×ˢ J)))
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    (∫⁻ s in J, eLpNorm (fun y => f (y, s)) (ENNReal.ofReal q)
      (volume.restrict E) ^ q) ≤ ENNReal.ofReal ε := by
  rw [vector_time_slice_norm_power_eq hq hf]
  calc (∫⁻ w in E ×ˢ J, ENNReal.ofReal ‖f w‖ ^ q)
      ≤ ∫⁻ w in E ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q :=
        lintegral_mono fun w => ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm (f w))) hq.le
    _ ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := lintegral_mono_set hsub
    _ ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q :=
        lintegral_mono fun w => le_add_left le_rfl
    _ ≤ _ := hsize

end CKN.Core.Step4
