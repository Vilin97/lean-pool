/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The two-reflection extension on the unit ball

The radial maps in this file are the two reflections used to continue a smooth
function across the unit sphere.  The geometric estimates are recorded on the
closed annulus and the gluing interface is kept independent of the radial maps.
-/

public section

open Set MeasureTheory
open scoped BigOperators
open scoped ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The open annulus on which both radial reflections are smooth. -/
@[expose]
def seeleyAnnulus : Set (Vec 3) :=
  {x | (1 / 2 : ℝ) < vecEuclideanNorm x ∧ vecEuclideanNorm x < 3}

/-- The closed annulus used for the extension estimates. -/
@[expose]
def seeleyClosedAnnulus : Set (Vec 3) :=
  {x | 1 ≤ vecEuclideanNorm x ∧ vecEuclideanNorm x ≤ 2}

/-- The first radial reflection, `x ↦ x / |x|²`. -/
@[expose]
def seeleyReflectionOne (x : Vec 3) : Vec 3 :=
  (vecNormSq x)⁻¹ • x

/-- The second radial reflection, `x ↦ x / ((2|x| - 1)|x|)`. -/
@[expose]
def seeleyReflectionTwo (x : Vec 3) : Vec 3 :=
  ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • x

/-- The exterior formula in the two-reflection extension. -/
@[expose]
def seeleyExterior (v : Vec 3 → ℝ) (x : Vec 3) : ℝ :=
  3 * v (seeleyReflectionOne x) - 2 * v (seeleyReflectionTwo x)

private theorem seeleyAnnulus_mem_of_closed {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) : x ∈ seeleyAnnulus := by
  exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩

private theorem seeley_norm_pos_of_mem_annulus {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) : 0 < vecEuclideanNorm x := by
  linarith only [hx.1]

private theorem seeley_norm_pos_of_mem_closed {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) : 0 < vecEuclideanNorm x := by
  linarith only [hx.1]

private theorem seeley_sq_pos_of_mem_annulus {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) : 0 < vecNormSq x := by
  rw [← vecEuclideanNorm_sq]
  exact sq_pos_of_pos (seeley_norm_pos_of_mem_annulus hx)

private theorem seeley_sq_ne_zero_of_mem_annulus {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) : vecNormSq x ≠ 0 :=
  (seeley_sq_pos_of_mem_annulus hx).ne'

private theorem seeley_second_den_pos_of_mem_annulus {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) :
    0 < (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x := by
  have hnorm : 0 < vecEuclideanNorm x := seeley_norm_pos_of_mem_annulus hx
  have hfactor : 0 < 2 * vecEuclideanNorm x - 1 := by
    linarith only [hx.1]
  exact mul_pos hfactor hnorm

private theorem seeley_second_den_ne_zero_of_mem_annulus {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) :
    (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x ≠ 0 :=
  (seeley_second_den_pos_of_mem_annulus hx).ne'

private theorem seeley_fderiv_vecNormSq_apply (x z : Vec 3) :
    (fderiv ℝ (fun y : Vec 3 => vecNormSq y) x) z =
      2 * ∑ i : Fin 3, x i * z i := by
  have hfun : (fun y : Vec 3 => vecNormSq y) =
      ∑ i : Fin 3, (fun y : Vec 3 => y i * y i) := by
    funext y
    simp [vecNormSq, vecDot]
  rw [hfun, fderiv_sum]
  · change ∑ i : Fin 3, (fderiv ℝ (fun y : Vec 3 => y i * y i) x) z = _
    conv_rhs => rw [Finset.mul_sum Finset.univ (fun i : Fin 3 => x i * z i) 2]
    apply Finset.sum_congr rfl
    intro i hi
    have hcoord : HasFDerivAt (fun y : Vec 3 => y i)
        (ContinuousLinearMap.proj i) x := hasFDerivAt_apply (𝕜 := ℝ) i x
    have hi' := hcoord.mul hcoord
    change (fderiv ℝ ((fun y : Vec 3 => y i) * fun y => y i) x) z = _
    rw [hi'.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply]
    ring
  · intro i hi
    exact (differentiableAt_apply i x).mul (differentiableAt_apply i x)

private theorem seeley_fderiv_norm_apply {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) (z : Vec 3) :
    (fderiv ℝ vecEuclideanNorm x) z =
      (2 * vecEuclideanNorm x)⁻¹ *
        (2 * ∑ i : Fin 3, x i * z i) := by
  have hq : DifferentiableAt ℝ (fun y : Vec 3 => vecNormSq y) x :=
    (contDiff_vecNormSq (d := 3)).differentiable (by simp) x
  have hq0 : vecNormSq x ≠ 0 :=
    (seeley_sq_pos_of_mem_annulus hx).ne'
  have hsqrt := hq.hasFDerivAt.sqrt hq0
  change (fderiv ℝ (fun y : Vec 3 => Real.sqrt (vecNormSq y)) x) z = _
  rw [hsqrt.fderiv]
  simp only [smul_apply]
  rw [seeley_fderiv_vecNormSq_apply]
  change (1 / (2 * Real.sqrt (vecNormSq x))) *
      (2 * ∑ i : Fin 3, x i * z i) =
        (2 * Real.sqrt (vecNormSq x))⁻¹ *
          (2 * ∑ i : Fin 3, x i * z i)
  ring

private theorem seeley_norm_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) vecEuclideanNorm seeleyAnnulus := by
  apply ContDiffOn.sqrt (contDiff_vecNormSq (d := 3)).contDiffOn
  intro x hx hzero
  have hnormzero : vecEuclideanNorm x = 0 := by
    change Real.sqrt (vecNormSq x) = 0
    rw [hzero]
    simp only [Real.sqrt_zero]
  linarith only [hx.1, hnormzero]

theorem seeleyReflectionOne_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) seeleyReflectionOne seeleyAnnulus := by
  have hscalar := (contDiff_vecNormSq (d := 3)).contDiffOn.inv
    (fun x hx => seeley_sq_ne_zero_of_mem_annulus hx)
  change ContDiffOn ℝ (⊤ : ℕ∞)
    ((fun x : Vec 3 => (vecNormSq x)⁻¹) • fun x => x) seeleyAnnulus
  exact hscalar.smul contDiffOn_id

theorem seeleyReflectionTwo_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) seeleyReflectionTwo seeleyAnnulus := by
  have hnorm := seeley_norm_contDiffOn
  have hden : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec 3 => (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)
      seeleyAnnulus := by
    exact (contDiffOn_const.mul hnorm).sub contDiffOn_const |>.mul hnorm
  have hscalar := hden.inv
    (fun x hx => seeley_second_den_ne_zero_of_mem_annulus hx)
  change ContDiffOn ℝ (⊤ : ℕ∞)
    ((fun x : Vec 3 => ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹) •
      fun x => x) seeleyAnnulus
  exact hscalar.smul contDiffOn_id

theorem seeleyReflectionOne_fderiv_apply {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) (z : Vec 3) :
    (fderiv ℝ seeleyReflectionOne x) z =
      (vecNormSq x)⁻¹ • z -
        ((vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)) • x := by
  have hq : DifferentiableAt ℝ (fun y : Vec 3 => vecNormSq y) x :=
    (contDiff_vecNormSq (d := 3)).differentiable (by simp) x
  have hqinv := (hasFDerivAt_inv (seeley_sq_ne_zero_of_mem_annulus hx)).comp x
    hq.hasFDerivAt
  have hrad := hqinv.smul (hasFDerivAt_id x)
  change (fderiv ℝ (((fun t : ℝ => t⁻¹) ∘
    (fun y : Vec 3 => vecNormSq y)) • (id : Vec 3 → Vec 3)) x) z = _
  rw [hrad.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply, id_eq]
  rw [seeley_fderiv_vecNormSq_apply]
  congr 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [seeley_sq_ne_zero_of_mem_annulus hx]

theorem seeleyReflectionOne_fderiv_sphere {x : Vec 3}
    (hx : vecEuclideanNorm x = 1) (z : Vec 3) :
    (fderiv ℝ seeleyReflectionOne x) z =
      z - (2 * ∑ i : Fin 3, x i * z i) • x := by
  have hAnn : x ∈ seeleyAnnulus := by
    exact ⟨by linarith only [hx], by linarith only [hx]⟩
  have hq : vecNormSq x = 1 := by
    rw [← vecEuclideanNorm_sq, hx]
    norm_num
  rw [seeleyReflectionOne_fderiv_apply hAnn z, hq]
  simp only [inv_one, one_pow, one_smul, one_mul]

theorem seeleyReflectionTwo_fderiv_sphere {x : Vec 3}
    (hx : vecEuclideanNorm x = 1) (z : Vec 3) :
    (fderiv ℝ seeleyReflectionTwo x) z =
      z - (3 * ∑ i : Fin 3, x i * z i) • x := by
  have hAnn : x ∈ seeleyAnnulus := by
    exact ⟨by linarith only [hx], by linarith only [hx]⟩
  have hq : DifferentiableAt ℝ (fun y : Vec 3 => vecNormSq y) x :=
    (contDiff_vecNormSq (d := 3)).differentiable (by simp) x
  have hq0 : vecNormSq x ≠ 0 := by
    rw [← vecEuclideanNorm_sq, hx]
    norm_num
  have hn : DifferentiableAt ℝ vecEuclideanNorm x := by
    change DifferentiableAt ℝ (fun y : Vec 3 => Real.sqrt (vecNormSq y)) x
    exact hq.hasFDerivAt.sqrt hq0 |>.differentiableAt
  have hdlin := hn.hasFDerivAt.const_mul 2
  have hdlin' := hdlin.sub (hasFDerivAt_const (x := x) 1)
  have hd := hdlin'.mul hn.hasFDerivAt
  have hden0 : ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ≠ 0 := by
    rw [hx]
    norm_num
  have hinv := (hasFDerivAt_inv hden0).comp x hd
  have hrad := hinv.smul (hasFDerivAt_id x)
  change (fderiv ℝ (((fun t : ℝ => t⁻¹) ∘
    (((fun y : Vec 3 => 2 * vecEuclideanNorm y) - fun _ => 1) *
      vecEuclideanNorm)) • id) x) z = _
  rw [hrad.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply, id_eq, sub_zero]
  rw [seeley_fderiv_norm_apply hAnn]
  simp only [Pi.mul_apply, Pi.sub_apply, hx]
  norm_num
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hq0]
  ring

theorem seeleyReflectionTwo_fderiv_apply {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) (z : Vec 3) :
    (fderiv ℝ seeleyReflectionTwo x) z =
      ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • z -
        (((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
          ((4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i)))) • x := by
  have hq : DifferentiableAt ℝ (fun y : Vec 3 => vecNormSq y) x :=
    (contDiff_vecNormSq (d := 3)).differentiable (by simp) x
  have hq0 : vecNormSq x ≠ 0 :=
    (seeley_sq_pos_of_mem_annulus hx).ne'
  have hn : DifferentiableAt ℝ vecEuclideanNorm x := by
    change DifferentiableAt ℝ (fun y : Vec 3 => Real.sqrt (vecNormSq y)) x
    exact hq.hasFDerivAt.sqrt hq0 |>.differentiableAt
  have hdlin := hn.hasFDerivAt.const_mul 2
  have hdlin' := hdlin.sub (hasFDerivAt_const (x := x) 1)
  have hd := hdlin'.mul hn.hasFDerivAt
  have hden0 :
      ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ≠ 0 :=
    seeley_second_den_ne_zero_of_mem_annulus hx
  have hinv := (hasFDerivAt_inv hden0).comp x hd
  have hrad := hinv.smul (hasFDerivAt_id x)
  change (fderiv ℝ (((fun t : ℝ => t⁻¹) ∘
    (((fun y : Vec 3 => 2 * vecEuclideanNorm y) - fun _ => 1) *
      vecEuclideanNorm)) • id) x) z = _
  rw [hrad.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply, id_eq, sub_zero]
  rw [seeley_fderiv_norm_apply hx]
  simp only [Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
  congr 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hden0, hq0]
  ring_nf

private theorem seeley_norm_continuous :
    Continuous (vecEuclideanNorm (d := 3)) := by
  change Continuous (fun x : Vec 3 => Real.sqrt (vecNormSq x))
  exact (contDiff_vecNormSq (d := 3)).continuous.sqrt

private theorem seeleyAnnulus_open : IsOpen seeleyAnnulus := by
  rw [seeleyAnnulus]
  exact (isOpen_lt continuous_const seeley_norm_continuous).inter
    (isOpen_lt seeley_norm_continuous continuous_const)

theorem seeleyExterior_eq_on_sphere (v : Vec 3 → ℝ) {x : Vec 3}
    (hx : vecEuclideanNorm x = 1) : seeleyExterior v x = v x := by
  have hq : vecNormSq x = 1 := by
    rw [← vecEuclideanNorm_sq, hx]
    norm_num
  have h1 : seeleyReflectionOne x = x := by
    simp only [seeleyReflectionOne, hq, inv_one, one_smul]
  have h2 : seeleyReflectionTwo x = x := by
    simp only [seeleyReflectionTwo, hx]
    norm_num
  simp only [seeleyExterior, h1, h2]
  ring

theorem seeleyExterior_fderiv_on_sphere (v : Vec 3 → ℝ)
    (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : vecEuclideanNorm x = 1) (z : Vec 3) :
    (fderiv ℝ (seeleyExterior v) x) z = (fderiv ℝ v x) z := by
  have hAnn : x ∈ seeleyAnnulus := by
    exact ⟨by linarith only [hx], by linarith only [hx]⟩
  have hρ1 : ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionOne x :=
    seeleyReflectionOne_contDiffOn.contDiffAt (seeleyAnnulus_open.mem_nhds hAnn)
  have hρ2 : ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionTwo x :=
    seeleyReflectionTwo_contDiffOn.contDiffAt (seeleyAnnulus_open.mem_nhds hAnn)
  have hρ1d := hρ1.differentiableAt (by simp)
  have hρ2d := hρ2.differentiableAt (by simp)
  have hcomp1 :=
    (hv.differentiable_one (seeleyReflectionOne x)).hasFDerivAt.comp x
      hρ1d.hasFDerivAt
  have hcomp2 :=
    (hv.differentiable_one (seeleyReflectionTwo x)).hasFDerivAt.comp x
      hρ2d.hasFDerivAt
  have he := (hcomp1.const_mul 3).sub (hcomp2.const_mul 2)
  change (fderiv ℝ (seeleyExterior v) x) z = _
  rw [show seeleyExterior v =
      (fun y => 3 * (v ∘ seeleyReflectionOne) y) -
        (fun y => 2 * (v ∘ seeleyReflectionTwo) y) by
    funext y
    rfl]
  rw [he.fderiv]
  have h1 : seeleyReflectionOne x = x := by
    have hq : vecNormSq x = 1 := by
      rw [← vecEuclideanNorm_sq, hx]
      norm_num
    simp only [seeleyReflectionOne, hq, inv_one, one_smul]
  have h2 : seeleyReflectionTwo x = x := by
    simp only [seeleyReflectionTwo, hx]
    norm_num
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply]
  rw [h1, h2, seeleyReflectionOne_fderiv_sphere hx,
    seeleyReflectionTwo_fderiv_sphere hx]
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

theorem seeley_glue_hasFDerivAt {C : Set (Vec 3)} {g h : Vec 3 → ℝ}
    (hC : IsClosed C) {x : Vec 3} (hx : x ∈ frontier C)
    (hvalue : g x = h x) {L : Vec 3 →L[ℝ] ℝ}
    (hg : HasFDerivAt g L x) (hh : HasFDerivAt h L x) :
    HasFDerivAt (fun y => if y ∈ C then g y else h y) L x := by
  have hxc : x ∈ C := hC.frontier_subset hx
  apply (hasFDerivAt_iff_isLittleO_nhds_zero).2
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hgo :=
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp hg).bound hc
  have hho :=
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp hh).bound hc
  filter_upwards [hgo, hho] with k hkg hkh
  by_cases hmem : x + k ∈ C
  · simp only [hmem, hxc]
    exact hkg
  · simp only [hmem, hxc]
    rw [hvalue]
    exact hkh

theorem seeley_glue_hasFDerivAt_of_mem_interior
    {C : Set (Vec 3)} {g h : Vec 3 → ℝ} {x : Vec 3}
    (hx : x ∈ interior C) {L : Vec 3 →L[ℝ] ℝ}
    (hg : HasFDerivAt g L x) :
    HasFDerivAt (fun y => if y ∈ C then g y else h y) L x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  have hyC : y ∈ C := interior_subset hy
  simp only [hyC, ite_true]

theorem seeley_glue_hasFDerivAt_of_not_mem
    {C : Set (Vec 3)} {g h : Vec 3 → ℝ} {x : Vec 3}
    (hC : IsClosed C) (hx : x ∉ C) {L : Vec 3 →L[ℝ] ℝ}
    (hh : HasFDerivAt h L x) :
    HasFDerivAt (fun y => if y ∈ C then g y else h y) L x := by
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_iff.mpr hC |>.mem_nhds hx] with y hy
  have hyC : y ∉ C := hy
  simp only [hyC, ite_false]

/-- The piecewise two-reflection extension, before a cutoff is applied. -/
@[expose]
def seeleyExtension (v : Vec 3 → ℝ) (x : Vec 3) : ℝ :=
  if x ∈ euclideanClosedBall (0 : Vec 3) 1 then v x else seeleyExterior v x

private theorem seeley_reflection_one_norm {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    vecEuclideanNorm (seeleyReflectionOne x) = (vecEuclideanNorm x)⁻¹ := by
  have ht : 0 < vecEuclideanNorm x := seeley_norm_pos_of_mem_closed hx
  have hq : 0 < vecNormSq x := by
    rw [← vecEuclideanNorm_sq]
    positivity
  rw [seeleyReflectionOne, vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hq)]
  have heq : (vecNormSq x)⁻¹ * vecEuclideanNorm x =
      (vecEuclideanNorm x)⁻¹ := by
    rw [← vecEuclideanNorm_sq]
    field_simp [ne_of_gt ht]
  exact heq

private theorem seeley_reflection_two_norm {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    vecEuclideanNorm (seeleyReflectionTwo x) =
      (2 * vecEuclideanNorm x - 1)⁻¹ := by
  have ht : 0 < vecEuclideanNorm x := seeley_norm_pos_of_mem_closed hx
  have hden := seeley_second_den_pos_of_mem_annulus
    (seeleyAnnulus_mem_of_closed hx)
  rw [seeleyReflectionTwo, vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hden)]
  have heq : ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ *
      vecEuclideanNorm x = (2 * vecEuclideanNorm x - 1)⁻¹ := by
    field_simp [ne_of_gt ht, ne_of_gt (by linarith only [hx.1] :
      0 < 2 * vecEuclideanNorm x - 1)]
  exact heq

theorem seeleyReflectionOne_maps_closedAnnulus {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    seeleyReflectionOne x ∈ euclideanClosedBall (0 : Vec 3) 1 := by
  rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)]
  simp only [sub_zero]
  rw [seeley_reflection_one_norm hx]
  exact (inv_le_one₀ (seeley_norm_pos_of_mem_closed hx)).2 hx.1

theorem seeleyReflectionTwo_maps_closedAnnulus {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    seeleyReflectionTwo x ∈ euclideanClosedBall (0 : Vec 3) 1 := by
  rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)]
  simp only [sub_zero]
  rw [seeley_reflection_two_norm hx]
  apply (inv_le_one₀ (by linarith only [hx.1] : 0 < 2 * vecEuclideanNorm x - 1)).2
  linarith only [hx.1]

theorem seeleyReflectionOne_injectiveOn_closedAnnulus :
    Set.InjOn seeleyReflectionOne seeleyClosedAnnulus := by
  intro x hx y hy hxy
  have hnorm : vecEuclideanNorm x = vecEuclideanNorm y := by
    apply inv_injective
    rw [← seeley_reflection_one_norm hx, ← seeley_reflection_one_norm hy]
    exact congrArg vecEuclideanNorm hxy
  have hq : vecNormSq x = vecNormSq y := by
    rw [← vecEuclideanNorm_sq, ← vecEuclideanNorm_sq, hnorm]
  have hqx : vecNormSq x ≠ 0 :=
    (seeley_sq_pos_of_mem_annulus (seeleyAnnulus_mem_of_closed hx)).ne'
  have hqy : vecNormSq y ≠ 0 := by
    rw [← hq]
    exact hqx
  have hxy' : (vecNormSq x)⁻¹ • x = (vecNormSq y)⁻¹ • y := by
    simpa only [seeleyReflectionOne] using hxy
  calc
    x = vecNormSq x • ((vecNormSq x)⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ hqx, one_smul]
    _ = vecNormSq x • ((vecNormSq y)⁻¹ • y) := by rw [hxy']
    _ = y := by
      rw [hq, smul_smul, mul_inv_cancel₀ hqy, one_smul]

theorem seeleyReflectionTwo_injectiveOn_closedAnnulus :
    Set.InjOn seeleyReflectionTwo seeleyClosedAnnulus := by
  intro x hx y hy hxy
  have hfactor :
      2 * vecEuclideanNorm x - 1 = 2 * vecEuclideanNorm y - 1 := by
    apply inv_injective
    rw [← seeley_reflection_two_norm hx, ← seeley_reflection_two_norm hy]
    exact congrArg vecEuclideanNorm hxy
  have hnorm : vecEuclideanNorm x = vecEuclideanNorm y := by
    linarith only [hfactor]
  have hq : vecNormSq x = vecNormSq y := by
    rw [← vecEuclideanNorm_sq, ← vecEuclideanNorm_sq, hnorm]
  have hdenx :
      (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x ≠ 0 :=
    seeley_second_den_ne_zero_of_mem_annulus (seeleyAnnulus_mem_of_closed hx)
  have hdeny :
      (2 * vecEuclideanNorm y - 1) * vecEuclideanNorm y ≠ 0 :=
    seeley_second_den_ne_zero_of_mem_annulus (seeleyAnnulus_mem_of_closed hy)
  have hxy' :
      ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • x =
        ((2 * vecEuclideanNorm y - 1) * vecEuclideanNorm y)⁻¹ • y := by
    simpa only [seeleyReflectionTwo] using hxy
  calc
    x = ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) •
        (((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ hdenx, one_smul]
    _ = ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) •
        (((2 * vecEuclideanNorm y - 1) * vecEuclideanNorm y)⁻¹ • y) := by
      rw [hxy']
    _ = y := by
      rw [hfactor, hnorm, smul_smul, mul_inv_cancel₀ hdeny, one_smul]

theorem seeleyClosedAnnulus_measurableSet :
    MeasurableSet seeleyClosedAnnulus := by
  rw [seeleyClosedAnnulus]
  exact (isClosed_le continuous_const seeley_norm_continuous).inter
    (isClosed_le seeley_norm_continuous continuous_const) |>.measurableSet

theorem seeleyReflectionOne_hasFDerivWithinAt {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    HasFDerivWithinAt seeleyReflectionOne (fderiv ℝ seeleyReflectionOne x)
      seeleyClosedAnnulus x := by
  have hA := seeleyAnnulus_mem_of_closed hx
  have hAt : ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionOne x :=
    seeleyReflectionOne_contDiffOn.contDiffAt (seeleyAnnulus_open.mem_nhds hA)
  exact (hAt.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt

theorem seeleyReflectionTwo_hasFDerivWithinAt {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    HasFDerivWithinAt seeleyReflectionTwo (fderiv ℝ seeleyReflectionTwo x)
      seeleyClosedAnnulus x := by
  have hA := seeleyAnnulus_mem_of_closed hx
  have hAt : ContDiffAt ℝ (⊤ : ℕ∞) seeleyReflectionTwo x :=
    seeleyReflectionTwo_contDiffOn.contDiffAt (seeleyAnnulus_open.mem_nhds hA)
  exact (hAt.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt

theorem seeley_changeVariables_lintegral_one {g : Vec 3 → ℝ≥0∞}
    :
    ∫⁻ x in seeleyReflectionOne '' seeleyClosedAnnulus, g x ∂volume =
      ∫⁻ x in seeleyClosedAnnulus,
        ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
          g (seeleyReflectionOne x) ∂volume := by
  exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    seeleyClosedAnnulus_measurableSet
    (fun x hx => seeleyReflectionOne_hasFDerivWithinAt hx)
    seeleyReflectionOne_injectiveOn_closedAnnulus g

theorem seeley_changeVariables_lintegral_two {g : Vec 3 → ℝ≥0∞}
    :
    ∫⁻ x in seeleyReflectionTwo '' seeleyClosedAnnulus, g x ∂volume =
      ∫⁻ x in seeleyClosedAnnulus,
        ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
          g (seeleyReflectionTwo x) ∂volume := by
  exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    seeleyClosedAnnulus_measurableSet
    (fun x hx => seeleyReflectionTwo_hasFDerivWithinAt hx)
    seeleyReflectionTwo_injectiveOn_closedAnnulus g

end
end CKN
