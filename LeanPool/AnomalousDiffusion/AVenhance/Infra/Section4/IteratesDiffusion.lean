/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesOscillatory

/-! Spatial derivative transfer for the current material diffusion term. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem iterate_gradient_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad f) := by
  have hjoint : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Vec 2 × Vec 2 => fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by simp)
  apply contDiff_pi.2
  intro i
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (x, basisVec i)) := by
    fun_prop
  have hcomp := hjoint.comp hmap
  simpa only [Function.comp_def, Prod.fst, Prod.snd, AVenhance.spaceGrad] using hcomp

theorem iterate_coordinate_derivatives_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x j =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y j) x i := by
  have hAt := hf.contDiffAt (x := x)
  have hC2 : ContDiffAt ℝ 2 f x := hAt.of_le (by norm_num)
  have hsymm := hC2.isSymmSndFDerivAt (by simp)
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hCderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hAt.fderiv_right (m := 1) (by simp)
    exact hCderiv.differentiableAt (by norm_num)
  have hu0 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec i) x :=
    differentiableAt_const (basisVec i)
  have hu1 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec j) x :=
    differentiableAt_const (basisVec j)
  have hderiv0 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec i) := by
    have h := fderiv_clm_apply hc hu0
    simpa using h
  have hderiv1 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec j) := by
    have h := fderiv_clm_apply hc hu1
    simpa using h
  have hleft : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y i) x j =
      fderiv ℝ (fderiv ℝ f) x (basisVec j) (basisVec i) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j) = _
    rw [hderiv0]
    rfl
  have hright : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y j) x i =
      fderiv ℝ (fderiv ℝ f) x (basisVec i) (basisVec j) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec i) = _
    rw [hderiv1]
    rfl
  rw [hleft, hright]
  exact hsymm (basisVec j) (basisVec i)

/-- The gradient of the Laplacian is the componentwise Laplacian of the
gradient. This justifies moving current diffusion derivatives to the preceding
increment in the oscillatory material pairing. -/
theorem iterate_gradient_laplacian_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (i : Fin 2) :
    spaceGrad (spaceLap f) x i = spaceLap (fun y => spaceGrad f y i) x := by
  have hg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => spaceGrad f y j) :=
    contDiff_pi.mp (iterate_gradient_smooth hf) j
  have hgg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => spaceGrad (fun z => spaceGrad f z j) y j) :=
    contDiff_pi.mp (iterate_gradient_smooth (hg j)) j
  change fderiv ℝ (fun y => ∑ j : Fin 2,
    spaceGrad (fun z => spaceGrad f z j) y j) x (basisVec i) = _
  rw [fderiv_fun_sum (fun j _ => (hgg j).differentiable (by simp) |>.differentiableAt)]
  simp only [sum_apply]
  unfold spaceLap
  apply Finset.sum_congr rfl
  intro j _
  change spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z j) y j) x i = _
  rw [iterate_coordinate_derivatives_commute (hg j) j i x]
  have hswap : (fun y => spaceGrad (fun z => spaceGrad f z j) y i) =
      (fun y => spaceGrad (fun z => spaceGrad f z i) y j) := by
    funext y
    exact iterate_coordinate_derivatives_commute hf j i y
  rw [hswap]

theorem iterate_laplacian_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (spaceLap f) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_pi.mp (iterate_gradient_smooth
    (contDiff_pi.mp (iterate_gradient_smooth hf) j)) j

/-- Differentiate the actual material PDE in space, commuting diffusion with
one coordinate derivative. No material-gradient equation is assumed. -/
theorem iterate_classical_material_gradient_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u) {t : ℝ} (ht : 0 < t) (x : Vec 2)
    (hF : DifferentiableAt ℝ (F t) x) (i : Fin 2) :
    spaceGrad (amnrMaterial b u t) x i =
      κ * spaceLap (fun y => spaceGrad (u t) y i) x + spaceGrad (F t) x i := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (u t) := by
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
    exact hsol.1.comp_contDiff hm (fun _ => ⟨ht.le, Set.mem_univ _⟩)
  have heq : amnrMaterial b u t = fun y => κ * spaceLap (u t) y + F t y := by
    funext y
    exact iterate_material_equation hsol ht y
  rw [heq]
  unfold spaceGrad
  have hL := ((iterate_laplacian_smooth hu).differentiable (by simp)).differentiableAt (x := x)
  rw [fderiv_fun_add (hL.const_mul κ) hF, fderiv_const_mul hL κ]
  change κ * spaceGrad (spaceLap (u t)) x i + spaceGrad (F t) x i = _
  rw [iterate_gradient_laplacian_commute hu]
  rfl

theorem iterate_gradient_periodic {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (AVenhance.spaceGrad f) := by
  intro k x
  let v : Vec 2 := AVenhance.latticeShift k
  have hfun : (fun y : Vec 2 => f (y + v)) = f := by
    funext y
    exact hper k y
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have htranslate : HasFDerivAt (fun y : Vec 2 => y + v)
      (ContinuousLinearMap.id ℝ (Vec 2)) x := by
    simpa only [id_eq] using (hasFDerivAt_id x).add_const v
  have hcomp := (hdiff (x + v)).hasFDerivAt.comp x htranslate
  have hshift : HasFDerivAt f (fderiv ℝ f (x + v)) x := by
    have hcomp' := hcomp
    change HasFDerivAt (fun y : Vec 2 => f (y + v))
      (fderiv ℝ f (x + v) ∘L ContinuousLinearMap.id ℝ (Vec 2)) x at hcomp'
    rw [ContinuousLinearMap.comp_id, hfun] at hcomp'
    exact hcomp'
  have hbase : HasFDerivAt f (fderiv ℝ f x) x := (hdiff x).hasFDerivAt
  have hderiv : fderiv ℝ f (x + v) = fderiv ℝ f x := hshift.unique hbase
  funext i
  change fderiv ℝ f (x + AVenhance.latticeShift k) (basisVec i) =
    fderiv ℝ f x (basisVec i)
  exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) hderiv

end AVenhance.Infra.Section4
