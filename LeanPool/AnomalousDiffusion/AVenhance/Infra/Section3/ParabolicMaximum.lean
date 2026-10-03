/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.LocalMaximumSecondDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Spatial second derivatives at a local maximum and the barrier maximum
principle for bounded solutions on the whole plane. -/

@[expose] public section

noncomputable section

open Filter Homogenization
open scoped Topology ContDiff

namespace AVenhance.Infra.Section3

open AVenhance

/-- Line through a point in one coordinate direction for the parabolic maximum argument. -/
def ParabolicMaximum.coordinateLine (x : Vec 2) (i : Fin 2) : ℝ → Vec 2 :=
  fun s => x + s • basisVec i

theorem ParabolicMaximum.coordinateLine_hasDerivAt (x : Vec 2) (i : Fin 2) (s : ℝ) :
    HasDerivAt (ParabolicMaximum.coordinateLine x i) (basisVec i) s := by
  change HasDerivAt (fun s : ℝ => x + s • basisVec i) (basisVec i) s
  simpa using ((hasDerivAt_id s).smul_const (basisVec i)).const_add x

/-- At a spatial local maximum of a `C²` function, every diagonal second
partial derivative and hence its Laplacian is nonpositive. -/
theorem spaceLap_nonpos_of_isLocalMax {f : Vec 2 → ℝ} {x : Vec 2}
    (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) : spaceLap f x ≤ 0 := by
  have hdiag (i : Fin 2) :
      spaceGrad (fun y => spaceGrad f y i) x i ≤ 0 := by
    let line := ParabolicMaximum.coordinateLine x i
    let g : ℝ → ℝ := fun s => f (line s)
    have hlineC : ContDiff ℝ (⊤ : ℕ∞) line := by
      dsimp [line, ParabolicMaximum.coordinateLine]
      exact contDiff_const.add (contDiff_id.smul_const (basisVec i))
    have hgC : ContDiff ℝ 2 g := by
      exact hf.comp (hlineC.of_le (by simp))
    have hmaxLine : IsLocalMax g 0 := by
      have hmax' : IsLocalMax f (line 0) := by
        simpa [line, ParabolicMaximum.coordinateLine] using hmax
      have h := hmax'.comp_continuous hlineC.continuous.continuousAt
      change IsLocalMax (fun s => f (line s)) 0 at h ⊢
      exact h
    have hderiv (s : ℝ) : HasDerivAt g
        (spaceGrad f (line s) i) s := by
      have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
      have houter := (hdiff (line s)).hasFDerivAt
      have hinner := ParabolicMaximum.coordinateLine_hasDerivAt x i s
      have hcomp := houter.comp_hasDerivAt s hinner
      change HasDerivAt (fun r => f (line r))
        (spaceGrad f (line s) i) s
      exact hcomp
    have hgderiv : deriv g = fun s => spaceGrad f (line s) i := by
      funext s
      exact (hderiv s).deriv
    have hgradJoint : ContDiff ℝ 1
        (fun p : Vec 2 × Vec 2 => fderiv ℝ f p.1 p.2) := by
      exact hf.contDiff_fderiv_apply (by norm_num)
    have hgradLine : ContDiff ℝ 1 (fun y : Vec 2 => spaceGrad f y i) := by
      have hconst : ContDiff ℝ 1 (fun y : Vec 2 => (y, basisVec i)) := by
        fun_prop
      change ContDiff ℝ 1 (fun y => fderiv ℝ f y (basisVec i))
      have hcomp := hgradJoint.comp hconst
      have heq : (fun y : Vec 2 => fderiv ℝ f y (basisVec i)) =
          (fun p : Vec 2 × Vec 2 => fderiv ℝ f p.1 p.2) ∘
            (fun y => (y, basisVec i)) := by
        funext y
        rfl
      rw [heq]
      exact hcomp
    have hsecond : HasDerivAt (deriv g)
        (spaceGrad (fun y => spaceGrad f y i) x i) 0 := by
      rw [hgderiv]
      have hdiff : Differentiable ℝ (fun y : Vec 2 => spaceGrad f y i) :=
        hgradLine.differentiable (by norm_num)
      have houter := (hdiff x).hasFDerivAt
      have hline0 : x = line 0 := by simp [line, ParabolicMaximum.coordinateLine]
      have hinner := ParabolicMaximum.coordinateLine_hasDerivAt x i 0
      have hcomp := houter.comp_hasDerivAt_of_eq 0 hinner hline0
      change HasDerivAt
        ((fun y => spaceGrad f y i) ∘ ParabolicMaximum.coordinateLine x i)
        (spaceGrad (fun y => spaceGrad f y i) x i) 0
      simpa only [AVenhance.spaceGrad] using hcomp
    have hsecondValue := (hsecond.deriv)
    rw [← hsecondValue]
    exact deriv_deriv_nonpos_of_isLocalMax hgC hmaxLine
  unfold spaceLap
  simp only [Fin.sum_univ_two]
  exact add_nonpos (hdiag 0) (hdiag 1)

/-- At a joint local maximum of a `C²` space-time function, the time
derivative is zero, the spatial gradient vanishes, and the Laplacian is
nonpositive. -/
theorem spaceTime_local_max_derivative_facts {f : ℝ × Vec 2 → ℝ}
    {t : ℝ} {x : Vec 2} (hf : ContDiff ℝ 2 f)
    (hmax : IsLocalMax f (t, x)) :
    deriv (fun s => f (s, x)) t = 0 ∧
      (∀ i : Fin 2, spaceGrad (fun y => f (t, y)) x i = 0) ∧
      spaceLap (fun y => f (t, y)) x ≤ 0 := by
  have htimeC : ContDiff ℝ 2 (fun s : ℝ => f (s, x)) := by
    exact hf.comp (by fun_prop)
  have hspaceC : ContDiff ℝ 2 (fun y : Vec 2 => f (t, y)) := by
    exact hf.comp (by fun_prop)
  have htimeMax : IsLocalMax (fun s => f (s, x)) t := by
    have hmapC : ContinuousAt (fun s : ℝ => (s, x)) t := by fun_prop
    have h := hmax.comp_continuous (g := fun s : ℝ => (s, x)) (b := t) hmapC
    change IsLocalMax (f ∘ fun s : ℝ => (s, x)) t
    exact h
  have hspaceMax : IsLocalMax (fun y => f (t, y)) x := by
    have hmapC : ContinuousAt (fun y : Vec 2 => (t, y)) x := by fun_prop
    have h := hmax.comp_continuous (g := fun y : Vec 2 => (t, y)) (b := x) hmapC
    change IsLocalMax (f ∘ fun y : Vec 2 => (t, y)) x
    exact h
  have htime : deriv (fun s => f (s, x)) t = 0 := htimeMax.deriv_eq_zero
  have hgrad : ∀ i : Fin 2, spaceGrad (fun y => f (t, y)) x i = 0 := by
    intro i
    have hfd := hspaceMax.fderiv_eq_zero
    simp [AVenhance.spaceGrad, hfd]
  exact ⟨htime, hgrad, spaceLap_nonpos_of_isLocalMax hspaceC hspaceMax⟩

/-- Coordinate derivative is linear under subtraction of differentiable
functions. -/
theorem spaceGrad_sub {f g : Vec 2 → ℝ} {x : Vec 2} (i : Fin 2)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    spaceGrad (fun y => f y - g y) x i = spaceGrad f x i - spaceGrad g x i := by
  change fderiv ℝ (fun y => f y - g y) x (basisVec i) = _
  rw [fderiv_fun_sub hf hg]
  simp [spaceGrad]

/-- Laplacian is linear under subtraction of `C²` functions. -/
theorem spaceLap_sub {f g : Vec 2 → ℝ} {x : Vec 2}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    spaceLap (fun y => f y - g y) x = spaceLap f x - spaceLap g x := by
  have hgradCont (F : Vec 2 → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin 2) :
      ContDiff ℝ 1 (fun y : Vec 2 => spaceGrad F y i) := by
    have hjoint : ContDiff ℝ 1
        (fun p : Vec 2 × Vec 2 => fderiv ℝ F p.1 p.2) :=
      hF.contDiff_fderiv_apply (by norm_num)
    have hmap : ContDiff ℝ 1 (fun y : Vec 2 => (y, basisVec i)) := by fun_prop
    have hcomp := hjoint.comp hmap
    have heq : (fun y : Vec 2 => fderiv ℝ F y (basisVec i)) =
        fun y => ((fun p : Vec 2 × Vec 2 => fderiv ℝ F p.1 p.2) ∘
          (fun y : Vec 2 => (y, basisVec i))) y := by
      funext y
      rfl
    rw [show (fun y : Vec 2 => spaceGrad F y i) =
        fun y => fderiv ℝ F y (basisVec i) by rfl, heq]
    exact hcomp
  have hinner (i : Fin 2) : (fun y : Vec 2 =>
      spaceGrad (fun z => f z - g z) y i) =
      fun y => spaceGrad f y i - spaceGrad g y i := by
    funext y
    exact spaceGrad_sub i (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y)
  have hfg0 : DifferentiableAt ℝ (fun y : Vec 2 => spaceGrad f y 0) x :=
    (hgradCont f hf 0).differentiable (by norm_num) x
  have hgg0 : DifferentiableAt ℝ (fun y : Vec 2 => spaceGrad g y 0) x :=
    (hgradCont g hg 0).differentiable (by norm_num) x
  have hfg1 : DifferentiableAt ℝ (fun y : Vec 2 => spaceGrad f y 1) x :=
    (hgradCont f hf 1).differentiable (by norm_num) x
  have hgg1 : DifferentiableAt ℝ (fun y : Vec 2 => spaceGrad g y 1) x :=
    (hgradCont g hg 1).differentiable (by norm_num) x
  unfold spaceLap
  simp only [Fin.sum_univ_two]
  rw [hinner 0, hinner 1]
  rw [spaceGrad_sub 0 hfg0 hgg0, spaceGrad_sub 1 hfg1 hgg1]
  ring

/-- The quadratic coercive function used to localize a bounded parabolic
maximum on the whole plane. -/
def parabolicRadialSq (x : Vec 2) : ℝ := x 0 ^ 2 + x 1 ^ 2

theorem ParabolicMaximum.parabolicRadialSq_line_deriv (x : Vec 2) (i : Fin 2) :
    HasDerivAt (fun s => parabolicRadialSq (ParabolicMaximum.coordinateLine x i s))
      (2 * x i) 0 := by
  fin_cases i
  · have hlin : HasDerivAt (fun s : ℝ => x 0 + s) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
    have hpow := hlin.pow 2
    have hc : HasDerivAt (fun _ : ℝ => x 1 ^ 2) 0 0 := hasDerivAt_const _ _
    have hs := hpow.add hc
    convert hs using 1
    · funext s
      simp [parabolicRadialSq, ParabolicMaximum.coordinateLine, basisVec_apply]
    · norm_num [basisVec_apply]
  · have hlin : HasDerivAt (fun s : ℝ => x 1 + s) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 1)
    have hpow := hlin.pow 2
    have hc : HasDerivAt (fun _ : ℝ => x 0 ^ 2) 0 0 := hasDerivAt_const _ _
    have hs := hc.add hpow
    convert hs using 1
    · funext s
      simp [parabolicRadialSq, ParabolicMaximum.coordinateLine, basisVec_apply]
    · norm_num [basisVec_apply]

/-- Coordinate derivatives of the coercive quadratic on `Vec 2`. -/
theorem spaceGrad_parabolicRadialSq (x : Vec 2) (i : Fin 2) :
    spaceGrad parabolicRadialSq x i = 2 * x i := by
  have hdiff : DifferentiableAt ℝ parabolicRadialSq x := by
    change DifferentiableAt ℝ (fun x : Vec 2 => x 0 ^ 2 + x 1 ^ 2) x
    fun_prop
  have houter := hdiff.hasFDerivAt
  have hline : HasDerivAt (ParabolicMaximum.coordinateLine x i) (basisVec i) 0 := by
    change HasDerivAt (fun s : ℝ => x + s • basisVec i) _ _
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec i)).const_add x
  have hline0 : ParabolicMaximum.coordinateLine x i 0 = x := by simp
      [ParabolicMaximum.coordinateLine]
  have hcomp := houter.comp_hasDerivAt_of_eq 0 hline hline0.symm
  have hcomp' : HasDerivAt (fun s => parabolicRadialSq (ParabolicMaximum.coordinateLine x i s))
      (spaceGrad parabolicRadialSq x i) 0 := by
    change HasDerivAt (parabolicRadialSq ∘ ParabolicMaximum.coordinateLine x i)
      (fderiv ℝ parabolicRadialSq x (basisVec i)) 0
    exact hcomp
  have huniq := (ParabolicMaximum.parabolicRadialSq_line_deriv x i).unique hcomp'
  simpa [spaceGrad] using huniq.symm

theorem spaceGrad_scaledCoordinate (c : ℝ) (j i : Fin 2)
    (x : Vec 2) :
    spaceGrad (fun y : Vec 2 => c * y j) x i = if i = j then c else 0 := by
  have hlin : HasFDerivAt (fun y : Vec 2 => c * y j)
      (c • (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ)) x := by
    convert (c • (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ)).hasFDerivAt using 1
    ext y
    simp
  change fderiv ℝ (fun y : Vec 2 => c * y j) x (basisVec i) = _
  rw [hlin.fderiv]
  simp [basisVec_apply, eq_comm]

/-- Spatial gradient of a constant multiple of the quadratic barrier. -/
theorem spaceGrad_constantRadialSq (c : ℝ) (x : Vec 2) (i : Fin 2) :
    spaceGrad (fun y : Vec 2 => c * (1 + parabolicRadialSq y)) x i =
      c * (2 * x i) := by
  have hdiff : DifferentiableAt ℝ
      (fun y : Vec 2 => 1 + parabolicRadialSq y) x := by
    change DifferentiableAt ℝ (fun y : Vec 2 => 1 + (y 0 ^ 2 + y 1 ^ 2)) x
    fun_prop
  have hlin := hdiff.hasFDerivAt.const_mul c
  change fderiv ℝ (fun y : Vec 2 => c * (1 + parabolicRadialSq y))
    x (basisVec i) = _
  rw [hlin.fderiv]
  have hfd : fderiv ℝ (fun y : Vec 2 => 1 + parabolicRadialSq y) x =
      fderiv ℝ parabolicRadialSq x := by
    rw [show (fun y : Vec 2 => 1 + parabolicRadialSq y) =
        fun y => parabolicRadialSq y + 1 by
      funext y
      ring]
    exact fderiv_add_const 1
  rw [hfd]
  change c * spaceGrad parabolicRadialSq x i = _
  rw [spaceGrad_parabolicRadialSq]

/-- Spatial Laplacian of a constant multiple of the quadratic barrier. -/
theorem spaceLap_constantRadialSq (c : ℝ) (x : Vec 2) :
    spaceLap (fun y : Vec 2 => c * (1 + parabolicRadialSq y)) x = 4 * c := by
  unfold spaceLap
  simp only [Fin.sum_univ_two]
  have h0 : (fun y : Vec 2 =>
      spaceGrad (fun z : Vec 2 => c * (1 + parabolicRadialSq z)) y 0) =
      fun y => (2 * c) * y 0 := by
    funext y
    rw [spaceGrad_constantRadialSq]
    ring
  have h1 : (fun y : Vec 2 =>
      spaceGrad (fun z : Vec 2 => c * (1 + parabolicRadialSq z)) y 1) =
      fun y => (2 * c) * y 1 := by
    funext y
    rw [spaceGrad_constantRadialSq]
    ring
  rw [h0, h1]
  rw [spaceGrad_scaledCoordinate (2 * c) 0 0 x,
    spaceGrad_scaledCoordinate (2 * c) 1 1 x]
  simp
  ring

/-- Exponential quadratic barrier for the bounded whole-plane maximum
principle. -/
def parabolicBarrier (ε A s : ℝ) (p : ℝ × Vec 2) : ℝ :=
  ε * (1 + parabolicRadialSq p.2) * Real.exp (A * (p.1 - s))

/-- Time derivative of the exponential quadratic barrier. -/
theorem parabolicBarrier_time_deriv (ε A s t : ℝ) (x : Vec 2) :
    deriv (fun r => parabolicBarrier ε A s (r, x)) t =
      ε * A * Real.exp (A * (t - s)) *
        (1 + parabolicRadialSq x) := by
  change deriv (fun r : ℝ =>
      (ε * (1 + parabolicRadialSq x)) * Real.exp (A * (r - s))) t = _
  rw [deriv_const_mul_field]
  have hi : DifferentiableAt ℝ (fun r : ℝ => A * (r - s)) t := by fun_prop
  rw [deriv_exp hi, deriv_const_mul_field]
  simp
  ring

end AVenhance.Infra.Section3
