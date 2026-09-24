/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Differentiation formulas for the heat kernel

The coordinate formulas below use the standard coordinate directions of
`Fin 3 → ℝ`.  They do not use the function space's ambient norm; all spatial
quadratic expressions are finite sums.
-/

@[expose] public section

open scoped BigOperators ENNReal Topology

open Filter Set


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-- Time derivative formula for the causal heat kernel. -/
def heatKernelTimeDerivative (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    heatKernel x t *
      ((∑ i, x i ^ 2) / (4 * t ^ 2) - (3 : ℝ) / (2 * t))
  else 0

/-- First spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceDerivative (x : Vec3) (t : ℝ) (i : Fin 3) : ℝ :=
  if 0 < t then -(x i) / (2 * t) * heatKernel x t else 0

/-- Pure second spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceSecondDerivative (x : Vec3) (t : ℝ) (i : Fin 3) : ℝ :=
  if 0 < t then
    ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel x t
  else 0

/-- Mixed second spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceMixedSecondDerivative (x : Vec3) (t : ℝ)
    (i j : Fin 3) : ℝ :=
  if 0 < t then
    ((x i) * (x j) / (4 * t ^ 2) -
      (if i = j then (1 : ℝ) / (2 * t) else 0)) * heatKernel x t
  else 0

/-- Third spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceThirdDerivative (x : Vec3) (t : ℝ)
    (i j k : Fin 3) : ℝ :=
  if 0 < t then
    (-(x i) * (x j) * (x k) / (8 * t ^ 3) +
      ((if i = j then x k else 0) +
        (if i = k then x j else 0) +
        (if j = k then x i else 0)) / (4 * t ^ 2)) * heatKernel x t
  else 0

/-- Fourth spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceFourthDerivative (x : Vec3) (t : ℝ)
    (i j k l : Fin 3) : ℝ :=
  if 0 < t then
    ((x i) * (x j) * (x k) * (x l) / (16 * t ^ 4) -
      ((if i = j then (x k) * (x l) else 0) +
        (if i = k then (x j) * (x l) else 0) +
        (if i = l then (x j) * (x k) else 0) +
        (if j = k then (x i) * (x l) else 0) +
        (if j = l then (x i) * (x k) else 0) +
        (if k = l then (x i) * (x j) else 0)) / (8 * t ^ 3) +
      ((if i = j then (if k = l then (1 : ℝ) else 0) else 0) +
        (if i = k then (if j = l then (1 : ℝ) else 0) else 0) +
        (if i = l then (if j = k then (1 : ℝ) else 0) else 0)) /
        (4 * t ^ 2)) * heatKernel x t
  else 0

/-- Spatial Laplacian of the heat kernel, summed over coordinate directions. -/
def heatKernelLaplacian (x : Vec3) (t : ℝ) : ℝ :=
  ∑ i, heatKernelSpaceSecondDerivative x t i

lemma heatKernel_contDiffOn_pos :
    ContDiffOn ℝ ⊤ (fun p : Vec3 × ℝ => heatKernel p.1 p.2)
      (univ ×ˢ Ioi (0 : ℝ)) := by
  intro p hp
  rcases hp with ⟨_, hp⟩
  change 0 < p.2 at hp
  have hformula : ContDiffAt ℝ ⊤
      (fun q : Vec3 × ℝ =>
        (4 * Real.pi * q.2) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, q.1 i ^ 2) / (4 * q.2))) p := by
    fun_prop (disch := positivity)
  apply hformula.contDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [eventually_mem_nhdsWithin] with q hq
    have hqpos : 0 < q.2 := hq.2
    rw [heatKernel, ite_eq_left hqpos]
  · rw [heatKernel, ite_eq_left hp]

lemma heatKernel_time_differentiableAt {x : Vec3} {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun s => heatKernel x s) t := by
  have hformula : ContDiffAt ℝ ⊤
      (fun s : ℝ =>
        (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, x i ^ 2) / (4 * s))) t := by
    fun_prop (disch := positivity)
  have heq :
      (fun s : ℝ => heatKernel x s) =ᶠ[nhds t]
        (fun s : ℝ =>
          (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ i, x i ^ 2) / (4 * s))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [heatKernel_eq_formula_sum hs]
  exact (hformula.congr_of_eventuallyEq heq).differentiableAt (by simp)

lemma heatKernel_time_deriv {x : Vec3} {t : ℝ} (ht : 0 < t) :
    deriv (fun s => heatKernel x s) t = heatKernelTimeDerivative x t := by
  let q : ℝ := ∑ i, x i ^ 2
  let a : ℝ := 4 * Real.pi
  have hformula : HasDerivAt
      (fun s : ℝ => (a * s) ^ (-(3 : ℝ) / 2) *
        Real.exp (-q / (4 * s)))
      (((4 * Real.pi) * (-(3 : ℝ) / 2) * (a * t) ^ (-(3 : ℝ) / 2 - 1)) *
          Real.exp (-q / (4 * t)) +
        (a * t) ^ (-(3 : ℝ) / 2) *
          (Real.exp (-q / (4 * t)) * (q / (4 * t ^ 2)))) t := by
    have hbase : HasDerivAt (fun s : ℝ => a * s) a t := by
      convert (hasDerivAt_const t a).mul (hasDerivAt_id t) using 1
      · funext s
        simp [a]
      · simp [a]
    have hpow := hbase.rpow_const (p := -(3 : ℝ) / 2)
      (Or.inl (by dsimp [a]; positivity : a * t ≠ 0))
    have hden : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      convert (hasDerivAt_const t (4 : ℝ)).mul (hasDerivAt_id t) using 1
      · funext s
        simp
      · simp
    have hinv := (hasDerivAt_inv (by positivity : 4 * t ≠ 0)).comp t hden
    have harg : HasDerivAt (fun s : ℝ => -q / (4 * s)) (q / (4 * t ^ 2)) t := by
      convert (hasDerivAt_const t (-q)).mul hinv using 1
      · funext s
        simp [Function.comp_def]
        ring_nf
      · field_simp
        ring_nf
    have hexp := harg.exp
    convert hpow.mul hexp using 1
  have heq :
      (fun s : ℝ => heatKernel x s) =ᶠ[nhds t]
        (fun s : ℝ => (a * s) ^ (-(3 : ℝ) / 2) * Real.exp (-q / (4 * s))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [heatKernel_eq_formula_sum hs]
  have hderiv := hformula.congr_of_eventuallyEq heq
  rw [hderiv.deriv]
  rw [heatKernelTimeDerivative, ite_eq_left ht]
  rw [heatKernel_eq_formula_sum ht]
  dsimp [a, q]
  rw [show -(3 : ℝ) / 2 - 1 = (-(3 : ℝ) / 2) + (-1) by ring,
    Real.rpow_add (by positivity : 0 < 4 * Real.pi * t),
    Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi * t)]
  field_simp [ht.ne']
  simp only [Real.rpow_one]
  ring_nf

private lemma quadratic_update (x : Vec3) (i : Fin 3) (s : ℝ) :
    ∑ j, (Function.update x i s j) ^ 2 =
      s ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2 := by
  classical
  have hfun : (fun j => (Function.update x i s j) ^ 2) =
      Function.update (fun j => x j ^ 2) i (s ^ 2) := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp

lemma heatKernel_space_deriv {x : Vec3} {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    deriv (fun s => heatKernel (Function.update x i s) t) (x i) =
      heatKernelSpaceDerivative x t i := by
  let q : ℝ := ∑ j ∈ Finset.univ.erase i, x j ^ 2
  have hformula : HasDerivAt
      (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(s ^ 2 + q) / (4 * t)))
      ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        (Real.exp (-(x i ^ 2 + q) / (4 * t)) * (-(x i) / (2 * t)))) (x i) := by
    have hquad : HasDerivAt (fun s : ℝ => s ^ 2 + q) (2 * x i) (x i) := by
      convert (hasDerivAt_id (x i)).pow 2 |>.add (hasDerivAt_const (x i) q) using 1
      · funext s
        simp
      · simp
    have harg := (hasDerivAt_const (x i) (-1 / (4 * t))).mul hquad
    have hexp := harg.exp
    have hconst : HasDerivAt (fun _ : ℝ => (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)) 0 (x i) :=
      hasDerivAt_const _ _
    convert hconst.mul hexp using 1
    · funext s
      simp only [Pi.mul_apply]
      ring_nf
    · simp only [Pi.mul_apply, zero_mul, zero_add]
      rw [show -(x i ^ 2 + q) / (4 * t) =
        -1 / (4 * t) * (x i ^ 2 + q) by ring_nf]
      congr 2
      field_simp [ht.ne']
      ring_nf
  have heq :
      (fun s : ℝ => heatKernel (Function.update x i s) t) =ᶠ[nhds (x i)]
        (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(s ^ 2 + q) / (4 * t))) := by
    filter_upwards with s
    rw [heatKernel_eq_formula_sum ht, quadratic_update]
  have hderiv := hformula.congr_of_eventuallyEq heq
  rw [hderiv.deriv, heatKernelSpaceDerivative, ite_eq_left ht]
  rw [heatKernel_eq_formula_sum ht]
  have hq : (∑ j, x j ^ 2) = x i ^ 2 + q := by
    have hupdate := quadratic_update x i (x i)
    rw [show Function.update x i (x i) = x by
      funext j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji]] at hupdate
    exact hupdate
  rw [hq]
  field_simp [ht.ne']

private lemma coord_fderiv_eq_deriv_update {f : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (fderiv ℝ f x) (CKN.basisVec i) =
      deriv (fun s => f (Function.update x i s)) (x i) := by
  have hcomp := HasFDerivAt.comp (x i)
    (by simpa only [Function.update_eq_self] using hf.hasFDerivAt)
    (hasFDerivAt_update (𝕜 := ℝ) (i := i) x (x i))
  have hderiv := hcomp.hasDerivAt
  have hderiv' : HasDerivAt (fun s : ℝ => f (Function.update x i s))
      ((fderiv ℝ f x ∘SL ContinuousLinearMap.pi
        (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1) (x i) := by
    simpa only [Function.comp_def] using hderiv
  rw [hderiv'.deriv]
  have hb : ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1 =
      CKN.basisVec i := by
    ext j
    by_cases hji : j = i <;> simp [CKN.basisVec, hji]
  rw [show (fderiv ℝ f x ∘SL
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1 =
      (fderiv ℝ f x) (ContinuousLinearMap.pi
      (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1) by rfl, hb]

lemma heatKernel_fderiv_apply_basisVec {x : Vec3} {t : ℝ} (ht : 0 < t)
    (i : Fin 3) :
    (fderiv ℝ (fun z : Vec3 => heatKernel z t) x) (CKN.basisVec i) =
      heatKernelSpaceDerivative x t i := by
  have hdiff : DifferentiableAt ℝ (fun z : Vec3 => heatKernel z t) x := by
    rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, z j ^ 2) / (4 * t)) by
      funext z
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  rw [coord_fderiv_eq_deriv_update hdiff i]
  exact heatKernel_space_deriv ht i

lemma heatKernel_heat_equation {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernelTimeDerivative x t = heatKernelLaplacian x t := by
  rw [heatKernelTimeDerivative, ite_eq_left ht, heatKernelLaplacian]
  simp only [heatKernelSpaceSecondDerivative, ite_eq_left ht]
  rw [heatKernel_eq_formula_sum ht]
  rw [← Finset.sum_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_fin]
  ring_nf


end CKN.Foundation.Heat
