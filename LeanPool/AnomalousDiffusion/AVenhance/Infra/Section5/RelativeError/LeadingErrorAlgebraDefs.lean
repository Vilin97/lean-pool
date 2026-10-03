/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! # The three remainder fields of `e.grad.tildetheta.again`: definitions and calculus

Source: `enhance.tex` 8112–8143 (and 8146–8170, the estimates).  Writing `Y = X⁻¹_{m-1,l_k}(t,·)`,
`A = ∇Y (x)`, `C = ∇Χ_{m,k}(Y x)` (`gradMatrix` convention: entry `(i,j) = ∂_i χ_j`),
`Fl = ∇X_{m-1,l_k}∘X⁻¹_{m-1,l_k} (x)` (`flowGrad`) and `g = ∇T_{m-1}(t,x)`, the three
remainder vector fields are

* `leadingErrFlowInv  = ((A - 1) C) g`   — the second term of `e.grad.tildetheta.again`;
* `leadingErrFlowFwd  = (A C (Fl - 1)) g` — the third term (`∇ΧTilde = A C` by the chain rule);
* `leadingErrHessian` — the fourth term `ΧTilde · ∇(∇(T∘X)∘X⁻¹)`, expanded by the product and chain
  rules into `∑_j χ_j(Yx) ∑_p ( Fl_{jp} ∂_i∂_p T + (∑_q A_{iq} ∂_q∂_j X^p(Yx)) ∂_p T )`.

This file contains the definitions, the smoothness of the objects, and the calculus lemmas
(chain rule for `∇ΧTilde`, entries of `∇G_{l_k}`) used by the identity file. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The second spatial derivative `∂_q ∂_j X^p_{m-1,l}(t,·)(z)` of the flow. -/
def xFlowHess (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (z : Vec 2) (p j q : Fin 2) : ℝ :=
  spaceGrad (fun w => spaceGrad (fun u => I.xFlow hΦ m l t u p) w j) z q

/-- The second spatial derivative `∂_i ∂_p f (x)` of a scalar function. -/
def spaceHess (f : Vec 2 → ℝ) (x : Vec 2) (i p : Fin 2) : ℝ :=
  spaceGrad (fun y => spaceGrad f y p) x i

/-- Second term of `e.grad.tildetheta.again` (before the factor `ξ_{m,k}` and the sum):
`(∇X⁻¹_{m-1,l_k} - I) (∇Χ_{m,k})∘X⁻¹_{m-1,l_k} ∇T_{m-1}`. -/
def leadingErrFlowInv (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x - 1) *
      gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).mulVec
    (spaceGrad (T t) x)

/-- Third term of `e.grad.tildetheta.again` (before the factor `ξ_{m,k}` and the sum):
`∇ΧTilde_{m,k} ((∇X_{m-1,l_k})∘X⁻¹_{m-1,l_k} - I) ∇T_{m-1}`, with the chain rule
`∇ΧTilde_{m,k} = ∇X⁻¹_{m-1,l_k} · (∇Χ_{m,k})∘X⁻¹_{m-1,l_k}` already expanded
(see `gradMatrix_chiTilde_eq`). -/
def leadingErrFlowFwd (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  (gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x *
      gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) *
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t x - 1)).mulVec
    (spaceGrad (T t) x)

/-- Fourth term of `e.grad.tildetheta.again` (before the factor `ξ_{m,k}` and the sum),
`ΧTilde_{m,k} · ∇(∇(T_{m-1}∘X_{m-1,l_k})∘X⁻¹_{m-1,l_k})`, expanded: component `i` is
`∑_j χ_{m,k,j}(Yx) ∑_p ( Fl_{jp} ∂_i∂_p T + (∑_q (∇Y)_{iq} ∂_q∂_j X^p (Yx)) ∂_p T )`. -/
def leadingErrHessian (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) : Vec 2 := fun i =>
  ∑ j : Fin 2, I.chiMK κm m k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j *
    ∑ p : Fin 2,
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t x j p * spaceHess (T t) x i p +
        (∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x i q *
            xFlowHess I hΦ m (lIdx β I.Λ m k) t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) p j q) *
          spaceGrad (T t) x p)

/-! ### Smoothness of the objects -/

theorem contDiff_chiMK (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) : ContDiff ℝ ∞ (I.chiMK κm m k t) := by
  unfold Ingredients.chiMK
  exact (contDiff_const (c := -(I.corrTime κm m k t))).smul (Integration.contDiff_uShear' β I.Λ m k)

theorem contDiff_xFlowInv_slice (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ ∞ (I.xFlowInv hΦ m l t) :=
  (Integration.xFlowInv_joint_contDiff_infty I hΦ m l).comp (contDiff_prodMk_right t)

theorem contDiff_xFlow_slice (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ ∞ (I.xFlow hΦ m l t) :=
  (Integration.xFlow_joint_contDiff_infty I hΦ m l).comp (contDiff_prodMk_right t)

theorem xFlow_xFlowInv (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x :=
  (LeftToShow.xFlowDiffeo I hΦ m l t).right_inv x

theorem contDiff_chiTilde (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ ∞ (I.chiTilde hΦ m κm k t) :=
  (contDiff_chiMK I κm m k t).comp (contDiff_xFlowInv_slice I hΦ m _ t)

theorem contDiff_G (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (l : ℤ) {t : ℝ}
    (hTt : ContDiff ℝ ∞ (T t)) : ContDiff ℝ ∞ (fun y => G I hΦ m T l t y) := by
  refine contDiff_pi.2 fun j => ?_
  have hcomp : ContDiff ℝ ∞ (fun y => T t (I.xFlow hΦ m l t y)) :=
    hTt.comp (contDiff_xFlow_slice I hΦ m l t)
  exact (Integration.contDiff_spaceGrad_component hcomp j).comp (contDiff_xFlowInv_slice I hΦ m l t)

/-- The corrector `Χ_{m,k}` vanishes for even `k` (`uShear = 0`). -/
theorem chiMK_eq_zero_of_not_odd (κ : ℝ) (m : ℕ) {k : ℤ} (hk : ¬ Odd k) (t : ℝ) :
    I.chiMK κ m k t = 0 := by
  have h1 : k % 4 ≠ 1 := by
    intro hmod
    rcases Int.even_or_odd k with he | ho
    · rcases he with ⟨z, hz⟩
      omega
    · exact hk ho
  have h3 : k % 4 ≠ 3 := by
    intro hmod
    rcases Int.even_or_odd k with he | ho
    · rcases he with ⟨z, hz⟩
      omega
    · exact hk ho
  funext x
  simp [Ingredients.chiMK, uShear, h1, h3]

/-! ### Elementary `spaceGrad` calculus -/

theorem spaceGrad_mul_of_differentiableAt {f g : Vec 2 → ℝ} {x : Vec 2}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    spaceGrad (fun y => f y * g y) x i = f x * spaceGrad g x i + g x * spaceGrad f x i := by
  simp only [spaceGrad]
  rw [fderiv_fun_mul hf hg]
  simp [smul_eq_mul]

theorem spaceGrad_sum_univ_of_differentiableAt {f : Fin 2 → Vec 2 → ℝ} {x : Vec 2}
    (h : ∀ p, DifferentiableAt ℝ (f p) x) (i : Fin 2) :
    spaceGrad (fun y => ∑ p, f p y) x i = ∑ p, spaceGrad (f p) x i := by
  simp only [spaceGrad]
  rw [fderiv_fun_sum (fun p _ => h p)]
  simp

/-- Chain rule `∇ΧTilde_{m,k} = ∇X⁻¹_{m-1,l_k} · (∇Χ_{m,k})∘X⁻¹_{m-1,l_k}`. -/
theorem gradMatrix_chiTilde_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ)
    (x : Vec 2) :
    gradMatrix (I.chiTilde hΦ m κm k t) x =
      gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x *
        gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) := by
  ext i j
  have hY := ((contDiff_xFlowInv_slice I hΦ m (lIdx β I.Λ m k) t).differentiable
    (by simp) x).hasFDerivAt
  have hf : HasFDerivAt (fun w => I.chiMK κm m k t w j)
      (fderiv ℝ (fun w => I.chiMK κm m k t w j) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) :=
    (((contDiff_apply ℝ ℝ j).comp (contDiff_chiMK I κm m k t)).differentiable (by simp)
        _).hasFDerivAt
  have h := spaceGrad_comp_eq_gradMatrix_mul hf hY i
  simpa [gradMatrix, Matrix.mul_apply, Ingredients.chiTilde] using h

/-- The product/chain-rule expansion of the entries of `∇G_{l}`. -/
theorem spaceGrad_G_component (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (l : ℤ) {t : ℝ}
    (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2) (i j : Fin 2) :
    spaceGrad (fun y => G I hΦ m T l t y j) x i =
      ∑ p : Fin 2,
        (I.flowGrad hΦ m l t x j p * spaceHess (T t) x i p +
          (∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i q *
              xFlowHess I hΦ m l t (I.xFlowInv hΦ m l t x) p j q) * spaceGrad (T t) x p) := by
  have hXs := contDiff_xFlow_slice I hΦ m l t
  have hYs := contDiff_xFlowInv_slice I hΦ m l t
  have hXp (p : Fin 2) : ContDiff ℝ ∞ (fun u => I.xFlow hΦ m l t u p) :=
    (contDiff_apply ℝ ℝ p).comp hXs
  -- the entries of the pulled-back gradient
  have hfun : (fun y => G I hΦ m T l t y j) = fun y => ∑ p : Fin 2,
      spaceGrad (fun u => I.xFlow hΦ m l t u p) (I.xFlowInv hΦ m l t y) j *
        spaceGrad (T t) y p := by
    funext y
    have hT := (hTt.differentiable (by simp) y).hasFDerivAt
    have hX := (hXs.differentiable (by simp) (I.xFlowInv hΦ m l t y)).hasFDerivAt
    have h := G_eq_flowGrad_mulVec I hΦ m T l t y hT hX (xFlow_xFlowInv I hΦ m l t y)
    rw [h]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Ingredients.flowGrad, gradMatrix]
  -- smoothness of the pieces
  have hfpj (p : Fin 2) : ContDiff ℝ ∞ (fun w => spaceGrad (fun u => I.xFlow hΦ m l t u p) w j) :=
    Integration.contDiff_spaceGrad_component (hXp p) j
  have hbp (p : Fin 2) : ContDiff ℝ ∞ (fun y => spaceGrad (T t) y p) :=
    Integration.contDiff_spaceGrad_component hTt p
  have hap (p : Fin 2) : ContDiff ℝ ∞ (fun y =>
      spaceGrad (fun u => I.xFlow hΦ m l t u p) (I.xFlowInv hΦ m l t y) j) :=
    (hfpj p).comp hYs
  rw [hfun]
  rw [spaceGrad_sum_univ_of_differentiableAt
    (fun p => ((hap p).mul (hbp p)).differentiable (by simp) x)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [spaceGrad_mul_of_differentiableAt ((hap p).differentiable (by simp) x)
    ((hbp p).differentiable (by simp) x)]
  have hYx := (hYs.differentiable (by simp) x).hasFDerivAt
  have hfx : HasFDerivAt (fun w => spaceGrad (fun u => I.xFlow hΦ m l t u p) w j)
      (fderiv ℝ (fun w => spaceGrad (fun u => I.xFlow hΦ m l t u p) w j)
        (I.xFlowInv hΦ m l t x)) (I.xFlowInv hΦ m l t x) :=
    ((hfpj p).differentiable (by simp) _).hasFDerivAt
  have hchain (i : Fin 2) := spaceGrad_comp_eq_gradMatrix_mul hfx hYx i
  rw [hchain i]
  simp only [Ingredients.flowGrad, gradMatrix, Matrix.of_apply, xFlowHess, spaceHess]
  ring

end AVenhance.Infra.Section5.RelativeError
