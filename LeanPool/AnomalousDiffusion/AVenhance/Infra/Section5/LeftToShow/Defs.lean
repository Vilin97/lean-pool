/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.XFlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.GradMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceAvgMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.XiMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MaterialGradient

/-! # Objects of the §5.3 additive energy estimate `e.left.to.show`

Source: `enhance.tex` 8271–8882.  The matrix field
`F(t,x) = ∑_{k∈2ℤ+1} ξ_{m,k}(t) (I + ∇Χ_{m,k}) ∘ X⁻¹_{m-1,l_k}(t,x)` (8298–8302), the leading
term `F ∇T_{m-1}` of `e.leadingord`, the space average `⟨FᵗF⟩(t)` of `e.ergodic.break.up`, and
the material gradient `D_{t,m-1} ∇T_{m-1}` of `e.barf.cascade`.

Conventions: `gradMatrix Χ x` has entry `(i,j) = ∂_{x_i} χ_{e_j}` (`e.gradcorrmatrix`), so the
leading term is the matrix–vector product `F.mulVec (∇T)`. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `F(t,x) := ∑_{k∈2ℤ+1} ξ_{m,k}(t) (I + ∇Χ_{m,k}(t,·)) ∘ X⁻¹_{m-1,l_k}(t,x)` (source 8298–8302),
with `κm = κ_m` the diffusivity of the correctors.  For each `t` only finitely many summands are
nonzero (`xiMK_odd_support_finite`). -/
def leadingMatrix (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (t : ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
    (1 + gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x))

/-- The leading-order gradient `F ∇T_{m-1}` of `e.leadingord` / `e.left.to.show`. -/
def leadingGrad (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (x : Vec 2) : Vec 2 :=
  (leadingMatrix I hΦ m κm t x).mulVec (spaceGrad (T t) x)

/-- The space average `⟨FᵗF⟩(t)` of `e.ergodic.break.up` / `e.bracket.FF`. -/
def leadingGramAvg (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  spaceAvgMat fun x => (leadingMatrix I hΦ m κm t x).transpose * leadingMatrix I hΦ m κm t x

end AVenhance.Infra.Section5.LeftToShow

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

/-- The material gradient `D_t ∇T = (∂_t + b·∇)∇T`, componentwise (`e.D.t.m.def`,
`e.barf.cascade` with `b = b_{m-1}`). -/
def materialGrad (b : ℝ → Vec 2 → Vec 2) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  fun i => materialDerivative (fun s y => spaceGrad (T s) y i) b t x

end AVenhance.Infra.Section5.LeftToShow
