/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! # Defect matrices, fluxes and nondivergence parts of `twistie4`, `twistie5`

In the corrected form, the slots are the divergences `twistie4 = -div(twistie4Flux)` and
`twistie5 = -div(twistie5Flux)` (`twistie4_eq_neg_div_flux`, `twistie5_eq_neg_div_flux`); the
earlier bodies are `twistie4ND`, `twistie5ND`.

`twistie4ND = -Σ_k ξ_k G_k · Div D_k` with the Lagrangian defect matrix
`D_k = κ_m (∇X⁻¹ - I)(∇Χ_{m,k} ∘ X⁻¹)`, and `twistie5 = -Σ_k ξ_k G_k · Div E_k` with
`E_k = (I - (∇X∘X⁻¹)ᵀ)(ζ̂ζ ψ_{m,k}∘X⁻¹ σ + κ_m ∇Χ_{m,k}∘X⁻¹)`.  Integrating the divergence by parts
(source `e.monster.twistie4.split`, `e.monster.twistie5.split`) gives
`twistie = (nondivergence part) - div (flux)`, with
`flux = Σ_k ξ_k D_k G_k` and `nondivergence part = Σ_k ξ_k D_k : ∇G_k`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open Homogenization AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The Lagrangian defect matrix `D_k` of `twistie4`. -/
def sdDefect4 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) (y : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  κm • ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) y - 1) *
    gradMatrix (fun z => I.chiMK κm m k t z) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))

/-- The push-forward defect matrix `E_k` of `twistie5`. -/
def sdDefect5 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) (y : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (1 - (flowGradK I hΦ m k t y).transpose) *
    ((I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
        psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) • sigmaMat +
      κm • gradMatrix (fun z => I.chiMK κm m k t z) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))

theorem twistie4ND_eq_defect (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) :
    twistie4ND I hΦ m κm T t x =
      -∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
        vecDot (G I hΦ m T (lIdx β I.Λ m k) t x) (matDiv (sdDefect4 I hΦ m κm k t) x) := rfl

theorem twistie5ND_eq_defect (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) :
    twistie5ND I hΦ m κm T t x =
      -∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
        vecDot (G I hΦ m T (lIdx β I.Λ m k) t x) (matDiv (sdDefect5 I hΦ m κm k t) x) := rfl

/-- The vector flux `Σ_k ξ_k D_k G_k` under the divergence in the split of `twistie4`. -/
def twistie4Flux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
    (sdDefect4 I hΦ m κm k t x).mulVec (G I hΦ m T (lIdx β I.Λ m k) t x)

/-- The vector flux `Σ_k ξ_k E_k G_k` under the divergence in the split of `twistie5`. -/
def twistie5Flux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
    (sdDefect5 I hΦ m κm k t x).mulVec (G I hΦ m T (lIdx β I.Λ m k) t x)

/-- In the corrected form, `twistie4` is the divergence of its flux. -/
theorem twistie4_eq_neg_div_flux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    twistie4 I hΦ m κm T t x = -vecDiv (twistie4Flux I hΦ m κm T t) x := rfl

/-- In the corrected form, `twistie5` is the divergence of its flux. -/
theorem twistie5_eq_neg_div_flux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    twistie5 I hΦ m κm T t x = -vecDiv (twistie5Flux I hΦ m κm T t) x := rfl

/-- The nondivergence part `Σ_k ξ_k D_k : ∇G_k` of `twistie4ND`. -/
def twistie4Nd (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
    frob (sdDefect4 I hΦ m κm k t x) (gradG I hΦ m T (lIdx β I.Λ m k) t x)

/-- The nondivergence part `Σ_k ξ_k E_k : ∇G_k` of `twistie5ND`. -/
def twistie5Nd (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
    frob (sdDefect5 I hΦ m κm k t x) (gradG I hΦ m T (lIdx β I.Λ m k) t x)

/-- Fast factor `∂_aΧ_{m,k,j}` (a `1/ε_m`-periodic function) of the nondivergence part of
`twistie4`. -/
def sdFast4 (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) (a j : Fin 2) (y : Vec 2) : ℝ :=
  gradMatrix (fun z => I.chiMK κm m k t z) y a j

/-- Fast factor `ζ̂ζ ψ_{m,k} σ_{aj} + κ_m ∂_aΧ_{m,k,j}` of the nondivergence part of `twistie5`. -/
def sdFast5 (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) (a j : Fin 2) (y : Vec 2) : ℝ :=
  (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t * psi β I.Λ m k y) * sigmaMat a j +
    κm * gradMatrix (fun z => I.chiMK κm m k t z) y a j

end AVenhance.Infra.Section5.Contracts
end
