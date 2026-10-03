/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorDiffusionDivergence

/-! Candidate objects: local aliases for the corrected-form definitions.

These are local candidate aliases with the exact bodies of
the corrected formulation §2, §7 and §9. `sMatPlus` and
`amnrBasePlus` become the `sMat` and the zero branch of `Amnr`
(`rfl`); the theorems of `Section5/LeftJacobian` take the equalities
`I.sMat = sMatPlus` and `I.Amnr · 0 = amnrBasePlus` as hypotheses, which are
then discharged by `rfl`. Every other object below keeps its meaning. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Candidate corrected-form coarse coefficient, the corrected formulation (4) and §9.1:
`s⁺ = K Σ_l ξ̂_l (F_l - I) + Σ_l ξ̂_l (F_lᵀ - I)(K - κ I) F_l`. -/
def sMatPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (t : ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  I.Kmat κm m t * ∑' l : ℤ, I.hatXiML m l t • (I.flowGrad hΦ m l t x - 1) +
    ∑' l : ℤ, I.hatXiML m l t •
      (((I.flowGrad hΦ m l t x).transpose - 1) *
        (I.Kmat κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        I.flowGrad hΦ m l t x)

/-- The Piola form of the coarse coefficient, `𝓚⁺ = Σ_l ξ̂_l [κ F_l + F_lᵀ (K - κ) F_l]`
(the corrected formulation (4)). -/
def coarseFluxPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (t : ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ∑' l : ℤ, I.hatXiML m l t •
    (κm • I.flowGrad hΦ m l t x +
      (I.flowGrad hΦ m l t x).transpose *
        (I.Kmat κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        I.flowGrad hΦ m l t x)

/-- Candidate corrected-form base tensor `A⁺_{n,0}^{ijk} = -L_n Σ_l ξ̂_l (F_l)_{ji} (F_l ∇T)_k`
(the corrected formulation (7), §9.2; index form `flowGrad … j i`). -/
def amnrBasePlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (n : ℕ)
    (Tm1 : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) (i j k : Fin 2) : ℝ :=
  -I.LMN κm m n t *
    ∑' l : ℤ, I.hatXiML m l t *
      (I.flowGrad hΦ m l t x j i *
        ∑ p : Fin 2, I.flowGrad hΦ m l t x k p * spaceGrad (Tm1 t) x p)

/-- The corrected-form forcing error `d⁺`, the corrected formulation (9) and the §9.4 body. -/
def sourceErrorDPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  (∑' l : ℤ, I.hatXiML m l t •
    ((I.flowGrad hΦ m l t x).transpose.mulVec
      ((I.Jhat κm m t - I.flux κm m t).mulVec
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))) +
  (fun i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
    I.Amnr hΦ m κm n T (Jcut β) t x i j k *
      I.qMNR κm m n (Jcut β) t j k)

/-- The coarse transport flux `V_tr = Σ_l ξ̂_l [κ F_l + F_lᵀ P F_l] ∇T`, `P = 𝒥 - κ`
(the corrected formulation (34)). -/
def transportFluxPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' l : ℤ, I.hatXiML m l t •
    ((κm • I.flowGrad hΦ m l t x +
      (I.flowGrad hΦ m l t x).transpose *
        (I.flux κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))

/-- `twistie3⁺ = -div Σ_k ξ_k p_k σ (∇T - G_k)`. -/
def twistie3Plus (hΦ : IsStreamSeq I Φ) (m : ℕ) (_κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -vecDiv (fun y => ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • (selCoeff I hΦ m k t y • sigmaMat).mulVec
      (spaceGrad (T t) y - G I hΦ m T (lIdx β I.Λ m k) t y)) x

/-- `twistie4⁺ = -div Σ_k ξ_k D_k G_k`, `D_k = κ (Q_k - I) B_k`. -/
def twistie4Plus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -vecDiv (fun y => ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • (correctorDefectMatrix I hΦ m k t κm y).mulVec
      (G I hΦ m T (lIdx β I.Λ m k) t y)) x

/-- `twistie5⁺ = -div Σ_k ξ_k E_k G_k`, `E_k = (I - F_kᵀ)(p_k σ + κ B_k)`. -/
def twistie5Plus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -vecDiv (fun y => ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • (correctorPushforwardMatrix I hΦ m k t κm y).mulVec
      (G I hΦ m T (lIdx β I.Λ m k) t y)) x

/-- `normie3⁺ = Σ_k ξ_k F_kᵀ (𝒥 - C⁰_k) : ∇G_k`. Its fast factor `𝒥 - C⁰_k` has
exact zero cell mean (the corrected formulation §7). -/
def normie3Plus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t * frob
      ((flowGradK I hΦ m k t x).transpose *
        (I.flux κm m t - cellFlux I hΦ m κm k t x))
      (gradG I hΦ m T (lIdx β I.Λ m k) t x)

/-- The literal-name normie3 of the corrected formulation (36) and §9.4:
`N_sel⁺ = Σ_k ξ_k (κ I + F_kᵀ P - C_k) : ∇G_k`. -/
def normie3Sel (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t * frob
      (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (flowGradK I hΦ m k t x).transpose *
          (I.flux κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
        correctorFlux I hΦ m κm k t x)
      (gradG I hΦ m T (lIdx β I.Λ m k) t x)

/-- The molecular divergence `𝓜 = div(κ Σ_k ξ_k (F_k - I) ∇T)`, the corrected formulation (37). -/
def molecular (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  vecDiv (fun y => κm • ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • ((flowGradK I hΦ m k t y - 1).mulVec (spaceGrad (T t) y))) x

/-- The nine terms in the literal-name split (36): the names, with `normie3`
replaced by `normie3Sel` (§9.4). -/
def nineTermsSel (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : ℝ :=
  cutoff1 I hΦ m κm T t x +
  twistie1 I hΦ m κm T t x +
  twistie3 I hΦ m κm T t x +
  twistie4ND I hΦ m κm T t x +
  twistie5ND I hΦ m κm T t x +
  normie1 I hΦ m κm T t x +
  normie2 I hΦ m κm T t x +
  tiny I hΦ m κm d e t x +
  normie3Sel I hΦ m κm T t x

/-- The nine revised terms of the corrected formulation §7 table, in the slot order
(`cutoff1, twistie1, twistie3, twistie4, twistie5, normie1, normie2, tiny, normie3`). -/
def nineTermsPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : ℝ :=
  cutoff1 I hΦ m κm T t x +
  twistie1 I hΦ m κm T t x +
  twistie3Plus I hΦ m κm T t x +
  twistie4Plus I hΦ m κm T t x +
  twistie5Plus I hΦ m κm T t x +
  normie1 I hΦ m κm T t x +
  normie2 I hΦ m κm T t x +
  tiny I hΦ m κm d e t x +
  normie3Plus I hΦ m κm T t x

/-- The literal-name corrected-form residual identity (36). -/
def residualIdentitySel (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2)
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : Prop :=
  advDiffOp b κm (I.ansatz hΦ m κm T) t x =
    nineTermsSel I hΦ m κm T d e t x + R46 I hΦ m κm T t x

/-- The repaired corrected-form residual identity (38): nine revised terms, `R46` and `𝓜`. -/
def residualIdentityPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2)
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : Prop :=
  advDiffOp b κm (I.ansatz hΦ m κm T) t x =
    nineTermsPlus I hΦ m κm T d e t x + R46 I hΦ m κm T t x +
      molecular I hΦ m κm T t x

/-! ### Identifications

The candidates are the Section 4 and Section 5 objects, definitionally. -/

theorem sMat_eq_sMatPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (t : ℝ) (x : Vec 2) :
    I.sMat hΦ m κm t x = sMatPlus I hΦ m κm t x := rfl

theorem Amnr_zero_eq_amnrBasePlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (n : ℕ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) (i j k : Fin 2) :
    I.Amnr hΦ m κm n T 0 t x i j k = amnrBasePlus I hΦ m κm n T t x i j k := rfl

theorem twistie4Plus_eq_twistie4 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    twistie4Plus I hΦ m κm T t x = twistie4 I hΦ m κm T t x := rfl

theorem twistie5Plus_eq_twistie5 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    twistie5Plus I hΦ m κm T t x = twistie5 I hΦ m κm T t x := by
  simp only [twistie5Plus, twistie5, correctorPushforwardMatrix, correctorBaseMatrix,
    flowGradK, Ingredients.zetaProd]

theorem normie3Plus_eq_normie3 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    normie3Plus I hΦ m κm T t x = normie3 I hΦ m κm T t x := rfl

end AVenhance.Infra.Section5.LeftJacobian

end
