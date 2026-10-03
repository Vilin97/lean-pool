/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Ansatz
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.AdvDiffOp
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.SMat

/-! Named terms in the Section 5.1 residual identity. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The flow-pulled gradient `G_l = ∇(T ∘ X_l) ∘ X_l⁻¹`. -/
def G (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (l : ℤ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  spaceGrad (fun y => T t (I.xFlow hΦ m l t y)) (I.xFlowInv hΦ m l t x)

/-- The spatial derivative matrix of `G_l`, with coordinate derivatives in rows. -/
def gradG (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (l : ℤ) (t : ℝ) (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => spaceGrad (fun y => G I hΦ m T l t y j) x i

/-- The scalar coefficient `ψTilde_m` obtained by pulling each `ψ_{m,k}` back
along the `l_k` inverse flow. -/
def psiTilde (hΦ : IsStreamSeq I Φ) (m : ℕ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
      psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)

/-- The diffusion matrix in the ansatz equation. -/
def diffusionMatrix (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (t : ℝ) (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) + psiTilde I hΦ m t x • sigmaMat

/-- The twisted corrector-gradient matrix `∇ΧTilde_{m,k}`. -/
def gradChiTilde (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  gradMatrix (I.chiTilde hΦ m κm k t) x

/-- The `l_k` flow-gradient matrix `∇X_{m-1,l_k} ∘ X⁻¹_{m-1,l_k}`. -/
def flowGradK (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  I.flowGrad hΦ m (lIdx β I.Λ m k) t x

/-- The spatial gradient of the divergence of a vector field. -/
def gradDiv (V : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : Vec 2 :=
  spaceGrad (fun y => vecDiv (V t) y) x

/-- Column-wise divergence of a matrix field: the flux coordinate is
differentiated and the column/corrector index is returned. This is the
convention in the per-corrector flux equation. -/
def matDiv (A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (x : Vec 2) : Vec 2 :=
  fun j => ∑ i : Fin 2, spaceGrad (fun y => A y i j) x i

/-- Frobenius contraction, matching the `:` convention in Section 5.1. -/
def frob (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, A i j * B i j

/-- The centered flow average used in the correction. -/
def Gbar (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' l : ℤ, I.hatXiML m l t • G I hΦ m T l t x

/-- The flux matrix attached to the `k`-th corrector in its cutoff window. -/
def correctorFlux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
        psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) • sigmaMat) *
    (1 + gradChiTilde I hΦ m κm k t x)

/-- `cutoff1`, the time-cutoff derivative term. -/
def cutoff1 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    deriv (I.xiMK m k) t *
      vecDot (I.chiTilde hΦ m κm k t x) (G I hΦ m T (lIdx β I.Λ m k) t x)

/-- `twistie1`, the transport of `T_{m-1}` through the `l_k` flow. -/
def twistie1 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t * vecDot (I.chiTilde hΦ m κm k t x)
      ((flowGradK I hΦ m k t x).mulVec
        (gradDiv (fun s y =>
          (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec (spaceGrad (T s) y))
          t x))

/-- `twistie3` in the `Σ_k ξ_{m,k}` form for the line-2 ansatz.
The source's printed `l`-average is the line-1 hybrid; with the line 2,
the gradient defect is `∇T - G_{l_k}`. Under this slot keeps its body: it is
the repaired `twistie3⁺ = -div Σ_k ξ_k p_k σ (∇T - G_k)` plus the molecular divergence
`𝓜 = div(κ Σ_k ξ_k (F_k - I)∇T)` of the corrected formulation (37) (`LeftJacobian.twistie3_eq`),
    so the ten slot
names are unchanged. -/
def twistie3 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -vecDiv (fun y => ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • (diffusionMatrix I hΦ m κm t y).mulVec
      (spaceGrad (T t) y -
        G I hΦ m T (lIdx β I.Λ m k) t y)) x

/-- `twistie4ND`, the non-divergence inverse-flow corrector-gradient error
`-Σ_k ξ_k G_k · Div D_k`. In the corrected form, `twistie4 = twistie4ND - Σ_k ξ_k D_k : ∇G_k`
(`LeftJacobian.twistie4Plus_eq`). -/
def twistie4ND (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -∑' k : {k : ℤ // Odd k},
    I.xiMK m k t *
      vecDot (G I hΦ m T (lIdx β I.Λ m k) t x)
        (matDiv (fun y => κm •
          ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) y - 1) *
            gradMatrix (fun z => I.chiMK κm m k t z)
              (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) x)

/-- `twistie5ND`, the non-divergence push-forward Jacobian error
`-Σ_k ξ_k G_k · Div E_k` (since `twistie5 = twistie5ND - Σ_k ξ_k E_k : ∇G_k`). The `gradMatrix`
convention stores coordinate derivatives in rows, so the Piola push-forward
acts by the transpose on vector fields. This is the corrected orientation of
the source's `I - ∇X` factor (see
`PushforwardOrientation`). -/
def twistie5ND (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -∑' k : {k : ℤ // Odd k},
    I.xiMK m k t *
      vecDot (G I hΦ m T (lIdx β I.Λ m k) t x)
        (matDiv (fun y =>
          (1 - (flowGradK I hΦ m k t y).transpose) *
            ((I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
                psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) • sigmaMat +
              κm • gradMatrix (fun z => I.chiMK κm m k t z)
                (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) x)

/-- `twistie4` (the corrected formulation §7, `twistie4⁺`): `-div Σ_k ξ_k D_k G_k` with the
inverse-flow corrector defect `D_k = κ (∇Y_{l_k} - I)(∇χ_k ∘ Y_{l_k})`. -/
def twistie4 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -vecDiv (fun y => ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • (κm •
      ((gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) y - 1) *
        gradMatrix (fun z => I.chiMK κm m k t z)
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))).mulVec
      (G I hΦ m T (lIdx β I.Λ m k) t y)) x

/-- `twistie5` (the corrected formulation §7, `twistie5⁺`): `-div Σ_k ξ_k E_k G_k` with the
push-forward Jacobian error `E_k = (I - F_kᵀ)(p_k σ + κ ∇χ_k ∘ Y_{l_k})` (transpose
orientation: see `PushforwardOrientation`). -/
def twistie5 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -vecDiv (fun y => ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • ((1 - (flowGradK I hΦ m k t y).transpose) *
      ((I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
          psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) • sigmaMat +
        κm • gradMatrix (fun z => I.chiMK κm m k t z)
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))).mulVec
      (G I hΦ m T (lIdx β I.Λ m k) t y)) x

/-- The rank-two product `ΧTilde_k ∇G_{l_k}`, contracted as a vector before
applying the diffusion matrix. -/
def chiGradG (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  fun i => ∑ j : Fin 2,
    I.chiTilde hΦ m κm k t x j * gradG I hΦ m T (lIdx β I.Λ m k) t x i j

/-- `normie1`, the corrector times the Hessian term. -/
def normie1 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -vecDiv (fun y => ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t • (diffusionMatrix I hΦ m κm t y).mulVec
      (chiGradG I hΦ m κm T k t y)) x

/-- `normie2`, the diffusion of the `H_m` corrector. -/
def normie2 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  -vecDiv (fun y => (diffusionMatrix I hΦ m κm t y).mulVec
    (spaceGrad (fun z => I.Hm hΦ m κm T t z) y)) x

/-- `tiny`, the residual generated by the two forcing fields. -/
def tiny (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (d e : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : ℝ :=
  vecDiv (fun y => d t y + e t y) x +
    ∑' k : {k : ℤ // Odd k},
      I.xiMK m k t *
        vecDot (I.chiTilde hΦ m κm k t x)
          ((flowGradK I hΦ m k t x).mulVec (gradDiv e t x))

/-- The selected cell coefficient `p_k = ζ̂_{l_k} ζ_k ψ_k ∘ Y_{l_k}` (the corrected formulation
    §7). -/
def selCoeff (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (x : Vec 2) : ℝ :=
  I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
    psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)

/-- The unpulled cell flux `C⁰_k = (κ I + p_k σ)(I + B_k)`, `B_k = (∇χ_k) ∘ Y_{l_k}`
(the corrected formulation §7): the cell flux integrand evaluated at `Y_{l_k}`. -/
def cellFlux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) + selCoeff I hΦ m k t x • sigmaMat) *
    (1 + gradMatrix (fun z => I.chiMK κm m k t z)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

/-- `normie3` (the corrected formulation §7, `normie3⁺`): `Σ_k ξ_k F_kᵀ (𝒥 - C⁰_k) : ∇G_k`. Its fast
factor `𝒥 - C⁰_k` has exact zero cell mean (`LeftJacobian.cellFluxCell_fastFactor_mean_zero`). This
corrects `(𝒥 - C_k) : ∇G_k`, whose slow part misses the left Jacobian. -/
def normie3 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    I.xiMK m k t * frob
      ((flowGradK I hΦ m k t x).transpose *
        (I.flux κm m t - cellFlux I hΦ m κm k t x))
      (gradG I hΦ m T (lIdx β I.Λ m k) t x)

/-- The transition-window remainder in divergence form. -/
def R46 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  vecDiv (fun y => (I.flux κm m t).mulVec
    (∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
      (Gbar I hΦ m T t y - G I hΦ m T (lIdx β I.Λ m k) t y))) x

/-- Sum of the nine residual terms, using the line-2 ansatz. -/
def nineTerms (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : ℝ :=
  cutoff1 I hΦ m κm T t x +
  twistie1 I hΦ m κm T t x +
  twistie3 I hΦ m κm T t x +
  twistie4 I hΦ m κm T t x +
  twistie5 I hΦ m κm T t x +
  normie1 I hΦ m κm T t x +
  normie2 I hΦ m κm T t x +
  tiny I hΦ m κm d e t x +
  normie3 I hΦ m κm T t x

/-- The Section 5.1 target proposition with the named residual terms. The
source-specific theorem establishing it is kept separate from this statement. -/
def residualIdentity (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2)
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : Prop :=
  advDiffOp b κm (I.ansatz hΦ m κm T) t x =
    nineTerms I hΦ m κm T d e t x + R46 I hΦ m κm T t x

end AVenhance.Infra.Section5

end
