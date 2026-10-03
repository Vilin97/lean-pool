/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.CellFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.RegroupSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.DivergenceLinearity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorLocalization
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum

/-!: the literal split (36) implies the repaired split (38).

For `1 ≤ m` and a spatially smooth `T t`, the literal-name nine terms (`twistie3`, `twistie4`,
`twistie5`, `normie3Sel`) differ from the revised nine terms (`twistie3⁺`, `twistie4⁺`,
`twistie5⁺`, `normie3⁺`) exactly by the molecular divergence `𝓜`:

* `twistie4⁺ = twistie4 - Σ_k ξ_k D_k : ∇G_k` and `twistie5⁺ = twistie5 - Σ_k ξ_k E_k : ∇G_k`
  (product rule on `div (A_k G_k)`, over the finite odd support);
* `twistie3 = twistie3⁺ + 𝓜` (`ψTilde = p_k` on `supp ξ_k`, and `κ (∇T - G_k) = -κ (F_k - I) ∇T`);
* `normie3Sel = normie3⁺ - Σ_k ξ_k (D_k + E_k) : ∇G_k` (`normie3Sel_eq`).

The only analytic hypothesis is `ContDiff ℝ ∞ (T t)`; all flow, corrector and cutoff
regularity is discharged from the smoothness lemmas. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-! ### Differentiable calculus helpers -/

theorem differentiableAt_mulVec_of_entries {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {V : Vec 2 → Vec 2} {x : Vec 2}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (hV : DifferentiableAt ℝ V x) :
    DifferentiableAt ℝ (fun y => (A y).mulVec (V y)) x := by
  rw [differentiableAt_pi]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact DifferentiableAt.fun_sum fun j _ => (hA i j).mul ((differentiableAt_pi.1 hV) j)

theorem vecDiv_sub_of_differentiableAt {V W : Vec 2 → Vec 2} {x : Vec 2}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    vecDiv (fun y => V y - W y) x = vecDiv V x - vecDiv W x := by
  unfold vecDiv spaceGrad
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hVi : DifferentiableAt ℝ (fun y => V y i) x :=
    differentiableAt_pi.1 hV i
  have hWi : DifferentiableAt ℝ (fun y => W y i) x :=
    differentiableAt_pi.1 hW i
  change fderiv ℝ ((fun y => V y i) - (fun y => W y i)) x (basisVec i) = _
  rw [fderiv_sub hVi hWi]
  rfl

theorem vecDot_comm' (u v : Vec 2) : vecDot u v = vecDot v u := by
  simp [vecDot, mul_comm]

/-- `∑'` over odd modes with a cutoff factor is the finite sum over the odd support. -/
theorem tsum_xi_mul_eq_sum (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (f : {k : ℤ // Odd k} → ℝ) :
    ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t * f q =
      ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t * f q := by
  simpa [smul_eq_mul] using xiMK_odd_tsum_eq_subtype_support_sum I m hm t f

/-- Product rule for the divergence of `Σ_k ξ_k A_k G_k` over the odd cutoff support. -/
theorem vecDiv_selected_matrix_vec (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    (A : ℤ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Gf : ℤ → Vec 2 → Vec 2) (x : Vec 2)
    (hA : ∀ k i j, DifferentiableAt ℝ (fun y => A k y i j) x)
    (hG : ∀ k, DifferentiableAt ℝ (Gf k) x) :
    vecDiv (fun y => ∑' k : {k : ℤ // Odd k},
        I.xiMK m k t • (A k.1 y).mulVec (Gf k.1 y)) x =
      ∑' k : {k : ℤ // Odd k}, I.xiMK m k t * vecDot (matDiv (A k.1) x) (Gf k.1 x) +
      ∑' k : {k : ℤ // Odd k}, I.xiMK m k t * frob (A k.1 x) (gradMatrix (Gf k.1) x) := by
  classical
  have hfun : (fun y => ∑' k : {k : ℤ // Odd k},
        I.xiMK m k t • (A k.1 y).mulVec (Gf k.1 y)) =
      fun y => ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t • (A q.1 y).mulVec (Gf q.1 y) := by
    funext y
    exact xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun q => (A q.1 y).mulVec (Gf q.1 y))
  have hdiff : ∀ k, DifferentiableAt ℝ (fun y => (A k y).mulVec (Gf k y)) x :=
    fun k => differentiableAt_mulVec_of_entries (hA k) (hG k)
  rw [hfun, vecDiv_finite_weighted_sum
    (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
    (fun q => I.xiMK m q.1 t) (fun q y => (A q.1 y).mulVec (Gf q.1 y)) x
    (LF := fun q => fderiv ℝ (fun y => (A q.1 y).mulVec (Gf q.1 y)) x)
    (fun q _ => (hdiff q.1).hasFDerivAt)]
  rw [tsum_xi_mul_eq_sum I m hm t (fun k => vecDot (matDiv (A k.1) x) (Gf k.1 x)),
    tsum_xi_mul_eq_sum I m hm t (fun k => frob (A k.1 x) (gradMatrix (Gf k.1) x)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hprod := vecDiv_matrixMulVec_frob (A := A q.1) (V := Gf q.1) (x := x)
    (LA := fun i j => fderiv ℝ (fun y => A q.1 y i j) x)
    (fun i j => (hA q.1 i j).hasFDerivAt) (hG q.1).hasFDerivAt
  rw [hprod]
  ring

/-! ### `twistie4⁺` and `twistie5⁺` -/

theorem twistie4Plus_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) (hT : ContDiff ℝ ∞ (T t)) :
    twistie4Plus I hΦ m κm T t x =
      twistie4ND I hΦ m κm T t x -
        ∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
          frob (correctorDefectMatrix I hΦ m k.1 t κm x)
            (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) := by
  unfold twistie4Plus
  rw [vecDiv_selected_matrix_vec I m hm t
    (fun k y => correctorDefectMatrix I hΦ m k t κm y)
    (fun k y => G I hΦ m T (lIdx β I.Λ m k) t y) x
    (fun k i j => ((contDiff_defect_entry I hΦ m κm k t i j).differentiable (by simp)) x)
    (fun k => ((RelativeError.contDiff_G I hΦ m T (lIdx β I.Λ m k) hT).differentiable (by simp)) x)]
  have h4 : twistie4ND I hΦ m κm T t x =
      -∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
        vecDot (matDiv (fun y => correctorDefectMatrix I hΦ m k.1 t κm y) x)
          (G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    unfold twistie4ND
    congr 1
    apply tsum_congr
    intro k
    rw [vecDot_comm']
    rfl
  have hg : ∀ k : {k : ℤ // Odd k}, gradG I hΦ m T (lIdx β I.Λ m k.1) t x =
      gradMatrix (fun y => G I hΦ m T (lIdx β I.Λ m k.1) t y) x := fun k => rfl
  simp only [hg]
  rw [h4]
  ring

theorem twistie5Plus_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) (hT : ContDiff ℝ ∞ (T t)) :
    twistie5Plus I hΦ m κm T t x =
      twistie5ND I hΦ m κm T t x -
        ∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
          frob (correctorPushforwardMatrix I hΦ m k.1 t κm x)
            (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) := by
  unfold twistie5Plus
  rw [vecDiv_selected_matrix_vec I m hm t
    (fun k y => correctorPushforwardMatrix I hΦ m k t κm y)
    (fun k y => G I hΦ m T (lIdx β I.Λ m k) t y) x
    (fun k i j => ((contDiff_pushforward_entry I hΦ m κm k t i j).differentiable
      (by simp)) x)
    (fun k => ((RelativeError.contDiff_G I hΦ m T (lIdx β I.Λ m k) hT).differentiable (by simp)) x)]
  have h5 : twistie5ND I hΦ m κm T t x =
      -∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
        vecDot (matDiv (fun y => correctorPushforwardMatrix I hΦ m k.1 t κm y) x)
          (G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    unfold twistie5ND
    congr 1
    apply tsum_congr
    intro k
    rw [vecDot_comm']
    rfl
  have hg : ∀ k : {k : ℤ // Odd k}, gradG I hΦ m T (lIdx β I.Λ m k.1) t x =
      gradMatrix (fun y => G I hΦ m T (lIdx β I.Λ m k.1) t y) x := fun k => rfl
  simp only [hg]
  rw [h5]
  ring

/-! ### `twistie3 = twistie3⁺ + 𝓜` -/

theorem twistie3_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) (hT : ContDiff ℝ ∞ (T t)) :
    twistie3 I hΦ m κm T t x =
      twistie3Plus I hΦ m κm T t x + molecular I hΦ m κm T t x := by
  classical
  set U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset with hU
  let g : Vec 2 → Vec 2 := fun y => spaceGrad (T t) y
  let pf : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun q y =>
    (selCoeff I hΦ m q.1 t y • sigmaMat).mulVec
      (g y - G I hΦ m T (lIdx β I.Λ m q.1) t y)
  let mf : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun q y =>
    (flowGradK I hΦ m q.1 t y - 1).mulVec (g y)
  let S2 : Vec 2 → Vec 2 := fun y => ∑ q ∈ U, I.xiMK m q.1 t • pf q y
  let S1 : Vec 2 → Vec 2 := fun y => ∑ q ∈ U, I.xiMK m q.1 t • mf q y
  -- the chain rule `G_k = F_k ∇T`
  have hGq : ∀ (k : ℤ) (y : Vec 2), G I hΦ m T (lIdx β I.Λ m k) t y =
      (flowGradK I hΦ m k t y).mulVec (g y) := by
    intro k y
    exact G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t y
      (hT.differentiable (by simp) y).hasFDerivAt
      (((RelativeError.contDiff_xFlow_slice I hΦ m (lIdx β I.Λ m k) t).differentiable (by simp)
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)).hasFDerivAt)
      (RelativeError.xFlow_xFlowInv I hΦ m (lIdx β I.Λ m k) t y)
  -- pointwise decomposition of the twisted diffusion sum
  have hfield : ∀ y, ∑' q : {k : ℤ // Odd k}, I.xiMK m q.1 t •
      (diffusionMatrix I hΦ m κm t y).mulVec
        (spaceGrad (T t) y - G I hΦ m T (lIdx β I.Λ m q.1) t y) =
      S2 y - κm • S1 y := by
    intro y
    rw [xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun q => (diffusionMatrix I hΦ m κm t y).mulVec
        (spaceGrad (T t) y - G I hΦ m T (lIdx β I.Λ m q.1) t y))]
    simp only [S2, S1, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hxi : I.xiMK m q.1 t ≠ 0 :=
      (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mp hq
    have hM : diffusionMatrix I hΦ m κm t y =
        κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) + selCoeff I hΦ m q.1 t y • sigmaMat := by
      change κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) + psiTilde I hΦ m t y • sigmaMat = _
      rw [psiTilde_eq_selected_mode I hΦ m hm q.1 t y q.2 hxi]
      rfl
    have hv : g y - G I hΦ m T (lIdx β I.Λ m q.1) t y =
        -((flowGradK I hΦ m q.1 t y - 1).mulVec (g y)) := by
      rw [hGq q.1 y, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    simp only [pf, mf]
    rw [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv]
    module
  -- identification of the target fields with `S2` and `κ S1`
  have hS2fun : (fun y => ∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
      (selCoeff I hΦ m k t y • sigmaMat).mulVec
        (spaceGrad (T t) y - G I hΦ m T (lIdx β I.Λ m k) t y)) = S2 := by
    funext y
    exact xiMK_odd_tsum_eq_subtype_support_sum I m hm t (fun q => pf q y)
  have hS1fun : (fun y => κm • ∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
      ((flowGradK I hΦ m k t y - 1).mulVec (spaceGrad (T t) y))) = fun y => κm • S1 y := by
    funext y
    rw [xiMK_odd_tsum_eq_subtype_support_sum I m hm t (fun q => mf q y)]
  -- differentiability of the two finite sums
  have hgT : DifferentiableAt ℝ g x :=
    (contDiff_spaceGrad_T hT).differentiable (by simp) x
  have hGd : ∀ k : ℤ, DifferentiableAt ℝ (fun y => G I hΦ m T (lIdx β I.Λ m k) t y) x :=
    fun k => (RelativeError.contDiff_G I hΦ m T (lIdx β I.Λ m k) hT).differentiable (by simp) x
  have hS2 : DifferentiableAt ℝ S2 x := by
    refine DifferentiableAt.fun_sum fun q _ => ?_
    refine DifferentiableAt.fun_const_smul ?_ _
    refine differentiableAt_mulVec_of_entries (fun i j => ?_) (hgT.sub (hGd q.1))
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact ((contDiff_selCoeff I hΦ m q.1 t).differentiable (by simp) x).mul_const _
  have hS1 : DifferentiableAt ℝ (fun y => κm • S1 y) x := by
    refine DifferentiableAt.fun_const_smul (DifferentiableAt.fun_sum fun q _ => ?_) _
    refine DifferentiableAt.fun_const_smul ?_ _
    refine differentiableAt_mulVec_of_entries (fun i j => ?_) hgT
    simp only [Matrix.sub_apply]
    exact ((contDiff_flowGradK_entry I hΦ m q.1 t i j).differentiable (by simp) x).sub_const _
  have hmain : (fun y => ∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
      (diffusionMatrix I hΦ m κm t y).mulVec
        (spaceGrad (T t) y - G I hΦ m T (lIdx β I.Λ m k) t y)) =
      fun y => S2 y - κm • S1 y := funext hfield
  unfold twistie3 twistie3Plus molecular
  rw [hmain, vecDiv_sub_of_differentiableAt hS2 hS1, hS2fun, hS1fun]
  ring

/-! ### The regrouping (36) ⇒ (38) -/

/-- The literal-name nine terms (36) equal the repaired nine terms (38) plus the molecular
divergence `𝓜`. The only hypotheses are `1 ≤ m` and spatial smoothness of `T t`. -/
theorem nineTermsSel_eq_nineTermsPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (hT : ContDiff ℝ ∞ (T t)) :
    nineTermsSel I hΦ m κm T d e t x =
      nineTermsPlus I hΦ m κm T d e t x + molecular I hΦ m κm T t x := by
  have h3 := twistie3_eq I hΦ m hm κm T t x hT
  have h4 := twistie4Plus_eq I hΦ m hm κm T t x hT
  have h5 := twistie5Plus_eq I hΦ m hm κm T t x hT
  have hn := normie3Sel_eq I hΦ m hm κm T t x
  have hsplit : ∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
      (frob (correctorDefectMatrix I hΦ m k.1 t κm x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) +
        frob (correctorPushforwardMatrix I hΦ m k.1 t κm x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x)) =
      ∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
        frob (correctorDefectMatrix I hΦ m k.1 t κm x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) +
      ∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
        frob (correctorPushforwardMatrix I hΦ m k.1 t κm x)
          (gradG I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    rw [tsum_xi_mul_eq_sum I m hm t, tsum_xi_mul_eq_sum I m hm t,
      tsum_xi_mul_eq_sum I m hm t, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold nineTermsSel nineTermsPlus
  rw [hsplit] at hn
  linarith

/-- Literal-name residual identity (36) implies the repaired identity (38). -/
theorem residualIdentityPlus_of_sel (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (b : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (x : Vec 2) (hT : ContDiff ℝ ∞ (T t)) :
    residualIdentitySel I hΦ m κm T d e b t x → residualIdentityPlus I hΦ m κm T d e b t x := by
  intro h
  unfold residualIdentitySel at h
  unfold residualIdentityPlus
  rw [h, nineTermsSel_eq_nineTermsPlus I hΦ m hm κm T d e t x hT]
  ring

/-! ### The named-slot identity

With the slot definitions of `Terms.lean` (`twistie4 = twistie4⁺`, `twistie5 = twistie5⁺`,
`normie3 = normie3⁺`, definitionally) and `twistie3 = twistie3⁺ + 𝓜`, the nine terms are
the repaired nine terms plus `𝓜`. -/

/-- `nineTerms = nineTermsPlus + 𝓜` (the ten slot names carry the repaired split (38)). -/
theorem nineTerms_eq_nineTermsPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (hT : ContDiff ℝ ∞ (T t)) :
    nineTerms I hΦ m κm T d e t x =
      nineTermsPlus I hΦ m κm T d e t x + molecular I hΦ m κm T t x := by
  have h3 := twistie3_eq I hΦ m hm κm T t x hT
  have h5 := twistie5Plus_eq_twistie5 I hΦ m κm T t x
  unfold nineTerms nineTermsPlus
  rw [h3, h5, twistie4Plus_eq_twistie4, normie3Plus_eq_normie3]
  ring

/-- The repaired identity (38) is the named-slot `residualIdentity`. -/
theorem residualIdentity_iff_plus (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (b : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (x : Vec 2) (hT : ContDiff ℝ ∞ (T t)) :
    residualIdentity I hΦ m κm T d e b t x ↔ residualIdentityPlus I hΦ m κm T d e b t x := by
  unfold residualIdentity residualIdentityPlus
  rw [nineTerms_eq_nineTermsPlus I hΦ m hm κm T d e t x hT]
  constructor <;> intro h <;> rw [h] <;> ring

end AVenhance.Infra.Section5.LeftJacobian

end
