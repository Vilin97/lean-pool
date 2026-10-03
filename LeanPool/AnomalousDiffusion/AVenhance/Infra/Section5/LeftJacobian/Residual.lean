/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Candidate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.SourceMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.AnsatzMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Regroup
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.NamedDiffusionExpansion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualR46
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.DivergenceLinearity

/-!: the end-to-end residual identity for the names.

This mirrors `Section5/ResidualCompletion.lean` (`frozen_source_residual_identity`) with the
corrected-form pieces switched in:

* `variantA_source_material_equation` (source transport equation with `V_tr` and `d⁺`),
* `variantA_ansatz_material_equation_of_source` (source-generic ansatz material equation),
* the unchanged named diffusion expansion,
* `variantA_residual_identity_sel_of_expansions` (literal-name identity (36)),
* `residualIdentityPlus_of_sel` (repaired identity (38), needs `T t` smooth).

Now the `I.sMat`, `I.Amnr · 0` are the corrected-form bodies by `rfl`
(`sMat_eq_sMatPlus`, `Amnr_zero_eq_amnrBasePlus`); the former switch-later hypotheses are gone.
`frozen_variantA_source_residual_identity` states the result with the slot names. -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Pointwise calculus data for the corrected-form source residual. The fields are those of
`FrozenResidualPointwiseData` that remain needed, with the corrected-form replacements:
`hAvg` is derived from `hVecGlobal`/`hIterateGlobal` (via `sMat_eq_sMatPlus`), `hTail`/`hBase` feed
the source material equation, `hr46`/`hDE` feed the divergence split of `V_tr + d⁺ + e`,
`hSmooth` gives the `C¹` regularity of `T t` and the regrouping (36) → (38), and `hTx`,
`hHx`, `hG` are derived from the global/odd-support derivative fields. -/
structure ResidualPointwiseData
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev : ℝ) (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) where
  /-- Time derivatives of the Hm recursion terms at the residual evaluation point. -/
  Dt : ℕ → ℝ
  /-- Spatial differentials of the Hm recursion terms at the residual evaluation point. -/
  LHm : ℕ → Vec 2 →L[ℝ] ℝ
  hDt : ∀ r ∈ Finset.range (Jcut β),
    HasDerivAt (fun s => I.Hmr hΦ m κm (T (Nstar β)) r s x) (Dt r) t
  hDx : ∀ r ∈ Finset.range (Jcut β),
    HasFDerivAt (I.Hmr hΦ m κm (T (Nstar β)) r t) (LHm r) x
  hA : ∀ r ∈ Finset.range (Jcut β),
    ∀ (n : ℕ) (i j k : Fin 2) (z : ST), 0 < z.1 →
      DifferentiableAt ℝ
        (fun w : ST => I.Amnr hΦ m κm n (T (Nstar β)) r w.1 w.2 i j k) z
  hPair : ∀ r ∈ Finset.range (Jcut β), ∀ (a : AmnrPairIndex)
    (z : ST), 0 < z.1 →
    DifferentiableAt ℝ
      (amnrPairFlux I hΦ m κm (T (Nstar β)) r a) z
  hFlux : ∀ r ∈ Finset.range (Jcut β), ContDiffAt ℝ 2
    (amnrPairFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) r) (t, x)
  hEndNext : ∀ r ∈ Finset.range (Jcut β),
    DifferentiableAt ℝ
      (amnrPairEndpointFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) (r + 1))
      (t, x)
  hEnd : ∀ r ∈ Finset.range (Jcut β),
    DifferentiableAt ℝ
      (amnrPairEndpointFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) r) (t, x)
  hTail : DifferentiableAt ℝ
    (terminalTail I hΦ m κm (T (Nstar β)) t) x
  hBase : DifferentiableAt ℝ
    (fun y => ∑' l : ℤ, I.hatXiML m l t •
      ((I.flowGrad hΦ m l t y).transpose.mulVec
        ((I.Jhat κm m t - I.Kmat κm m t).mulVec
          ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T (Nstar β) t) y))))) x
  hTtime : HasDerivAt (fun s => T (Nstar β) s x)
    (deriv (fun s => T (Nstar β) s x) t) t
  hHtime : HasDerivAt (fun s => I.Hm hΦ m κm (T (Nstar β)) s x)
    (deriv (fun s => I.Hm hΦ m κm (T (Nstar β)) s x) t) t
  hXi : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
    HasDerivAt (I.xiMK m k) (deriv (I.xiMK m k) t) t
  /-- Joint time-space differentials of the transported corrector components. -/
  Lχ : ℤ → (ℝ × Vec 2) →L[ℝ] Vec 2
  /-- Joint time-space differentials of the transported temperature gradients. -/
  LG : ℤ → (ℝ × Vec 2) →L[ℝ] Vec 2
  hChiJoint : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
    HasFDerivAt (Function.uncurry fun s y => I.chiTilde hΦ m κm k s y)
      (Lχ k) (t, x)
  hGJoint : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
    HasFDerivAt (Function.uncurry fun s y =>
      G I hΦ m (T (Nstar β)) (lIdx β I.Λ m k) s y) (LG k) (t, x)
  hr46 : DifferentiableAt ℝ (r46Flux I hΦ m κm (T (Nstar β)) t) x
  hDE : DifferentiableAt ℝ
    (fun y => sourceErrorDPlus I hΦ m κm (T (Nstar β)) t y +
      iterateError I hΦ m κm κprev T t y) x
  hSmooth : ContDiff ℝ ∞ (T (Nstar β) t)
  hHGlobal : ∀ y, HasFDerivAt (I.Hm hΦ m κm (T (Nstar β)) t)
    (fderiv ℝ (I.Hm hΦ m κm (T (Nstar β)) t) y) y
  hChiGlobal : ∀ k ∈ (I.xiMK_support_finite m t).toFinset, ∀ y,
    HasFDerivAt (I.chiTilde hΦ m κm k t)
      (fderiv ℝ (I.chiTilde hΦ m κm k t) y) y
  hGGlobal : ∀ k ∈ (I.xiMK_support_finite m t).toFinset, ∀ y,
    HasFDerivAt (fun z => G I hΦ m (T (Nstar β)) (lIdx β I.Λ m k) t z)
      (fderiv ℝ (fun z => G I hΦ m (T (Nstar β))
        (lIdx β I.Λ m k) t z) y) y
  hCorrectorFlux : ∀ q ∈
      (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
      ∀ i j, HasFDerivAt
        (fun y => correctorFlux I hΦ m κm q.1 t y i j)
        (fderiv ℝ (fun y => correctorFlux I hΦ m κm q.1 t y i j) x) x
  hGodd : ∀ q : {k : ℤ // Odd k}, HasFDerivAt
    (fun y => G I hΦ m (T (Nstar β)) (lIdx β I.Λ m q.1) t y)
    (fderiv ℝ (fun y => G I hΦ m (T (Nstar β))
      (lIdx β I.Λ m q.1) t y) x) x
  /-- Spatial differential of the diffusion-weighted gradient mismatch. -/
  LM : Vec 2 →L[ℝ] Vec 2
  /-- Spatial differential of the cutoff-weighted corrector gradient flux. -/
  LC : Vec 2 →L[ℝ] Vec 2
  /-- Spatial differential of the Hm flux contribution to the residual. -/
  LHflux : Vec 2 →L[ℝ] Vec 2
  hMismatch : HasFDerivAt (fun y =>
    (diffusionMatrix I hΦ m κm t y).mulVec
      (spaceGrad (T (Nstar β) t) y -
        ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
          I.xiMK m q.1 t •
            G I hΦ m (T (Nstar β)) (lIdx β I.Λ m q.1) t y)) LM x
  hChiFlux : HasFDerivAt (fun y =>
    ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
      I.xiMK m q.1 t •
        (diffusionMatrix I hΦ m κm t y).mulVec
          (chiGradG I hΦ m κm (T (Nstar β)) q.1 t y)) LC x
  hHmFlux : HasFDerivAt (fun y =>
    (diffusionMatrix I hΦ m κm t y).mulVec
      (spaceGrad (I.Hm hΦ m κm (T (Nstar β)) t) y)) LHflux x
  hVecGlobal : ∀ y, DifferentiableAt ℝ (fun z =>
    (I.Kmat κm m t + I.sMat hΦ m κm t z).mulVec
      (spaceGrad (T (Nstar β) t) z)) y
  hIterateGlobal : ∀ y, DifferentiableAt ℝ
    (fun z => iterateError I hΦ m κm κprev T t z) y
  hVecDiv : DifferentiableAt ℝ (fun y => vecDiv (fun z =>
    (I.Kmat κm m t + I.sMat hΦ m κm t z).mulVec
      (spaceGrad (T (Nstar β) t) z)) y) x
  hIterateDiv : DifferentiableAt ℝ (fun y => vecDiv
    (fun z => iterateError I hΦ m κm κprev T t z) y) x
  hAnsatz : ContDiffAt ℝ 2 (I.ansatz hΦ m κm (T (Nstar β)) t) x

theorem Residual.spaceGrad_add_residual'
    {f g : Vec 2 → ℝ} {x : Vec 2}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    spaceGrad (fun y => f y + g y) x = spaceGrad f x + spaceGrad g x := by
  funext i
  change fderiv ℝ (f + g) x (basisVec i) = _
  rw [fderiv_add hf hg]
  simp [spaceGrad]

/-- **corrected-form literal-name residual identity (36)** for the names, given the
pointwise calculus data (`sMat`, `Amnr`). -/
theorem variantA_source_residual_identity_sel
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (R : ResidualPointwiseData I hΦ m hm κm κprev θ₀ θprev T hT
      t ht x ρ hρ) :
    residualIdentitySel I hΦ m κm (T (Nstar β))
      (sourceErrorDPlus I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) (streamVel (Φ m)) t x := by
  classical
  let Tlast : ℝ → Vec 2 → ℝ := T (Nstar β)
  let S := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hpartition : ∑ q ∈ S, I.xiMK m q.1 t = 1 :=
    sum_xiMK_odd_support I m hm t
  have hT1 : ContDiff ℝ 1 (Tlast t) := R.hSmooth.of_le (by exact_mod_cast le_top)
  have hTglobal : ∀ y, HasFDerivAt (Tlast t) (fderiv ℝ (Tlast t) y) y := fun y =>
    (R.hSmooth.differentiable (by simp) y).hasFDerivAt
  have hAvg : DifferentiableAt ℝ
      (fun y => (I.Kmat κm m t + sMatPlus I hΦ m κm t y).mulVec
          (spaceGrad (T (Nstar β) t) y) +
        iterateError I hΦ m κm κprev T t y) x := by
    have h := (R.hVecGlobal x).fun_add (R.hIterateGlobal x)
    simpa only [sMat_eq_sMatPlus] using h
  have hsrc := variantA_source_material_equation I hΦ m hm κm κprev θ₀ θprev T hT
    t ht x R.Dt R.LHm R.hDt R.hDx R.hA R.hPair R.hFlux R.hEndNext
    R.hEnd hAvg R.hTail R.hBase
  have hmaterial := variantA_ansatz_material_equation_of_source I hΦ m hm κm κprev
    θ₀ θprev T hT t ht x ρ hρ (fderiv ℝ (Tlast t) x)
    (fderiv ℝ (I.Hm hΦ m κm Tlast t) x) R.hTtime R.hHtime R.hXi (hTglobal x)
    (R.hHGlobal x) R.Lχ R.LG R.hChiJoint R.hGJoint _ hsrc
  have hdiffusion := frozen_ansatz_diffusion_named_expansion I hΦ m hm κm
    Tlast t x hTglobal R.hHGlobal R.hChiGlobal R.hGGlobal R.hCorrectorFlux
    (fun q hq => R.hGodd q) R.hMismatch R.hChiFlux R.hHmFlux
  have hdiffusion' :
      vecDiv (fun y => (diffusionMatrix I hΦ m κm t y).mulVec
          (spaceGrad (I.ansatz hΦ m κm Tlast t) y)) x =
        (∑ q ∈ S, I.xiMK m q.1 t *
          vecDot (matDiv (correctorDefectMatrix I hΦ m q.1 t κm) x)
            (G I hΦ m Tlast (lIdx β I.Λ m q.1) t x)) +
        (∑ q ∈ S, I.xiMK m q.1 t *
          vecDot (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κm) x)
            (G I hΦ m Tlast (lIdx β I.Λ m q.1) t x)) +
        (∑ q ∈ S, I.xiMK m q.1 t *
          frob (correctorFlux I hΦ m κm q.1 t x)
            (gradG I hΦ m Tlast (lIdx β I.Λ m q.1) t x)) +
        (∑ q ∈ S, I.xiMK m q.1 t *
          vecDot (fun j => deriv (fun s => I.chiMK κm m q.1 s
            (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
            (G I hΦ m Tlast (lIdx β I.Λ m q.1) t x)) -
        twistie3 I hΦ m κm Tlast t x - normie1 I hΦ m κm Tlast t x -
          normie2 I hΦ m κm Tlast t x := by
    simpa [mul_add, Finset.sum_add_distrib, gradG, AVenhance.gradMatrix] using
      hdiffusion
  have hgradDivSplit :
      gradDiv (fun s y =>
        (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
            (spaceGrad (Tlast s) y) + iterateError I hΦ m κm κprev T s y)
          t x =
        gradDiv (fun s y =>
          (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
              (spaceGrad (Tlast s) y)) t x +
          gradDiv (iterateError I hΦ m κm κprev T) t x := by
    have hdiv : ∀ y, vecDiv (fun z =>
        (I.Kmat κm m t + I.sMat hΦ m κm t z).mulVec
            (spaceGrad (Tlast t) z) + iterateError I hΦ m κm κprev T t z) y =
        vecDiv (fun z => (I.Kmat κm m t + I.sMat hΦ m κm t z).mulVec
            (spaceGrad (Tlast t) z)) y +
          vecDiv (fun z => iterateError I hΦ m κm κprev T t z) y := by
      intro y
      exact vecDiv_add_of_hasFDerivAt (R.hVecGlobal y).hasFDerivAt
        (R.hIterateGlobal y).hasFDerivAt
    have hfun : (fun y => vecDiv (fun z =>
        (I.Kmat κm m t + I.sMat hΦ m κm t z).mulVec
            (spaceGrad (Tlast t) z) + iterateError I hΦ m κm κprev T t z) y) =
        (fun y => vecDiv (fun z => (I.Kmat κm m t + I.sMat hΦ m κm t z).mulVec
            (spaceGrad (Tlast t) z)) y +
          vecDiv (fun z => iterateError I hΦ m κm κprev T t z) y) := by
      funext y
      exact hdiv y
    change spaceGrad (fun y => vecDiv (fun z =>
        (I.Kmat κm m t + I.sMat hΦ m κm t z).mulVec
            (spaceGrad (Tlast t) z) + iterateError I hΦ m κm κprev T t z) y) x = _
    rw [hfun]
    exact Residual.spaceGrad_add_residual' R.hVecDiv R.hIterateDiv
  exact variantA_residual_identity_sel_of_expansions I hΦ m hm κm Tlast
    (sourceErrorDPlus I hΦ m κm Tlast) (iterateError I hΦ m κm κprev T)
    t x S rfl hpartition hgradDivSplit hmaterial hdiffusion' hT1
    (fun q _ => (R.hGodd q).differentiableAt) R.hr46 R.hDE R.hAnsatz

/-- **corrected-form repaired residual identity (38)** for the names, given the pointwise
calculus data (`sMat`, `Amnr`). -/
theorem variantA_source_residual_identity
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (R : ResidualPointwiseData I hΦ m hm κm κprev θ₀ θprev T hT
      t ht x ρ hρ) :
    residualIdentityPlus I hΦ m κm (T (Nstar β))
      (sourceErrorDPlus I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) (streamVel (Φ m)) t x :=
  residualIdentityPlus_of_sel I hΦ m hm κm (T (Nstar β)) _ _ _ t x R.hSmooth
    (variantA_source_residual_identity_sel I hΦ m hm κm κprev θ₀ θprev T hT
      t ht x ρ hρ R)

/-- **The named-slot Section 5.1 residual identity** (corrected form, ten slot names):
`sourceResidualIdentity` with the slot bodies of `Terms.lean` and the §9.4 `sourceErrorD`. -/
theorem frozen_variantA_source_residual_identity
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (R : ResidualPointwiseData I hΦ m hm κm κprev θ₀ θprev T hT
      t ht x ρ hρ) :
    sourceResidualIdentity I hΦ m κm κprev T t x :=
  (residualIdentity_iff_plus I hΦ m hm κm (T (Nstar β)) _ _ _ t x R.hSmooth).mpr
    (variantA_source_residual_identity I hΦ m hm κm κprev θ₀ θprev T hT t ht x ρ hρ R)

end AVenhance.Infra.Section5.LeftJacobian

end
