/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PulledGradientIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MaterialGradient

/-! Fixed-point material form of the pulled-gradient transport identity. -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance Infra.Flow

/-- The transported gradient of the last iterate obeys the source's
fixed-point material identity. This is `e.tbm1.two` after changing from a
characteristic to its fixed spatial point. -/
theorem final_iterate_pulled_gradient_material_transport
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (l : ℤ) {t : ℝ} (ht : 0 < t) (x : Vec 2) (j : Fin 2)
    {L : (ℝ × Vec 2) →L[ℝ] Vec 2}
    (hG : HasFDerivAt
      (Function.uncurry fun r y => G I hΦ m (T (Nstar β)) l r y)
      L (t, x)) :
    deriv (fun r => G I hΦ m (T (Nstar β)) l r x j) t +
      fderiv ℝ (G I hΦ m (T (Nstar β)) l t) x
        (streamVel (Φ (m - 1)) t x) j =
      (I.flowGrad hΦ m l t x).mulVec
        (gradDiv (fun r y =>
          (I.Kmat κm m r + I.sMat hΦ m κm r y).mulVec
            (spaceGrad (T (Nstar β) r) y) +
          iterateError I hΦ m κm κprev T r y)
          t x) j := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ (m - 1))
  let X : ℝ → Vec 2 → ℝ → Vec 2 := flow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s : ℝ := (l : ℝ) * tauPP β I.Λ m
  let y : Vec 2 := I.xFlowInv hΦ m l t x
  have hX : IsFlow b X :=
    flow_isFlow b (hΦ.adm_pred m).vel_continuous
      (hΦ.adm_pred m).vel_lipschitz
  have hpath : I.xFlow hΦ m l t y = x := by
    change X t (X s x t) s = x
    calc
      X t (X s x t) s = X t x t :=
        Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hX x t s t
      _ = x := hX.1 x t
  have hpathX : X t y s = x := by
    simpa [y, X, s, Ingredients.xFlow] using hpath
  let g : ℝ → Vec 2 → ℝ := fun r z => G I hΦ m (T (Nstar β)) l r z j
  have hgj : HasFDerivAt (Function.uncurry g)
      ((ContinuousLinearMap.proj j).comp L) (t, x) := by
    have h := (ContinuousLinearMap.proj j).hasFDerivAt.comp (t, x) hG
    change HasFDerivAt (fun p : ℝ × Vec 2 =>
      G I hΦ m (T (Nstar β)) l p.1 p.2 j)
      ((ContinuousLinearMap.proj j).comp L) (t, x)
    exact h
  have hgSlice : HasFDerivAt (G I hΦ m (T (Nstar β)) l t)
      (L.comp ((0 : Vec 2 →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (Vec 2)))) x := by
    have hpair : HasFDerivAt (fun z : Vec 2 => (t, z))
        ((0 : Vec 2 →L[ℝ] ℝ).prod
          (ContinuousLinearMap.id ℝ (Vec 2))) x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    have h := hG.comp x hpair
    simpa [Function.uncurry, Function.comp_def] using h
  have hcoord (v : Vec 2) :
      fderiv ℝ (G I hΦ m (T (Nstar β)) l t) x v j =
        fderiv ℝ (fun z => g t z) x v := by
    rw [fderiv_apply hgSlice.differentiableAt j]
    rfl
  have hdot : vecDot (streamVel (Φ (m - 1)) t x)
      (spaceGrad (fun z => g t z) x) =
      fderiv ℝ (G I hΦ m (T (Nstar β)) l t) x
        (streamVel (Φ (m - 1)) t x) j := by
    rw [hcoord]
    rw [fderiv_scalar_eq_sum_spaceGrad]
    simp [vecDot]
  have hmat := materialDerivative_eq_advective_of_hasFDerivAt
    (T := g) (b := b) hgj
  have hfixed : deriv (fun r => g r x) t +
      fderiv ℝ (G I hΦ m (T (Nstar β)) l t) x (b t x) j =
      materialDerivative g b t x := by
    rw [hmat, hdot]
  have hgjF : HasFDerivAt (Function.uncurry g)
      (fderiv ℝ (Function.uncurry g) (t, x)) (t, x) := by
    convert hgj using 1
    exact hgj.fderiv
  have hgjAtPath : HasFDerivAt (Function.uncurry g)
      (fderiv ℝ (Function.uncurry g) (t, X t y s)) (t, X t y s) := by
    simpa only [hpathX] using hgjF
  have hchar := deriv_comp_flow_eq_materialDerivative
    (T := g) (b := b) (X := X) (t := t) (s := s) (y := y) hX hgjAtPath
  have htransport := final_iterate_pulled_gradient_transport I hΦ m hm
    κm κprev θ₀ θprev T hT l ht y j
  have htransport' :
      deriv (fun r => g r (X r y s)) t =
        (I.flowGrad hΦ m l t x).mulVec
          (gradDiv (fun r z =>
            (I.Kmat κm m r + I.sMat hΦ m κm r z).mulVec
              (spaceGrad (T (Nstar β) r) z) +
            iterateError I hΦ m κm κprev T r z)
            t x) j := by
    simpa [g, b, X, s, Ingredients.xFlow, hpathX] using htransport
  calc
    deriv (fun r => G I hΦ m (T (Nstar β)) l r x j) t +
        fderiv ℝ (G I hΦ m (T (Nstar β)) l t) x (b t x) j =
        materialDerivative g b t x := by simpa [g] using hfixed
    _ = deriv (fun r => g r (X r y s)) t := by
      simpa [hpathX] using hchar.symm
    _ = _ := htransport'

end AVenhance.Infra.Section5

end
