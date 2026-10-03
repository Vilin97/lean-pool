/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMKCorrector
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TransportCalculus

/-! Source transport identities for fields pulled back by the flow. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem TransportIdentities.frozen_inverse_flow_left
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (r : ℝ) (y : Vec 2) :
    I.xFlowInv hΦ m l r (I.xFlow hΦ m l r y) = y := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  have hX : IsFlow b X := by
    exact flow_isFlow b (hΦ.adm_pred m).vel_continuous
      (hΦ.adm_pred m).vel_lipschitz
  change X s (X r y s) r = y
  calc
    X s (X r y s) r = X s y s :=
      Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hX y s r s
    _ = y := hX.1 y s

theorem TransportIdentities.frozen_inverse_flow_right
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (r : ℝ) (y : Vec 2) :
    I.xFlow hΦ m l r (I.xFlowInv hΦ m l r y) = y := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  have hX : IsFlow b X := by
    exact flow_isFlow b (hΦ.adm_pred m).vel_continuous
      (hΦ.adm_pred m).vel_lipschitz
  change X r (X s y r) s = y
  calc
    X r (X s y r) s = X r y r :=
      Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hX y r s r
    _ = y := hX.1 y r

theorem TransportIdentities.chiMK_joint_contDiff_one
    (κ : ℝ) (m : ℕ) (k : ℤ) :
    ContDiff ℝ 1
      (Function.uncurry fun r y => I.chiMK κ m k r y) := by
  change ContDiff ℝ 1 (fun p : ℝ × Vec 2 => I.chiMK κ m k p.1 p.2)
  apply contDiff_pi.2
  intro j
  exact (Infra.Section3.chiMK_component_contDiff_two I κ k j).of_le
    (by norm_num)

/-- With the inverse slice regularity derived from the flow, transport
of the single-mode corrector is exactly the source identity
`e.tbm1.one` (at a fixed spatial point and coordinate). -/
theorem chiTilde_material_transport_component
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) (i : Fin 2) :
    deriv (fun r => I.chiTilde hΦ m κ k r x i) t +
      fderiv ℝ (I.chiTilde hΦ m κ k t) x
        (streamVel (Φ (m - 1)) t x) i =
      deriv (fun r => I.chiMK κ m k r
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) i) t := by
  let l := lIdx β I.Λ m k
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let F : ℝ → Vec 2 → Vec 2 := fun r y => I.chiMK κ m k r y
  let Z : ℝ → Vec 2 → Vec 2 := fun r y => I.xFlowInv hΦ m l r y
  let L : (ℝ × Vec 2) →L[ℝ] Vec 2 :=
    fderiv ℝ (Function.uncurry F) (t, Z t x)
  have hF : HasFDerivAt (Function.uncurry F) L (t, Z t x) := by
    exact ((TransportIdentities.chiMK_joint_contDiff_one I κ m k).differentiable
      (by norm_num) (t, Z t x)).hasFDerivAt
  have hZ : HasFDerivAt (Function.uncurry Z)
      (fderiv ℝ (Function.uncurry Z) (t, x)) (t, x) := by
    exact xFlowInv_hasFDerivAt I hΦ m l t x
  have hX : IsFlow b X := by
    exact flow_isFlow b (hΦ.adm_pred m).vel_continuous
      (hΦ.adm_pred m).vel_lipschitz
  have hleft : ∀ r y, Z r (X r y ((l : ℝ) * tauPP β I.Λ m)) = y := by
    intro r y
    simpa [Z, X, b, Ingredients.xFlow, Ingredients.xFlowInv,
      AVenhance.flowInv, l] using TransportIdentities.frozen_inverse_flow_left I hΦ m l r y
  have hright : ∀ r y, X r (Z r y) ((l : ℝ) * tauPP β I.Λ m) = y := by
    intro r y
    simpa [Z, X, b, Ingredients.xFlow, Ingredients.xFlowInv,
      AVenhance.flowInv, l] using TransportIdentities.frozen_inverse_flow_right I hΦ m l r y
  have htransport := inverse_flow_transport_comp_apply
    (F := F) (Z := Z) (X := X) (b := b)
    (s := (l : ℝ) * tauPP β I.Λ m) (t := t) (x := x)
    (L := L) (M := fderiv ℝ (Function.uncurry Z) (t, x))
    hF hZ hX hleft hright i
  have hcurve : HasDerivAt (fun r : ℝ => (r, Z t x))
      (1, (0 : Vec 2)) t := by
    exact (hasDerivAt_id t).prodMk (hasDerivAt_const t (Z t x))
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let Fi : ℝ → Vec 2 → ℝ := fun r y => F r y i
  let Li : (ℝ × Vec 2) →L[ℝ] ℝ := P.comp L
  have hFi : HasFDerivAt (Function.uncurry Fi) Li (t, Z t x) := by
    have hproj : HasFDerivAt (fun y : Vec 2 => y i)
        P (F t (Z t x)) := by
      change HasFDerivAt (fun y => P y) P (F t (Z t x))
      exact P.hasFDerivAt
    have h := hproj.comp (t, Z t x) hF
    change HasFDerivAt (fun p : ℝ × Vec 2 => F p.1 p.2 i)
      (P.comp L) (t, Z t x)
    exact h
  let J : Vec 2 →L[ℝ] ℝ × Vec 2 :=
    (0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))
  have hpair : HasFDerivAt (fun y : Vec 2 => (t, y)) J x := by
    exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hZspace : HasFDerivAt (Z t)
      ((fderiv ℝ (Function.uncurry Z) (t, x)).comp J) x := by
    have h := hZ.comp x hpair
    simpa [Z, J, Function.uncurry, Function.comp_def] using h
  let JZ : Vec 2 →L[ℝ] ℝ × Vec 2 :=
    (0 : Vec 2 →L[ℝ] ℝ).prod
      ((fderiv ℝ (Function.uncurry Z) (t, x)).comp J)
  have hpull : HasFDerivAt (fun y : Vec 2 => (t, Z t y)) JZ x := by
    exact (hasFDerivAt_const t x).prodMk hZspace
  have hFspace : HasFDerivAt (fun y => F t (Z t y)) (L.comp JZ) x := by
    have h := hF.comp x hpull
    simpa [F, Function.uncurry, Function.comp_def] using h
  have hcoordFDeriv := fderiv_apply hFspace.differentiableAt i
  have hcoordEval :
      fderiv ℝ (fun y => F t (Z t y) i) x (b t x) =
        (fderiv ℝ (fun y => F t (Z t y)) x (b t x)) i := by
    have h := congrArg (fun D : Vec 2 →L[ℝ] ℝ => D (b t x)) hcoordFDeriv
    simpa [P, ContinuousLinearMap.comp_apply] using h
  have hpartial := deriv_uncurry_comp (F := Fi) hFi hcurve
  have hcoordEval' :
      fderiv ℝ (fun y => I.chiTilde hΦ m κ k t y i) x (b t x) =
        (fderiv ℝ (I.chiTilde hΦ m κ k t) x (b t x)) i := by
    change fderiv ℝ (fun y => I.chiMK κ m k t
        (I.xFlowInv hΦ m l t y) i) x (b t x) =
      (fderiv ℝ (fun y => I.chiMK κ m k t
        (I.xFlowInv hΦ m l t y)) x (b t x)) i
    exact hcoordEval
  have htransport'' :
      deriv (fun r => I.chiTilde hΦ m κ k r x i) t +
        fderiv ℝ (fun y => I.chiTilde hΦ m κ k t y i) x (b t x) =
      L (1, (0 : Vec 2)) i := by
    simpa [F, Z, l, Ingredients.chiTilde] using htransport
  have htransport' :
      deriv (fun r => I.chiTilde hΦ m κ k r x i) t +
        fderiv ℝ (I.chiTilde hΦ m κ k t) x (b t x) i =
      L (1, (0 : Vec 2)) i := by
    rw [← hcoordEval']
    exact htransport''
  have hpartial' :
      deriv (fun r => I.chiMK κ m k r
        (I.xFlowInv hΦ m l t x) i) t = L (1, (0 : Vec 2)) i := by
    simpa [Fi, Li, P, F, Z, Function.uncurry] using hpartial
  rw [htransport', hpartial']

end AVenhance.Infra.Section5
