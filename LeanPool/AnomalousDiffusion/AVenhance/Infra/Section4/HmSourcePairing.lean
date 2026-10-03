/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmTransportedEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HmBaseFluxIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmSourceIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.BaseFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PulledFluxSmooth

/-! The endpoint difference uses the left-Jacobian Piola base flux and the
`d_m` vector source. -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section4

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)

/-- The terminal endpoint flux at the index, before taking divergence. -/
def hmFrozenTerminalFlux (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : Vec 2 := fun i =>
  ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
    I.Amnr hΦ m κ n T (Jcut β) t x i j k *
      I.qMNR κ m n (Jcut β) t j k

/-- The actual base Piola flux at the zero endpoint. -/
def hmFrozenBaseFlux (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' l : ℤ, I.hatXiML m l t •
    ((I.flowGrad hΦ m l t x).transpose.mulVec
      ((I.Jhat κ m t - I.Kmat κ m t).mulVec
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))

/-- The first (nonterminal) summand of the `d_m` field. -/
def hmFrozenDFirstFlux (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' l : ℤ, I.hatXiML m l t •
    ((I.flowGrad hΦ m l t x).transpose.mulVec
      ((I.Jhat κ m t - I.flux κ m t).mulVec
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))

/-- The Piola flux left after subtracting the first summand of `d_m` from the
zero-endpoint base flux. -/
def hmFrozenRegularFlux (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' l : ℤ, I.hatXiML m l t •
    ((I.flowGrad hΦ m l t x).transpose.mulVec
      ((I.flux κ m t - I.Kmat κ m t).mulVec
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))

/-- The previous source pairing, retained for downstream migration. It is no
longer the scalar source in the endpoint identity. -/
def hmFrozenRegularSource (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  frob (I.flux κ m t - I.Kmat κ m t)
    (gradMatrix (Gbar I hΦ m T t) x)

/-- The actual regular scalar in the endpoint split, the divergence of
the remaining Piola flux. -/
def hmFrozenPiolaSource (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  vecDiv (hmFrozenRegularFlux I hΦ m κ T t) x

theorem HmSourcePairing.hmFrozenBaseFlux_eq_dFirst_add_regular (m : ℕ) (hm : 1 ≤ m)
    (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    hmFrozenBaseFlux I hΦ m κ T t x =
      hmFrozenDFirstFlux I hΦ m κ T t x + hmFrozenRegularFlux I hΦ m κ T t x := by
  classical
  have hbase := LeftJacobian.tsum_hatXiML_smul_eq_sum I m hm t
    (fun l : ℤ => (I.flowGrad hΦ m l t x).transpose.mulVec
      ((I.Jhat κ m t - I.Kmat κ m t).mulVec
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))
  have hfirst := LeftJacobian.tsum_hatXiML_smul_eq_sum I m hm t
    (fun l : ℤ => (I.flowGrad hΦ m l t x).transpose.mulVec
      ((I.Jhat κ m t - I.flux κ m t).mulVec
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))
  have hregular := LeftJacobian.tsum_hatXiML_smul_eq_sum I m hm t
    (fun l : ℤ => (I.flowGrad hΦ m l t x).transpose.mulVec
      ((I.flux κ m t - I.Kmat κ m t).mulVec
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))
  rw [hmFrozenBaseFlux, hmFrozenDFirstFlux, hmFrozenRegularFlux,
    hbase, hfirst, hregular]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← smul_add]
  congr 1
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub]
  abel

theorem HmSourcePairing.hmFrozenSourceErrorD_eq_dFirst_add_tail (m : ℕ) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) :
    sourceErrorD I hΦ m κ T t = fun x =>
      hmFrozenDFirstFlux I hΦ m κ T t x + hmFrozenTerminalFlux I hΦ m κ T t x := by
  rfl

theorem HmSourcePairing.hmFrozenPulledFlux_contDiff (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hT : ContDiff ℝ ∞ (T t)) :
    ContDiff ℝ ∞ (hmFrozenRegularFlux I hΦ m κ T t) := by
  exact LeftJacobian.contDiff_pulledGapFlux I hΦ m hm
    (I.flux κ m t - I.Kmat κ m t) T t hT

theorem HmSourcePairing.hmSource_vecDiv_add_of_differentiableAt
    {V W : Vec 2 → Vec 2} {x : Vec 2}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    vecDiv (fun y => V y + W y) x = vecDiv V x + vecDiv W x := by
  unfold vecDiv spaceGrad
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hVi : DifferentiableAt ℝ (fun y => V y i) x := by
    have h := (ContinuousLinearMap.proj i).differentiableAt.comp x hV
    simpa [Function.comp_def] using h
  have hWi : DifferentiableAt ℝ (fun y => W y i) x := by
    have h := (ContinuousLinearMap.proj i).differentiableAt.comp x hW
    simpa [Function.comp_def] using h
  change fderiv ℝ ((fun y => V y i) + (fun y => W y i)) x
      (basisVec i) = _
  rw [fderiv_add hVi hWi]
  rfl

/-- The exact terminal endpoint is divergence of the terminal `Aq` tail. -/
theorem hm_frozen_terminal_endpoint_eq_div
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    hmEndpoint I hΦ m κ T (Jcut β) t x =
      vecDiv (hmFrozenTerminalFlux I hΦ m κ T t) x := by
  rfl

/-- The finite endpoint difference is the divergence of the Piola
regular source and the new `d_m` vector field. This uses the actual
zero-endpoint base flux, with each `F_l` on both sides of the matrix gap. -/
theorem hm_frozen_endpoint_difference_source_split
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    {t : ℝ} {x : Vec 2}
    (hT : ContDiff ℝ ∞ (T t))
    (hTail : DifferentiableAt ℝ (hmFrozenTerminalFlux I hΦ m κ T t) x) :
    hmEndpoint I hΦ m κ T (Jcut β) t x - hmEndpoint I hΦ m κ T 0 t x =
      hmFrozenPiolaSource I hΦ m κ T t x +
        vecDiv (sourceErrorD I hΦ m κ T t) x := by
  let Base : Vec 2 → Vec 2 := hmFrozenBaseFlux I hΦ m κ T t
  let First : Vec 2 → Vec 2 := hmFrozenDFirstFlux I hΦ m κ T t
  let Regular : Vec 2 → Vec 2 := hmFrozenRegularFlux I hΦ m κ T t
  let Tail : Vec 2 → Vec 2 := hmFrozenTerminalFlux I hΦ m κ T t
  have hBaseEq : Base = fun y => First y + Regular y := by
    funext y
    exact HmSourcePairing.hmFrozenBaseFlux_eq_dFirst_add_regular I hΦ m hm κ T t y
  have hFirstDiff : DifferentiableAt ℝ First x := by
    have hcont := LeftJacobian.contDiff_pulledGapFlux I hΦ m hm
      (I.Jhat κ m t - I.flux κ m t) T t hT
    exact ((hcont.contDiffAt (x := x)).differentiableAt (by norm_num))
  have hRegularDiff : DifferentiableAt ℝ Regular x := by
    have hcont := HmSourcePairing.hmFrozenPulledFlux_contDiff I hΦ m hm κ T t hT
    exact ((hcont.contDiffAt (x := x)).differentiableAt (by norm_num))
  have hTailDiff : DifferentiableAt ℝ Tail x := by simpa [Tail] using hTail
  have hbaseDiv : vecDiv Base x = vecDiv First x + vecDiv Regular x := by
    rw [hBaseEq]
    exact HmSourcePairing.hmSource_vecDiv_add_of_differentiableAt hFirstDiff hRegularDiff
  have hdSource : sourceErrorD I hΦ m κ T t = fun y => First y + Tail y := by
    exact HmSourcePairing.hmFrozenSourceErrorD_eq_dFirst_add_tail I hΦ m κ T t
  have hdDiv : vecDiv (sourceErrorD I hΦ m κ T t) x =
      vecDiv First x + vecDiv Tail x := by
    rw [hdSource]
    exact HmSourcePairing.hmSource_vecDiv_add_of_differentiableAt hFirstDiff hTailDiff
  have hBaseEndpoint := LeftJacobian.variantA_hmEndpoint_zero I hΦ m hm κ T t x
  have hBaseEndpoint' : hmEndpoint I hΦ m κ T 0 t x = -vecDiv Base x := by
    change hmEndpoint I hΦ m κ T 0 t x =
      -vecDiv (hmFrozenBaseFlux I hΦ m κ T t) x at hBaseEndpoint
    simpa [Base] using hBaseEndpoint
  calc
    _ = vecDiv Tail x +
        vecDiv Base x := by
          rw [hm_frozen_terminal_endpoint_eq_div I hΦ m κ T t x,
            hBaseEndpoint']
          ring
    _ = vecDiv Tail x + vecDiv First x + vecDiv Regular x := by
      rw [hbaseDiv]
      abel
    _ = hmFrozenPiolaSource I hΦ m κ T t x +
        vecDiv (sourceErrorD I hΦ m κ T t) x := by
          rw [hmFrozenPiolaSource, hdDiv]
          abel

end AVenhance.Infra.Section4

end
