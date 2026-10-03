/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmGradientActual
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmGradientTheta
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorBound

/-! # `HmGradientContract` (`e.Hm.gradient.L2`, `enhance.tex` 5975-5995)

`√κ_{m-1} ‖∇HTilde_m‖_{L²((0,1)×𝕋²)} ≤ CH ε_{m-1}^{4δ} B`, the `κ_{m-1}`-normalised gradient bound.

Route (all pieces exist; this file only wires them):
* `thetaProfile` (amplitude `B`) and `iterate_V_upgrade_of_theta` give the V-increment amplitude;
* `RelativeError.relative_iterate_gradient_jets` (ATA): positive spatial jets of `∇T_i`, every `i
    ≤ N*`;
* `RelativeError.relative_Amnr_tensor_of_jets` (ATB): the AMNR Hessian tensor bound at amplitude
    `B`;
* `hm_gradient_sharp_actual` (`HmGradientActual.lean`): the `κ_{m-1}`-sharp HTilde gradient
  bound with the open-time regularity discharged.

Normalisation check: the sharp bound needs `a_m² ε_m⁴/κ_m ≲ κ_{m-1}`
(`left_to_show_scales`, one-sided at `m = M`), the diffusivity upper bound for `κ_{m-1}` (index
`m - 1 < M`), `ε_m²/(κ_m τ_m) ≤ 1` (which only needs `ε_m²/(κ_m τ_m) ≲ ε_{m-1}^{2δ}` from
`left_to_show_scales`, valid through `m = M`) and the `Params` bounds.  The `κ_{m-1}` form is
therefore true and proved through `m = M`; no printed `m = M` diffusivity bound is used.

Producers:
* `hmGradient_of_thetaProfile_contract`: abstract amplitude `B` (step-down part (ii) use at `B =
    S`), conditional
  on `ThetaProfileContract` at amplitude `B`;
* `hmGradient_contract`: the unconditional producer at `B = ‖θ₀‖`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5
  AVenhance.Infra.Section5.Integration AVenhance.Infra.Section5.RelativeError

/-- `HmGradientContract` at an abstract amplitude `B`, conditional only on the θ profile at
amplitude `B` (profile constant `Cs ≥ CsReq`, chosen before the instance). -/
theorem hmGradient_of_thetaProfile_contract (β Ccut CsReq : ℝ) (hReq : 1 ≤ CsReq) :
    ∃ Cs CH C₁ : ℝ, CsReq ≤ Cs ∧ 0 ≤ CH ∧
      OnA7Instances β Ccut C₁ (fun I _Φ hΦ κ M _R _θ₀ m θprev T =>
        ∀ B : ℝ, 0 ≤ B → ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs B →
          HmGradientContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T CH B) := by
  obtain ⟨cv, Cv, hcv, hcvC, hv⟩ := iterate_V_upgrade_of_theta β Ccut
  let Cs := max CsReq (iterateReducedSourceConstant β Ccut cv Cv 40 (2 ^ 10) 1)
  have hReqCs : CsReq ≤ Cs := le_max_left _ _
  have hSrc : iterateReducedSourceConstant β Ccut cv Cv 40 (2 ^ 10) 1 ≤ Cs := le_max_right _ _
  have hCs : 1 ≤ Cs := hReq.trans hReqCs
  have hCspos : 0 < Cs := zero_lt_one.trans_le hCs
  obtain ⟨Cg, hCg, Λj, hj⟩ := relative_iterate_gradient_jets β Cs hCspos
  obtain ⟨CA, hCA, Λb, hTen⟩ :=
    relative_Amnr_tensor_of_jets β Ccut Cg (max Cs 1) hCg (le_max_right _ _)
  obtain ⟨CH, hCH, Λc, hH⟩ := hm_gradient_sharp_actual β Ccut CA hCA
  obtain ⟨Λs, hscale⟩ := iterate_contract_scales β Cs hCs
  refine ⟨Cs, CH, max Λs (max Λj (max Λb Λc)), hReqCs, hCH, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hset M hM hperm R hR θ₀ hsm hp hmz ha m hm hmM θprev T hθ hT B hB
    hbase
  have hΛs : Λs ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hΛ
  have hΛj : Λj ≤ (I.Λ : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛb : Λb ≤ (I.Λ : ℝ) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hΛ
  have hΛc : Λc ≤ (I.Λ : ℝ) :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hΛ
  obtain ⟨hm2, hradius, hsmall⟩ := hscale I hΛs R hR m hm
  have hκ : 0 < κ := (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (Real.rpow_pos_of_pos
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _)).trans_le hperm.1
  have hκm : 0 < I.kappaSeq κ M m := Infra.Section3.kappaAt_pos I hκ m (M - m)
  have hκp : 0 < I.kappaSeq κ M (m - 1) := Infra.Section3.kappaAt_pos I hκ (m - 1) (M - (m - 1))
  have hV := hv I hz hx hh hΦ κ M hT hθ hm2 hmM hperm 1 R Cs B hB hR hSrc hradius hsmall hbase
  have hjet := hj I hΛj Φ hΦ κ M m hm2 θ₀ θprev T hκm hκp hθ hT B R hB hradius hbase hV
  have hten := hTen I hz hx hh hΛb Φ hΦ κ hset M hM hperm m hm2 hmM θ₀ θprev T hθ hT B hB hjet
  exact hH I hz hx hh hΛc Φ hΦ κ hset M hM hperm m hm2 hmM θ₀ θprev T hθ hT B hB hten

/-- **`HmGradientContract`** (`e.Hm.gradient.L2`) at the datum amplitude `B = ‖θ₀‖_{L²}`:
the exact unconditional producer. -/
theorem hmGradient_contract (β C₀ : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
      HmGradientContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C
        (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨CsReq, hReq, hth⟩ := thetaProfileA7_contract β C₀
  obtain ⟨Cs, CH, C₁, hCs, hCH, hcond⟩ := hmGradient_of_thetaProfile_contract β C₀ CsReq hReq
  refine ⟨2 * CH, C₁, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hset M hM hperm R hR θ₀ hsm hp hmz ha m hm hmM θprev T hθ hT
  have hprof := hth Cs hCs I hz hx hh (Nat.cast_nonneg _) Φ hΦ κ hset M hM hperm R hR θ₀ hsm hp
    hmz ha m hm hmM θprev T hθ hT
  have hB : 0 ≤ 2 * Real.sqrt (l2NormSq θ₀) := by positivity
  have h := hcond I hz hx hh hΛ Φ hΦ κ hset M hM hperm R hR θ₀ hsm hp hmz ha m hm hmM θprev T hθ hT
    _ hB hprof
  refine h.trans (le_of_eq ?_)
  ring

end AVenhance.Infra.Section5.Contracts
