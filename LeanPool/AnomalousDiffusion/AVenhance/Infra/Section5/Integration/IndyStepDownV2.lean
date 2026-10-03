/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.IndyStepDownPartI
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeStep
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.MatrixContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing

/-! # Step-down assembly: `IndyStepDownStatement` from named inputs

`indystepdown_v2_of_inputs` proves the literal step-down proposition `IndyStepDownStatement β C₀`
(conjuncts (i) and (ii), one constant) from the `Prop`-valued input record `IndyStepDownV2Inputs`.

* conjunct (i) is `indystepdown_part_i_of_all_inputs` (big-bound estimate inputs `BigBoundInputs`
    and step-down part (i) inputs
  `IndyPartIInputs`);
* conjunct (ii) is `RelativeError.relative_step`, fed by the *same* `BigBoundInputs` /
    `IndyPartIInputs`
  instances for the leaves they already contain (residual identity, the ten-term joint continuity,
  the `HTilde_m` regularity is currently carried by `RelativeLeaves`, see its provisional fields)
      and by
  the additional record `RelativeLeaves`;
* the joint continuity of `leadingGrad … (T (Nstar β))` is proved here
  (`leadingGrad_continuousOn_Ici`) from `leadingMatrix_continuous` and `spaceGrad_continuousOn`.

No field is (or contains) a step-down estimate conjunct.  The statement files are not imported. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

/-! ### Continuity of the leading gradient (a derived leaf) -/

section Leading

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `∇^{lead} T = F ∇T` is jointly continuous on `[0,∞) × ℝ²` when `T` is smooth up to `t = 0`. -/
theorem leadingGrad_continuousOn_Ici (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => LeftToShow.leadingGrad I hΦ m κm T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hg := LeftToShow.spaceGrad_continuousOn hT
  have hF := LeftToShow.leadingMatrix_continuous I hΦ hm hκm
  refine continuousOn_pi.2 fun i => ?_
  have h0 := hF.matrix_elem i 0
  have h1 := hF.matrix_elem i 1
  have g0 := continuousOn_pi.1 hg 0
  have g1 := continuousOn_pi.1 hg 1
  simp only [LeftToShow.leadingGrad, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fun_prop

end Leading

/-! ### The relative leaves -/

section Leaves

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The relative-step leaves of one step-down instance that are *not* already fields of
    `BigBoundInputs`
or `IndyPartIInputs` (and not proved here).  For one instance `(I, Φ, m, κ_m = κm, κ_{m-1} = κprev,
θ_m = θm, θ_{m-1} = θprev, T)`, with `N = T (Nstar β)`, `ε = ε_{m-1}`,
`S = √κ_{m-1} ‖∇θ_{m-1}‖_{L²((0,1)×𝕋²)}` and `v = θTilde_m` the ansatz built from `N`.
The field types are exactly the hypotheses of `AVenhance.Infra.Section5.RelativeError.relative_step`
(`S`, `ε`, `v` unfolded), each an `OpenInputs` contract; no field involves `t = 0`.  Deduplicated
    against the big-bound estimate / step-down part (i) inputs (taken from there, not
fields): the residual identity, the ten-term joint continuity.  Proved in this file (not a field):
    joint continuity of `leadingGrad … N` on
`[0,∞) × ℝ²` (`leadingGrad_continuousOn_Ici`). -/
structure RelativeLeaves (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (θm θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (A Ci Cr Ca Ct : ℝ) : Prop where
  /-- `‖∇T_{m-1}‖` at most `A ‖∇θ_{m-1}‖` (`l.Tm.minus.thetam` gradient form, positive-temperature
  premise `hT0`). -/
  hT0 : TGradientContract β κprev T A
    (Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))
  /-- The material-derivative bound `hDt` for `T_{m-1}` at scale `ε^{3δ} κ_{m-1}^{-1/2} S
      τ_m^{-1}`. -/
  hDt : TMaterialContract I Φ m κprev T A
    (Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))
  /-- Positive-temperature jets of `T_{m-1}` (`PositiveTemperatureJets`: positive jets and
  integrated gradients only). -/
  hJets : TPositiveJetsContract I m T A
    (Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))
  /-- Relative initial layer from the right, `‖θ_m(s) − θTilde_m(s)‖_{L²} ≤ C_i ε^δ S` as `s → 0⁺`
  (`InitialLayerContract` at amplitude `S`). -/
  hInitial : InitialLayerContract I hΦ m κm θm T Ci
    (Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))
  /-- The ten relative `HDot⁻¹` term bounds `‖term_i‖_{L²_t HDot⁻¹} ≤ C_r √κ_m ε^δ S`, `i < 10`
  (relative §5.2 term estimates, with slots 3,4,8 centered). -/
  hterms : RelativeTermsContract I hΦ m κm κprev T Cr
    (Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))
  /-- Leading-order gradient error of the ansatz, `√κ_m ‖∇v − ∇^{lead} N‖ ≤ C_a ε^{2δ} S`
  (`e.leading` comparison). -/
  hLeadingError : LeadingErrorContract I hΦ m κm T Ca
    (Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))
  /-- Gradient distance of the last iterate to the previous solution,
  `√κ_{m-1} ‖∇T_{m-1} − ∇θ_{m-1}‖ ≤ C_t ε^{2δ} S` (`l.Tm.minus.thetam`). -/
  hTemperatureError : TemperatureErrorContract I m κprev θprev T Ct
    (Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))

end Leaves

/-- **Family contract for step-down part (ii)** (`IndyStepDownV2Inputs.relative`): for constants
    `A Ci Cr Ca Ct`
and the Λ-threshold `CΛ` (all chosen before `I`), `RelativeLeaves` on the step-down premise block
`OnA8Instances`, under the gate `6/5 ≤ β` and the later-scale condition. -/
def RelativeFamilyContract (β C₀ CΛ A Ci Cr Ca Ct : ℝ) : Prop :=
  OnA8Instances β C₀ CΛ (fun I _Φ hΦ κ M R _θ₀ m θm θprev T =>
    (6 : ℝ) / 5 ≤ β →
    epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
    RelativeLeaves I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θm θprev T A Ci Cr Ca Ct)

/-! ### The input record for the whole of step-down -/

/-- All remaining inputs of the literal step-down proposition `IndyStepDownStatement β C₀`.
`bigbound` is exactly the big-bound estimate input hypothesis of
    `indystepdown_part_i_of_all_inputs`, `partI` exactly its step-down part (i) input hypothesis,
    and `relative` supplies `RelativeLeaves` under the gate (`6/5 ≤ β` and the later
scale condition) once the Λ-threshold `CΛ ≤ Λ` holds.  The reals `A Ci Cr Ca Ct` are the constants
of `RelativeError.relative_step`.  No field is (or contains) a step-down estimate conjunct. -/
structure IndyStepDownV2Inputs (β C₀ : ℝ) : Type where
  /-- Constant `A` of `RelativeError.relative_step` (positive-jet constant). -/
  A : ℝ
  /-- Constant of the relative initial defect. -/
  Ci : ℝ
  /-- Constant of the ten relative term bounds. -/
  Cr : ℝ
  /-- Constant of the leading gradient error. -/
  Ca : ℝ
  /-- Constant of the temperature gradient error. -/
  Ct : ℝ
  /-- Side condition `2 ^ 14 ≤ A`. -/
  hA : 2 ^ (14 : ℕ) ≤ A
  /-- Side condition `0 ≤ Ci`. -/
  hCi : 0 ≤ Ci
  /-- Side condition `0 ≤ Cr`. -/
  hCr : 0 ≤ Cr
  /-- Side condition `0 ≤ Ca`. -/
  hCa : 0 ≤ Ca
  /-- Side condition `0 ≤ Ct`. -/
  hCt : 0 ≤ Ct
  /-- The big-bound estimate inputs (`BigBoundInputs` for every admissible instance). -/
  bigbound : BigBoundFamilyContract β C₀
  /-- The step-down part (i) inputs (`IndyPartIInputs` for every admissible instance). -/
  partI : PartIFamilyContract β C₀
  /-- Λ-threshold beyond which the relative leaves are supplied. -/
  CΛ : ℝ
  /-- The relative leaves (`RelativeLeaves`), needed only under the gate. -/
  relative : RelativeFamilyContract β C₀ CΛ A Ci Cr Ca Ct

/-! ### The assembly theorem -/

/-- **Step-down assembly.**  The literal step-down proposition from the named inputs: conjunct (i)
by `indystepdown_part_i_of_all_inputs`, conjunct (ii) by `RelativeError.relative_step`, with one
    constant
`C = max (max C_i C_ii) (max (max C₁ᵇᵇ C₁ᴵ) CΛ)`. -/
theorem indystepdown_v2_of_inputs (β C₀ : ℝ) (h : IndyStepDownV2Inputs β C₀) :
    IndyStepDownStatement β C₀ := by
  obtain ⟨Ci', hi⟩ := indystepdown_part_i_of_all_inputs β C₀ h.bigbound h.partI
  obtain ⟨Cii, hii⟩ := RelativeError.relative_step β C₀ h.A h.Ci h.Cr h.Ca h.Ct h.hA h.hCi h.hCr
      h.hCa h.hCt
  obtain ⟨Cb₁, Cb₂, hbb⟩ := h.bigbound
  obtain ⟨Cp₁, Cᵢ, Cₐ, Cₜ, hpi⟩ := h.partI
  refine ⟨max (max Ci' Cii) (max (max Cb₁ Cp₁) h.CΛ), ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT
  have hΛ_i : Ci' ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛ
  have hΛ_ii : Cii ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛ
  have hΛ_b : Cb₁ ≤ (I.Λ : ℝ) := le_trans (le_trans (le_trans (le_max_left _ _)
    (le_max_left _ _)) (le_max_right _ _)) hΛ
  have hΛ_p : Cp₁ ≤ (I.Λ : ℝ) := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_left _ _)) (le_max_right _ _)) hΛ
  have hΛ_r : h.CΛ ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) hΛ
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hepos : ∀ n : ℕ, 0 < epsilon β I.Λ n := fun n =>
    Infra.Cutoff.epsilon_pos hβ hβ' I.two_pow_seven_le
  have hed0 : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β := Real.rpow_nonneg (hepos _).le _
  have hκpos : 0 < κ :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos (hepos M) _))
      (Set.mem_Icc.mp hperm).1
  have hν : 0 < I.kappaSeq κ M (m - 1) := LeftToShow.kappaSeq_pos I hκpos M (m - 1)
  have hκm : 0 < I.kappaSeq κ M m := LeftToShow.kappaSeq_pos I hκpos M m
  have hm2 : 2 ≤ m := by
    have hstar : 2 ≤ mTheta0 β I.Λ R := (mTheta0_spec hβ hβ' I.two_pow_seven_le hR).1
    omega
  refine ⟨?_, ?_⟩
  · -- conjunct (i)
    intro t ht
    refine (hi I hz hx hh hΛ_i Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
      hθm hθprev hT t ht).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_left _ _)) hed0) (Real.sqrt_nonneg _)
  · -- conjunct (ii)
    intro hβ65 hlater
    have hBB := hbb I hz hx hh hΛ_b Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
      θprev T hθprev hT
    have hP := hpi I hz hx hh hΛ_p Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
      θm θprev T hθm hθprev hT
    have hL := h.relative I hz hx hh hΛ_r Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm
      hmM θm θprev T hθm hθprev hT hβ65 hlater
    have hsol := RelativeError.tIterates_classicalSol hT
    have hLead := leadingGrad_continuousOn_Ici I hΦ (m := m) (by omega) hκm hsol.1
    have hmain := hii I hz hx hh hΛ_ii Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
      θm θprev T hθm hθprev hT hL.hT0 hL.hDt hL.hJets hL.hInitial hBB.residual
      hBB.term_continuous hBB.group_meanZero hL.hterms hL.hLeadingError hL.hTemperatureError
      hLead hβ65 hlater
    refine hmain.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_left _ _)) hed0)
      (mul_nonneg hν.le (LeftToShow.spaceTimeGradNormSq_nonneg' _))

end AVenhance.Infra.Section5.Integration
