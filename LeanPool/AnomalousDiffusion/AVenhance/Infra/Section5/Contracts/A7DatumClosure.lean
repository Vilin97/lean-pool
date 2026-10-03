/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A7Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJetsSourceClosure
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJetsR46Closed
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTiny
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SourceErrorD
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.MeanZero
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxes
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTwistie4
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTwistie5
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Contract

/-! # Big-bound estimate at the datum amplitude: the last closures and `bigbound_of_remaining`

The big-bound estimate needs every `BigBoundInputs` contract only at the datum amplitude `B =
    ‖θ₀‖_{L²}`.
* `normie2Source_datum_closed_contract`: `normie2Source_contract` with `hmGradient_contract`.
* `vIncrement_datum_contract`: the V upgrade (`iterate_V_upgrade_of_theta`) with the big-bound
    premise block θ
  profile at amplitude `2‖θ₀‖` (`thetaProfileA7_contract`), at a constant `Cs` large for both.
* `tinyHMinusSource_datum_closed_contract`: `tinyHMinusSource_contract` at `B = 2‖θ₀‖` with
  `sourceErrorD_contract`, `vIncrement_datum_contract`, `tinyMeanZero_contract`, rescaled to `‖θ₀‖`.
* `bigbound_of_remaining`: the literal big-bound estimate statement from a datum-amplitude
  `Normie3CenteredSourceContract` producer. `bigbound_contract` supplies the proved
  `normie3CenteredSource_datum_closed_contract`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5 Integration

/-- Exact datum producer of `Normie2SourceContract`, every input discharged. -/
theorem normie2Source_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Normie2SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨CH, Ch, hH⟩ := hmGradient_contract β Ccut
  obtain ⟨C, _, Cs, hsource⟩ := normie2Source_contract β Ccut (max CH 0) (le_max_right _ _)
  refine ⟨C, max Ch Cs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hg := hH I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
    ha m hm hmM θprev T hθ hT
  have he : 0 ≤ epsilon β I.Λ (m - 1) ^ (4 * delta β) :=
    Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have hg' : HmGradientContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T (max CH 0)
      (Real.sqrt (l2NormSq θ₀)) :=
    hg.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) he)
      (Real.sqrt_nonneg _))
  exact hsource I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
    ha m hm hmM θprev T hθ hT (Real.sqrt (l2NormSq θ₀)) (Real.sqrt_nonneg _) hg'

/-- The V increments of the actual iterates at amplitude `2‖θ₀‖`, with radius the block's `R`. -/
theorem vIncrement_datum_contract (β Ccut : ℝ) :
    ∃ Cs C₁ : ℝ, 1 ≤ Cs ∧ OnA7Instances β Ccut C₁
      (fun I _Φ _hΦ κ M R θ₀ m _θprev T =>
        VIncrementContract I m (I.kappaSeq κ M (m - 1)) T Cs R (2 * Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨c, Ck, _, _, hv⟩ := iterate_V_upgrade_of_theta β Ccut
  obtain ⟨CsReq, hReq, hprof⟩ := thetaProfileA7_contract β Ccut
  let Cs := max CsReq (iterateReducedSourceConstant β Ccut c Ck 40 (2 ^ 10) 1)
  have hCs : 1 ≤ Cs := hReq.trans (le_max_left _ _)
  obtain ⟨C₁, hscale⟩ := iterate_contract_scales β Cs hCs
  refine ⟨Cs, max C₁ 0, hCs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  obtain ⟨hm2, hradius, hsmall⟩ := hscale I ((le_max_left _ _).trans hΛ) R hR m hm
  have hbase := hprof Cs (le_max_left _ _) I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM
    hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  exact hv I hz hx hh hΦ κ M hT hθ hm2 hmM hperm 1 R Cs (2 * Real.sqrt (l2NormSq θ₀))
    (by positivity) hR (le_max_right _ _) hradius hsmall hbase

/-- Exact datum producer of `TinyHMinusSourceContract`, every input discharged. -/
theorem tinyHMinusSource_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        TinyHMinusSourceContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨Cd, Cd₁, hd⟩ := sourceErrorD_contract β Ccut
  obtain ⟨Cs, Cv₁, hCs, hvinc⟩ := vIncrement_datum_contract β Ccut
  obtain ⟨Cm₁, hmz⟩ := tinyMeanZero_contract β Ccut
  obtain ⟨C, _, Ct₁, htiny⟩ := tinyHMinusSource_contract β Ccut (max Cd 0) Cs (le_max_right _ _)
    (zero_le_one.trans hCs)
  obtain ⟨Cr₁, hscale⟩ := iterate_contract_scales β Cs hCs
  refine ⟨2 * C, max (max Cd₁ Cv₁) (max Cm₁ (max Ct₁ Cr₁)), ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hΛ1 : Cd₁ ≤ (I.Λ : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛ2 : Cv₁ ≤ (I.Λ : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛ3 : Cm₁ ≤ (I.Λ : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛ4 : Ct₁ ≤ (I.Λ : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hΛ))
  have hΛ5 : Cr₁ ≤ (I.Λ : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hΛ))
  obtain ⟨_, hradius, _⟩ := hscale I hΛ5 R hR m hm
  have hD := hd I hz hx hh hΛ1 Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hV := hvinc I hz hx hh hΛ2 Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hZ := hmz I hz hx hh hΛ3 Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have he : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
    Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have hB : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  have hD' : SourceErrorDContract I hΦ m (I.kappaSeq κ M m) T (max Cd 0)
      (2 * Real.sqrt (l2NormSq θ₀)) := by
    refine hD.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Cd ≤ max Cd 0 := le_max_left _ _
    have h0 : 0 ≤ max Cd 0 := le_max_right _ _
    have hk : 0 ≤ Real.sqrt (I.kappaSeq κ M m) := Real.sqrt_nonneg _
    calc Cd * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt (I.kappaSeq κ M m) *
          Real.sqrt (l2NormSq θ₀)
        ≤ max Cd 0 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt (I.kappaSeq κ M m) *
          Real.sqrt (l2NormSq θ₀) := by gcongr
      _ ≤ max Cd 0 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt (I.kappaSeq κ M m) *
          (2 * Real.sqrt (l2NormSq θ₀)) := by
        apply mul_le_mul_of_nonneg_left (by linarith only [hB]); positivity
  have hT2 := htiny I hz hx hh hΛ4 Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ
      hT
    (2 * Real.sqrt (l2NormSq θ₀)) (by positivity) R hradius hD' hV hZ
  refine hT2.trans (le_of_eq ?_)
  congr 1
  ring

/-- **Big-bound estimate from a normie3 producer.** The literal `BigBoundStatement β C₀`
(= the body of `AVenhance.bigbound`), with every other big-bound estimate contract discharged by
its datum producer. `bigbound_contract` supplies the proved
`normie3CenteredSource_datum_closed_contract` for the displayed hypothesis. -/
theorem bigbound_of_remaining (β C₀ : ℝ)
    (hNormie3 : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (l2NormSq θ₀)))) :
    BigBoundStatement β C₀ :=
  bigbound_of_contracts β C₀
    { residual := residual_contract β C₀
      cutoff1_meanZero := cutoff1MeanZero_contract β C₀
      cutoff1_source := cutoff1Source_datum_closed_contract β C₀
      twistie1_hminus_source := twistie1HMinusSource_datum_closed_contract β C₀
      twistie3_flux_smooth := twistie3FluxSmooth_contract β C₀
      twistie3_flux_periodic := twistie3FluxPeriodic_contract β C₀
      twistie3_source := twistie3Source_datum_closed_contract β C₀
      group_meanZero := groupMeanZero_contract β C₀
      twistie4_centered_source := twistie4CenteredSource_datum_closed_contract β C₀
      twistie5_centered_source := twistie5CenteredSource_datum_closed_contract β C₀
      normie3_centered_source := hNormie3
      normie1_flux_smooth := normie1FluxSmooth_contract β C₀
      normie1_flux_periodic := normie1FluxPeriodic_contract β C₀
      normie1_source := normie1Source_datum_closed_contract β C₀
      normie2_flux_smooth := normie2FluxSmooth_contract β C₀
      normie2_flux_periodic := normie2FluxPeriodic_contract β C₀
      normie2_source := normie2Source_datum_closed_contract β C₀
      tiny_hminus_source := tinyHMinusSource_datum_closed_contract β C₀
      R46_flux_smooth := r46FluxSmooth_contract β C₀
      R46_flux_periodic := r46FluxPeriodic_contract β C₀
      R46_source := r46Source_datum_closed_contract β C₀
      term_continuous := termContinuous_contract β C₀ }

/-- **Big-bound estimate, closed**: the literal `BigBoundStatement β C₀` with every big-bound
    estimate contract
discharged, `Normie3CenteredSourceContract` by `normie3CenteredSource_datum_closed_contract`.
This is the producer body for `AVenhance.bigbound`. -/
theorem bigbound_closed (β C₀ : ℝ) : BigBoundStatement β C₀ :=
  bigbound_of_remaining β C₀ (normie3CenteredSource_datum_closed_contract β C₀)

end AVenhance.Infra.Section5.Contracts
