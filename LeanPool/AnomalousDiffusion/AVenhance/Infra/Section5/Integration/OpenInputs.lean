/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Statements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.KeystoneStatements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound.Grouped
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.ScaleTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Twistie3
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Normie1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Normie2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Defs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoordinateProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHigherEnergyBudget
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBasic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDiffusion

/-! # Input contracts of the main theorem

This module states, in one place, every named input of the following assemblies; each input is
proved in another module (the main theorem is unconditional). The named inputs of
* Big-bound estimate (`BigBoundInputs`, one instance),
* Step-down part (i) (`IndyPartIInputs`, one instance),
* Step-down part (ii) (`RelativeLeaves`, one instance), including the leaf inputs of the
    conditional producers
  `section_four_ansatz_bound` and `RelativeError.relative_leading_error_of_jets`,
* Main theorem (`anomalous_dissipation_of_A8_A1c`: the step-down and classical well-posedness
    statements),

is a `def <Name>Contract … : Prop` below, stated **exactly** as its consumer uses it.  The three
per-instance input records are defined here with fields typed by these contracts, and the
family-level contracts (`BigBoundFamilyContract`, `PartIFamilyContract`, `RelativeFamilyContract`)
are the corresponding fields of `IndyStepDownV2Inputs`.  Producers prove exactly `<Name>Contract`
(per instance), quantified as in the family contract that contains it: constants first (chosen
before `I`), then a Λ-threshold, then the step-down premise block.

Conventions.
* Open time: every contract that involves the ansatz, `HTilde_m` or `Amnr` is stated for
  `t > 0` only (the `Amnr` uses the two-sided time `deriv`, so these objects are
  extension-dependent at `t ≤ 0`).  No consumer field carries a `t = 0` form
      (`RelativeError.relative_step` uses the open-time
  energy estimate and the proved open-time `HTilde_m` regularity).
* Centered slots: the relative term bounds are on `section5CenteredTerm` (slots 3, 4, 8 centered),
  with the grouped mean zero `GroupMeanZeroContract`.
* Abstract amplitude: contracts used with both normalisations (`B = ‖θ₀‖_{L²}` for
    big-bound/step-down part (i) and
  `B = S = √κ_{m-1} ‖∇θ_{m-1}‖` for step-down part (ii)) take the amplitude `B`/`N` as a parameter.

Source lines refer to the pinned `source/enhance.tex`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

/-! ## big-bound estimate (`e.bigbound`): per-instance contracts

Notation: `N := T (Nstar β)`, `d := sourceErrorD I hΦ m κm N`,
`e := iterateError I hΦ m κm κprev T`.
**Abstract amplitude:** every `*SourceContract` has right side `C ε_{m-1}^δ √κ_m B`.  big-bound
    estimate
(`BigBoundInputs`) uses `B = ‖θ₀‖_{L²}` (then the scale is `section5SourceScale β I.Λ m κm C θ₀`,
definitionally); the relative term bounds of step-down part (ii) use the same objects at `B = S`,
    so one producer per term with a free amplitude serves both.  The mean-zero, flux
regularity and continuity contracts are amplitude-free and shared by big-bound estimate and
    step-down part (ii). -/

section A7

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The exact residual identity `e.monster` for the ansatz built from `N = T (Nstar β)`
with the source errors `d_m` (`e.dm`) and `e_{m-1}`, on `t ∈ (0,1)` (`enhance.tex` 6886–6990). -/
def ResidualContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x, sourceResidualIdentity I hΦ m κm κprev T t x

/-- Mean zero of `cutoff1(t)` on the cube, `t ∈ (0,1)`. -/
def Cutoff1MeanZeroContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (cutoff1 I hΦ m κm (T (Nstar β)) t)

/-- Source-scale space-time `L²` bound for `cutoff1` (`e.monster.est.*`, 7300–7500). -/
def Cutoff1SourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1,
    ENNReal.ofReal ((2 * Real.pi)⁻¹ *
      Real.sqrt (l2NormSq (cutoff1 I hΦ m κm (T (Nstar β)) t))) ^ 2) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Mean zero of `twistie1(t)` (source mean condition),
`t ∈ (0,1)`.  Not a field of `BigBoundInputs`: a producer **input** of
`Twistie1HMinusSourceContract` (the ergodic lemma needs the product mean). -/
def Twistie1MeanZeroContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (twistie1 I hΦ m κm (T (Nstar β)) t)

/-- **Negative-norm** source bound for `twistie1` (`e.monster.est.5`, 7371–7460): the time
`HDot⁻¹` norm of `twistie1` is at most `C ε^δ √κ_m B`.  The source proves it with the ergodic lemma
(Remark `r.Hminusone.flow`, choice `e.fg.choice.1`), whose gain `ε_m` is a negative-norm gain: an
`L²` bound of `twistie1` at this scale is NOT available (it is larger by `≈ ε_{m-1}^{8δ-q}`).
    Replaces the former `Twistie1SourceContract` (`L²`). -/
def Twistie1HMinusSourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  timeHMinusOneNorm (fun t => twistie1 I hΦ m κm (T (Nstar β)) t) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Smoothness of the divergence flux of `twistie3` (`e.monster.twistie3`, 6912), `t ∈ (0,1)`. -/
def Twistie3FluxSmoothContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (twistie3Flux I hΦ m κm (T (Nstar β)) t)

/-- `ℤ²`-periodicity of the `twistie3` flux, `t ∈ (0,1)`. -/
def Twistie3FluxPeriodicContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, IsZ2Periodic (twistie3Flux I hΦ m κm (T (Nstar β)) t)

/-- Source-scale space-time `L²` bound on the `twistie3` flux gradient. -/
def Twistie3SourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt
      (gradNormSq (twistie3Flux I hΦ m κm (T (Nstar β)) t))) ^ 2) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Grouped mean zero: the *sum* `twistie4 + twistie5 + normie3` is
mean zero on the cube, `t ∈ (0,1)` (the three are not individually so).  Used by big-bound
    estimate and, through
`RelativeError.relative_step`, by step-down part (ii). -/
def GroupMeanZeroContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (fun x =>
    twistie4 I hΦ m κm (T (Nstar β)) t x + twistie5 I hΦ m κm (T (Nstar β)) t x +
      normie3 I hΦ m κm (T (Nstar β)) t x)

/-- Centered negative-norm bound for `twistie4`. -/
def Twistie4CenteredSourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  timeHMinusOneNorm (fun t x => centerCell (twistie4 I hΦ m κm (T (Nstar β)) t) x) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Centered negative-norm bound for `twistie5`. -/
def Twistie5CenteredSourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  timeHMinusOneNorm (fun t x => centerCell (twistie5 I hΦ m κm (T (Nstar β)) t) x) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Centered negative-norm bound for `normie3`. -/
def Normie3CenteredSourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  timeHMinusOneNorm (fun t x => centerCell (normie3 I hΦ m κm (T (Nstar β)) t) x) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Smoothness of the divergence flux of `normie1` (`e.monster.normie1`, 6950), `t ∈ (0,1)`. -/
def Normie1FluxSmoothContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (normie1Flux I hΦ m κm (T (Nstar β)) t)

/-- `ℤ²`-periodicity of the `normie1` flux, `t ∈ (0,1)`. -/
def Normie1FluxPeriodicContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, IsZ2Periodic (normie1Flux I hΦ m κm (T (Nstar β)) t)

/-- Source-scale space-time `L²` bound on the `normie1` flux gradient. -/
def Normie1SourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt
      (gradNormSq (normie1Flux I hΦ m κm (T (Nstar β)) t))) ^ 2) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Smoothness of the divergence flux of `normie2` (`e.monster.normie2`, 6959), `t ∈ (0,1)`. -/
def Normie2FluxSmoothContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (normie2Flux I hΦ m κm (T (Nstar β)) t)

/-- `ℤ²`-periodicity of the `normie2` flux, `t ∈ (0,1)`. -/
def Normie2FluxPeriodicContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, IsZ2Periodic (normie2Flux I hΦ m κm (T (Nstar β)) t)

/-- Source-scale space-time `L²` bound on the `normie2` flux gradient (`H_m` estimates). -/
def Normie2SourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt
      (gradNormSq (normie2Flux I hΦ m κm (T (Nstar β)) t))) ^ 2) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Mean zero of `tiny(t)`,
`t ∈ (0,1)`.  Not a field of `BigBoundInputs`: a producer **input** of
`TinyHMinusSourceContract` (it gives the mean of `tinyNondivergencePart`). -/
def TinyMeanZeroContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    MeanZeroOn unitCube (tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) t)

/-- **Negative-norm** source bound for `tiny` (`e.monster.est.tiny`, 7930–8000): the time `HDot⁻¹`
norm of `tiny` is at most `C ε^δ √κ_m B`.  The source proves it in divergence form —
`‖d_m + e_{m-1}‖_{L²}` (`e.dm.bounds`, `e.Em-1.thetam` with `n = 0`) plus the `L²` norm of
`tinyNondivergencePart` (`e.Em-1.thetam` with `n = 2`); see `hMinusOneNorm_tiny_le_of_components`
(`Terms/Tiny.lean`).  It never bounds `∇·(d_m + e_{m-1})` in `L²`, so this replaces the former
`TinySourceContract` (`L²` of `tiny`). -/
def TinyHMinusSourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  timeHMinusOneNorm (fun t => tiny I hΦ m κm (sourceErrorD I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) t) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- **`d_m` bound, abstract amplitude `B`** (`e.monster.est.11.a.d`, 7860–7880, from `e.dm.bounds`):
the time-`L²` of the spatial `L²` norm of `sourceErrorD` is at most `Cd ε_{m-1}^{2δ} √κ_m B`.
Producer input of `TinyHMinusSourceContract` (with `VIncrementContract` for `e_{m-1}`). -/
def SourceErrorDContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (Cd B : ℝ) : Prop :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt
      (gradNormSq (sourceErrorD I hΦ m κm (T (Nstar β)) t))) ^ 2) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (Cd * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt κm * B)

/-- Smoothness of the transition-window flux of `R46` (the transition remainder), `t ∈ (0,1)`. -/
def R46FluxSmoothContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm (T (Nstar β)) t)

/-- `ℤ²`-periodicity of the `R46` flux, `t ∈ (0,1)`. -/
def R46FluxPeriodicContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) 1, IsZ2Periodic (r46Flux I hΦ m κm (T (Nstar β)) t)

/-- Source-scale `L²` bound on the `R46` flux gradient (transition-window estimate the source
does not state). -/
def R46SourceContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt
      (gradNormSq (r46Flux I hΦ m κm (T (Nstar β)) t))) ^ 2) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B)

/-- Joint continuity of each of the ten §5.1 terms on `(0,1) × ℝ²` (all pieces are smooth for
`t > 0`).  Used by big-bound estimate and by step-down part (ii). -/
def TermContinuousContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ i, i < 10 → ContinuousOn
    (fun p : ℝ × Vec 2 => section5Term I hΦ m κm (T (Nstar β))
      (sourceErrorD I hΦ m κm (T (Nstar β))) (iterateError I hΦ m κm κprev T) i p.1 p.2)
    (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)

end A7

/-! ## step-down part (i) (`indystepdown` conjunct (i)): per-instance contracts -/

section PartI

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- **Initial layer, abstract amplitude `B`.**  The defect `‖θ_m(s) − θTilde_m(s)‖_{L²} ≤ Cᵢ ε^δ
    B` for
all small `s > 0` (right limit; the ansatz at `t = 0` itself is extension-dependent).  Source:
`e.tildethetam.to.Tm` initial data (oscillatory corrector `ε^{4δ}`, `HTilde_m` only `ε^δ`).
Used with `B = ‖θ₀‖_{L²}` by step-down part (i) (`IndyPartIInputs.hInitial`) and with `B = S` by
    step-down part (ii)
(`RelativeLeaves.hInitial`, consumed by `RelativeError.relative_step` through
    `forced_energy_estimate_Ioi`). -/
def InitialLayerContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (θm : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (Cᵢ B : ℝ) : Prop :=
  ∀ᶠ s in 𝓝[>] (0 : ℝ), Real.sqrt (l2NormSq (fun x => θm s x -
      I.ansatz hΦ m κm (T (Nstar β)) s x)) ≤
    Cᵢ * epsilon β I.Λ (m - 1) ^ delta β * B

/-- `e.tildethetam.to.Tm` (8882–9133): `‖θTilde_m(t) − T_{m-1}(t)‖_{L²} ≤ Cₐ ε^δ ‖θ₀‖` for `t ∈
    (0,1]`. Produced by `Integration.section_four_ansatz_bound` from
`FirstOrderSliceJetContract` (amplitude `‖θ₀‖`) and `HmSupContract`. -/
def SectionFourAnsatzContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (θ₀ : Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (Cₐ : ℝ) : Prop :=
  ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κm (T (Nstar β)) t x -
      T (Nstar β) t x)) ≤
      Cₐ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)

/-- `e.Tm.thetam` / `l.Tm.minus.thetam`: `‖T_{m-1}(t) − θ_{m-1}(t)‖_{L²} ≤ Cₜ ε^δ ‖θ₀‖`, `t ∈ [0,1]`
(both are classical up to `t = 0`, so the closed interval is legitimate). -/
def SectionFourIterateContract (m : ℕ) (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (Cₜ : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) ≤
      Cₜ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)

/-- Leaf of `section_four_ansatz_bound` (`hTjet`), **abstract amplitude `B`**: first-order slice jet
`‖∂_i T_{m-1}(s)‖_{L²} ≤ AT · B · ε_{m-1}^{-(1+γ/2)}`, `s ∈ [0,1]` (`e.Tm.reg.upgrade`, first
order).
Step-down part (i) uses `B = ‖θ₀‖_{L²}`.  Implied by the second conjunct of the T upgrade
(`iterate_T_upgrade_of_theta*`, `v = [i]`) with amplitude `N = 2‖θ₀‖` . -/
def FirstOrderSliceJetContract (m : ℕ) (T : ℕ → ℝ → Vec 2 → ℝ) (AT B : ℝ) : Prop :=
  ∀ i : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    Real.sqrt (l2NormSq (fun x => spaceGrad (T (Nstar β) s) x i)) ≤
      AT * B * epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))

/-- Leaf of `section_four_ansatz_bound` (`hHsup`): `e.Hm.Linfty`, `‖HTilde_m(t)‖_{L²} ≤ CHs ε^δ
    ‖θ₀‖`
for `t ∈ (0,1]` (open time).  See `frozen_hm_halfCell_eLpNorm_bound`,
`HmDmScales`. -/
def HmSupContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (θ₀ : Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (CHs : ℝ) : Prop :=
  ∀ t ∈ Set.Ioc (0 : ℝ) 1, Real.sqrt (l2NormSq (I.Hm hΦ m κm (T (Nstar β)) t)) ≤
    CHs * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)

/-- **`HTilde_m` gradient, abstract amplitude `B`, `κ_{m-1}` normalisation** (`e.Hm.gradient.L2`,
5990; `e.hcorrm`): `√κ_{m-1} ‖∇HTilde_m‖_{L²((0,1)×𝕋²)} ≤ CH ε_{m-1}^{4δ} B`.  Input of
`Normie2SourceContract` (`e.monster.est.11` multiplies by `‖κ_m + ψTilde_m σ‖_∞ ≲ √(κ_m κ_{m-1})`).
At `B = ‖θ₀‖` this is `p.Hm.bounds`; at `B = S` note that
    `RelativeError.relative_Hm_gradient_actual` gives
only the weaker `κ_m` normalisation `√κ_m ‖∇HTilde_m‖ ≤ CH ε^{4δ} S`. -/
def HmGradientContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (CH B : ℝ) : Prop :=
  Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (I.Hm hΦ m κm (T (Nstar β)) s) x)) ≤
    CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B

end PartI

/-! ## step-down part (ii) (`indystepdown` conjunct (ii), relative step): per-instance contracts

Here `S` is the relative amplitude `√κ_{m-1} ‖∇θ_{m-1}‖_{L²((0,1)×𝕋²)}`; it is a parameter of each
contract and is instantiated by that expression in `RelativeLeaves`. -/

section RelativeExplicit

/-- `hT0`: `√κ_{m-1} ‖∇T_{m-1}‖ ≤ A S` (`l.Tm.minus.thetam`, gradient form).  First conjunct of
the T upgrade with amplitude `N = S`. -/
def TGradientContract (β : ℝ) (κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (A S : ℝ) : Prop :=
  Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (T (Nstar β) s) x)) ≤ A * S

/-- `hDt`: the material derivative of `T_{m-1}` at scale `ε^{3δ} κ_{m-1}^{-1/2} S τ'_m^{-1}`
(`e.barf.cascade`). -/
def TMaterialContract {β : ℝ} (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ) (κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (A S : ℝ) : Prop :=
  Real.sqrt (spaceTimeGradNormSq
      (LeftToShow.materialGrad (streamVel (Φ (m - 1))) (T (Nstar β)))) ≤
    A * epsilon β I.Λ (m - 1) ^ (3 * delta β) * (Real.sqrt κprev)⁻¹ * S * (tauP β I.Λ m)⁻¹

end RelativeExplicit

section Relative

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `hJets`: positive spatial jets of `T_{m-1}` with amplitude `S`
    (`RelativeError.PositiveTemperatureJets`;
positive orders only, no zeroth-order norm).  Slice part of the T upgrade with `N = S`
. -/
def TPositiveJetsContract (m : ℕ) (T : ℕ → ℝ → Vec 2 → ℝ) (A S : ℝ) : Prop :=
  RelativeError.PositiveTemperatureJets A (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) S (T (Nstar
      β))

/-- `hterms`: the ten relative `HDot⁻¹` term bounds `≤ C_r √κ_m ε^δ S` on the **centered** family
`section5CenteredTerm` (slots 3, 4, 8 centered). -/
def RelativeTermsContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (Cr S : ℝ) : Prop :=
  ∀ i, i < 10 → timeHMinusOneNorm
    (section5CenteredTerm I hΦ m κm (T (Nstar β))
      (sourceErrorD I hΦ m κm (T (Nstar β)))
      (iterateError I hΦ m κm κprev T) i) ≤
    ENNReal.ofReal (Cr * Real.sqrt κm * epsilon β I.Λ (m - 1) ^ delta β * S)

/-- `hLeadingError`: `√κ_m ‖∇θTilde_m − F∇T_{m-1}‖ ≤ C_a ε^{2δ} S` (`e.leading`). Produced by
    `RelativeError.relative_leading_error_of_jets` from `TGradientContract`,
`FirstOrderGradJetContract`, `ThetaProfileContract` and `VIncrementContract` (all amplitude `S`). -/
def LeadingErrorContract (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (Ca S : ℝ) : Prop :=
  Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (I.ansatz hΦ m κm (T (Nstar β)) s) x -
        LeftToShow.leadingGrad I hΦ m κm (T (Nstar β)) s x)) ≤
    Ca * epsilon β I.Λ (m - 1) ^ (2 * delta β) * S

/-- `hTemperatureError`: `√κ_{m-1} ‖∇T_{m-1} − ∇θ_{m-1}‖ ≤ C_t ε^{2δ} S` (`l.Tm.minus.thetam`).
    Produced by upstream `RelativeError.temperatureError_leaf_of_abstract_V` /
    `temperature_error_of_V_zero_bounds` from the V increments (`VIncrementContract`, amplitude
    `S`). -/
def TemperatureErrorContract (m : ℕ) (κprev : ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (Ct S : ℝ) : Prop :=
  Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (T (Nstar β) s) x - spaceGrad (θprev s) x)) ≤
    Ct * epsilon β I.Λ (m - 1) ^ (2 * delta β) * S

/-- Leaf of `relative_leading_error_of_jets` (`hT1`): first-order word part of the coordinate energy
profile, `√κ_{m-1} ‖∇ ∂_i T_{m-1}‖ ≤ A (A/ε^{1+γ/2}) S`.  Gradient part of the
T upgrade (`w = [i]`) with `N = S`. -/
def FirstOrderGradJetContract (m : ℕ) (κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (A S : ℝ) : Prop :=
  ∀ i : Fin 2, Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
      (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [i] (T (Nstar β) s)))) ≤
    A * (A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) * S

/-- Second-order word part of the coordinate energy profile, abstract amplitude `B` (`e.nabm2` with
`n = 2`): `√κ_{m-1} ‖∇ ∂_i ∂_j T_{m-1}‖ ≤ A (A/ε^{1+γ/2})² B`.  Input of
`Twistie1HMinusSourceContract` (the ergodic gain `ε_m` multiplies the space-time `L²` norm of
`∇∇·((K_m + s_{m-1})∇T)`; slice-only jets lose `≈ ε^{-(2-β)/2}`).  Gradient part of the
T upgrade (`v = w = [i, j]`) with `N = B`. -/
def SecondOrderGradJetContract (m : ℕ) (κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (A S : ℝ) : Prop :=
  ∀ i j : Fin 2, Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
      (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [i, j] (T (Nstar β) s)))) ≤
    A * (A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ 2 * S

/-- **θ_{m-1} base profile, abstract amplitude `N`**: `iterateCoordinateEnergyProfile θ_{m-1}
    κ_{m-1} N (Cs ε^{-1-γ/2}) 0`
(gradient-only at order zero).  step-down part (ii) uses `N = S` (requires the S-amplitude initial
    trace); Step-down part (i) uses `N = 2‖θ₀‖` (`theta_iterate_profile_of_analytic_*`). -/
def ThetaProfileContract (m : ℕ) (κprev : ℝ) (θprev : ℝ → Vec 2 → ℝ) (Cs N : ℝ) : Prop :=
  Infra.Section4.iterateCoordinateEnergyProfile θprev κprev N
    (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0

/-- **V increments, abstract amplitude `N`**: the literal conclusion of the
`iterate_V_abstract_amplitude_of_diffusivity_and_flow` (`Section4/IteratesVAbstractAmplitude.lean`).
Used with `N = S` by `relative_leading_error_of_jets` and by the temperature-error leaf. -/
def VIncrementContract (m : ℕ) (κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (Cs Rθ N : ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ Nstar β → ∀ v w : List (Fin 2), v.length = w.length →
    ∀ s, 0 ≤ s → s ≤ 1 →
    Real.sqrt (l2NormSq (Infra.Section4.iterateSpatialWord v
        (Infra.Section4.iterateIncrement T i s))) +
      Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
        (fun t => spaceGrad (Infra.Section4.iterateSpatialWord w
          (Infra.Section4.iterateIncrement T i t)))) ≤
    N * Infra.Section4.iterateAmplitude
      (Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
        max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ))) i *
      Infra.Section4.iterateAnalyticWeight v.length i
        (max (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (Cs / Rθ))

end Relative

/-! ## Quantifier blocks for producers

A producer of a per-instance contract `P` proves `∃ C₁, OnA7Instances β C₀ C₁ P` (or the step-down
    estimate
version), with all its constants chosen before this (i.e. before `I`). -/

/-- The big-bound estimate / step-down part (i) premise block (`IndyStepDownV2Inputs.bigbound`):
    cutoff bounds, Λ-threshold `C₁`,
stream sequence, permissible `κ`, analytic mean-zero datum, `m ≥ m_θ₀(R)`, classical `θ_{m-1}`,
the T-iterates. -/
def OnA7Instances (β C₀ C₁ : ℝ)
    (P : ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ → ℝ → ℕ → ℝ →
      (Vec 2 → ℝ) → ℕ → (ℝ → Vec 2 → ℝ) → (ℕ → ℝ → Vec 2 → ℝ) → Prop) : Prop :=
  ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C₁ ≤ (I.Λ : ℝ) →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
    ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
    ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
    ∀ R : ℝ, 0 < R →
    ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
      IsThetaAnalytic R θ₀ →
    ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
    ∀ (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
      IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
      I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      P I Φ hΦ κ M R θ₀ m θprev T

/-- The full step-down premise block (`IndyStepDownV2Inputs.partI` / `.relative`): `OnA7Instances`
    plus the
classical `θ_m`. -/
def OnA8Instances (β C₀ C₁ : ℝ)
    (P : ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ → ℝ → ℕ → ℝ →
      (Vec 2 → ℝ) → ℕ → (ℝ → Vec 2 → ℝ) → (ℝ → Vec 2 → ℝ) → (ℕ → ℝ → Vec 2 → ℝ) → Prop) :
    Prop :=
  ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C₁ ≤ (I.Λ : ℝ) →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
    ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
    ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
    ∀ R : ℝ, 0 < R →
    ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
      IsThetaAnalytic R θ₀ →
    ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
    ∀ (θm θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
      IsClassicalSol (streamVel (Φ m)) (I.kappaSeq κ M m) (fun _ _ => 0) θ₀ θm →
      IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
      I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      P I Φ hΦ κ M R θ₀ m θm θprev T

/-! ## main theorem main contracts -/

/-- The literal step-down body (`AVenhance.indystepdown`), consumed by main theorem
(`anomalous_dissipation_of_A8_A1c`). Produced by `indystepdown_v2_of_inputs` from
`IndyStepDownV2Inputs`. -/
def IndyStepDownContract (β C₀ : ℝ) : Prop := IndyStepDownStatement β C₀

/-- The literal classical well-posedness body (`AVenhance.classical_wellposed`, public), consumed
    by main theorem
(`anomalous_dissipation_of_A8_A1c`) for the classical solvability of every finite drift. -/
def ClassicalWellposedContract : Prop := ClassicalWellposedStatement

end AVenhance.Infra.Section5.Integration
