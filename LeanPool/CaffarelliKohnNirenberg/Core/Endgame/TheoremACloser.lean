/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.ThetaDecayTShape
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.InitialUniform
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapPressureConsumer
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.FinalPressureConsumer
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CarrierRestriction
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.StartCaccioppoli
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremABudgetBridge
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRemainderMajorant
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseDerivativeShared
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTranslatedSlice
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.GradientSlotDuhamel
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSided
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPAffineSlot
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.GAAdaptersCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremBAdaptersCZSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremAAdaptersLin34
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremAAdaptersCZ

/-! # Composition of the small-data regularity theorem

This module writes the proof of `thm:A` once, in the order of the manuscript,
as a family of statements each of which assumes one remaining display.
The theorem does not go through this file: it is proved by
`CKN.Core.Endgame.epsilonRegularityL3_of_instance_slots_q`, whose proof is
the same composition with the pressure-gradient hypothesis narrowed to the
two exponent-radius triples that `thm:A` actually consumes. Read this file
for the shape of the argument and that one for what is checked.

`epsilonRegularityL3_closer_of_pending_inputs` is that shape. Reading its
proof against the manuscript:

* `thetaDecay_T_of_inputs` is `eq:theta-decay-2`, and fixes `κ`, `η`, `Λ₀`
  of `conv:kappa`.
* `theoremA_initial_uniform_of_displays` is the start lemma
  `lem:thmA-start` together with Steps 1 and 2 of the proof of `thm:A`: the
  scale iteration `prop:iteration` at every centre of `Q_{3/4}`, giving
  `eq:thmA-morrey`, and the one-sided Morrey transfer onto the cylinder of
  radius `11/16`, giving `eq:step2-morrey` for the velocity and its gradient.
  The manuscript states the transfer on `Q₂^♯` of radius `5/8`; the larger
  radius is proved here because the bootstrap round of `prop:bootstrap`
  consumes the outer cylinder and produces the inner one. The pressure
  Morrey norm of `eq:step2-morrey` is available from the same transfer and
  is not needed downstream, exactly as in the manuscript.
* `exists_uniform_bootstrap_of_initial_pressure` is `prop:bootstrap` at
  `τ = τ₂ = 25/3`, with the sources split at `t = 0` as in Step 3, taking
  the velocity from `𝓜^{3,25/3}` on radius `11/16` to `𝓜^{3,25}` on radius
  `5/8`. This is the single round of `cor:one-round`.
* `exists_uniform_halfCylinder_of_final_pressure` is `thm:endgame` on the
  one-sided cylinder, again with the sources split at `t = 0`. It consumes
  the velocity in both `𝓜^{3,25}` and `𝓜^{3,25/3}`, and produces the
  Hölder representative of `thm:A` with exponent
  `γ₀ = min {2 - 5/q, 1/5}` of `eq:gamma-value`.
* The hypothesis `hGA` is `lem:pressure-gradient-morrey`, asked for at the
  two triples `(τ, R₀, R₁) = (25/3, 11/16, 43/64)` and `(25, 5/8, 19/32)`.
  Its Morrey exponent `min ((1/τ + 8/25)⁻¹) q` of
  `eq:pressure-gradient-morrey` is `25/11` at the first triple and
  `min {q, 25/9}` at the second.

The carrier of the pressure gradient is the backward cylinder about the
origin rather than a symmetric parabolic ball: the only containment `thm:A`
supplies is `closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I`, and a
symmetric ball about any point of that set contains times after it.
The numerical majorant is `oneSidedPressureGradientKPAffine`, and all
numerical constants are fixed before the solution fields.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential


noncomputable section

namespace CKN

namespace Core.Endgame

/-- The small-data conclusion `thm:A` from the two remaining pressure
displays.  The oscillation display `eq:lin35-force` and the localized heat
representation of `lem:local-equation` are discharged by their
suitable-weak-solution theorems. -/
theorem epsilonRegularityL3_closer_of_pending_inputs
    (q C₁₂_p1 C_CZ : ℝ) (hq : 5 / 2 < q) (hC : 0 ≤ C_CZ)
    (hCZ_p1 :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ r : ℝ}, (hρ : 0 < ρ) → 0 < r → r ≤ ρ / 2 →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
          ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ *
            alpha u z ρ * beta u Du z ρ))
    (hGA : ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
      5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
      0 ≤ C_CZ →
      0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
      KU < ∞ → KD < ∞ →
      ∃ KP : ℝ≥0∞, KP < ∞ ∧
        ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
          (∀ i, morreyNorm 3 τ
            ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
              (fun z => u z i)) ≤ KU) →
          (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
            ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
              (fun z => Du z i j)) ≤ KD) →
          ((∫⁻ z in parabolicCylinder 0 0 1,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε) →
          ∃ Dp : ParabolicPoint → Vec3,
            (∀ i, AEMeasurable (fun z => Dp z i)
              (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
            (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
              U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
              Integrable (fun z => Dp z i)
                (volume.restrict (spaceTimeSet U J))) ∧
            (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
              ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
              tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
              (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
            (∀ i, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
                (fun z => Dp z i)) ≤ KP)) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  let C₃₂ := theoremALin34Constant q
  have hC₃₂ : 0 ≤ C₃₂ := theoremALin34Constant_nonneg q hq
  obtain ⟨C₂₇, C₂₈, hC₂₇, hC₂₈, hThetaDecay⟩ :=
    thetaDecay_T_of_inputs q C₁₂_p1 hCZ_p1
  obtain ⟨ε₀, KUinitial, KD, hε₀, hKUinitial, hKD, hinitial⟩ :=
    theoremA_initial_uniform_of_displays q startGammaConstant (caccioppoliC₂₆ q)
      C₂₇ C₂₈ C₃₂ hq hC₂₇ hC₂₈ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC₃₂
      (fun hsol => caccioppoli_gamma_display_fixed hsol) (theoremA_hLin34_of_sws q)
      (fun {Ω I u Du p f} hsol => hThetaDecay Ω I u Du p f hsol)
  obtain ⟨KU, hKU, hbootstrap⟩ := exists_uniform_bootstrap_of_initial_pressure
    q ε₀ KUinitial KD hq hKUinitial hKD
    (by
      obtain ⟨KP, hKP, hpressure⟩ := hGA q (25 / 3) C_CZ (11 / 16) (43 / 64)
        ε₀ KUinitial KD hq (by norm_num) (by norm_num) hC
        (by norm_num) (by norm_num) (by norm_num) hε₀.le hKUinitial hKD
      refine ⟨KP, hKP, ?_⟩
      intro Ω I u f Du p hsol hdom hsmall hU hD
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hpressure hsol hdom hU hD hsmall
      refine ⟨Dp, hAE, hInt, hweak, ?_⟩
      intro i
      have hmin : min (((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹) q = 25 / 11 := by
        rw [show ((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹ = 25 / 11 by norm_num]
        exact min_eq_left (by linarith only [hq])
      simpa only [hmin] using hN i)
    (fun _ _ _ _ _ _ _ hsol _ _ _ hφ hbox hsupp hInt hweak =>
      localized_gradient_slot_duhamel_of_sws hsol hφ hbox hsupp hInt hweak)
  obtain ⟨C₄, hC₄, hfinal⟩ := exists_uniform_halfCylinder_of_final_pressure
    q ε₀ KU KUinitial KD hq hε₀.le hKU hKUinitial hKD
    (by
      obtain ⟨KP, hKP, hpressure⟩ := hGA q 25 C_CZ (5 / 8) (19 / 32)
        ε₀ KU KD hq (by norm_num) (by norm_num) hC
        (by norm_num) (by norm_num) (by norm_num) hε₀.le hKU hKD
      refine ⟨KP, hKP, ?_⟩
      intro Ω I u f Du p hsol hdom hsmall hU hD
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hpressure hsol hdom hU hD hsmall
      refine ⟨Dp, hAE, hInt, hweak, ?_⟩
      intro i
      have hexp : ((1 / (25 : ℝ)) + 8 / 25)⁻¹ = 25 / 9 := by norm_num
      simpa only [hexp, min_comm] using hN i)
    (fun _ _ _ _ _ _ _ hsol _ _ _ hφ hbox hsupp hInt hweak =>
      localized_gradient_slot_duhamel_of_sws hsol hφ hbox hsupp hInt hweak)
  refine ⟨ε₀, stepGamma₀ q, C₄, hε₀, stepGamma₀_pos hq,
    (stepGamma₀_le_fifth q).trans (by norm_num), hC₄, ?_⟩
  intro Ω I u Du p f hsol hdom hsmall
  obtain ⟨hUinitial, hD⟩ := hinitial hsol hdom hsmall
  have hU := hbootstrap Ω I u f Du p hsol hdom hUinitial hD hsmall
  have hsub : parabolicCylinder (0 : Vec3) 0 (5 / 8) ⊆
      parabolicCylinder (0 : Vec3) 0 (11 / 16) :=
    parabolicCylinder_mono (by norm_num) (by norm_num)
  apply hfinal Ω I u f Du p hsol hdom hU
  · intro i
    exact (morreyNorm_indicator_mono_set (by norm_num : (0 : ℝ) ≤ 3)
      hsub (fun z => u z i)).trans (hUinitial i)
  · intro i j
    exact (morreyNorm_indicator_mono_set (by norm_num : (0 : ℝ) ≤ 2)
      hsub (fun z => Du z i j)).trans (hD i j)
  · exact hsmall

/-- The same conclusion from the two displays in the shape their own arguments
produce them: the almost-every-time slice certificate of `ext:CZ` and the
explicit-majorant form of `prop:bootstrap`. -/
theorem epsilonRegularityL3_closer_of_slice_and_quantitative
    (q C₁₂_p1 C_CZ : ℝ) (hq : 5 / 2 < q) (hC_CZ : 0 ≤ C_CZ)
    (hconst : C_CZ * (9 * sobolevPoincareL6Constant.toReal) ≤ C₁₂_p1)
    (hSlice :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          MemLp (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
          lpNorm (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
            C_CZ *
              (∫ y in vec3Ball z.1 ρ,
                (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ))
    (hGA : oneSidedPressureGradientQuantitative) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  refine epsilonRegularityL3_closer_of_pending_inputs q C₁₂_p1 C_CZ hq hC_CZ
    (theoremA_hCZ_p1_of_slice_bounds q C₁₂_p1 C_CZ hC_CZ hconst hSlice) ?_
  intro q' τ C R₀ R₁ ε KU KD hq' hτ hτ' hC' hR₁ hR₁R₀ hR₀ hε hKU hKD
  obtain ⟨hKP, hout⟩ :=
    hGA q' τ C R₀ R₁ ε KU KD hq' hτ hτ' hC' hR₁ hR₁R₀ hR₀ hε hKU hKD
  exact ⟨_, hKP, hout⟩

/-- **The exact conclusion of `thm:A` from two displays.**  The cylinder
constant of `ext:CZ` is fixed to the value the slice transfer produces, so the
only data preceding the solution are the force exponent and the slice constant
of `ext:CZ`, and the only assumptions are the almost-every-time slice
certificate of `ext:CZ` and the explicit-majorant display `prop:bootstrap`.
Apart from those two, this is the statement of `thm:A` verbatim. -/
theorem epsilonRegularityL3_closer_of_two_displays
    (q C_CZ : ℝ) (hq : 5 / 2 < q) (hC_CZ : 0 ≤ C_CZ)
    (hSlice :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          MemLp (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
          lpNorm (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
            C_CZ *
              (∫ y in vec3Ball z.1 ρ,
                (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ))
    (hGA : oneSidedPressureGradientQuantitative) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z :=
  epsilonRegularityL3_closer_of_slice_and_quantitative q
    (C_CZ * (9 * sobolevPoincareL6Constant.toReal)) C_CZ hq hC_CZ le_rfl
    hSlice hGA

/-- **Reduction to pressure-gradient and bootstrap estimates.**  The
pressure-gradient input is reduced to the origin-cell estimate of
`prop:bootstrap`, and the pressure input to the almost-every-time slice
certificate of `ext:CZ`; the cylinder constant is fixed by the slice transfer.
Everything else in `thm:A` is proved. -/
theorem epsilonRegularityL3_closer_of_cell_and_slice
    (q C_CZ : ℝ) (hq : 5 / 2 < q) (hC_CZ : 0 ≤ C_CZ)
    (hSlice :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          MemLp (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
          lpNorm (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
            C_CZ *
              (∫ y in vec3Ball z.1 ρ,
                (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ))
    (hcell : ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
      5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
      0 ≤ C_CZ →
      0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
      KU < ∞ → KD < ∞ →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3}
          {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
          (∀ i, morreyNorm 3 τ
            ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
              (fun z => u z i)) ≤ KU) →
          (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
            ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
              (fun z => Du z i j)) ≤ KD) →
          ((∫⁻ z in parabolicCylinder 0 0 1,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε) →
          ∃ Dp : ParabolicPoint → Vec3,
            (∀ i, AEMeasurable (fun z => Dp z i)
              (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
            (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
              U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
              Integrable (fun z => Dp z i)
                (volume.restrict (spaceTimeSet U J))) ∧
            (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
              ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
              tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
              (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
            oneSidedPressureGradientOriginCellOutput R₁
              (min ((1 / τ + 8 / 25)⁻¹) q)
              (oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD) Dp) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z :=
  epsilonRegularityL3_closer_of_pending_inputs q
    (C_CZ * (9 * sobolevPoincareL6Constant.toReal)) C_CZ hq hC_CZ
    (theoremA_hCZ_p1_of_slice_bounds q
      (C_CZ * (9 * sobolevPoincareL6Constant.toReal)) C_CZ hC_CZ le_rfl hSlice)
    (pressure_gradient_existential_of_origin_cell_producer hcell)

/-- **`thm:A` from the one-sided pressure-gradient display alone.**  With the
Calderón--Zygmund estimate `ext:CZ` supplied at solution level, the oscillation
display `eq:lin35-force` of `prop:lin34` supplied by its own theorem, and the
localized heat representation of `lem:local-equation` supplied by its own
theorem, the explicit-majorant form of `prop:bootstrap` is the only remaining
assumption.  Apart from it, this is the statement of `thm:A` verbatim. -/
theorem epsilonRegularityL3_closer_of_gradient_display
    (q : ℝ) (hq : 5 / 2 < q)
    (hGA :
    ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ⊤ → KD < ⊤ →
    oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD < ⊤ ∧
    ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
            (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
            (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ)
              (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
                (fun z => Dp z i)) ≤
            oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD)) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  apply epsilonRegularityL3_closer_of_pending_inputs q
    ((9 * max czP1OperatorConstant 0) *
      (9 * sobolevPoincareL6Constant.toReal)) 0 hq le_rfl
    (theoremB_hCZ_p1_of_sws q)
  intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  obtain ⟨hKP, hout⟩ := hGA q' τ C_CZ R₀ R₁ ε KU KD
    hq' hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  exact ⟨_, hKP, hout⟩

/-- **`thm:A` from the origin-cell estimate of `prop:bootstrap` alone.**  This
is the deepest reduction available: every other display used by the small-data
argument is proved, and the single assumption is the Morrey-cell bound for the
selected pressure gradient on the one-sided cylinder. -/
theorem epsilonRegularityL3_closer_of_cell_producer
    (q : ℝ) (hq : 5 / 2 < q)
    (hcell : ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
      5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
      0 ≤ C_CZ →
      0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
      KU < ∞ → KD < ∞ →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
          {u : ParabolicPoint → Vec3}
          {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
          (∀ i, morreyNorm 3 τ
            ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
              (fun z => u z i)) ≤ KU) →
          (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
            ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
              (fun z => Du z i j)) ≤ KD) →
          ((∫⁻ z in parabolicCylinder 0 0 1,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε) →
          ∃ Dp : ParabolicPoint → Vec3,
            (∀ i, AEMeasurable (fun z => Dp z i)
              (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
            (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
              U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
              Integrable (fun z => Dp z i)
                (volume.restrict (spaceTimeSet U J))) ∧
            (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
              ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
              tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
              (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
            oneSidedPressureGradientOriginCellOutput R₁
              (min ((1 / τ + 8 / 25)⁻¹) q)
              (oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD) Dp) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z :=
  epsilonRegularityL3_closer_of_gradient_display q hq
    (oneSidedPressureGradientQuantitative_to_KPAffine
      (pressure_gradient_quantitative_of_origin_cell_producer hcell))


/-- The carrier Morrey norms of a measurable field bound its clipped slice
integrals on every cell. -/
theorem theoremA_clipped_growth_of_carrier_morrey {κ R₁ : ℝ} {Dp : ParabolicPoint → Vec3}
    (hm : Measurable Dp) (i : Fin 3) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-R₁ ^ 2) 0,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
      (∑ j : Fin 3, morreyNorm (6 / 5 : ℝ) κ
        ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun w => Dp w j)) ^ (6 / 5 : ℝ)) *
        ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / κ))) := by
  let Q := parabolicCylinder (0 : Vec3) 0 R₁
  let N := fun j : Fin 3 => morreyNorm (6 / 5 : ℝ) κ (Q.indicator (fun w => Dp w j))
  let A := ∑ j : Fin 3, N j ^ (6 / 5 : ℝ)
  have hQm : MeasurableSet Q := measurableSet_parabolicCylinder _ _ _
  have hFi := (measurable_pi_apply i).comp hm
  have hmass := cylinderPowerIntegral_le_morreyNorm_pow (q := κ)
    (by norm_num : (0 : ℝ) < 6 / 5) (hFi.indicator hQm).aemeasurable (z := z) hr
  rw [ENNReal.ofReal_rpow_of_pos hr] at hmass
  have hnA : N i ^ (6 / 5 : ℝ) ≤ A :=
    Finset.single_le_sum (f := fun j : Fin 3 => N j ^ (6 / 5 : ℝ))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  have hbound : cylinderPowerIntegral (6 / 5 : ℝ) (Q.indicator (fun w => Dp w i)) z r ≤
      A * ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / κ))) :=
    hmass.trans ((mul_le_mul' le_rfl hnA).trans_eq (mul_comm _ _))
  have hprod : AEStronglyMeasurable (fun w => Dp w i)
      ((volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)).prod
        (volume.restrict (Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-R₁ ^ 2) 0))) := by
    rw [← originClauseRestrict_prod_eq]
    exact hFi.aestronglyMeasurable.restrict
  rw [(glued_slice_norm_power_integral (by norm_num : (0 : ℝ) < 6 / 5) hprod).2]
  rw [cylinderPowerIntegral_carrier_eq (by norm_num) hQm,
    parabolicCylinder_inter_origin_eq_prod] at hbound
  convert hbound using 1
  simp only [Real.enorm_eq_ofReal_abs]
  rfl

section FullSumAssembly

variable (hFullSumComparison :
  ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε → KU < ⊤ → KD < ⊤ →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
      ((∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
      oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) R₁
        (∑ i : Fin 3, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
          ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun w => Dp w i)) ^ (6 / 5 : ℝ))
        ((∑ i : Fin 3, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
          ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun w => Dp w i)) ^ (6 / 5 : ℝ)) *
          ENNReal.ofReal (R₁ ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) ≤
        oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD)

include hFullSumComparison

/-- The concrete temporal remainder and the full-sum comparison give the
pressure-gradient bound with the enlarged numerical constant. -/
theorem theoremA_hGA_of_full_sum_comparison :
  ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ∞ → KD < ∞ →
    oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD < ⊤ ∧
    ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
            (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
            (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ)
              (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
                (fun z => Dp z i)) ≤
            oneSidedPressureGradientKPAffine q τ C_CZ R₀ R₁ ε KU KD) := by
  intro q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  refine ⟨oneSidedPressureGradientKPAffine_lt_top q' τ C_CZ R₀ R₁ ε KU KD hq' hKU hKD, ?_⟩
  intro Ω I u Du p f hsol hdom hU hD hsize
  obtain ⟨Dp, hm, hw, _hn⟩ := originClause_derivative_morrey_of_temporal_majorant
    fixed_remainder_temporal_majorant_of_sws hq' hτ hτu hR₁ hR₁R₀
    (by linarith only [hR₀]) hKU hKD hsol hdom hU hD
  let A := ∑ j : Fin 3, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q')
    ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun w => Dp w j)) ^ (6 / 5 : ℝ)
  let B := A * ENNReal.ofReal
    (R₁ ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q')))
  let M : Fin 3 → Vec3 → ℝ → ℝ → ℝ≥0∞ := fun i x r s =>
    eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁))
  obtain ⟨htop, hint⟩ := origin_carrier_slice_time_obligations_of_sws
    hR₁ (hR₁R₀.trans hR₀) hsol hdom Dp hm hw
  have hgrowth := fun i z r (hr : 0 < r) =>
    theoremA_clipped_growth_of_carrier_morrey (κ := min ((1 / τ + 8 / 25)⁻¹) q') (R₁ := R₁) hm i z
      hr
  have hglobal : ∀ i : Fin 3,
      (∫⁻ s in Ioc (-(R₁ ^ 2)) 0, M i (0 : Vec3) R₁ s ^ (6 / 5 : ℝ)) ≤ B := by
    intro j
    simpa only [M, B, zero_sub, inter_self] using hgrowth j ((0 : Vec3), 0) R₁ hR₁
  have htop' : ∀ i : Fin 3, ∀ᵐ s ∂(volume.restrict I), M i (0 : Vec3) R₁ s ≠ ⊤ := by
    simpa only [M, inter_self] using htop
  have hint' : ∀ i : Fin 3, ∀ T : Set ℝ, IsCompact (closure T) → closure T ⊆ I →
      Integrable (fun s => (M i (0 : Vec3) R₁ s).toReal) (volume.restrict T) := by
    simpa only [M, inter_self] using hint
  obtain ⟨D, hAE, hInt, hpair, hcells⟩ :=
    theoremA_origin_cell_producer_of_clipped_data (A := A) (B := B)
      (KP := oneSidedPressureGradientKPAffine q' τ C_CZ R₀ R₁ ε KU KD)
      hq' hτ hR₁ hR₁R₀ hR₀ hsol hdom M
      ⟨(fun j x r => hw.mono (fun s hs =>
        ⟨fun y => Dp (y, s) j, (hs j).1, (hs j).2, le_rfl⟩)),
        htop', hint', (fun j z _hz r hr _hrR => hgrowth j z r hr), hglobal⟩
      (hFullSumComparison q' τ C_CZ R₀ R₁ ε KU KD hq' hτ hτu hC hR₁ hR₁R₀ hR₀ hε hKU hKD
        hsol hdom hU hD hsize Dp hm hw)
  exact ⟨D, hAE, hInt, hpair,
    fun i => pressure_gradient_morrey_bound (fun z r => hcells i z r)⟩

/-- The small-data regularity conclusion from the full-sum comparison,
with the temporal remainder and carrier time estimates supplied by suitability. -/
theorem epsilonRegularityL3_closer_of_full_sum_comparison
    (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
              ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  exact epsilonRegularityL3_closer_of_gradient_display q hq
    (theoremA_hGA_of_full_sum_comparison hFullSumComparison)

end FullSumAssembly

end Core.Endgame

end CKN
