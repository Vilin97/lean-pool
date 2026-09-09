/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingDilation
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricTerminalCompensation
public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatProfileExtension

@[expose] public section

/-!
# The physical heat continuation with exact terminal compensation

One normalized outgoing profile supplies the angular reset and axial amplitude.
Its radial dilation is heated with diffusion `1 - eta^2`, and three additive
bumps on its actual second reserved patch restore the three changed moments.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators
open NavierStokes.OutgoingProfile (Profile)
open NavierStokes.OutgoingDilation (switchRadius patchRadius patchRatio compensationPatch
  shapedPatchAmplitude)

namespace NavierStokes.HeatedOutgoing

abbrev Coeff := TerminalCompensation.Coeff

def parameterDomain : Set ℝ := Icc (-1) 1
def domain : Set (ℝ × ℝ) := Ioi 0 ×ˢ parameterDomain

noncomputable def heatE (F : Profile) (XR : ℝ) (p : ℝ × ℝ) : ℝ :=
  OutgoingDilation.E F XR p * HeatTailEdit.multiplier F.data.h
    (ParametricHeatTail.diffusion p.2) (switchRadius F XR) p.1

noncomputable def patchIncrement (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  shapedPatchAmplitude F p.2 * TerminalCompensation.correction compensationPatch (c p.2)
    (p.1 / patchRadius F XR)

noncomputable def E (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  heatE F XR p + patchIncrement F XR c p

noncomputable def U (F : Profile) (XR : ℝ) : ℝ × ℝ → ℝ := OutgoingDilation.U F XR
noncomputable def H (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (2 * p.1) * E F XR c p

noncomputable def canonicalKernel (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) : ℝ :=
  E F XR c (X, eta) ^ 2 / X
noncomputable def Pi (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ X in Ioi p.1, canonicalKernel F XR c p.2 X
noncomputable def axisDatum (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ X in Ioi 0, canonicalKernel F XR c eta X
noncomputable def energyDensity (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) : ℝ :=
  U F XR (X, eta) ^ 2 - E F XR c (X, eta) ^ 2 / 2
noncomputable def totalS (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  ∫ X in Ioi 0, energyDensity F XR c eta X
noncomputable def M (F : Profile) (XR eta X : ℝ) : ℝ := ∫ u in Ioc 0 X, U F XR (u, eta)
noncomputable def J (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) : ℝ :=
  ∫ u in Ioc 0 X, H F XR c (u, eta) * U F XR (u, eta)

/-- Only the already proved smooth extension is used off the physical band. -/
noncomputable def extendedHeatE (F : Profile) (XR : ℝ) (p : ℝ × ℝ) : ℝ :=
  OutgoingDilation.E F XR p * (1 + HeatTailEdit.switch (switchRadius F XR) p.1 *
    (HeatProfileExtension.physicalProfile (1 + F.data.h) p.1 p.2 - 1))

theorem heatE_eq_extended (F : Profile) (XR : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain) :
    heatE F XR p = extendedHeatE F XR p := by
  rw [extendedHeatE, HeatProfileExtension.physicalProfile_eq_profile (1 + F.data.h) hp.1 hp.2]
  rfl

theorem extendedHeatE_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) :
    ContDiffOn ℝ ∞ (extendedHeatE F XR) OutgoingProfile.domain := by
  have hs := (HeatTailEdit.switch_contDiffOn (OutgoingDilation.switchRadius_pos F XR hXR)).comp
    contDiffOn_fst (fun p (hp : p ∈ OutgoingProfile.domain) => hp.1)
  have hp := HeatProfileExtension.physicalProfile_contDiffOn
    (show 1 < 1 + F.data.h by linarith [F.data.h_pos])
  exact (OutgoingDilation.E_contDiffOn F XR hXR).mul
    (contDiffOn_const.add (hs.mul (hp.sub contDiffOn_const)))

theorem heatE_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) :
    ContDiffOn ℝ ∞ (heatE F XR) domain := by
  apply ((extendedHeatE_contDiffOn F XR hXR).mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).congr
  intro p hp
  exact heatE_eq_extended F XR hp

theorem patchIncrement_contDiffOn (F : Profile) (XR : ℝ) {c : ℝ → Coeff}
    (hc : ContDiffOn ℝ ∞ c parameterDomain) :
    ContDiffOn ℝ ∞ (patchIncrement F XR c) domain := by
  have hr := (TerminalCompensation.correction_family_contDiffOn compensationPatch hc).comp
    (contDiffOn_snd.prodMk (contDiffOn_fst.div_const (patchRadius F XR)))
    (fun p (hp : p ∈ domain) => ⟨hp.2, mem_univ _⟩)
  exact ((OutgoingDilation.shapedPatchAmplitude_contDiff F).comp_contDiffOn contDiffOn_snd).mul hr

theorem E_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) {c : ℝ → Coeff}
    (hc : ContDiffOn ℝ ∞ c parameterDomain) : ContDiffOn ℝ ∞ (E F XR c) domain :=
  (heatE_contDiffOn F XR hXR).add (patchIncrement_contDiffOn F XR hc)

theorem U_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) : ContDiffOn ℝ ∞ (U F XR) domain :=
  (OutgoingDilation.U_contDiffOn F XR hXR).mono (fun _ hp => ⟨hp.1, mem_univ _⟩)

theorem H_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) {c : ℝ → Coeff}
    (hc : ContDiffOn ℝ ∞ c parameterDomain) : ContDiffOn ℝ ∞ (H F XR c) domain :=
  ((contDiffOn_const.mul contDiffOn_fst).sqrt
    (fun _ hp => ne_of_gt (mul_pos (by norm_num) hp.1))).mul (E_contDiffOn F XR hXR hc)

theorem heatE_before (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X)
    (hXK : X ≤ switchRadius F XR) : heatE F XR (X, eta) = OutgoingDilation.E F XR (X, eta) :=
  HeatTailEdit.edit_before (fun u => OutgoingDilation.E F XR (u, eta)) F.data.h _
    (OutgoingDilation.switchRadius_pos F XR hXR) hX hXK

theorem heatE_after (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR)
    (hXK : switchRadius F XR ≤ X) :
    heatE F XR (X, eta) = ParametricHeatTail.physicalEdit F.data (switchRadius F XR) eta X := by
  unfold heatE ParametricHeatTail.physicalEdit HeatTailEdit.outgoingEdit HeatTailEdit.edit
  rw [OutgoingDilation.E_eq_clean_switch_profile F XR eta X hXR hXK]

theorem E_after_switch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) (hXR : 0 < XR)
    (hXK : switchRadius F XR ≤ X) :
    E F XR c (X, eta) = ParametricHeatTail.physicalEdit F.data (switchRadius F XR) eta X := by
  rw [E, patchIncrement, OutgoingDilation.correction_zero_after_switch F XR X hXR (c eta) hXK,
    mul_zero, add_zero, heatE_after F XR eta X hXR hXK]

theorem patch_below_switch (F : Profile) (XR X : ℝ) (hXR : 0 < XR)
    (hpatch : X / patchRadius F XR ∈ Icc compensationPatch.left compensationPatch.right) :
    X < switchRadius F XR := by
  have hx : X ≤ patchRadius F XR * compensationPatch.right := by
    simpa only [mul_comm] using (div_le_iff₀ (OutgoingDilation.patchRadius_pos F XR hXR)).mp
      hpatch.2
  exact hx.trans_lt (OutgoingDilation.patch_before_switch F XR hXR)

theorem E_on_patch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) (hXR : 0 < XR)
    (hX : 0 < X) (hpatch : X / patchRadius F XR ∈ Icc compensationPatch.left
      compensationPatch.right) :
    E F XR c (X, eta) = TerminalCompensation.physicalProfile compensationPatch F.data.core.lam
      (patchRadius F XR) (shapedPatchAmplitude F eta) (c eta) X := by
  rw [E, heatE_before F XR eta X hXR hX (patch_below_switch F XR X hXR hpatch).le,
    OutgoingDilation.patch_model F XR eta X hXR hpatch]
  unfold patchIncrement TerminalCompensation.physicalProfile TerminalCompensation.cleanProfile
  ring

theorem patchIncrement_eq_difference (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) :
    patchIncrement F XR c (X, eta) =
      TerminalCompensation.physicalProfile compensationPatch F.data.core.lam
        (patchRadius F XR) (shapedPatchAmplitude F eta) (c eta) X -
      TerminalCompensation.cleanProfile F.data.core.lam (patchRadius F XR) (shapedPatchAmplitude F
        eta) X := by
  unfold patchIncrement TerminalCompensation.physicalProfile TerminalCompensation.cleanProfile
  ring

theorem correction_zero_outside (c : Coeff) {x : ℝ}
    (hx : x ∉ Icc compensationPatch.left compensationPatch.right) :
    TerminalCompensation.correction compensationPatch c x = 0 := by
  by_contra hn
  exact hx (TerminalCompensation.correction_support compensationPatch c hn)

theorem E_before_patch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) (hpatch : X ≤ patchRadius F XR) :
    E F XR c (X, eta) = OutgoingDilation.E F XR (X, eta) := by
  have hright : 1 ≤ compensationPatch.right := compensationPatch.ordered.le
  have hK : X ≤ switchRadius F XR := hpatch.trans
    ((le_mul_of_one_le_right (OutgoingDilation.patchRadius_pos F XR hXR).le hright).trans
      (OutgoingDilation.patch_before_switch F XR hXR).le)
  have hc : TerminalCompensation.correction compensationPatch (c eta) (X / patchRadius F XR) = 0 :=
    by
    by_contra hn
    have ht := TerminalCompensation.correction_tsupport compensationPatch (c eta) (subset_tsupport
      _ hn)
    have hx := (div_le_one (OutgoingDilation.patchRadius_pos F XR hXR)).mpr hpatch
    exact (not_lt_of_ge hx) ht.1
  rw [E, heatE_before F XR eta X hXR hX hK, patchIncrement, hc, mul_zero, add_zero]

theorem heatE_pos (F : Profile) (XR eta X : ℝ) (hX : 0 < X) (heta : eta ∈ parameterDomain) :
    0 < heatE F XR (X, eta) :=
  mul_pos (OutgoingDilation.positive F XR _) (HeatTailEdit.multiplier_bounds F.data.h_pos
    (ParametricHeatTail.diffusion_mem heta).1 hX).1

noncomputable def heatRow (F : Profile) (XR eta : ℝ) (i : Fin 3) (X : ℝ) : ℝ :=
  ![HeatTailEdit.squareChange (HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta)
      F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X / X,
    HeatTailEdit.squareChange (HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta)
      F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X,
    Real.sqrt (2 * X) * HeatTailEdit.change (HeatTailEdit.outgoingProfile F.data (switchRadius F
      XR) eta)
      F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X] i

noncomputable def patchRow (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ) (i : Fin 3) (X : ℝ) : ℝ
  :=
  let A := TerminalCompensation.physicalProfile compensationPatch F.data.core.lam
    (patchRadius F XR) (shapedPatchAmplitude F eta) (c eta) X
  let B := TerminalCompensation.cleanProfile F.data.core.lam (patchRadius F XR)
    (shapedPatchAmplitude F eta) X
  ![(A ^ 2 - B ^ 2) / X, A ^ 2 - B ^ 2, Real.sqrt (2 * X) * (A - B)] i

noncomputable def changeRow (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ) (i : Fin 3) (X : ℝ) :
  ℝ :=
  ![(E F XR c (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2) / X,
    E F XR c (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2,
    Real.sqrt (2 * X) * (E F XR c (X, eta) - OutgoingDilation.E F XR (X, eta))] i

theorem heat_differences (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    heatE F XR (X, eta) - OutgoingDilation.E F XR (X, eta) =
      HeatTailEdit.change (HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta)
        F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X ∧
    heatE F XR (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2 =
      HeatTailEdit.squareChange (HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta)
        F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X := by
  by_cases hle : X ≤ switchRadius F XR
  · rw [heatE_before F XR eta X hXR hX hle]
    simp only [HeatTailEdit.change, HeatTailEdit.squareChange,
      HeatTailEdit.edit_before _ _ _ (OutgoingDilation.switchRadius_pos F XR hXR) hX hle, sub_self,
        and_self]
  · have hge := (lt_of_not_ge hle).le
    rw [heatE_after F XR eta X hXR hge, OutgoingDilation.E_eq_clean_switch_profile F XR eta X hXR
      hge]
    exact ⟨rfl, rfl⟩

theorem patch_square_difference (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) :
    E F XR c (X, eta) ^ 2 - heatE F XR (X, eta) ^ 2 = patchRow F XR c eta 1 X := by
  by_cases hp : X / patchRadius F XR ∈ Icc compensationPatch.left compensationPatch.right
  · rw [E_on_patch F XR c eta X hXR hX hp,
      heatE_before F XR eta X hXR hX (patch_below_switch F XR X hXR hp).le,
      OutgoingDilation.patch_model F XR eta X hXR hp]
    rfl
  · have hc := correction_zero_outside (c eta) hp
    simp [E, patchIncrement, hc, patchRow, TerminalCompensation.physicalProfile,
      TerminalCompensation.cleanProfile]

theorem changeRow_decomposition (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ)
    (i : Fin 3) (X : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    changeRow F XR c eta i X = heatRow F XR eta i X + patchRow F XR c eta i X := by
  have hh := heat_differences F XR eta X hXR hX
  have hp := patch_square_difference F XR c eta X hXR hX
  have hl := patchIncrement_eq_difference F XR c eta X
  fin_cases i <;> norm_num [changeRow, heatRow, patchRow] at hp ⊢
  · rw [← hh.2, ← hp]
    ring
  · rw [← hh.2, ← hp]
    ring
  · rw [← hh.1]
    rw [E]
    rw [hl]
    ring

theorem positive_tail_indicator (f : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (hz : ∀ X : ℝ, 0 < X → X ≤ K → f X = 0) :
    (Ioi (0 : ℝ)).indicator f = (Ioi K).indicator f := by
  funext X
  by_cases h0 : X ∈ Ioi (0 : ℝ)
  · by_cases hk : X ∈ Ioi K
    · rw [indicator_of_mem h0, indicator_of_mem hk]
    · rw [indicator_of_mem h0, indicator_of_notMem hk]
      exact hz X h0 (le_of_not_gt hk)
  · have hk : X ∉ Ioi K := fun hx => h0 (hK.trans hx)
    rw [indicator_of_notMem h0, indicator_of_notMem hk]

theorem integrable_positive_tail (f : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (hz : ∀ X : ℝ, 0 < X → X ≤ K → f X = 0) (hi : IntegrableOn f (Ioi K)) :
    IntegrableOn f (Ioi 0) := by
  rw [← integrable_indicator_iff measurableSet_Ioi, positive_tail_indicator f K hK hz,
    integrable_indicator_iff measurableSet_Ioi]
  exact hi

theorem integral_positive_tail (f : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (hz : ∀ X : ℝ, 0 < X → X ≤ K → f X = 0) :
    (∫ X in Ioi 0, f X) = ∫ X in Ioi K, f X := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    positive_tail_indicator f K hK hz]

theorem heatRow_zero_before (F : Profile) (XR eta : ℝ) (i : Fin 3) (X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) (hXK : X ≤ switchRadius F XR) : heatRow F XR eta i X = 0 := by
  fin_cases i <;> simp [heatRow, HeatTailEdit.change, HeatTailEdit.squareChange,
    HeatTailEdit.edit_before _ _ _ (OutgoingDilation.switchRadius_pos F XR hXR) hX hXK]

theorem heatRow_integrable (F : Profile) (XR eta : ℝ) (i : Fin 3) (hXR : 0 < XR)
    (heta : eta ∈ parameterDomain) : IntegrableOn (heatRow F XR eta i) (Ioi 0) := by
  apply integrable_positive_tail _ (switchRadius F XR) (OutgoingDilation.switchRadius_pos F XR hXR)
    (fun X hX hXK => heatRow_zero_before F XR eta i X hXR hX hXK)
  have hi := ParametricHeatTail.physical_debts_integrable F.data
    (OutgoingDilation.switchRadius_pos F XR hXR) heta
  fin_cases i
  · exact hi.1
  · exact hi.2.1
  · exact hi.2.2

theorem heatRow_integral (F : Profile) (XR eta : ℝ) (i : Fin 3) (hXR : 0 < XR) :
    (∫ X in Ioi 0, heatRow F XR eta i X) =
      ParametricTerminalCompensation.physicalDebt F.data (switchRadius F XR) eta i := by
  rw [integral_positive_tail _ (switchRadius F XR) (OutgoingDilation.switchRadius_pos F XR hXR)
    (fun X hX hXK => heatRow_zero_before F XR eta i X hXR hX hXK)]
  fin_cases i <;> rfl

theorem patchRow_integrable (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ)
    (i : Fin 3) (hXR : 0 < XR) : IntegrableOn (patchRow F XR c eta i) (Ioi 0) := by
  have hi := TerminalCompensation.physicalMoments_integrable compensationPatch F.data.core.lam
    (patchRadius F XR) (shapedPatchAmplitude F eta) (OutgoingDilation.patchRadius_pos F XR hXR) (c
      eta)
  fin_cases i
  · exact hi.1.integrableOn
  · exact hi.2.1.integrableOn
  · exact hi.2.2.integrableOn

theorem patchRow_integral (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ)
    (i : Fin 3) (hXR : 0 < XR) :
    (∫ X in Ioi 0, patchRow F XR c eta i X) =
      TerminalCompensation.physicalMoments compensationPatch F.data.core.lam
        (patchRadius F XR) (shapedPatchAmplitude F eta) (c eta) i := by
  have he := TerminalCompensation.physicalMoments_positive_radius compensationPatch F.data.core.lam
    (patchRadius F XR) (shapedPatchAmplitude F eta) (OutgoingDilation.patchRadius_pos F XR hXR) (c
      eta)
  fin_cases i
  · exact (congrFun he 0).symm
  · exact (congrFun he 1).symm
  · exact (congrFun he 2).symm

/-- The coefficients are obtained below from the actual physical heat debts.
The base profile, hence its original reset and amplitude, is retained. -/
structure CompensationWitness (F : Profile) (XR C : ℝ) where
  radius_pos : 0 < XR
  switch_large : 1 ≤ switchRadius F XR
  coefficients : ℝ → Coeff
  smooth : ContDiffOn ℝ ∞ coefficients parameterDomain
  moments : ∀ eta ∈ parameterDomain,
    TerminalCompensation.physicalMoments compensationPatch F.data.core.lam
      (patchRadius F XR) (shapedPatchAmplitude F eta) (coefficients eta) +
      ParametricTerminalCompensation.physicalDebt F.data (switchRadius F XR) eta = 0
  coefficient_bound : ∀ eta ∈ parameterDomain, ‖coefficients eta‖ ≤ C / switchRadius F XR
  derivative_bound : ∀ eta ∈ parameterDomain,
    ‖derivWithin coefficients parameterDomain eta‖ ≤ C / switchRadius F XR
  first_jet : ∀ eta ∈ parameterDomain,
    ParametricTerminalCompensation.FirstJetWithinBound compensationPatch (shapedPatchAmplitude F)
      coefficients parameterDomain eta (C / switchRadius F XR)
  patch_positive : ∀ eta ∈ parameterDomain, ∀ X : ℝ, 0 < X →
    0 < TerminalCompensation.physicalProfile compensationPatch F.data.core.lam
      (patchRadius F XR) (shapedPatchAmplitude F eta) (coefficients eta) X

theorem exists_compensation (F : Profile) :
    ∃ XR₀ C : ℝ, 0 < XR₀ ∧ 0 < C ∧ ∀ XR : ℝ, XR₀ ≤ XR → Nonempty (CompensationWitness F XR C) := by
  obtain ⟨K₀, C, hK₀, hC, hc⟩ := ParametricTerminalCompensation.exists_physical_heat_compensation
    compensationPatch F.data.core.lam F.data.core.lam_pos.le F.data (patchRatio F)
    (OutgoingDilation.patchRatio_pos F) (shapedPatchAmplitude F)
    (OutgoingDilation.shapedPatchAmplitude_contDiff F).contDiffOn
    (fun eta _ => OutgoingDilation.shapedPatchAmplitude_pos F eta)
  let A : ℝ := Real.exp (HeatTailEdit.switchStart F.data)
  have hA : 0 < A := Real.exp_pos _
  let XR₀ : ℝ := max K₀ 1 / A
  have hXR₀ : 0 < XR₀ := div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hA
  refine ⟨XR₀, C, hXR₀, hC, ?_⟩
  intro XR hlarge
  have hXR : 0 < XR := hXR₀.trans_le hlarge
  have hK : max K₀ 1 ≤ switchRadius F XR := by
    exact (div_le_iff₀ hA).mp hlarge
  obtain ⟨c, hs, hspec⟩ := hc (switchRadius F XR) ((le_max_left _ _).trans hK)
  have hr := OutgoingDilation.patchRadius_eq_ratio F XR
  refine ⟨{
    radius_pos := hXR
    switch_large := (le_max_right _ _).trans hK
    coefficients := c
    smooth := hs
    moments := ?_
    coefficient_bound := fun eta heta => (hspec eta heta).2.1
    derivative_bound := fun eta heta => (hspec eta heta).2.2.1
    first_jet := fun eta heta => (hspec eta heta).2.2.2.1
    patch_positive := ?_ }⟩
  · intro eta heta
    rw [hr]
    exact (hspec eta heta).1
  · intro eta heta X hX
    rw [hr]
    exact (hspec eta heta).2.2.2.2 X hX

namespace CompensationWitness

variable {F : Profile} {XR C : ℝ} (w : CompensationWitness F XR C)

theorem positive (eta X : ℝ) (heta : eta ∈ parameterDomain) (hX : 0 < X) :
    0 < E F XR w.coefficients (X, eta) := by
  by_cases hp : X / patchRadius F XR ∈ Icc compensationPatch.left compensationPatch.right
  · rw [E_on_patch F XR w.coefficients eta X w.radius_pos hX hp]
    exact w.patch_positive eta heta X hX
  · have hc := correction_zero_outside (w.coefficients eta) hp
    rw [E, patchIncrement, hc, mul_zero, add_zero]
    exact heatE_pos F XR eta X hX heta

theorem changeRow_integrable (eta : ℝ) (i : Fin 3) (heta : eta ∈ parameterDomain) :
    IntegrableOn (changeRow F XR w.coefficients eta i) (Ioi 0) :=
  IntegrableOn.congr_fun ((heatRow_integrable F XR eta i w.radius_pos heta).add
    (patchRow_integrable F XR w.coefficients eta i w.radius_pos))
    (fun X hX => (changeRow_decomposition F XR w.coefficients eta i X w.radius_pos hX).symm)
    measurableSet_Ioi

theorem changeRow_integral_zero (eta : ℝ) (i : Fin 3) (heta : eta ∈ parameterDomain) :
    (∫ X in Ioi 0, changeRow F XR w.coefficients eta i X) = 0 := by
  calc
    _ = ∫ X in Ioi 0, heatRow F XR eta i X + patchRow F XR w.coefficients eta i X :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun X hX => changeRow_decomposition F XR w.coefficients eta i X w.radius_pos hX)
    _ = _ := by
      rw [integral_add (heatRow_integrable F XR eta i w.radius_pos heta)
        (patchRow_integrable F XR w.coefficients eta i w.radius_pos), heatRow_integral F XR eta i
          w.radius_pos,
        patchRow_integral F XR w.coefficients eta i w.radius_pos]
      have h := congrFun (w.moments eta heta) i
      simp only [Pi.add_apply, Pi.zero_apply] at h
      linarith

end CompensationWitness

theorem kernel_decomposition (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) :
    canonicalKernel F XR c eta X = OutgoingDilation.canonicalKernel F XR eta X + changeRow F XR c
      eta 0 X := by
  change E F XR c (X, eta) ^ 2 / X = OutgoingDilation.E F XR (X, eta) ^ 2 / X +
    (E F XR c (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2) / X
  ring

theorem energy_decomposition (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) :
    energyDensity F XR c eta X = OutgoingDilation.energyDensity F XR eta X - changeRow F XR c eta 1
      X / 2 := by
  change OutgoingDilation.U F XR (X, eta) ^ 2 - E F XR c (X, eta) ^ 2 / 2 =
    OutgoingDilation.U F XR (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2 / 2 -
      (E F XR c (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2) / 2
  ring

theorem renormalized_decomposition (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) :
    H F XR c (X, eta) - OutgoingDilation.powerH F XR X =
      (OutgoingDilation.H F XR (X, eta) - OutgoingDilation.powerH F XR X) + changeRow F XR c eta 2
        X := by
  change Real.sqrt (2 * X) * E F XR c (X, eta) - _ =
    (Real.sqrt (2 * X) * OutgoingDilation.E F XR (X, eta) - _) +
      Real.sqrt (2 * X) * (E F XR c (X, eta) - OutgoingDilation.E F XR (X, eta))
  ring

theorem parameter_sq_le_one {eta : ℝ} (heta : eta ∈ parameterDomain) : eta ^ 2 ≤ 1 := by
  have h := mul_nonneg (show 0 ≤ eta + 1 by linarith [heta.1]) (show 0 ≤ 1 - eta by linarith
    [heta.2])
  nlinarith

theorem pulseEnd_le_switch (F : Profile) (XR : ℝ) (hXR : 0 < XR) :
    OutgoingDilation.pulseEndRadius F XR ≤ switchRadius F XR := by
  have hy : F.data.core.endpoint ≤ HeatTailEdit.switchStart F.data := by
    have hf := OutgoingTail.flattenEnd_gt_core F.data
    have hr := OutgoingTail.releaseStart_gt_flattenEnd F.data
    have ht := OutgoingTail.tailStart_gt_release F.data
    dsimp only [HeatTailEdit.switchStart]
    linarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) hXR.le

theorem U_after_switch (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR)
    (hK : switchRadius F XR ≤ X) : U F XR (X, eta) = 0 :=
  (OutgoingDilation.after_pulse F XR eta X hXR
    ((OutgoingDilation.switchRadius_pos F XR hXR).trans_le hK)
    ((pulseEnd_le_switch F XR hXR).trans hK)).1

theorem heatE_times_U (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    heatE F XR (X, eta) * U F XR (X, eta) = OutgoingDilation.E F XR (X, eta) * U F XR (X, eta) := by
  by_cases hle : X ≤ switchRadius F XR
  · rw [heatE_before F XR eta X hXR hX hle]
  · rw [U_after_switch F XR eta X hXR (lt_of_not_ge hle).le, mul_zero, mul_zero]

theorem E_times_U (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) :
    E F XR c (X, eta) * U F XR (X, eta) = OutgoingDilation.E F XR (X, eta) * U F XR (X, eta) := by
  have hp : patchIncrement F XR c (X, eta) * U F XR (X, eta) = 0 := by
    rw [patchIncrement, mul_assoc]
    change shapedPatchAmplitude F eta *
      (TerminalCompensation.correction compensationPatch (c eta) (X / patchRadius F XR) *
        OutgoingDilation.U F XR (X, eta)) = 0
    rw [OutgoingDilation.correction_times_U_zero F XR eta X hXR, mul_zero]
  rw [E, add_mul, heatE_times_U F XR eta X hXR hX, hp, add_zero]

theorem J_integrand_eq (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) :
    H F XR c (X, eta) * U F XR (X, eta) = OutgoingDilation.H F XR (X, eta) * OutgoingDilation.U F
      XR (X, eta) := by
  simpa only [H, OutgoingDilation.H, U, mul_assoc] using
    congrArg (fun z => Real.sqrt (2 * X) * z) (E_times_U F XR c eta X hXR hX)

theorem M_unchanged (F : Profile) (XR eta X : ℝ) : M F XR eta X = OutgoingDilation.M F XR eta X :=
  rfl

theorem J_unchanged (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) (hXR : 0 < XR) :
    J F XR c eta X = OutgoingDilation.J F XR eta X :=
  setIntegral_congr_fun measurableSet_Ioc (fun u hu => J_integrand_eq F XR c eta u hXR hu.1)

theorem entrance_before_patch (F : Profile) (XR : ℝ) (hXR : 0 < XR) : XR < patchRadius F XR := by
  have hy : 0 < OutgoingDilation.patchClock F :=
    F.data.core.holdStart_pos.trans (OutgoingDilation.patchClock_after_hold F)
  have he : 1 < Real.exp (OutgoingDilation.patchClock F) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hy
  unfold patchRadius OutgoingDilation.radius
  simpa only [mul_one] using mul_lt_mul_of_pos_left he hXR

namespace CompensationWitness

variable {F : Profile} {XR C : ℝ} (w : CompensationWitness F XR C)

theorem canonicalKernel_integrable (eta : ℝ) (heta : eta ∈ parameterDomain) :
    IntegrableOn (canonicalKernel F XR w.coefficients eta) (Ioi 0) := by
  have he := funext (kernel_decomposition F XR w.coefficients eta)
  rw [he]
  exact (OutgoingDilation.canonicalKernel_integrable F XR eta w.radius_pos).add
    (w.changeRow_integrable eta 0 heta)

theorem pressure_integral_unchanged (eta : ℝ) (heta : eta ∈ parameterDomain) :
    (∫ X in Ioi 0, canonicalKernel F XR w.coefficients eta X) =
      ∫ X in Ioi 0, OutgoingDilation.canonicalKernel F XR eta X := by
  simp_rw [kernel_decomposition]
  rw [integral_add (OutgoingDilation.canonicalKernel_integrable F XR eta w.radius_pos)
    (w.changeRow_integrable eta 0 heta), w.changeRow_integral_zero eta 0 heta, add_zero]

theorem axisDatum_eq (eta : ℝ) (heta : eta ∈ parameterDomain) :
    axisDatum F XR w.coefficients eta = F.axisDatum eta := by
  rw [axisDatum, w.pressure_integral_unchanged eta heta]
  change OutgoingDilation.axisDatum F XR eta = F.axisDatum eta
  rw [OutgoingDilation.axisDatum_unchanged F XR w.radius_pos]

theorem energy_integrable (eta : ℝ) (heta : eta ∈ parameterDomain) :
    IntegrableOn (energyDensity F XR w.coefficients eta) (Ioi 0) := by
  have he := funext (energy_decomposition F XR w.coefficients eta)
  rw [he]
  exact (OutgoingDilation.energy_integrable F XR eta w.radius_pos).sub
    ((w.changeRow_integrable eta 1 heta).div_const 2)

theorem energy_zero {B : ℝ} (hF : OutgoingProfile.Specification F B) (eta : ℝ)
    (heta : eta ∈ parameterDomain) : totalS F XR w.coefficients eta = 0 := by
  unfold totalS
  simp_rw [energy_decomposition]
  rw [integral_sub (OutgoingDilation.energy_integrable F XR eta w.radius_pos)
    ((w.changeRow_integrable eta 1 heta).div_const 2), integral_div,
    w.changeRow_integral_zero eta 1 heta, zero_div, sub_zero]
  exact OutgoingDilation.energy_zero hF XR eta w.radius_pos (parameter_sq_le_one heta)

theorem renormalized_integrable (eta : ℝ) (heta : eta ∈ parameterDomain) :
    IntegrableOn (fun X => H F XR w.coefficients (X, eta) - OutgoingDilation.powerH F XR X) (Ioi 0)
      := by
  have he := funext (renormalized_decomposition F XR w.coefficients eta)
  rw [he]
  exact (OutgoingDilation.renormalized_integrable F XR eta w.radius_pos).add
    (w.changeRow_integrable eta 2 heta)

theorem renormalized_zero (eta : ℝ) (heta : eta ∈ parameterDomain) :
    (∫ X in Ioi 0, H F XR w.coefficients (X, eta) - OutgoingDilation.powerH F XR X) = 0 := by
  simp_rw [renormalized_decomposition]
  rw [integral_add (OutgoingDilation.renormalized_integrable F XR eta w.radius_pos)
    (w.changeRow_integrable eta 2 heta), w.changeRow_integral_zero eta 2 heta, add_zero]
  exact OutgoingDilation.renormalized_zero F XR eta w.radius_pos

include w in
theorem mass_integrable (eta : ℝ) : IntegrableOn (fun X => U F XR (X, eta)) (Ioi 0) :=
  OutgoingDilation.mass_integrable F XR eta w.radius_pos

theorem angular_integrable (eta : ℝ) :
    IntegrableOn (fun X => H F XR w.coefficients (X, eta) * U F XR (X, eta)) (Ioi 0) :=
  IntegrableOn.congr_fun (OutgoingDilation.angular_integrable F XR eta w.radius_pos)
    (fun X hX => (J_integrand_eq F XR w.coefficients eta X w.radius_pos hX).symm) measurableSet_Ioi

include w in
theorem mass_zero (eta : ℝ) : (∫ X in Ioi 0, U F XR (X, eta)) = 0 :=
  OutgoingDilation.mass_total_zero F XR eta w.radius_pos

theorem angular_zero (eta : ℝ) :
    (∫ X in Ioi 0, H F XR w.coefficients (X, eta) * U F XR (X, eta)) = 0 := by
  calc
    _ = ∫ X in Ioi 0, OutgoingDilation.H F XR (X, eta) * OutgoingDilation.U F XR (X, eta) :=
      setIntegral_congr_fun measurableSet_Ioi (fun X hX => J_integrand_eq F XR w.coefficients eta X
        w.radius_pos hX)
    _ = 0 := OutgoingDilation.angular_total_zero F XR eta w.radius_pos

theorem after_pulse (eta X : ℝ) (hX : 0 < X) (hfar : OutgoingDilation.pulseEndRadius F XR ≤ X) :
    U F XR (X, eta) = 0 ∧ M F XR eta X = 0 ∧ J F XR w.coefficients eta X = 0 := by
  rw [M_unchanged, J_unchanged F XR w.coefficients eta X w.radius_pos]
  exact OutgoingDilation.after_pulse F XR eta X w.radius_pos hX hfar

theorem Pi_before_patch (eta X : ℝ) (heta : eta ∈ parameterDomain) (hX : 0 < X)
    (hpatch : X ≤ patchRadius F XR) : Pi F XR w.coefficients (X, eta) = OutgoingDilation.Pi F XR
      (X, eta) := by
  have hs : Ioi X ⊆ Ioi (0 : ℝ) := fun u hu => hX.trans hu
  have hi := (w.changeRow_integrable eta 0 heta).mono_set hs
  have hb := (OutgoingDilation.canonicalKernel_integrable F XR eta w.radius_pos).mono_set hs
  have hz : (∫ u in Ioi X, changeRow F XR w.coefficients eta 0 u) = 0 := by
    rw [← integral_positive_tail _ X hX (fun u hu huX => ?_), w.changeRow_integral_zero eta 0 heta]
    change (E F XR w.coefficients (u, eta) ^ 2 - OutgoingDilation.E F XR (u, eta) ^ 2) / u = 0
    rw [E_before_patch F XR w.coefficients eta u w.radius_pos hu (huX.trans hpatch), sub_self,
      zero_div]
  unfold Pi
  simp_rw [kernel_decomposition]
  rw [integral_add hb hi, hz, add_zero]
  exact (OutgoingDilation.Pi_canonical F XR eta X w.radius_pos hX).symm

theorem ideal_prefix (eta X : ℝ) (heta : eta ∈ parameterDomain) (hX : 0 < X) (hX' : X ≤ XR) :
    E F XR w.coefficients (X, eta) = F.data.core.P * OutgoingSchedule.shape eta * (X / XR) ^ (1 /
      10 : ℝ) ∧
    U F XR (X, eta) = 4 * eta ∧
    Pi F XR w.coefficients (X, eta) = F.axisDatum eta +
      (5 / 2) * F.data.core.P ^ 2 * OutgoingSchedule.shape eta ^ 2 * (X / XR) ^ (1 / 5 : ℝ) := by
  have hp := hX'.trans (entrance_before_patch F XR w.radius_pos).le
  rw [E_before_patch F XR w.coefficients eta X w.radius_pos hX hp, w.Pi_before_patch eta X heta hX
    hp]
  have h := OutgoingDilation.ideal_prefix F XR eta X w.radius_pos hX hX'
  rw [OutgoingDilation.axisDatum_unchanged F XR w.radius_pos] at h
  exact h

end CompensationWitness

/-! Pressure regularity is proved using finite integrals with free bump
coefficients, then composing with the constructed relative smooth branch. -/

noncomputable def freeLogE (F : Profile) (XR : ℝ) (z : (Coeff × ℝ) × ℝ) : ℝ :=
  extendedHeatE F XR (Real.exp z.2, z.1.2) + shapedPatchAmplitude F z.1.2 *
    TerminalCompensation.correction compensationPatch z.1.1 (Real.exp z.2 / patchRadius F XR)

theorem freeLogE_contDiff (F : Profile) (XR : ℝ) (hXR : 0 < XR) :
    ContDiff ℝ ∞ (freeLogE F XR) := by
  have he : ContDiff ℝ ∞ (fun z : (Coeff × ℝ) × ℝ =>
      extendedHeatE F XR (Real.exp z.2, z.1.2)) :=
    (extendedHeatE_contDiffOn F XR hXR).comp_contDiff
      (contDiff_snd.exp.prodMk contDiff_fst.snd) (fun z => ⟨Real.exp_pos _, mem_univ _⟩)
  have hc : ContDiff ℝ ∞ (fun z : (Coeff × ℝ) × ℝ =>
      TerminalCompensation.correction compensationPatch z.1.1 (Real.exp z.2 / patchRadius F XR)) :=
        by
    apply ContDiff.sum
    intro j _
    exact ((contDiff_apply ℝ ℝ j).comp contDiff_fst.fst).mul
      ((TerminalCompensation.bump_contDiff compensationPatch j).comp
        (contDiff_snd.exp.div_const _))
  exact he.add (((OutgoingDilation.shapedPatchAmplitude_contDiff F).comp contDiff_fst.snd).mul hc)

theorem freeLogE_eq (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta y : ℝ)
    (heta : eta ∈ parameterDomain) :
    freeLogE F XR ((c eta, eta), y) = E F XR c (Real.exp y, eta) := by
  rw [E, heatE_eq_extended F XR (show (Real.exp y, eta) ∈ domain from ⟨Real.exp_pos _, heta⟩)]
  rfl

theorem primitive_contDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (f : P × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun z : P × ℝ => ∫ t in (0 : ℝ)..z.2, f (z.1, t)) := by
  let G : (P × ℝ) × ℝ → ℝ := fun z => f (z.1.1, z.1.2 * z.2)
  have hG : ContDiff ℝ ∞ G :=
    hf.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have hi : ContDiff ℝ ∞ (fun z => ∫ t in (0 : ℝ)..1, G (z, t)) :=
    contDiffOn_univ.mp (ParametricRephase.intervalIntegral_contDiffOn_of_joint G univ
      isOpen_univ hG.contDiffOn 0 1 (by norm_num))
  have he : (fun z : P × ℝ => ∫ t in (0 : ℝ)..z.2, f (z.1, t)) =
      (fun z => z.2 * ∫ t in (0 : ℝ)..1, G (z, t)) := by
    funext z
    simpa only [G, smul_eq_mul, mul_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left (fun t => f (z.1, t)) z.2
        (a := 0) (b := 1)).symm
  rw [he]
  exact contDiff_snd.mul hi

theorem anchoredPrimitive_contDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (f : P × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun z : P × ℝ => ∫ t in a..z.2, f (z.1, t)) := by
  have hg : ContDiff ℝ ∞ (fun z : P × ℝ => f (z.1, a + z.2)) :=
    hf.comp (contDiff_fst.prodMk (contDiff_const.add contDiff_snd))
  have hp := primitive_contDiff _ hg
  have hm : ContDiff ℝ ∞ (fun z : P × ℝ => (z.1, z.2 - a)) :=
    contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)
  have hc := hp.comp hm
  convert! hc using 1
  funext z
  change (∫ t in a..z.2, f (z.1, t)) = ∫ t in (0 : ℝ)..(z.2 - a), f (z.1, a + t)
  rw [intervalIntegral.integral_comp_add_left (fun t => f (z.1, t)) a]
  congr 1 <;> ring

theorem canonicalKernel_comp_exp (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta y : ℝ) :
    |Real.exp y| • canonicalKernel F XR c eta (Real.exp y) = E F XR c (Real.exp y, eta) ^ 2 := by
  simp only [abs_of_pos (Real.exp_pos y), smul_eq_mul, canonicalKernel]
  field_simp

theorem Pi_exp (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta y : ℝ) :
    Pi F XR c (Real.exp y, eta) = -(1 / 2 : ℝ) * ∫ t in Ioi y, E F XR c (Real.exp t, eta) ^ 2 := by
  rw [Pi, ← OutgoingProfile.image_exp_Ioi,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  simp_rw [canonicalKernel_comp_exp]

namespace CompensationWitness

variable {F : Profile} {XR C : ℝ} (w : CompensationWitness F XR C)

theorem logE_square_integrable (eta : ℝ) (heta : eta ∈ parameterDomain) :
    Integrable (fun y => E F XR w.coefficients (Real.exp y, eta) ^ 2) := by
  have hi := w.canonicalKernel_integrable eta heta
  rw [← Real.range_exp, ← image_univ] at hi
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn _).mp hi
  simp_rw [canonicalKernel_comp_exp] at h
  simpa only [integrableOn_univ] using h

theorem Pi_exp_primitive (eta y : ℝ) (heta : eta ∈ parameterDomain) :
    Pi F XR w.coefficients (Real.exp y, eta) = OutgoingDilation.Pi F XR (patchRadius F XR, eta) +
      (1 / 2 : ℝ) * ∫ t in Real.log (patchRadius F XR)..y,
        freeLogE F XR ((w.coefficients eta, eta), t) ^ 2 := by
  have hi := w.logE_square_integrable eta heta
  have hy := intervalIntegral.integral_Iic_add_Ioi
    (hi.integrableOn (s := Iic y)) (hi.integrableOn (s := Ioi y))
  have ha := intervalIntegral.integral_Iic_add_Ioi
    (hi.integrableOn (s := Iic (Real.log (patchRadius F XR))))
    (hi.integrableOn (s := Ioi (Real.log (patchRadius F XR))))
  have hd := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn (s := Iic (Real.log (patchRadius F XR)))) (hi.integrableOn (s := Iic y))
  have he := w.Pi_before_patch eta (patchRadius F XR) heta
    (OutgoingDilation.patchRadius_pos F XR w.radius_pos) le_rfl
  have hp := Pi_exp F XR w.coefficients eta (Real.log (patchRadius F XR))
  rw [Real.exp_log (OutgoingDilation.patchRadius_pos F XR w.radius_pos), he] at hp
  rw [Pi_exp]
  simp_rw [freeLogE_eq F XR w.coefficients eta _ heta]
  linarith

theorem Pi_log_contDiffOn : ContDiffOn ℝ ∞
    (fun p : ℝ × ℝ => Pi F XR w.coefficients (Real.exp p.1, p.2)) (univ ×ˢ parameterDomain) := by
  have hf := (freeLogE_contDiff F XR w.radius_pos).pow 2
  have hi := anchoredPrimitive_contDiff _ hf (Real.log (patchRadius F XR))
  have hc : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => ((w.coefficients p.2, p.2), p.1))
      (univ ×ˢ parameterDomain) :=
    ((w.smooth.comp contDiffOn_snd (fun _ hp => hp.2)).prodMk contDiffOn_snd).prodMk contDiffOn_fst
  have hb : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => OutgoingDilation.Pi F XR (patchRadius F XR, p.2))
      (univ ×ˢ parameterDomain) :=
    (OutgoingDilation.Pi_contDiffOn F XR w.radius_pos).comp
      (contDiffOn_const.prodMk contDiffOn_snd)
      (fun _ _ => ⟨OutgoingDilation.patchRadius_pos F XR w.radius_pos, mem_univ _⟩)
  apply (hb.add (contDiffOn_const.mul (hi.comp_contDiffOn hc))).congr
  intro p hp
  exact w.Pi_exp_primitive p.2 p.1 hp.2

theorem Pi_contDiffOn : ContDiffOn ℝ ∞ (Pi F XR w.coefficients) domain := by
  have hl : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (Real.log p.1, p.2)) domain :=
    (contDiffOn_fst.log (fun p hp => ne_of_gt hp.1)).prodMk contDiffOn_snd
  apply (w.Pi_log_contDiffOn.comp hl (fun _ hp => ⟨mem_univ _, hp.2⟩)).congr
  intro p hp
  dsimp only [Function.comp_def]
  rw [Real.exp_log hp.1]

end CompensationWitness

theorem E_between_patch_and_switch (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    (eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X)
    (hpatch : patchRadius F XR * compensationPatch.right ≤ X)
    (hswitch : X ≤ switchRadius F XR) : E F XR c (X, eta) = OutgoingDilation.E F XR (X, eta) := by
  have hc : TerminalCompensation.correction compensationPatch (c eta) (X / patchRadius F XR) = 0 :=
    by
    by_contra hn
    have ht := TerminalCompensation.correction_tsupport compensationPatch (c eta) (subset_tsupport
      _ hn)
    have hx : compensationPatch.right ≤ X / patchRadius F XR :=
      (le_div_iff₀ (OutgoingDilation.patchRadius_pos F XR hXR)).mpr (by simpa only [mul_comm] using
        hpatch)
    exact (not_lt_of_ge hx) ht.2
  rw [E, heatE_before F XR eta X hXR hX hswitch, patchIncrement, hc, mul_zero, add_zero]

theorem full_switch_above_radius {K X : ℝ} (hK : 0 < K) (hX : 0 < X)
    (hfull : 1 / 2 ≤ Real.log (X / K) + 1 / 5) : K ≤ X := by
  have hl : 0 ≤ Real.log (X / K) := by linarith
  have hx := (Real.log_nonneg_iff (div_pos hX hK)).mp hl
  exact (one_le_div hK).mp hx

theorem E_full_switch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X)
    (hfull : 1 / 2 ≤ Real.log (X / switchRadius F XR) + 1 / 5) :
    E F XR c (X, eta) =
      (OutgoingDilation.carrierAmplitude F * (switchRadius F XR) ^ HeatTailEdit.exponent F.data.h) *
        RadialHeatProfile.spatialProfile (1 + F.data.h) (ParametricHeatTail.diffusion eta) X *
          OutgoingTail.tailShape F.data (Real.log (X / switchRadius F XR) + 1 / 5) := by
  rw [E_after_switch F XR c eta X hXR
    (full_switch_above_radius (OutgoingDilation.switchRadius_pos F XR hXR) hX hfull)]
  exact HeatTailEdit.outgoingEdit_heat_factorization F.data _ _
    (OutgoingDilation.switchRadius_pos F XR hXR) hX hfull

theorem E_eventual_heat (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X)
    (hlate : 3 ≤ Real.log (X / switchRadius F XR) + 1 / 5) :
    E F XR c (X, eta) =
      (OutgoingDilation.carrierAmplitude F * (switchRadius F XR) ^ HeatTailEdit.exponent F.data.h) *
        RadialHeatProfile.spatialProfile (1 + F.data.h) (ParametricHeatTail.diffusion eta) X := by
  rw [E_full_switch F XR c eta X hXR hX (by linarith), OutgoingTail.tailShape_late F.data hlate,
    mul_one]

theorem E_eventual_heat_carrier (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    {q s τ eta : ℝ} (hXR : 0 < XR) (hq : 0 < q) (hs : 0 < s)
    (hν : ParametricHeatTail.diffusion eta = τ / q)
    (hlate : 3 ≤ Real.log ((s / q) / switchRadius F XR) + 1 / 5) :
    q ^ (-HeatTailEdit.exponent F.data.h) * E F XR c (s / q, eta) =
      (OutgoingDilation.carrierAmplitude F * (switchRadius F XR) ^ HeatTailEdit.exponent F.data.h) *
        RadialHeatProfile.spatialProfile (1 + F.data.h) τ s := by
  rw [E_after_switch F XR c eta (s / q) hXR
    (full_switch_above_radius (OutgoingDilation.switchRadius_pos F XR hXR) (div_pos hs hq) (by
      linarith))]
  exact ParametricHeatTail.physicalEdit_eventual_heat_carrier F.data
    (OutgoingDilation.switchRadius_pos F XR hXR) hq hs hν hlate

theorem Pi_after_switch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : switchRadius F XR ≤ X) :
    Pi F XR c (X, eta) = -(1 / 2 : ℝ) * ∫ u in Ioi X,
      ParametricHeatTail.physicalEdit F.data (switchRadius F XR) eta u ^ 2 / u := by
  unfold Pi canonicalKernel
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => by rw [E_after_switch F XR c eta u hXR
    (hX.trans hu.le)])

namespace CompensationWitness

variable {F : Profile} {XR C : ℝ} (w : CompensationWitness F XR C)

theorem Pi_tendsto_axis (eta : ℝ) (heta : eta ∈ parameterDomain) :
    Tendsto (fun X => Pi F XR w.coefficients (X, eta)) (𝓝[>] (0 : ℝ)) (𝓝 (F.axisDatum eta)) := by
  have he : (fun X => Pi F XR w.coefficients (X, eta)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun X => OutgoingDilation.Pi F XR (X, eta)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (OutgoingDilation.patchRadius_pos F XR
        w.radius_pos))] with X hX hp
    exact w.Pi_before_patch eta X heta hX hp.le
  have ht := OutgoingDilation.Pi_tendsto_axis F XR eta w.radius_pos
  rw [OutgoingDilation.axisDatum_unchanged F XR w.radius_pos] at ht
  exact ht.congr' he.symm

theorem axisDatum_analytic_extension :
    AnalyticOnNhd ℂ (SchedulePressure.complexAxisPressure F.data) PressureDatum.strip ∧
      ∀ eta ∈ parameterDomain, SchedulePressure.complexAxisPressure F.data (eta : ℂ) =
        (axisDatum F XR w.coefficients eta : ℂ) := by
  refine ⟨F.axisDatum_analytic_extension.1, ?_⟩
  intro eta heta
  rw [w.axisDatum_eq eta heta]
  exact F.axisDatum_analytic_extension.2 eta

end CompensationWitness

/-! All properties below refer to the same actual fields and the same
outgoing profile. The coefficient witness also retains its quantitative
relative first-jet bounds. -/

structure Specification (F : Profile) (XR : ℝ) (c : ℝ → Coeff) : Prop where
  angular_smooth : ContDiffOn ℝ ∞ (E F XR c) domain
  axial_smooth : ContDiffOn ℝ ∞ (U F XR) domain
  momentum_smooth : ContDiffOn ℝ ∞ (H F XR c) domain
  pressure_smooth : ContDiffOn ℝ ∞ (Pi F XR c) domain
  angular_positive : ∀ eta ∈ parameterDomain, ∀ X : ℝ, 0 < X → 0 < E F XR c (X, eta)
  axial_unchanged : U F XR = OutgoingDilation.U F XR
  mass_unchanged : ∀ eta X : ℝ, M F XR eta X = OutgoingDilation.M F XR eta X
  angular_unchanged : ∀ eta X : ℝ, J F XR c eta X = OutgoingDilation.J F XR eta X
  mass_integrable : ∀ eta : ℝ, IntegrableOn (fun X => U F XR (X, eta)) (Ioi 0)
  angular_integrable : ∀ eta : ℝ,
    IntegrableOn (fun X => H F XR c (X, eta) * U F XR (X, eta)) (Ioi 0)
  mass_zero : ∀ eta : ℝ, (∫ X in Ioi 0, U F XR (X, eta)) = 0
  angular_zero : ∀ eta : ℝ, (∫ X in Ioi 0, H F XR c (X, eta) * U F XR (X, eta)) = 0
  after_pulse : ∀ eta X : ℝ, 0 < X → OutgoingDilation.pulseEndRadius F XR ≤ X →
    U F XR (X, eta) = 0 ∧ M F XR eta X = 0 ∧ J F XR c eta X = 0
  energy_integrable : ∀ eta ∈ parameterDomain, IntegrableOn (energyDensity F XR c eta) (Ioi 0)
  energy_zero : ∀ eta ∈ parameterDomain, totalS F XR c eta = 0
  renormalized_integrable : ∀ eta ∈ parameterDomain,
    IntegrableOn (fun X => H F XR c (X, eta) - OutgoingDilation.powerH F XR X) (Ioi 0)
  renormalized_zero : ∀ eta ∈ parameterDomain,
    (∫ X in Ioi 0, H F XR c (X, eta) - OutgoingDilation.powerH F XR X) = 0
  pressure_integrable : ∀ eta ∈ parameterDomain, IntegrableOn (canonicalKernel F XR c eta) (Ioi 0)
  pressure_canonical : ∀ eta X : ℝ,
    Pi F XR c (X, eta) = -(1 / 2 : ℝ) * ∫ u in Ioi X, E F XR c (u, eta) ^ 2 / u
  axis_unchanged : ∀ eta ∈ parameterDomain, axisDatum F XR c eta = F.axisDatum eta
  axis_limit : ∀ eta ∈ parameterDomain,
    Tendsto (fun X => Pi F XR c (X, eta)) (𝓝[>] (0 : ℝ)) (𝓝 (F.axisDatum eta))
  analytic_axis_datum : AnalyticOnNhd ℂ (SchedulePressure.complexAxisPressure F.data)
    PressureDatum.strip ∧
    ∀ eta ∈ parameterDomain, SchedulePressure.complexAxisPressure F.data (eta : ℂ) =
      (axisDatum F XR c eta : ℂ)
  before_patch : ∀ eta ∈ parameterDomain, ∀ X : ℝ, 0 < X → X ≤ patchRadius F XR →
    E F XR c (X, eta) = OutgoingDilation.E F XR (X, eta) ∧
      Pi F XR c (X, eta) = OutgoingDilation.Pi F XR (X, eta)
  ideal_prefix : ∀ eta ∈ parameterDomain, ∀ X : ℝ, 0 < X → X ≤ XR →
    E F XR c (X, eta) = F.data.core.P * OutgoingSchedule.shape eta * (X / XR) ^ (1 / 10 : ℝ) ∧
      U F XR (X, eta) = 4 * eta ∧
      Pi F XR c (X, eta) = F.axisDatum eta +
        (5 / 2) * F.data.core.P ^ 2 * OutgoingSchedule.shape eta ^ 2 * (X / XR) ^ (1 / 5 : ℝ)
  switch_overlap : ∀ eta X : ℝ, switchRadius F XR ≤ X →
    E F XR c (X, eta) = ParametricHeatTail.physicalEdit F.data (switchRadius F XR) eta X
  terminal_heat : ∀ eta X : ℝ, 0 < X → 3 ≤ Real.log (X / switchRadius F XR) + 1 / 5 →
    E F XR c (X, eta) =
      (OutgoingDilation.carrierAmplitude F * (switchRadius F XR) ^ HeatTailEdit.exponent F.data.h) *
        RadialHeatProfile.spatialProfile (1 + F.data.h) (ParametricHeatTail.diffusion eta) X
  patch_disjoint : Disjoint (Icc (patchRadius F XR) (patchRadius F XR * compensationPatch.right))
    (Ici (switchRadius F XR))

theorem CompensationWitness.specification {F : Profile} {XR B C : ℝ}
    (w : CompensationWitness F XR C) (hF : OutgoingProfile.Specification F B) :
    Specification F XR w.coefficients where
  angular_smooth := E_contDiffOn F XR w.radius_pos w.smooth
  axial_smooth := U_contDiffOn F XR w.radius_pos
  momentum_smooth := H_contDiffOn F XR w.radius_pos w.smooth
  pressure_smooth := w.Pi_contDiffOn
  angular_positive := fun eta heta X hX => w.positive eta X heta hX
  axial_unchanged := rfl
  mass_unchanged := M_unchanged F XR
  angular_unchanged := fun eta X => J_unchanged F XR w.coefficients eta X w.radius_pos
  mass_integrable := w.mass_integrable
  angular_integrable := w.angular_integrable
  mass_zero := w.mass_zero
  angular_zero := w.angular_zero
  after_pulse := w.after_pulse
  energy_integrable := w.energy_integrable
  energy_zero := w.energy_zero hF
  renormalized_integrable := w.renormalized_integrable
  renormalized_zero := w.renormalized_zero
  pressure_integrable := w.canonicalKernel_integrable
  pressure_canonical := fun _ _ => rfl
  axis_unchanged := w.axisDatum_eq
  axis_limit := w.Pi_tendsto_axis
  analytic_axis_datum := w.axisDatum_analytic_extension
  before_patch := fun eta heta X hX hp =>
    ⟨E_before_patch F XR w.coefficients eta X w.radius_pos hX hp, w.Pi_before_patch eta X heta hX
      hp⟩
  ideal_prefix := fun eta heta X hX hp => w.ideal_prefix eta X heta hX hp
  switch_overlap := fun eta X hX => E_after_switch F XR w.coefficients eta X w.radius_pos hX
  terminal_heat := fun eta X hX htail => E_eventual_heat F XR w.coefficients eta X w.radius_pos hX
    htail
  patch_disjoint := OutgoingDilation.patch_switch_disjoint F XR w.radius_pos

/-- For a single fixed outgoing profile, every sufficiently large entrance
radius allows the actual physical heat continuation and its exact repair. -/
theorem exists_heated_profile {F : Profile} {B : ℝ} (hF : OutgoingProfile.Specification F B) :
    ∃ XR₀ C : ℝ, 0 < XR₀ ∧ 0 < C ∧ ∀ XR : ℝ, XR₀ ≤ XR →
      ∃ w : CompensationWitness F XR C, Specification F XR w.coefficients := by
  obtain ⟨XR₀, C, hXR₀, hC, hc⟩ := exists_compensation F
  refine ⟨XR₀, C, hXR₀, hC, ?_⟩
  intro XR hXR
  obtain ⟨w⟩ := hc XR hXR
  exact ⟨w, w.specification hF⟩

/-- The order of choices is `P,m`, one positive `lam`, permitted `h`, one
reset/amplitude profile, and then large `X_R` and its terminal coefficients. -/
theorem exists_fixed_schedule (P m : ℝ) (hP : 0 < P) (hm : 0 < m) :
    ∃ lam B : ℝ, 0 < lam ∧ 0 < B ∧ ∀ h : ℝ, 0 < h → 2 * h < lam →
      ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧
        F.data.core.lam = lam ∧ F.data.h = h ∧ OutgoingProfile.Specification F B ∧
        ∃ XR₀ C : ℝ, 0 < XR₀ ∧ 0 < C ∧ ∀ XR : ℝ, XR₀ ≤ XR →
          ∃ w : CompensationWitness F XR C, Specification F XR w.coefficients := by
  obtain ⟨lam, B, hlam, hB, hc⟩ := OutgoingProfile.exists_fixed_lambda P m hP hm
  refine ⟨lam, B, hlam, hB, ?_⟩
  intro h hh hsmall
  obtain ⟨F, hP', hm', hlam', hh', hF⟩ := hc h hh hsmall
  exact ⟨F, hP', hm', hlam', hh', hF, exists_heated_profile hF⟩

end NavierStokes.HeatedOutgoing
