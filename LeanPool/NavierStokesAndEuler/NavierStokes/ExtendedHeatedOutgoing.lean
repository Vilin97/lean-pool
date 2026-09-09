/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatedOutgoing
public import LeanPool.NavierStokesAndEuler.NavierStokes.ExtendedHeatDebts

@[expose] public section

/-!
# An actual compensated outgoing profile on an open parameter neighborhood

The coefficients are solved once for the literal extended heat debts. Their
restriction supplies the physical-band witness; no comparison of unrelated
existential choices is used.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators
open NavierStokes.OutgoingProfile (Profile)
open NavierStokes.OutgoingDilation (switchRadius patchRadius patchRatio compensationPatch
  shapedPatchAmplitude)

namespace NavierStokes.ExtendedHeatedOutgoing

abbrev Coeff := TerminalCompensation.Coeff

def parameterDomain : Set ℝ := Ioo (-(3 / 2 : ℝ)) (3 / 2)
def domain : Set (ℝ × ℝ) := Ioi 0 ×ˢ parameterDomain

theorem parameterDomain_open : IsOpen parameterDomain := isOpen_Ioo

theorem parameterDomain_subset : parameterDomain ⊆ ExtendedHeatDebts.enlargedBand :=
  fun _ h => ⟨h.1.le, h.2.le⟩

theorem physicalBand_subset : HeatedOutgoing.parameterDomain ⊆ parameterDomain :=
  ExtendedHeatDebts.physicalBand_subset_openNeighborhood

theorem enlargedBand_mem_nhds {eta : ℝ} (heta : eta ∈ parameterDomain) :
    ExtendedHeatDebts.enlargedBand ∈ 𝓝 eta :=
  mem_of_superset (parameterDomain_open.mem_nhds heta) parameterDomain_subset

noncomputable def heatE (F : Profile) (XR : ℝ) : ℝ × ℝ → ℝ := HeatedOutgoing.extendedHeatE F XR
noncomputable def E (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  heatE F XR p + HeatedOutgoing.patchIncrement F XR c p
noncomputable def U (F : Profile) (XR : ℝ) : ℝ × ℝ → ℝ := HeatedOutgoing.U F XR
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
noncomputable def M (F : Profile) (XR eta X : ℝ) : ℝ := HeatedOutgoing.M F XR eta X
noncomputable def J (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) : ℝ :=
  ∫ u in Ioc 0 X, H F XR c (u, eta) * U F XR (u, eta)

/-- Quantitative data from one solve on the enlarged compact parameter set. -/
structure Witness (F : Profile) (XR C : ℝ) where
  radius_pos : 0 < XR
  switch_large : 1 ≤ switchRadius F XR
  coefficients : ℝ → Coeff
  smooth : ContDiffOn ℝ ∞ coefficients ExtendedHeatDebts.enlargedBand
  moments : ∀ eta ∈ ExtendedHeatDebts.enlargedBand,
    TerminalCompensation.physicalMoments compensationPatch F.data.core.lam
      (patchRadius F XR) (shapedPatchAmplitude F eta) (coefficients eta) +
      ExtendedHeatDebts.physicalDebt F.data (switchRadius F XR) eta = 0
  coefficient_bound : ∀ eta ∈ ExtendedHeatDebts.enlargedBand,
    ‖coefficients eta‖ ≤ C / switchRadius F XR
  derivative_bound : ∀ eta ∈ ExtendedHeatDebts.enlargedBand,
    ‖derivWithin coefficients ExtendedHeatDebts.enlargedBand eta‖ ≤ C / switchRadius F XR
  first_jet : ∀ eta ∈ ExtendedHeatDebts.enlargedBand,
    ParametricTerminalCompensation.FirstJetWithinBound compensationPatch (shapedPatchAmplitude F)
      coefficients ExtendedHeatDebts.enlargedBand eta (C / switchRadius F XR)
  patch_positive : ∀ eta ∈ ExtendedHeatDebts.enlargedBand, ∀ X : ℝ, 0 < X →
    0 < TerminalCompensation.physicalProfile compensationPatch F.data.core.lam
      (patchRadius F XR) (shapedPatchAmplitude F eta) (coefficients eta) X
  heat_positive : ∀ eta ∈ ExtendedHeatDebts.enlargedBand, ∀ X : ℝ, 0 < X →
    0 < ExtendedHeatDebts.physicalEdit F.data (switchRadius F XR) eta X

theorem exists_witness (F : Profile) :
    ∃ XR₀ C : ℝ, 0 < XR₀ ∧ 0 < C ∧ ∀ XR : ℝ, XR₀ ≤ XR → Nonempty (Witness F XR C) := by
  obtain ⟨B, hB, hb⟩ := ExtendedHeatDebts.exists_normalized_C1_within_bounds F.data
  obtain ⟨K₀, C, hK₀, hC, hc⟩ :=
    ParametricTerminalCompensation.exists_compensation_for_switch_family
    compensationPatch F.data.core.lam F.data.core.lam_pos.le (patchRatio F)
    (OutgoingDilation.patchRatio_pos F) ExtendedHeatDebts.enlargedBand_isCompact
    ExtendedHeatDebts.enlargedBand_uniqueDiffOn (shapedPatchAmplitude F)
    (OutgoingDilation.shapedPatchAmplitude_contDiff F).contDiffOn
    (fun eta _ => OutgoingDilation.shapedPatchAmplitude_pos F eta)
    (ExtendedHeatDebts.physicalDebt F.data) B hB
    (fun K hK => (ExtendedHeatDebts.normalizedDebt_contDiff F.data hK).contDiffOn) hb
  obtain ⟨Kp, _hKp, hp⟩ := ExtendedHeatDebts.eventually_physicalEdit_pos F.data
  let A : ℝ := Real.exp (HeatTailEdit.switchStart F.data)
  let XR₀ : ℝ := max K₀ (max Kp 1) / A
  have hA : 0 < A := Real.exp_pos _
  have hXR₀ : 0 < XR₀ := div_pos
    (lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans (le_max_right _ _))) hA
  refine ⟨XR₀, C, hXR₀, hC, ?_⟩
  intro XR hlarge
  have hXR : 0 < XR := hXR₀.trans_le hlarge
  have hK : max K₀ (max Kp 1) ≤ switchRadius F XR := (div_le_iff₀ hA).mp hlarge
  have hKp' : Kp ≤ switchRadius F XR := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  obtain ⟨c, hs, hspec⟩ := hc (switchRadius F XR) ((le_max_left _ _).trans hK)
  have hr := OutgoingDilation.patchRadius_eq_ratio F XR
  refine ⟨{
    radius_pos := hXR
    switch_large := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
    coefficients := c
    smooth := hs
    moments := ?_
    coefficient_bound := fun eta heta => (hspec eta heta).2.1
    derivative_bound := fun eta heta => (hspec eta heta).2.2.1
    first_jet := fun eta heta => (hspec eta heta).2.2.2.1
    patch_positive := ?_
    heat_positive := hp (switchRadius F XR) hKp' }⟩
  · intro eta heta
    rw [hr]
    exact (hspec eta heta).1
  · intro eta heta X hX
    rw [hr]
    exact (hspec eta heta).2.2.2.2 X hX

namespace Witness

variable {F : Profile} {XR C : ℝ} (w : Witness F XR C)

theorem coefficients_contDiffOn : ContDiffOn ℝ ∞ w.coefficients parameterDomain :=
  w.smooth.mono parameterDomain_subset

theorem coefficients_contDiffAt {eta : ℝ} (heta : eta ∈ parameterDomain) :
    ContDiffAt ℝ ∞ w.coefficients eta := w.smooth.contDiffAt (enlargedBand_mem_nhds heta)

theorem derivative_bound_open {eta : ℝ} (heta : eta ∈ parameterDomain) :
    ‖deriv w.coefficients eta‖ ≤ C / switchRadius F XR := by
  have h := w.derivative_bound eta (parameterDomain_subset heta)
  rwa [derivWithin_of_mem_nhds (enlargedBand_mem_nhds heta)] at h

theorem parameter_correction_contDiffOn (x : ℝ) :
    ContDiffOn ℝ ∞ (fun eta => shapedPatchAmplitude F eta *
      TerminalCompensation.correction compensationPatch (w.coefficients eta) x)
      ExtendedHeatDebts.enlargedBand :=
  (OutgoingDilation.shapedPatchAmplitude_contDiff F).contDiffOn.mul
    ((TerminalCompensation.correction_family_contDiffOn compensationPatch w.smooth).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ heta => ⟨heta, mem_univ _⟩))

/-- Restriction of the constructed branch, rather than a new existential solve. -/
noncomputable def physical : HeatedOutgoing.CompensationWitness F XR C where
  radius_pos := w.radius_pos
  switch_large := w.switch_large
  coefficients := w.coefficients
  smooth := w.coefficients_contDiffOn.mono physicalBand_subset
  moments := by
    intro eta heta
    have h := w.moments eta (parameterDomain_subset (physicalBand_subset heta))
    rwa [ExtendedHeatDebts.physicalDebt_eq_original F.data
      (OutgoingDilation.switchRadius_pos F XR w.radius_pos) heta] at h
  coefficient_bound := fun eta heta => w.coefficient_bound eta (parameterDomain_subset
    (physicalBand_subset heta))
  derivative_bound := by
    intro eta heta
    have hd := ((w.coefficients_contDiffAt (physicalBand_subset heta)).differentiableAt (by
      simp)).hasDerivAt
    dsimp only [HeatedOutgoing.parameterDomain]
    rw [hd.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)) eta heta)]
    exact w.derivative_bound_open (physicalBand_subset heta)
  first_jet := by
    intro eta heta x
    have hp := physicalBand_subset heta
    have h := w.first_jet eta (parameterDomain_subset hp) x
    refine ⟨h.1, h.2.1, ?_⟩
    have hd := (((w.parameter_correction_contDiffOn x).contDiffAt (enlargedBand_mem_nhds
      hp)).differentiableAt (by simp)).hasDerivAt
    dsimp only [HeatedOutgoing.parameterDomain]
    rw [hd.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)) eta heta)]
    simpa only [derivWithin_of_mem_nhds (enlargedBand_mem_nhds hp)] using h.2.2
  patch_positive := fun eta heta => w.patch_positive eta (parameterDomain_subset
    (physicalBand_subset heta))

@[simp] theorem physical_coefficients : w.physical.coefficients = w.coefficients := rfl

end Witness

theorem heatE_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) :
    ContDiffOn ℝ ∞ (heatE F XR) OutgoingProfile.domain :=
  HeatedOutgoing.extendedHeatE_contDiffOn F XR hXR

theorem E_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) {c : ℝ → Coeff}
    (hc : ContDiffOn ℝ ∞ c parameterDomain) : ContDiffOn ℝ ∞ (E F XR c) domain := by
  have hr := (TerminalCompensation.correction_family_contDiffOn compensationPatch hc).comp
    (contDiffOn_snd.prodMk (contDiffOn_fst.div_const (patchRadius F XR)))
    (fun p (hp : p ∈ domain) => ⟨hp.2, mem_univ _⟩)
  exact ((heatE_contDiffOn F XR hXR).mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).add
    (((OutgoingDilation.shapedPatchAmplitude_contDiff F).comp_contDiffOn contDiffOn_snd).mul hr)

theorem U_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) : ContDiffOn ℝ ∞ (U F XR) domain :=
  (OutgoingDilation.U_contDiffOn F XR hXR).mono (fun _ hp => ⟨hp.1, mem_univ _⟩)

theorem H_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) {c : ℝ → Coeff}
    (hc : ContDiffOn ℝ ∞ c parameterDomain) : ContDiffOn ℝ ∞ (H F XR c) domain :=
  ((contDiffOn_const.mul contDiffOn_fst).sqrt
    (fun _ hp => ne_of_gt (mul_pos (by norm_num) hp.1))).mul (E_contDiffOn F XR hXR hc)

theorem E_eq_physical (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) (hX : 0 < X) :
    E F XR c (X, eta) = HeatedOutgoing.E F XR c (X, eta) := by
  rw [HeatedOutgoing.E, HeatedOutgoing.heatE_eq_extended F XR
    (show (X, eta) ∈ HeatedOutgoing.domain from ⟨hX, heta⟩)]
  rfl

theorem H_eq_physical (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) (hX : 0 < X) :
    H F XR c (X, eta) = HeatedOutgoing.H F XR c (X, eta) := by
  rw [H, HeatedOutgoing.H, E_eq_physical F XR c eta X heta hX]

theorem Pi_eq_physical (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) (hX : 0 ≤ X) :
    Pi F XR c (X, eta) = HeatedOutgoing.Pi F XR c (X, eta) := by
  unfold Pi HeatedOutgoing.Pi canonicalKernel HeatedOutgoing.canonicalKernel
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => by rw [E_eq_physical F XR c eta u heta
    (hX.trans_lt hu)])

theorem heatE_eq_edit (F : Profile) (XR eta X : ℝ) :
    heatE F XR (X, eta) = ExtendedHeatDebts.edit (fun u => OutgoingDilation.E F XR (u, eta))
      F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X := rfl

theorem edit_before (f : ℝ → ℝ) (h nu : ℝ) {K X : ℝ} (hK : 0 < K) (hX : 0 < X) (hle : X ≤ K) :
    ExtendedHeatDebts.edit f h nu K X = f X := by
  unfold ExtendedHeatDebts.edit ExtendedHeatDebts.multiplier ExtendedHeatDebts.correction
  rw [HeatTailEdit.switch_zero hK hX hle]
  ring

theorem heatE_before (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X)
    (hle : X ≤ switchRadius F XR) : heatE F XR (X, eta) = OutgoingDilation.E F XR (X, eta) := by
  rw [heatE_eq_edit, edit_before _ _ _ (OutgoingDilation.switchRadius_pos F XR hXR) hX hle]

theorem heatE_after (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hle : switchRadius F XR ≤ X) :
    heatE F XR (X, eta) = ExtendedHeatDebts.physicalEdit F.data (switchRadius F XR) eta X := by
  rw [heatE_eq_edit]
  unfold ExtendedHeatDebts.physicalEdit ExtendedHeatDebts.edit
  dsimp only
  rw [OutgoingDilation.E_eq_clean_switch_profile F XR eta X hXR hle]

theorem E_after_switch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) (hXR : 0 < XR)
    (hle : switchRadius F XR ≤ X) :
    E F XR c (X, eta) = ExtendedHeatDebts.physicalEdit F.data (switchRadius F XR) eta X := by
  rw [E, HeatedOutgoing.patchIncrement, OutgoingDilation.correction_zero_after_switch F XR X hXR (c
    eta) hle,
    mul_zero, add_zero, heatE_after F XR eta X hXR hle]

theorem E_before_patch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) (hp : X ≤ patchRadius F XR) :
    E F XR c (X, eta) = OutgoingDilation.E F XR (X, eta) := by
  have hK : X ≤ switchRadius F XR := hp.trans
    ((le_mul_of_one_le_right (OutgoingDilation.patchRadius_pos F XR hXR).le
      compensationPatch.ordered.le).trans
      (OutgoingDilation.patch_before_switch F XR hXR).le)
  have hh := HeatedOutgoing.E_before_patch F XR c eta X hXR hX hp
  rw [HeatedOutgoing.E, HeatedOutgoing.heatE_before F XR eta X hXR hX hK] at hh
  rw [E, heatE_before F XR eta X hXR hX hK]
  exact hh

theorem E_on_patch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X)
    (hp : X / patchRadius F XR ∈ Icc compensationPatch.left compensationPatch.right) :
    E F XR c (X, eta) = TerminalCompensation.physicalProfile compensationPatch F.data.core.lam
      (patchRadius F XR) (shapedPatchAmplitude F eta) (c eta) X := by
  rw [E, heatE_before F XR eta X hXR hX (HeatedOutgoing.patch_below_switch F XR X hXR hp).le,
    OutgoingDilation.patch_model F XR eta X hXR hp]
  unfold HeatedOutgoing.patchIncrement TerminalCompensation.physicalProfile
    TerminalCompensation.cleanProfile
  ring

noncomputable def heatRow (F : Profile) (XR eta : ℝ) (i : Fin 3) (X : ℝ) : ℝ :=
  ![ExtendedHeatDebts.squareChange (HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta)
      F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X / X,
    ExtendedHeatDebts.squareChange (HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta)
      F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X,
    Real.sqrt (2 * X) * ExtendedHeatDebts.change (HeatTailEdit.outgoingProfile F.data (switchRadius
      F XR) eta)
      F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X] i

noncomputable def changeRow (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ) (i : Fin 3) (X : ℝ) :
  ℝ :=
  ![(E F XR c (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2) / X,
    E F XR c (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2,
    Real.sqrt (2 * X) * (E F XR c (X, eta) - OutgoingDilation.E F XR (X, eta))] i

theorem heat_differences (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    heatE F XR (X, eta) - OutgoingDilation.E F XR (X, eta) =
      ExtendedHeatDebts.change (HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta)
        F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X ∧
    heatE F XR (X, eta) ^ 2 - OutgoingDilation.E F XR (X, eta) ^ 2 =
      ExtendedHeatDebts.squareChange (HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta)
        F.data.h (ParametricHeatTail.diffusion eta) (switchRadius F XR) X := by
  by_cases hle : X ≤ switchRadius F XR
  · rw [heatE_before F XR eta X hXR hX hle]
    simp only [ExtendedHeatDebts.change, ExtendedHeatDebts.squareChange,
      edit_before _ _ _ (OutgoingDilation.switchRadius_pos F XR hXR) hX hle, sub_self, and_self]
  · have hge := (lt_of_not_ge hle).le
    rw [heatE_after F XR eta X hXR hge, OutgoingDilation.E_eq_clean_switch_profile F XR eta X hXR
      hge]
    exact ⟨rfl, rfl⟩

theorem patch_square_difference (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) :
    E F XR c (X, eta) ^ 2 - heatE F XR (X, eta) ^ 2 = HeatedOutgoing.patchRow F XR c eta 1 X := by
  by_cases hp : X / patchRadius F XR ∈ Icc compensationPatch.left compensationPatch.right
  · rw [E_on_patch F XR c eta X hXR hX hp,
      heatE_before F XR eta X hXR hX (HeatedOutgoing.patch_below_switch F XR X hXR hp).le,
      OutgoingDilation.patch_model F XR eta X hXR hp]
    rfl
  · have hc := HeatedOutgoing.correction_zero_outside (c eta) hp
    simp [E, HeatedOutgoing.patchIncrement, hc, HeatedOutgoing.patchRow,
      TerminalCompensation.physicalProfile, TerminalCompensation.cleanProfile]

theorem changeRow_decomposition (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta : ℝ)
    (i : Fin 3) (X : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    changeRow F XR c eta i X = heatRow F XR eta i X + HeatedOutgoing.patchRow F XR c eta i X := by
  have hh := heat_differences F XR eta X hXR hX
  have hp := patch_square_difference F XR c eta X hXR hX
  have hl := HeatedOutgoing.patchIncrement_eq_difference F XR c eta X
  fin_cases i <;> norm_num [changeRow, heatRow, HeatedOutgoing.patchRow] at hp ⊢
  · rw [← hh.2, ← hp]; ring
  · rw [← hh.2, ← hp]; ring
  · rw [← hh.1, E, hl]; ring

theorem heatRow_zero_before (F : Profile) (XR eta : ℝ) (i : Fin 3) (X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) (hle : X ≤ switchRadius F XR) : heatRow F XR eta i X = 0 := by
  fin_cases i <;> simp [heatRow, ExtendedHeatDebts.change, ExtendedHeatDebts.squareChange,
    edit_before _ _ _ (OutgoingDilation.switchRadius_pos F XR hXR) hX hle]

theorem heatRow_integral (F : Profile) (XR eta : ℝ) (i : Fin 3) (hXR : 0 < XR) :
    (∫ X in Ioi 0, heatRow F XR eta i X) = ExtendedHeatDebts.physicalDebt F.data (switchRadius F
      XR) eta i := by
  rw [HeatedOutgoing.integral_positive_tail _ (switchRadius F XR)
    (OutgoingDilation.switchRadius_pos F XR hXR)
    (fun X hX hXK => heatRow_zero_before F XR eta i X hXR hX hXK)]
  fin_cases i <;> rfl

namespace Witness

variable {F : Profile} {XR C : ℝ} (w : Witness F XR C)

include w in
theorem heatRow_integrable (eta : ℝ) (i : Fin 3) : IntegrableOn (heatRow F XR eta i) (Ioi 0) := by
  apply HeatedOutgoing.integrable_positive_tail _ (switchRadius F XR)
    (OutgoingDilation.switchRadius_pos F XR w.radius_pos)
    (fun X hX hXK => heatRow_zero_before F XR eta i X w.radius_pos hX hXK)
  have hi := ExtendedHeatDebts.physical_debts_integrable F.data w.switch_large eta
  fin_cases i
  · exact hi.1
  · exact hi.2.1
  · exact hi.2.2

theorem changeRow_integrable (eta : ℝ) (i : Fin 3) :
    IntegrableOn (changeRow F XR w.coefficients eta i) (Ioi 0) :=
  IntegrableOn.congr_fun ((w.heatRow_integrable eta i).add
    (HeatedOutgoing.patchRow_integrable F XR w.coefficients eta i w.radius_pos))
    (fun X hX => (changeRow_decomposition F XR w.coefficients eta i X w.radius_pos hX).symm)
    measurableSet_Ioi

theorem changeRow_integral_zero (eta : ℝ) (i : Fin 3) (heta : eta ∈ parameterDomain) :
    (∫ X in Ioi 0, changeRow F XR w.coefficients eta i X) = 0 := by
  calc
    _ = ∫ X in Ioi 0, heatRow F XR eta i X + HeatedOutgoing.patchRow F XR w.coefficients eta i X :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun X hX => changeRow_decomposition F XR w.coefficients eta i X w.radius_pos hX)
    _ = _ := by
      rw [integral_add (w.heatRow_integrable eta i)
        (HeatedOutgoing.patchRow_integrable F XR w.coefficients eta i w.radius_pos),
          heatRow_integral F XR eta i w.radius_pos,
        HeatedOutgoing.patchRow_integral F XR w.coefficients eta i w.radius_pos]
      have h := congrFun (w.moments eta (parameterDomain_subset heta)) i
      simp only [Pi.add_apply, Pi.zero_apply] at h
      linarith

theorem positive (eta X : ℝ) (heta : eta ∈ parameterDomain) (hX : 0 < X) :
    0 < E F XR w.coefficients (X, eta) := by
  by_cases hp : X / patchRadius F XR ∈ Icc compensationPatch.left compensationPatch.right
  · rw [E_on_patch F XR w.coefficients eta X w.radius_pos hX hp]
    exact w.patch_positive eta (parameterDomain_subset heta) X hX
  · rw [E, HeatedOutgoing.patchIncrement, HeatedOutgoing.correction_zero_outside (w.coefficients
    eta) hp,
      mul_zero, add_zero]
    by_cases hle : X ≤ switchRadius F XR
    · rw [heatE_before F XR eta X w.radius_pos hX hle]
      exact OutgoingDilation.positive F XR _
    · rw [heatE_after F XR eta X w.radius_pos (lt_of_not_ge hle).le]
      exact w.heat_positive eta (parameterDomain_subset heta) X hX

end Witness

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

theorem E_times_U (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) :
    E F XR c (X, eta) * U F XR (X, eta) = OutgoingDilation.E F XR (X, eta) * U F XR (X, eta) := by
  have hh : heatE F XR (X, eta) * U F XR (X, eta) = OutgoingDilation.E F XR (X, eta) * U F XR (X,
    eta) := by
    by_cases hle : X ≤ switchRadius F XR
    · rw [heatE_before F XR eta X hXR hX hle]
    · have hu : U F XR (X, eta) = 0 := HeatedOutgoing.U_after_switch F XR eta X hXR (lt_of_not_ge
      hle).le
      rw [hu, mul_zero, mul_zero]
  have hp : HeatedOutgoing.patchIncrement F XR c (X, eta) * U F XR (X, eta) = 0 := by
    rw [HeatedOutgoing.patchIncrement, mul_assoc]
    change shapedPatchAmplitude F eta *
      (TerminalCompensation.correction compensationPatch (c eta) (X / patchRadius F XR) *
        OutgoingDilation.U F XR (X, eta)) = 0
    rw [OutgoingDilation.correction_times_U_zero F XR eta X hXR, mul_zero]
  rw [E, add_mul, hh, hp, add_zero]

theorem J_integrand_eq (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) :
    H F XR c (X, eta) * U F XR (X, eta) = OutgoingDilation.H F XR (X, eta) * OutgoingDilation.U F
      XR (X, eta) := by
  simpa only [H, OutgoingDilation.H, U, HeatedOutgoing.U, mul_assoc] using
    congrArg (fun z => Real.sqrt (2 * X) * z) (E_times_U F XR c eta X hXR hX)

theorem M_unchanged (F : Profile) (XR eta X : ℝ) : M F XR eta X = OutgoingDilation.M F XR eta X :=
  rfl

theorem J_unchanged (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ) (hXR : 0 < XR) :
    J F XR c eta X = OutgoingDilation.J F XR eta X :=
  setIntegral_congr_fun measurableSet_Ioc (fun u hu => J_integrand_eq F XR c eta u hXR hu.1)

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

theorem freeLogE_eq (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta y : ℝ) :
    HeatedOutgoing.freeLogE F XR ((c eta, eta), y) = E F XR c (Real.exp y, eta) := rfl

namespace Witness

variable {F : Profile} {XR C : ℝ} (w : Witness F XR C)

theorem canonicalKernel_integrable (eta : ℝ) :
    IntegrableOn (canonicalKernel F XR w.coefficients eta) (Ioi 0) := by
  rw [funext (kernel_decomposition F XR w.coefficients eta)]
  exact (OutgoingDilation.canonicalKernel_integrable F XR eta w.radius_pos).add
    (w.changeRow_integrable eta 0)

theorem pressure_integral_unchanged (eta : ℝ) (heta : eta ∈ parameterDomain) :
    (∫ X in Ioi 0, canonicalKernel F XR w.coefficients eta X) =
      ∫ X in Ioi 0, OutgoingDilation.canonicalKernel F XR eta X := by
  simp_rw [kernel_decomposition]
  rw [integral_add (OutgoingDilation.canonicalKernel_integrable F XR eta w.radius_pos)
    (w.changeRow_integrable eta 0), w.changeRow_integral_zero eta 0 heta, add_zero]

theorem axisDatum_eq (eta : ℝ) (heta : eta ∈ parameterDomain) :
    axisDatum F XR w.coefficients eta = F.axisDatum eta := by
  rw [axisDatum, w.pressure_integral_unchanged eta heta]
  change OutgoingDilation.axisDatum F XR eta = F.axisDatum eta
  rw [OutgoingDilation.axisDatum_unchanged F XR w.radius_pos]

theorem energy_integrable (eta : ℝ) : IntegrableOn (energyDensity F XR w.coefficients eta) (Ioi 0)
  := by
  rw [funext (energy_decomposition F XR w.coefficients eta)]
  exact (OutgoingDilation.energy_integrable F XR eta w.radius_pos).sub ((w.changeRow_integrable eta
    1).div_const 2)

theorem totalS_eq (eta : ℝ) (heta : eta ∈ parameterDomain) :
    totalS F XR w.coefficients eta = OutgoingDilation.totalS F XR eta := by
  unfold totalS OutgoingDilation.totalS
  simp_rw [energy_decomposition]
  rw [integral_sub (OutgoingDilation.energy_integrable F XR eta w.radius_pos)
    ((w.changeRow_integrable eta 1).div_const 2), integral_div,
    w.changeRow_integral_zero eta 1 heta, zero_div, sub_zero]

theorem renormalized_integrable (eta : ℝ) :
    IntegrableOn (fun X => H F XR w.coefficients (X, eta) - OutgoingDilation.powerH F XR X) (Ioi 0)
      := by
  rw [funext (renormalized_decomposition F XR w.coefficients eta)]
  exact (OutgoingDilation.renormalized_integrable F XR eta w.radius_pos).add
    (w.changeRow_integrable eta 2)

theorem renormalized_zero (eta : ℝ) (heta : eta ∈ parameterDomain) :
    (∫ X in Ioi 0, H F XR w.coefficients (X, eta) - OutgoingDilation.powerH F XR X) = 0 := by
  simp_rw [renormalized_decomposition]
  rw [integral_add (OutgoingDilation.renormalized_integrable F XR eta w.radius_pos)
    (w.changeRow_integrable eta 2), w.changeRow_integral_zero eta 2 heta, add_zero]
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
  have hi := (w.changeRow_integrable eta 0).mono_set hs
  have hb := (OutgoingDilation.canonicalKernel_integrable F XR eta w.radius_pos).mono_set hs
  have hz : (∫ u in Ioi X, changeRow F XR w.coefficients eta 0 u) = 0 := by
    rw [← HeatedOutgoing.integral_positive_tail _ X hX (fun u hu huX => ?_),
      w.changeRow_integral_zero eta 0 heta]
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
  have hp := hX'.trans (HeatedOutgoing.entrance_before_patch F XR w.radius_pos).le
  rw [E_before_patch F XR w.coefficients eta X w.radius_pos hX hp, w.Pi_before_patch eta X heta hX
    hp]
  have h := OutgoingDilation.ideal_prefix F XR eta X w.radius_pos hX hX'
  rw [OutgoingDilation.axisDatum_unchanged F XR w.radius_pos] at h
  exact h

theorem logE_square_integrable (eta : ℝ) :
    Integrable (fun y => E F XR w.coefficients (Real.exp y, eta) ^ 2) := by
  have hi := w.canonicalKernel_integrable eta
  rw [← Real.range_exp, ← image_univ] at hi
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn _).mp hi
  simp_rw [canonicalKernel_comp_exp] at h
  simpa only [integrableOn_univ] using h

theorem Pi_exp_primitive (eta y : ℝ) (heta : eta ∈ parameterDomain) :
    Pi F XR w.coefficients (Real.exp y, eta) = OutgoingDilation.Pi F XR (patchRadius F XR, eta) +
      (1 / 2 : ℝ) * ∫ t in Real.log (patchRadius F XR)..y,
        HeatedOutgoing.freeLogE F XR ((w.coefficients eta, eta), t) ^ 2 := by
  have hi := w.logE_square_integrable eta
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
  simp_rw [freeLogE_eq]
  linarith

theorem Pi_log_contDiffOn : ContDiffOn ℝ ∞
    (fun p : ℝ × ℝ => Pi F XR w.coefficients (Real.exp p.1, p.2)) (univ ×ˢ parameterDomain) := by
  have hf := (HeatedOutgoing.freeLogE_contDiff F XR w.radius_pos).pow 2
  have hi := HeatedOutgoing.anchoredPrimitive_contDiff _ hf (Real.log (patchRadius F XR))
  have hc : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => ((w.coefficients p.2, p.2), p.1))
      (univ ×ˢ parameterDomain) :=
    ((w.coefficients_contDiffOn.comp contDiffOn_snd (fun _ hp => hp.2)).prodMk
      contDiffOn_snd).prodMk contDiffOn_fst
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
    (contDiffOn_fst.log (fun _ hp => ne_of_gt hp.1)).prodMk contDiffOn_snd
  apply (w.Pi_log_contDiffOn.comp hl (fun _ hp => ⟨mem_univ _, hp.2⟩)).congr
  intro p hp
  dsimp only [Function.comp_def]
  rw [Real.exp_log hp.1]

theorem fields_contDiffAt {p : ℝ × ℝ} (hp : p ∈ domain) :
    ContDiffAt ℝ ∞ (E F XR w.coefficients) p ∧ ContDiffAt ℝ ∞ (U F XR) p ∧
      ContDiffAt ℝ ∞ (H F XR w.coefficients) p ∧ ContDiffAt ℝ ∞ (Pi F XR w.coefficients) p := by
  have hn := (isOpen_Ioi.prod parameterDomain_open).mem_nhds hp
  exact ⟨(E_contDiffOn F XR w.radius_pos w.coefficients_contDiffOn).contDiffAt hn,
    (U_contDiffOn F XR w.radius_pos).contDiffAt hn,
    (H_contDiffOn F XR w.radius_pos w.coefficients_contDiffOn).contDiffAt hn,
    w.Pi_contDiffOn.contDiffAt hn⟩

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

end Witness

/-! The original amplitude is a globally smooth clamped formula. Its actual
energy equation holds on this explicit open set. The schedule bounds below
place the entire physical band strictly inside that set. -/

noncomputable def energyDomain (F : Profile) : Set ℝ :=
  parameterDomain ∩ {eta | CorrectedPulseAmplitude.constantTerm F.data F.reset.coefficients eta <
    -(1 / 5)}

theorem energyDomain_open (F : Profile) : IsOpen (energyDomain F) :=
  parameterDomain_open.inter
    (isOpen_lt (CorrectedPulseAmplitude.constantTerm_contDiff F.data F.reset.smooth).continuous
      continuous_const)

structure ScheduleBounds (F : Profile) : Prop where
  coefficient_pos : 0 < F.coefficientBound
  lambda_small : F.data.core.lam ≤ 1 / 120
  wait_eq : F.data.core.wait = 60 * Real.log (1 / F.data.core.lam)
  scale_small : CorrectedPulseAmplitude.combinedScale F.data F.coefficientBound ≤ 1 / 1000

theorem ScheduleBounds.constantTerm_bound {F : Profile} (b : ScheduleBounds F)
    {eta : ℝ} (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    CorrectedPulseAmplitude.constantTerm F.data F.reset.coefficients eta ≤ -(23 / 100) := by
  have he := HeatedOutgoing.parameter_sq_le_one heta
  have ho := CorrectedPulseAmplitude.old_error_bounds F.data F.coefficientBound b.coefficient_pos
    b.lambda_small b.wait_eq eta he
  have hs := CorrectedPulseAmplitude.energyShift_bounds F.reset b.coefficient_pos eta he
  exact (CorrectedPulseAmplitude.numerical_coefficient_bounds F.data F.reset.coefficients eta
    (CorrectedPulseAmplitude.combinedScale F.data F.coefficientBound) he ho hs.1
      b.scale_small).2.2.2.2

theorem ScheduleBounds.physicalBand_subset {F : Profile} (b : ScheduleBounds F) :
    HeatedOutgoing.parameterDomain ⊆ energyDomain F := by
  intro eta heta
  exact ⟨NavierStokes.ExtendedHeatedOutgoing.physicalBand_subset heta,
    lt_of_le_of_lt (b.constantTerm_bound heta) (by norm_num)⟩

noncomputable def amplitudeBound (F : Profile) : ℝ :=
  128 * CorrectedPulseAmplitude.combinedConstant F.data.core.P F.data.core.m F.coefficientBound

theorem ScheduleBounds.amplitudeBound_pos {F : Profile} (b : ScheduleBounds F) :
    0 < amplitudeBound F := mul_pos (by norm_num)
      (CorrectedPulseAmplitude.combinedConstant_pos F.data.core.P_pos F.data.core.m _
        b.coefficient_pos)

/-- The same reset and amplitude provide the original full specification,
with the stronger quantitative data retained for the open extension. -/
theorem ScheduleBounds.specification {F : Profile} (b : ScheduleBounds F) :
    OutgoingProfile.Specification F (amplitudeBound F) := by
  have hs := CorrectedPulseAmplitude.amplitude_spec F.reset b.coefficient_pos
    b.lambda_small b.wait_eq b.scale_small
  refine {
    amplitude_smooth := F.amp_contDiff
    angular_smooth := F.E_contDiffOn
    axial_smooth := F.U_contDiffOn
    momentum_smooth := F.H_contDiffOn
    pressure_smooth := F.Pi_contDiffOn
    angular_positive := fun p _ => F.E_pos p
    amplitude_bounds := ?_
    mass_integrable := F.mass_integrable
    angular_integrable := F.angular_integrable
    mass_total_zero := F.mass_integral_zero
    angular_total_zero := F.angular_integral_zero
    after_pulse := fun eta X hX hfar => ⟨F.U_after eta hfar, F.moments_after eta hX hfar⟩
    energy_integrable := F.energy_integrable
    energy_zero := ?_
    renormalized_integrable := F.renormalized_integrable
    renormalized_zero := F.renormalized_angular_moment
    eventual_power := fun eta X hX hfar =>
      ⟨F.U_after eta (F.tailEnd_after_endpoint.trans hfar), F.E_eventual eta hX hfar,
        F.angular_history_eventual eta hX hfar⟩
    ideal_prefix := fun eta X hX hX' =>
      ⟨F.E_ideal eta hX hX', F.U_ideal eta hX hX', F.Pi_ideal eta hX hX'⟩
    pressure_integrable := F.canonicalKernel_integrable
    pressure_canonical := fun eta X hX => F.Pi_canonical eta hX
    same_axis_datum := F.axisDatum_eq
    axis_limit := F.Pi_tendsto_axis
    analytic_axis_datum := F.axisDatum_analytic_extension }
  · intro eta heta
    obtain ⟨ha, ha', _, hd, _⟩ := hs.2 eta heta
    refine ⟨ha, ha', ?_⟩
    convert! hd using 1
    unfold amplitudeBound CorrectedPulseAmplitude.combinedScale PulseAmplitude.logarithmicRate
    ring
  · intro eta heta
    rw [F.totalS_eq]
    exact (hs.2 eta heta).2.2.1

theorem base_energy_zero (F : Profile) (XR eta : ℝ) (hXR : 0 < XR)
    (heta : eta ∈ energyDomain F) : OutgoingDilation.totalS F XR eta = 0 := by
  rw [OutgoingDilation.totalS_scaling F XR eta hXR, F.totalS_eq]
  have h := CorrectedPulseAmplitude.amplitude_totalEnergy_zero F.data F.reset.coefficients eta
    heta.2.le
  change CorrectedPulseAmplitude.totalEnergy F.data F.reset.coefficients (F.amp eta) eta = 0 at h
  rw [h, mul_zero]

theorem Witness.energy_zero {F : Profile} {XR C : ℝ} (w : Witness F XR C)
    (eta : ℝ) (heta : eta ∈ energyDomain F) : totalS F XR w.coefficients eta = 0 := by
  rw [w.totalS_eq eta heta.1]
  exact base_energy_zero F XR eta w.radius_pos heta

/-- The quantitative schedule is chosen directly with one actual reset.
The amplitude attached to the resulting `Profile` is unchanged thereafter. -/
theorem exists_scheduled_profile (P m : ℝ) (hP : 0 < P) (hm : 0 < m) :
    ∃ lam B : ℝ, 0 < lam ∧ 0 < B ∧ ∀ h : ℝ, 0 < h → 2 * h < lam →
      ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧ F.data.core.lam = lam ∧
        F.data.h = h ∧ ScheduleBounds F ∧ OutgoingProfile.Specification F B := by
  obtain ⟨resetLam, K, hresetLam, hK, hreset⟩ := UniformAngularReset.exists_scheduled_reset
  obtain ⟨delta, hdelta, hrate⟩ := PulseAmplitude.exists_rate_threshold
    (CorrectedPulseAmplitude.combinedConstant P m K)
  let lam₀ := min resetLam (min delta (1 / 120 : ℝ))
  have hlam₀ : 0 < lam₀ := lt_min hresetLam (lt_min hdelta (by norm_num))
  let lam := lam₀ / 2
  have hlam : 0 < lam := half_pos hlam₀
  have hlam₀' : lam < lam₀ := half_lt_self hlam₀
  have hreset' : lam < resetLam := hlam₀'.trans_le (min_le_left _ _)
  have hdelta' : lam < delta := hlam₀'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : lam < 1 / 120 := hlam₀'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨lam, 128 * CorrectedPulseAmplitude.combinedConstant P m K, hlam,
    mul_pos (by norm_num) (CorrectedPulseAmplitude.combinedConstant_pos hP m K hK), ?_⟩
  intro h hh htail
  let d : OutgoingTail.TailData := ⟨OutgoingSchedule.paperParameters P m lam hP hm hlam (by
    linarith), h, hh, htail⟩
  obtain ⟨r⟩ := hreset d hreset'
  let F : Profile := ⟨d, K, r⟩
  have b : ScheduleBounds F := {
    coefficient_pos := hK
    lambda_small := hsmall.le
    wait_eq := rfl
    scale_small := hrate lam hlam hdelta' }
  exact ⟨F, rfl, rfl, rfl, rfl, b, b.specification⟩

theorem E_full_switch (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X)
    (hfull : 1 / 2 ≤ Real.log (X / switchRadius F XR) + 1 / 5) :
    E F XR c (X, eta) =
      (OutgoingDilation.carrierAmplitude F * (switchRadius F XR) ^ HeatTailEdit.exponent F.data.h) *
        X ^ (-HeatTailEdit.exponent F.data.h) * HeatProfileExtension.physicalProfile (1 + F.data.h)
          X eta *
          OutgoingTail.tailShape F.data (Real.log (X / switchRadius F XR) + 1 / 5) := by
  have hK := OutgoingDilation.switchRadius_pos F XR hXR
  rw [E_after_switch F XR c eta X hXR (HeatedOutgoing.full_switch_above_radius hK hX hfull)]
  unfold ExtendedHeatDebts.physicalEdit ExtendedHeatDebts.edit ExtendedHeatDebts.multiplier
    ExtendedHeatDebts.correction
  rw [HeatTailEdit.switch_one (by linarith), one_mul, add_sub_cancel,
    HeatTailEdit.outgoingProfile_eq_powerTail_of_log F.data hK hX (by linarith)]
  change HeatTailEdit.outgoingAmplitude F.data * (X / switchRadius F XR) ^ (-HeatTailEdit.exponent
    F.data.h) *
    OutgoingTail.tailShape F.data (Real.log (X / switchRadius F XR) + 1 / 5) *
    HeatProfileExtension.physicalProfile (1 + F.data.h) X eta = _
  rw [Real.div_rpow hX.le hK.le, Real.rpow_neg hK.le, div_inv_eq_mul]
  unfold OutgoingDilation.carrierAmplitude
  ring

theorem E_eventual_extended_heat (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X)
    (hlate : 3 ≤ Real.log (X / switchRadius F XR) + 1 / 5) :
    E F XR c (X, eta) =
      (OutgoingDilation.carrierAmplitude F * (switchRadius F XR) ^ HeatTailEdit.exponent F.data.h) *
        X ^ (-HeatTailEdit.exponent F.data.h) * HeatProfileExtension.physicalProfile (1 + F.data.h)
          X eta := by
  rw [E_full_switch F XR c eta X hXR hX (by linarith), OutgoingTail.tailShape_late F.data hlate,
    mul_one]

theorem E_eventual_heat (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) (heta : eta ∈ HeatedOutgoing.parameterDomain)
    (hlate : 3 ≤ Real.log (X / switchRadius F XR) + 1 / 5) :
    E F XR c (X, eta) =
      (OutgoingDilation.carrierAmplitude F * (switchRadius F XR) ^ HeatTailEdit.exponent F.data.h) *
        RadialHeatProfile.spatialProfile (1 + F.data.h) (ParametricHeatTail.diffusion eta) X := by
  rw [E_eq_physical F XR c eta X heta hX]
  exact HeatedOutgoing.E_eventual_heat F XR c eta X hXR hX hlate

theorem E_between_patch_and_switch (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    (eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X)
    (hp : patchRadius F XR * compensationPatch.right ≤ X) (hK : X ≤ switchRadius F XR) :
    E F XR c (X, eta) = OutgoingDilation.E F XR (X, eta) := by
  have h := HeatedOutgoing.E_between_patch_and_switch F XR c eta X hXR hX hp hK
  rw [HeatedOutgoing.E, HeatedOutgoing.heatE_before F XR eta X hXR hX hK] at h
  rw [E, heatE_before F XR eta X hXR hX hK]
  exact h

theorem exists_symmetric_neighborhood {V : Set ℝ} (hV : IsOpen V)
    (hband : HeatedOutgoing.parameterDomain ⊆ V) :
    ∃ a : ℝ, 1 < a ∧ a < 3 / 2 ∧ Ioo (-a) a ⊆ V := by
  obtain ⟨r, hr, hL⟩ := Metric.isOpen_iff.mp hV (-1) (hband (by constructor <;> norm_num))
  obtain ⟨s, hs, hR⟩ := Metric.isOpen_iff.mp hV 1 (hband (by constructor <;> norm_num))
  let d := min (min r s) (1 / 2 : ℝ) / 2
  have hmin : 0 < min (min r s) (1 / 2 : ℝ) := lt_min (lt_min hr hs) (by norm_num)
  have hd : 0 < d := half_pos hmin
  have hdmin : d < min (min r s) (1 / 2 : ℝ) := half_lt_self hmin
  have hdr : d < r := hdmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hds : d < s := hdmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hdhalf : d < 1 / 2 := hdmin.trans_le (min_le_right _ _)
  refine ⟨1 + d, by linarith, by linarith, ?_⟩
  intro eta heta
  by_cases hlow : eta < -1
  · apply hL
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith : eta - -1 < 0)]
    linarith [heta.1]
  · by_cases hhigh : 1 < eta
    · apply hR
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < eta - 1)]
      linarith [heta.2]
    · exact hband ⟨le_of_not_gt hlow, le_of_not_gt hhigh⟩

theorem ScheduleBounds.exists_parameter_interval {F : Profile} (b : ScheduleBounds F) :
    ∃ a : ℝ, 1 < a ∧ a < 3 / 2 ∧ Ioo (-a) a ⊆ energyDomain F :=
  exists_symmetric_neighborhood (energyDomain_open F) b.physicalBand_subset

namespace Witness

variable {F : Profile} {XR C : ℝ} (w : Witness F XR C)

theorem first_jet_open {eta : ℝ} (heta : eta ∈ parameterDomain) :
    TerminalCompensation.FirstJetBound compensationPatch (shapedPatchAmplitude F)
      w.coefficients eta (C / switchRadius F XR) :=
  (w.first_jet eta (parameterDomain_subset heta)).toFirstJetBound (enlargedBand_mem_nhds heta)

theorem physical_specification (b : ScheduleBounds F) :
    HeatedOutgoing.Specification F XR w.physical.coefficients :=
  w.physical.specification b.specification

theorem fields_eq_physical (eta X : ℝ) (heta : eta ∈ HeatedOutgoing.parameterDomain) (hX : 0 < X) :
    E F XR w.coefficients (X, eta) = HeatedOutgoing.E F XR w.physical.coefficients (X, eta) ∧
    U F XR (X, eta) = HeatedOutgoing.U F XR (X, eta) ∧
    H F XR w.coefficients (X, eta) = HeatedOutgoing.H F XR w.physical.coefficients (X, eta) ∧
    Pi F XR w.coefficients (X, eta) = HeatedOutgoing.Pi F XR w.physical.coefficients (X, eta) :=
  ⟨E_eq_physical F XR w.coefficients eta X heta hX, rfl,
    H_eq_physical F XR w.coefficients eta X heta hX, Pi_eq_physical F XR w.coefficients eta X heta
      hX.le⟩

theorem axisDatum_analytic_extension :
    AnalyticOnNhd ℂ (SchedulePressure.complexAxisPressure F.data) PressureDatum.strip ∧
      ∀ eta ∈ parameterDomain, SchedulePressure.complexAxisPressure F.data (eta : ℂ) =
        (axisDatum F XR w.coefficients eta : ℂ) := by
  refine ⟨F.axisDatum_analytic_extension.1, ?_⟩
  intro eta heta
  rw [w.axisDatum_eq eta heta]
  exact F.axisDatum_analytic_extension.2 eta

end Witness

/-- The complete open-neighborhood specification. All functions are the
literal extended fields of the same chosen outgoing profile. -/
structure Specification (F : Profile) (XR : ℝ) (c : ℝ → Coeff) : Prop where
  neighborhood_open : IsOpen (energyDomain F)
  neighborhood_contains : HeatedOutgoing.parameterDomain ⊆ energyDomain F
  fields_smooth : ∀ p ∈ Ioi (0 : ℝ) ×ˢ energyDomain F,
    ContDiffAt ℝ ∞ (E F XR c) p ∧ ContDiffAt ℝ ∞ (U F XR) p ∧
      ContDiffAt ℝ ∞ (H F XR c) p ∧ ContDiffAt ℝ ∞ (Pi F XR c) p
  angular_positive : ∀ eta ∈ energyDomain F, ∀ X : ℝ, 0 < X → 0 < E F XR c (X, eta)
  axial_unchanged : U F XR = OutgoingDilation.U F XR
  mass_unchanged : ∀ eta X : ℝ, M F XR eta X = OutgoingDilation.M F XR eta X
  angular_unchanged : ∀ eta X : ℝ, J F XR c eta X = OutgoingDilation.J F XR eta X
  mass_integrable : ∀ eta : ℝ, IntegrableOn (fun X => U F XR (X, eta)) (Ioi 0)
  angular_integrable : ∀ eta : ℝ, IntegrableOn (fun X => H F XR c (X, eta) * U F XR (X, eta)) (Ioi
    0)
  energy_integrable : ∀ eta : ℝ, IntegrableOn (energyDensity F XR c eta) (Ioi 0)
  pressure_integrable : ∀ eta : ℝ, IntegrableOn (canonicalKernel F XR c eta) (Ioi 0)
  renormalized_integrable : ∀ eta : ℝ,
    IntegrableOn (fun X => H F XR c (X, eta) - OutgoingDilation.powerH F XR X) (Ioi 0)
  mass_zero : ∀ eta : ℝ, (∫ X in Ioi 0, U F XR (X, eta)) = 0
  angular_zero : ∀ eta : ℝ, (∫ X in Ioi 0, H F XR c (X, eta) * U F XR (X, eta)) = 0
  energy_zero : ∀ eta ∈ energyDomain F, totalS F XR c eta = 0
  renormalized_zero : ∀ eta ∈ energyDomain F,
    (∫ X in Ioi 0, H F XR c (X, eta) - OutgoingDilation.powerH F XR X) = 0
  pressure_canonical : ∀ eta X : ℝ,
    Pi F XR c (X, eta) = -(1 / 2 : ℝ) * ∫ u in Ioi X, E F XR c (u, eta) ^ 2 / u
  axis_unchanged : ∀ eta ∈ energyDomain F, axisDatum F XR c eta = F.axisDatum eta
  axis_limit : ∀ eta ∈ energyDomain F,
    Tendsto (fun X => Pi F XR c (X, eta)) (𝓝[>] (0 : ℝ)) (𝓝 (F.axisDatum eta))
  analytic_axis_datum : AnalyticOnNhd ℂ (SchedulePressure.complexAxisPressure F.data)
    PressureDatum.strip ∧
    ∀ eta ∈ energyDomain F, SchedulePressure.complexAxisPressure F.data (eta : ℂ) =
      (axisDatum F XR c eta : ℂ)
  after_pulse : ∀ eta X : ℝ, 0 < X → OutgoingDilation.pulseEndRadius F XR ≤ X →
    U F XR (X, eta) = 0 ∧ M F XR eta X = 0 ∧ J F XR c eta X = 0
  before_patch : ∀ eta ∈ energyDomain F, ∀ X : ℝ, 0 < X → X ≤ patchRadius F XR →
    E F XR c (X, eta) = OutgoingDilation.E F XR (X, eta) ∧
      Pi F XR c (X, eta) = OutgoingDilation.Pi F XR (X, eta)
  ideal_prefix : ∀ eta ∈ energyDomain F, ∀ X : ℝ, 0 < X → X ≤ XR →
    E F XR c (X, eta) = F.data.core.P * OutgoingSchedule.shape eta * (X / XR) ^ (1 / 10 : ℝ) ∧
      U F XR (X, eta) = 4 * eta ∧
      Pi F XR c (X, eta) = F.axisDatum eta +
        (5 / 2) * F.data.core.P ^ 2 * OutgoingSchedule.shape eta ^ 2 * (X / XR) ^ (1 / 5 : ℝ)
  terminal_extended_heat : ∀ eta X : ℝ, 0 < X → 3 ≤ Real.log (X / switchRadius F XR) + 1 / 5 →
    E F XR c (X, eta) =
      (OutgoingDilation.carrierAmplitude F * (switchRadius F XR) ^ HeatTailEdit.exponent F.data.h) *
        X ^ (-HeatTailEdit.exponent F.data.h) * HeatProfileExtension.physicalProfile (1 + F.data.h)
          X eta
  physical_specification : HeatedOutgoing.Specification F XR c

theorem Witness.specification {F : Profile} {XR C : ℝ} (w : Witness F XR C) (b : ScheduleBounds F) :
    Specification F XR w.coefficients where
  neighborhood_open := energyDomain_open F
  neighborhood_contains := b.physicalBand_subset
  fields_smooth := fun _ hp => w.fields_contDiffAt ⟨hp.1, hp.2.1⟩
  angular_positive := fun eta heta X hX => w.positive eta X heta.1 hX
  axial_unchanged := rfl
  mass_unchanged := M_unchanged F XR
  angular_unchanged := fun eta X => J_unchanged F XR w.coefficients eta X w.radius_pos
  mass_integrable := w.mass_integrable
  angular_integrable := w.angular_integrable
  energy_integrable := w.energy_integrable
  pressure_integrable := w.canonicalKernel_integrable
  renormalized_integrable := w.renormalized_integrable
  mass_zero := w.mass_zero
  angular_zero := w.angular_zero
  energy_zero := w.energy_zero
  renormalized_zero := fun eta heta => w.renormalized_zero eta heta.1
  pressure_canonical := fun _ _ => rfl
  axis_unchanged := fun eta heta => w.axisDatum_eq eta heta.1
  axis_limit := fun eta heta => w.Pi_tendsto_axis eta heta.1
  analytic_axis_datum := ⟨w.axisDatum_analytic_extension.1,
    fun eta heta => w.axisDatum_analytic_extension.2 eta heta.1⟩
  after_pulse := w.after_pulse
  before_patch := fun eta heta X hX hp =>
    ⟨E_before_patch F XR w.coefficients eta X w.radius_pos hX hp, w.Pi_before_patch eta X heta.1 hX
      hp⟩
  ideal_prefix := fun eta heta X hX hp => w.ideal_prefix eta X heta.1 hX hp
  terminal_extended_heat := fun eta X hX htail => E_eventual_extended_heat F XR w.coefficients eta
    X w.radius_pos hX htail
  physical_specification := w.physical_specification b

theorem exists_open_profile {F : Profile} (b : ScheduleBounds F) :
    ∃ XR₀ C : ℝ, 0 < XR₀ ∧ 0 < C ∧ ∀ XR : ℝ, XR₀ ≤ XR →
      ∃ w : Witness F XR C, Specification F XR w.coefficients := by
  obtain ⟨XR₀, C, hXR₀, hC, hc⟩ := exists_witness F
  exact ⟨XR₀, C, hXR₀, hC, fun XR hXR => by
    obtain ⟨w⟩ := hc XR hXR
    exact ⟨w, w.specification b⟩⟩

/-- One schedule and one reset/amplitude pair yield an open parameter
interval and the actual compensated profile at every sufficiently large
entrance radius. The physical witness is the constructed restriction. -/
theorem exists_fixed_schedule (P m : ℝ) (hP : 0 < P) (hm : 0 < m) :
    ∃ lam B : ℝ, 0 < lam ∧ 0 < B ∧ ∀ h : ℝ, 0 < h → 2 * h < lam →
      ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧ F.data.core.lam = lam ∧
        F.data.h = h ∧ ScheduleBounds F ∧ OutgoingProfile.Specification F B ∧
        ∃ a : ℝ, 1 < a ∧ a < 3 / 2 ∧ Ioo (-a) a ⊆ energyDomain F ∧
        ∃ XR₀ C : ℝ, 0 < XR₀ ∧ 0 < C ∧ ∀ XR : ℝ, XR₀ ≤ XR →
          ∃ w : Witness F XR C, Specification F XR w.coefficients := by
  obtain ⟨lam, B, hlam, hB, hc⟩ := exists_scheduled_profile P m hP hm
  refine ⟨lam, B, hlam, hB, ?_⟩
  intro h hh hsmall
  obtain ⟨F, hP', hm', hlam', hh', b, hs⟩ := hc h hh hsmall
  obtain ⟨a, ha, ha', hsub⟩ := b.exists_parameter_interval
  exact ⟨F, hP', hm', hlam', hh', b, hs, a, ha, ha', hsub, exists_open_profile b⟩

end NavierStokes.ExtendedHeatedOutgoing
