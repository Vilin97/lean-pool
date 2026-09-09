/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleResidualBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.TailGaugePotential
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCurlCovariance

@[expose] public section

/-!
# Exterior identities for the actual finite physical prefixes

The assumptions concern the primitive potential, direct velocity, and
pressure stages on the genuine past exterior sublevel. Openness turns their
pointwise identities into the germs needed by the spatial curl. No global
support condition or final velocity identity is assumed.
-/

noncomputable section

namespace NavierStokes.ActualExteriorPrefix

open Set Filter ProblemStatement PhysicalWaveSum CorrectionInitialization
open scoped Topology BigOperators

/-- The open physical exterior on which the raw stages are constructed. -/
noncomputable def exteriorDomain (Nr : ℕ) : Set SpaceTime :=
  {w | w ∈ preterminal ∧ w ∉ ActualPolarCoverage.active} ∩
    CutStageEstimates.physicalSublevel ActualPrimary.h (ChartScales.Q Nr)

theorem mem_exteriorDomain {Nr : ℕ} {w : SpaceTime} :
    w ∈ exteriorDomain Nr ↔ w ∈ preterminal ∧
      physicalQ ActualPrimary.h w < ChartScales.Q Nr ∧ w ∉ ActualPolarCoverage.active := by
  constructor
  · intro hw
    exact ⟨hw.1.1, hw.2.2, hw.1.2⟩
  · rintro ⟨ht, hq, hout⟩
    exact ⟨⟨ht, hout⟩, ht, hq⟩

theorem exteriorDomain_open (Nr : ℕ) : IsOpen (exteriorDomain Nr) := by
  have ho : IsOpen {w : SpaceTime | w ∈ preterminal ∧ w ∉ ActualPolarCoverage.active} := by
    exact BaseResidual.chartedDomain_isOpen ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half
      (show IsOpen {p : ℝ × ℝ | p.1 ∉ Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
        (NominalConeAssembly.activeRight ActualPrimary.nominal)} from
        (isClosed_Icc.preimage continuous_fst).isOpen_compl)
  exact ho.inter (CutStageEstimates.physicalSublevel_open
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half _)

/-- Local primitive equality gives an ambient germ at every exterior point. -/
theorem eqOn_exterior_germ {V : Type*} {Nr : ℕ} {f g : SpaceTime → V}
    (h : EqOn f g (exteriorDomain Nr)) {w : SpaceTime} (hw : w ∈ exteriorDomain Nr) :
    f =ᶠ[𝓝 w] g := by
  filter_upwards [(exteriorDomain_open Nr).mem_nhds hw] with y hy
  exact h hy

/-- Primitive stage data on the valid exterior. The direct angular field
vanishes also at stage zero; the potential and pressure retain their actual
slow-base stage zero. -/
structure ExteriorStages (B Nr : ℕ) (A D : ℕ → VelocityField) (P : ℕ → PressureField) : Prop where
  potential_zero : EqOn (A 0)
    (TailGaugePotential.finalPotential ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B)
    (exteriorDomain Nr)
  potential_succ : ∀ k, EqOn (A (k + 1)) 0 (exteriorDomain Nr)
  direct_zero : ∀ k, EqOn (D k) 0 (exteriorDomain Nr)
  pressure_zero : EqOn (P 0)
    (FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation ActualPrimary.upper
      B)
    (exteriorDomain Nr)
  pressure_succ : ∀ k, EqOn (P (k + 1)) 0 (exteriorDomain Nr)

section PrefixAlgebra

variable {V : Type*} [NormedAddCommGroup V]

theorem uncutPrefix_eqOn_first {A : ℕ → SpaceTime → V} {f : SpaceTime → V} {U : Set SpaceTime}
    (h0 : EqOn (A 0) f U) (h : ∀ k, EqOn (A (k + 1)) 0 U) (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix A (J + 1)) f U := by
  classical
  intro w hw
  calc
    DiagonalJetBounds.uncutPrefix A (J + 1) w = A 0 w := by
      unfold DiagonalJetBounds.uncutPrefix
      apply Finset.sum_eq_single 0
      · intro k hk hk0
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        exact h l hw
      · intro hmem
        exact False.elim (hmem (Finset.mem_range.mpr (Nat.zero_lt_succ J)))
    _ = f w := h0 hw

theorem uncutPrefix_eqOn_zero {A : ℕ → SpaceTime → V} {U : Set SpaceTime}
    (h : ∀ k, EqOn (A k) 0 U) (N : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix A N) 0 U := by
  intro w hw
  unfold DiagonalJetBounds.uncutPrefix
  exact Finset.sum_eq_zero (fun k _ => h k hw)

end PrefixAlgebra

namespace ExteriorStages

variable {B Nr : ℕ} {A D : ℕ → VelocityField} {P : ℕ → PressureField}
    (H : ExteriorStages B Nr A D P)

include H

theorem potential_prefix_eqOn (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix A (J + 1))
      (TailGaugePotential.finalPotential ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B)
      (exteriorDomain Nr) :=
  uncutPrefix_eqOn_first H.potential_zero H.potential_succ J

theorem direct_prefix_eqOn (N : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix D N) 0 (exteriorDomain Nr) :=
  uncutPrefix_eqOn_zero H.direct_zero N

theorem pressure_prefix_eqOn (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix P (J + 1))
      (FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B)
      (exteriorDomain Nr) :=
  uncutPrefix_eqOn_first H.pressure_zero H.pressure_succ J

theorem potential_prefix_germ (J : ℕ) {w : SpaceTime} (hw : w ∈ exteriorDomain Nr) :
    DiagonalJetBounds.uncutPrefix A (J + 1) =ᶠ[𝓝 w]
      TailGaugePotential.finalPotential ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B :=
  eqOn_exterior_germ (H.potential_prefix_eqOn J) hw

/-- The spatial curl sees the actual potential germ, so the finite velocity
prefix agrees with the slow base without any differentiability premise on
the totalized raw stages. -/
theorem velocity_prefix_eqOn (J : ℕ) :
    EqOn (MixedDiagonalResidual.uncutVelocity A D J)
      (FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B)
      (exteriorDomain Nr) := by
  intro w hw
  change SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1)) w +
    DiagonalJetBounds.uncutPrefix D (J + 1) w = _
  rw [PhysicalCurlCovariance.spatialCurl_congr (H.potential_prefix_germ J hw),
    H.direct_prefix_eqOn (J + 1) hw]
  simpa only [Pi.zero_apply, add_zero] using
    TailGaugePotential.finalPotential_sameCurl ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B hw.1.1

/-- The exterior part of the physical realization required for each finite
cycle follows solely from the primitive stage identities. -/
theorem prefix_exterior (J : ℕ) {w : SpaceTime} (ht : w ∈ preterminal)
    (hq : physicalQ ActualPrimary.h w < ChartScales.Q Nr) (hout : w ∉ ActualPolarCoverage.active) :
    MixedDiagonalResidual.uncutVelocity A D J w =
        FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B w ∧
      DiagonalJetBounds.uncutPrefix P (J + 1) w =
        FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B w := by
  have hw := mem_exteriorDomain.mpr ⟨ht, hq, hout⟩
  exact ⟨H.velocity_prefix_eqOn J hw, H.pressure_prefix_eqOn J hw⟩

theorem prefix_germs (J : ℕ) {w : SpaceTime} (hw : w ∈ exteriorDomain Nr) :
    MixedDiagonalResidual.uncutVelocity A D J =ᶠ[𝓝 w]
        FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B ∧
      DiagonalJetBounds.uncutPrefix P (J + 1) =ᶠ[𝓝 w]
        FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B :=
  ⟨eqOn_exterior_germ (H.velocity_prefix_eqOn J) hw,
    eqOn_exterior_germ (H.pressure_prefix_eqOn J) hw⟩

end ExteriorStages

end NavierStokes.ActualExteriorPrefix
