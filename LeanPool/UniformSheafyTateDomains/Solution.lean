/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.Palomar.Defs
import LeanPool.UniformSheafyTateDomains.Palomar.Bridge
import LeanPool.UniformSheafyTateDomains.Palomar.Bridge.Jet
import LeanPool.UniformSheafyTateDomains.Palomar.Bridge.TateExt
import LeanPool.UniformSheafyTateDomains.AdicSpaces

/-!
# Palomar solution: [FJP] Theorem 1.1

Proves each statement of `Challenge.lean` by forwarding the library's theorem across
the bridges of `Palomar/Bridge.lean` (the Challenge's notions are the library's) and
`Palomar/Bridge/Jet.lean` (the Challenge's `𝓐` is the library's, `jetAEquiv`).

This module does not import `Challenge.lean` — Comparator forbids that, since the
Challenge's theorems carry `sorry` — but `Palomar/Defs.lean`, the verbatim copy of its
definitions, so that every constant appearing in a statement is the same constant in both
environments. The statements below are spelled with fully qualified names; they elaborate to
exactly the Challenge's types.
-/


noncomputable section

open FiniteJetOver ValuationSpectrum TopologicalRing PalomarBridge PalomarBridge.Jet
  PalomarBridge.TateExt
open scoped NormedField Valued

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### The instances the library's transports expect on the Challenge's `𝓐` -/

/-- `𝓐` is complete: a closed subring of the complete ring `K⟨W, W⁻¹, Q⟩`. -/
instance : CompleteSpace (Palomar.JetA K) :=
  (show IsClosed (Palomar.jetSubring K : Set (Palomar.TateAlgebra K (ℤ × ℕ))) from
    Subring.isClosed_topologicalClosure _).completeSpace_coe

instance : @CompleteSpace (Palomar.JetA K)
    (IsTopologicalAddGroup.rightUniformSpace (Palomar.JetA K)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-! ### The statements -/

/-- **[FJP] Theorem 1.1 (integral domain)**. -/
theorem Palomar.fjp_1_1_isDomain : IsDomain (Palomar.JetA K) :=
  haveI := finiteJet_isDomain K
  (jetAEquiv K).injective.isDomain (jetAEquiv K)

/-- **[FJP] Theorem 1.1 (nonnoetherian)**. -/
theorem Palomar.fjp_1_1_not_isNoetherianRing : ¬ IsNoetherianRing (Palomar.JetA K) := fun h =>
  haveI := h
  finiteJet_not_noetherian K (isNoetherianRing_of_ringEquiv _ (jetAEquiv K))

variable [IsDiscreteValuationRing 𝒪[K]]

/-- **[FJP] Theorem 1.1 (sheafy)**. -/
theorem Palomar.fjp_1_1_isSheafy :
    Palomar.ValuationSpectrum.IsSheafyComplete (Palomar.JetA K) :=
  isSheafyComplete_iff.mpr
    ((isSheafyComplete_congr (jetAEquiv K).symm (continuous_jetAEquiv_symm K)
      (continuous_jetAEquiv K)).mp (finiteJet_isSheafyComplete_of_dvr K))

/-- **[FJP] Theorem 1.1 (uniform)**. -/
theorem Palomar.fjp_1_1_isUniform : Palomar.IsUniform (Palomar.JetA K) :=
  isUniform_iff.mpr (FiniteJet.isUniform_of_ringEquiv (jetAEquiv K).symm
    (continuous_jetAEquiv_symm K) (continuous_jetAEquiv K) (finiteJet_isUniform_of_dvr K))

/-- **[FJP] Theorem 1.1 (`𝓐° = 𝓐₀`)**. -/
theorem Palomar.fjp_1_1_powerBounded_eq_unitBall :
    Palomar.powerBoundedSubring (Palomar.JetA K) =
      (Palomar.unitBall (Palomar.JetA K) : Set (Palomar.JetA K)) := by
  ext x
  have h := finiteJet_powerBounded_eq_unitBall_of_dvr K
  have hx : TopologicalRing.IsPowerBounded x ↔ TopologicalRing.IsPowerBounded (jetAEquiv K x) :=
    ⟨fun hx => FiniteJet.isPowerBounded_map_of_ringEquiv (jetAEquiv K) (continuous_jetAEquiv K)
      (continuous_jetAEquiv_symm K) hx,
     fun hx => by
      simpa using FiniteJet.isPowerBounded_map_of_ringEquiv (jetAEquiv K).symm
        (continuous_jetAEquiv_symm K) (continuous_jetAEquiv K) hx⟩
  change TopologicalRing.IsPowerBounded x ↔ ‖x‖ ≤ 1
  rw [hx, ← norm_jetAEquiv K x]
  exact Set.ext_iff.mp h (jetAEquiv K x)

/-- **[FJP] Theorem 1.1 (not stably uniform)**. -/
theorem Palomar.fjp_1_1_not_isStablyUniform :
    ¬ Palomar.ValuationSpectrum.IsStablyUniform (Palomar.JetA K) := by
  intro h
  letI : PlusSubring (Palomar.JetA K) := ⟨⊥⟩
  let ϖ : Uniformizer K := Uniformizer.ofDVR K
  have hchart := chartDatum_isRational K ϖ
  -- pull the non-uniform chart datum back to the Challenge's `𝓐`
  let D' : RationalLocData (Palomar.JetA K) :=
    (chartDatum K ϖ).mapRationalRingEquiv (jetAEquiv K).symm (continuous_jetAEquiv_symm K)
      (continuous_jetAEquiv K) hchart
  have hD' : D'.IsRational :=
    mapRationalRingEquiv_isRational _ _ _ _ hchart
  -- `rldOf` copies `T` verbatim and the two `IsRational` predicates are the same
  -- proposition, so the library-side rationality discharges the Challenge-side one.
  have hu : TopologicalRing.IsUniform (presheafValue D') := ⟨h.1 (rldOf D') hD'⟩
  have hu2 := FiniteJet.isUniform_of_ringEquiv
    (presheafValueRingEquivOfRingEquiv (jetAEquiv K) (continuous_jetAEquiv K)
      (continuous_jetAEquiv_symm K) D' hD')
    (presheafValueRingEquivOfRingEquiv_continuous _ _ _ _ _)
    (presheafValueRingEquivOfRingEquiv_symm_continuous _ _ _ _ _) hu
  rw [RationalLocData.mapRationalRingEquiv_map_symm] at hu2
  exact not_isUniform_chart K ϖ hu2

/-! ### Strong sheafiness -/

/-- The Challenge's `𝓐⟨X₁, …, Xₙ⟩` is a Tate ring (the constants of `𝓐` of norm `< 1` are
scaling pseudouniformizers). -/
instance (n : ℕ) : Palomar.IsTateRing (Palomar.JetAExt K n) := by
  obtain ⟨c, hc⟩ := NontriviallyNormedField.non_trivial (α := K)
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  have hC : ‖Palomar.C K c⁻¹‖ = ‖c⁻¹‖ := by simpa using Palomar.norm_C_mul K c⁻¹ 1
  refine isTateRing_tateAlgebra (Palomar.C K c⁻¹)
    ⟨⟨Palomar.C K c⁻¹, Palomar.C K c, ?_, ?_⟩, rfl⟩ ?_ ?_ fun x => by rw [Palomar.norm_C_mul, hC]
  · rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  · rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
  · rw [hC, norm_inv]; exact inv_lt_one_of_one_lt₀ hc
  · rw [hC, norm_inv]; exact inv_pos.mpr (zero_lt_one.trans hc)

instance (n : ℕ) : @CompleteSpace (Palomar.JetAExt K n)
    (IsTopologicalAddGroup.rightUniformSpace (Palomar.JetAExt K n)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- **[FJP] Theorem 1.1 (strongly sheafy)**. -/
theorem Palomar.fjp_1_1_stronglySheafy (n : ℕ) :
    Palomar.ValuationSpectrum.IsSheafyComplete (Palomar.JetAExt K n) :=
  isSheafyComplete_iff.mpr
    ((isSheafyComplete_congr (gaussEquiv (jetAEquiv K) (norm_jetAEquiv K) n).symm
      (continuous_gaussEquiv_symm _ _ n) (continuous_gaussEquiv _ _ n)).mp
      (ext_isSheafyComplete K n (Uniformizer.ofDVR K) (isNoetherianRing_unitBall K)))


/-! ### Non-vacuity of the sheafiness statements

`IsSheafyComplete` quantifies over rings of integral elements conditionally, so without a
witness both sheafiness statements would be satisfied by a ring admitting no valid `A⁺`.
The maximal plus ring `A°` is one, in any Huber ring — open because it contains a ring of
definition (Wedhorn 6.4(4)), integrally closed by Wedhorn 5.30(4). Both `𝓐` and its Tate
algebras are Tate, hence Huber, so the same lemma serves both. -/

/-- **[FJP] Theorem 1.1 (`𝓐` admits a ring of integral elements)**. -/
theorem Palomar.fjp_1_1_exists_ringOfIntegralElements :
    ∃ B : Subring (Palomar.JetA K), Palomar.ValuationSpectrum.IsRingOfIntegralElements B :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (Palomar.JetA K),
    (PalomarBridge.isRingOfIntegralElements_iff _).mpr
      ValuationSpectrum.isRingOfIntegralElements_powerBoundedSubring⟩

/-- **[FJP] Theorem 1.1 (the Tate algebras admit rings of integral elements)**. -/
theorem Palomar.fjp_1_1_tateExt_exists_ringOfIntegralElements (n : ℕ) :
    ∃ B : Subring (Palomar.JetAExt K n),
      Palomar.ValuationSpectrum.IsRingOfIntegralElements B :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (Palomar.JetAExt K n),
    (PalomarBridge.isRingOfIntegralElements_iff _).mpr
      ValuationSpectrum.isRingOfIntegralElements_powerBoundedSubring⟩

end
