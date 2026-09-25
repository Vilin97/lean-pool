/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.ExtendedCornerPackage
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.Functoriality

/-!
# The extended finite-jet corner package over a general base

This is the base-independent version of `FiniteJet.extPinch`.  The four
corners are finite Gauss extensions of the `FiniteJetOver` rings.  An
explicit uniformizer is needed only for the noetherian package used by the
graph--Koszul argument.
-/

@[expose] public section

@[expose] public section

noncomputable section

open Filter Topology

namespace FiniteJetOver

open FiniteJet.RestrictedLaurent FiniteJet.GraphKoszul
open ValuationSpectrum StrictLoc

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

noncomputable instance (n : ℕ) : DecidableEq (PA K n) := Classical.decEq _
noncomputable instance (n : ℕ) : DecidableEq (PB K n) := Classical.decEq _
noncomputable instance (n : ℕ) : DecidableEq (PC K n) := Classical.decEq _
noncomputable instance (n : ℕ) : DecidableEq (PD K n) := Classical.decEq _

instance (n : ℕ) : IsTateRing (PA K n) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact FiniteJet.isTateRing_of_scale (polyToP (MvPolynomial.C (constA K c)))
    (isUnit_tP _ (IsUnit.map (constA K) hcu))
    (by rw [norm_tP _ (norm_constA_mul K c), norm_constA]; exact hc1)
    (by rw [norm_tP _ (norm_constA_mul K c), norm_constA]; exact hc0)
    (fun x => by
      rw [norm_tP _ (norm_constA_mul K c)]
      exact norm_tP_mul _ (norm_constA_mul K c) x)

instance (n : ℕ) : IsTateRing (PB K n) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact FiniteJet.isTateRing_of_scale (polyToP (MvPolynomial.C (constB K c)))
    (isUnit_tP _ (isUnit_constB K hcu))
    (by rw [norm_tP _ (norm_constB_mul K c), norm_constB]; exact hc1)
    (by rw [norm_tP _ (norm_constB_mul K c), norm_constB]; exact hc0)
    (fun x => by
      rw [norm_tP _ (norm_constB_mul K c)]
      exact norm_tP_mul _ (norm_constB_mul K c) x)

instance (n : ℕ) : IsTateRing (PC K n) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  have hscale : ∀ x : JetC K,
      ‖constC K c * x‖ = ‖constC K c‖ * ‖x‖ := fun x => by
    rw [norm_constC_mul, norm_constC]
  exact FiniteJet.isTateRing_of_scale (polyToP (MvPolynomial.C (constC K c)))
    (isUnit_tP _ (IsUnit.map (constC K) hcu))
    (by rw [norm_tP _ hscale, norm_constC]; exact hc1)
    (by rw [norm_tP _ hscale, norm_constC]; exact hc0)
    (fun x => by
      rw [norm_tP _ hscale]
      exact norm_tP_mul _ hscale x)

instance (n : ℕ) : IsTateRing (PD K n) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window K
  exact FiniteJet.isTateRing_of_scale (polyToP (MvPolynomial.C (constD K c)))
    (isUnit_tP _ (isUnit_constD K hcu))
    (by rw [norm_tP _ (norm_constD_mul K c), norm_constD]; exact hc1)
    (by rw [norm_tP _ (norm_constD_mul K c), norm_constD]; exact hc0)
    (fun x => by
      rw [norm_tP _ (norm_constD_mul K c)]
      exact norm_tP_mul _ (norm_constD_mul K c) x)

noncomputable instance (n : ℕ) : PlusSubring (PA K n) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (PA K n)⟩
noncomputable instance (n : ℕ) : PlusSubring (PB K n) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (PB K n)⟩
noncomputable instance (n : ℕ) : PlusSubring (PC K n) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (PC K n)⟩
noncomputable instance (n : ℕ) : PlusSubring (PD K n) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (PD K n)⟩

instance (n : ℕ) : IsRingOfIntegralElements ((PA K n)⁺ : Subring (PA K n)) :=
  FiniteJet.isRingOfIntegralElements_powerBounded
instance (n : ℕ) : IsRingOfIntegralElements ((PB K n)⁺ : Subring (PB K n)) :=
  FiniteJet.isRingOfIntegralElements_powerBounded
instance (n : ℕ) : IsRingOfIntegralElements ((PC K n)⁺ : Subring (PC K n)) :=
  FiniteJet.isRingOfIntegralElements_powerBounded
instance (n : ℕ) : IsRingOfIntegralElements ((PD K n)⁺ : Subring (PD K n)) :=
  FiniteJet.isRingOfIntegralElements_powerBounded

instance (n : ℕ) : @CompleteSpace (PA K n)
    (IsTopologicalAddGroup.rightUniformSpace (PA K n)) := by
  have : IsUniformAddGroup (PA K n) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

instance (n : ℕ) : @CompleteSpace (PB K n)
    (IsTopologicalAddGroup.rightUniformSpace (PB K n)) := by
  have : IsUniformAddGroup (PB K n) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

instance (n : ℕ) : @CompleteSpace (PC K n)
    (IsTopologicalAddGroup.rightUniformSpace (PC K n)) := by
  have : IsUniformAddGroup (PC K n) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

instance (n : ℕ) : @CompleteSpace (PD K n)
    (IsTopologicalAddGroup.rightUniformSpace (PD K n)) := by
  have : IsUniformAddGroup (PD K n) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

instance (n : ℕ) : HasLocLiftPowerBounded (PA K n) := hasLocLiftPowerBounded_faithful
instance (n : ℕ) : HasLocLiftPowerBounded (PB K n) := hasLocLiftPowerBounded_faithful
instance (n : ℕ) : HasLocLiftPowerBounded (PC K n) := hasLocLiftPowerBounded_faithful
instance (n : ℕ) : HasLocLiftPowerBounded (PD K n) := hasLocLiftPowerBounded_faithful

/-- The finite-Tate-extension square as an abstract pinch. -/
noncomputable def extPinch (n : ℕ) (ϖ : Uniformizer K) :
    FiniteJet.Pinch (PA K n) (PB K n) (PC K n) (PD K n) where
  φB := extJB K n
  φC := extIotaC K n
  ψB := extRhoB K n
  ψC := extRhoC K n
  norm_φB_le := fun p => norm_mapRestricted_le _ _ _ p
  norm_φC := fun p => FiniteJet.norm_mapRestricted_eq
    (JetA K) (iotaC K) (norm_iotaC K) p
  norm_ψB := fun p => FiniteJet.norm_mapRestricted_eq
    (JetB K) (rhoB K) (norm_rhoB K) p
  norm_ψC_le := fun p => norm_mapRestricted_le _ _ _ p
  square := ext_square_commutes K n
  row := ext_milnorRow_exact K n
  max_norm := ext_max_norm_eq K n
  secD := fun d => (extRhoC_strict_surjective K n d).choose
  ψC_secD := fun d => (extRhoC_strict_surjective K n d).choose_spec.1
  norm_secD := fun d => (extRhoC_strict_surjective K n d).choose_spec.2
  tB := polyToP (MvPolynomial.C (piB ϖ))
  tB_isUnit := isUnit_tP _ (isUnit_piB ϖ)
  norm_tB_lt_one := by
    rw [norm_tP _ (norm_piB_mul ϖ), norm_piB]
    exact ϖ.norm_val_lt_one
  norm_tB_pos := by
    rw [norm_tP _ (norm_piB_mul ϖ), norm_piB]
    exact ϖ.norm_val_pos
  norm_tB_mul := fun x => by
    rw [norm_tP _ (norm_piB_mul ϖ)]
    exact norm_tP_mul _ (norm_piB_mul ϖ) x
  tC := polyToP (MvPolynomial.C (piC ϖ))
  tC_isUnit := isUnit_tP _ (isUnit_piC ϖ)
  norm_tC_lt_one := by
    rw [norm_tP _ (norm_piC_mul ϖ), norm_piC]
    exact ϖ.norm_val_lt_one
  norm_tC_pos := by
    rw [norm_tP _ (norm_piC_mul ϖ), norm_piC]
    exact ϖ.norm_val_pos
  norm_tC_mul := fun x => by
    rw [norm_tP _ (norm_piC_mul ϖ)]
    exact norm_tP_mul _ (norm_piC_mul ϖ) x
  tD := polyToP (MvPolynomial.C (piD ϖ))
  tD_isUnit := isUnit_tP _ (isUnit_piD ϖ)
  norm_tD_lt_one := by
    rw [norm_tP _ (norm_piD_mul ϖ), norm_piD]
    exact ϖ.norm_val_lt_one
  norm_tD_pos := by
    rw [norm_tP _ (norm_piD_mul ϖ), norm_piD]
    exact ϖ.norm_val_pos
  norm_tD_mul := fun x => by
    rw [norm_tP _ (norm_piD_mul ϖ)]
    exact norm_tP_mul _ (norm_piD_mul ϖ) x

/-- The noetherian package for every rational localization of the extended square. -/
theorem extNoethPack (n : ℕ) (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (m : ℕ) :
    FiniteJet.NoethPack (PB K n) (PC K n) (PD K n) m := by
  obtain ⟨eB, heB⟩ := FiniteJet.exists_flattenPP (JetB K) n m
  obtain ⟨eC, heC⟩ := FiniteJet.exists_flattenPP (JetC K) n m
  obtain ⟨eD, heD⟩ := FiniteJet.exists_flattenPP (JetD K) n m
  have hb := StrictLoc.isNoetherianRing_PB K (n + m) ϖ hK₀
  have hc := StrictLoc.isNoetherianRing_PC K (n + m) ϖ hK₀
  have hd := StrictLoc.isNoetherianRing_PD K (n + m) ϖ hK₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isNoetherianRing_of_surjective (PB K (n + m)) _
      eB.symm.toRingHom eB.symm.surjective
  · exact isNoetherianRing_of_surjective (PC K (n + m)) _
      eC.symm.toRingHom eC.symm.surjective
  · exact isNoetherianRing_of_surjective (PD K (n + m)) _
      eD.symm.toRingHom eD.symm.surjective
  · exact FiniteJet.isNoetherianRing_unitBall_of_isometry eB.symm
      (fun g => by
        conv_rhs => rw [← eB.apply_symm_apply g]
        rw [heB]) (StrictLoc.isNoetherianRing_unitBall_PB K (n + m) ϖ hK₀)
  · exact FiniteJet.isNoetherianRing_unitBall_of_isometry eC.symm
      (fun g => by
        conv_rhs => rw [← eC.apply_symm_apply g]
        rw [heC]) (StrictLoc.isNoetherianRing_unitBall_PC K (n + m) ϖ hK₀)
  · exact FiniteJet.isNoetherianRing_unitBall_of_isometry eD.symm
      (fun g => by
        conv_rhs => rw [← eD.apply_symm_apply g]
        rw [heD]) (StrictLoc.isNoetherianRing_unitBall_PD K (n + m) ϖ hK₀)
  · exact StrictLoc.isNoetherianRing_unitBall_PD K n ϖ hK₀

end FiniteJetOver
