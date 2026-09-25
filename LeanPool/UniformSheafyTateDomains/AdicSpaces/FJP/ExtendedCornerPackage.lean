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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CornerSquareBridge

/-!
# The extended corner package (T626, campaign B)

The `⟨V⟩`-extended finite-jet square as an abstract pinch: the corners are the
Gauss-normed Tate extensions `P (Jet• F) n` and the homs the coefficientwise
`ext•` maps of `FiniteJetStrictLocalization` at arity `n` — whose package facts
(`ext_milnorRow_exact` = the paper's extended integral row, `ext_max_norm_eq`,
`extRhoC_strict_surjective`, `ext_square_commutes`) are already proven there.

* `flattenPP` — the ring-level restricted Fubini `P (P E n) m ≃ P E (n+m)`,
  norm-preservingly (iterating `finSuccOne`/`congrBase`, the
  `exists_flatten'` pattern of `ExampleUnitDisc.lean` with a multivariable
  inner layer); this discharges the `NoethPack` of the extended square from
  the base facts at arity `n + m`.
* Huber/Tate instance stack on the `P`-corners (scale = the constant series of
  the Jet scale, via `isTateRing_of_scale` + `norm_tP_mul`).
* `extPinch F n : Pinch (PA F n) (PB F n) (PC F n) (PD F n)`.
* `extNoethPack F n m : NoethPack (PB F n) (PC F n) (PD F n) m`.

[Reviewer] §5.1: "adjoining variables preserves the coefficientwise split
Milnor row, while B⟨T⟩, C⟨T⟩, and D⟨T⟩ remain strongly noetherian affinoids."
-/

@[expose] public section

@[expose] public section

noncomputable section

open Filter Topology

namespace FiniteJet

open RestrictedLaurent GraphKoszul ValuationSpectrum StrictLoc

/-! ### The ring-level restricted Fubini (iterated `P`) -/

section Flatten

variable (E : Type*) [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E]

/-- **Ring-level restricted Fubini**: `m`-variable radius-one restricted series
over `P E n` are `(n+m)`-variable restricted series over `E`, norm-preservingly
(the `exists_flatten'` chain with a multivariable inner layer). -/
theorem exists_flattenPP (n m : ℕ) :
    ∃ e : (P (P E n) m ≃+* P E (n + m)), ∀ f, ‖e f‖ = ‖f‖ := by
  induction m with
  | zero =>
    exact ⟨restrictedFinZeroEquiv (P E n) (fun _ : Fin 0 => (1 : ℝ)), fun f => foo_norm_map f⟩
  | succ m ih =>
    obtain ⟨eIH, hIH⟩ := ih
    refine ⟨(UnitDiscExample.finSuccOne (P E n) m).trans
      ((UnitDiscExample.congrBase 1 eIH hIH).trans
        (UnitDiscExample.finSuccOne E (n + m)).symm), fun f => ?_⟩
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply,
      UnitDiscExample.finSuccOne_symm_norm, UnitDiscExample.congrBase_norm,
      UnitDiscExample.finSuccOne_norm]

omit [NormOneClass E] [CompleteSpace E] in
/-- Norm-isometry of `mapRestricted` along an isometric base hom. -/
theorem norm_mapRestricted_eq {E' : Type*} [NormedCommRing E'] [IsUltrametricDist E']
    {m : ℕ} (φ : E →+* E') (hφ : ∀ x, ‖φ x‖ = ‖x‖) (f : P E m) :
    ‖mapRestricted φ (fun x => le_of_eq (hφ x)) (fun _ : Fin m => (1 : ℝ)) f‖ = ‖f‖ := by
  rw [MvRestricted.norm_eq, MvRestricted.norm_eq]
  show MvPowerSeries.gaussNorm _ _ (MvPowerSeries.map φ f.1) = _
  rw [MvPowerSeries.gaussNorm, MvPowerSeries.gaussNorm]
  refine iSup_congr fun s => ?_
  rw [MvPowerSeries.coeff_map, hφ]

end Flatten

/-! ### The Huber/Tate instance stack on the `P`-corners -/

section Instances

variable (F : Type*) [Field F]

noncomputable instance (n : ℕ) : DecidableEq (PA F n) := Classical.decEq _
noncomputable instance (n : ℕ) : DecidableEq (PB F n) := Classical.decEq _
noncomputable instance (n : ℕ) : DecidableEq (PC F n) := Classical.decEq _
noncomputable instance (n : ℕ) : DecidableEq (PD F n) := Classical.decEq _

instance (n : ℕ) : IsTateRing (PA F n) :=
  isTateRing_of_scale (polyToP (MvPolynomial.C (tA F)))
    (isUnit_tP _ (isUnit_tA F))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tP_mul _ (norm_tA_mul F) x)

instance (n : ℕ) : IsTateRing (PB F n) :=
  isTateRing_of_scale (polyToP (MvPolynomial.C (tB F)))
    (isUnit_tP _ (isUnit_tB F))
    (by rw [norm_tP _ (norm_tB_mul F), norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tB_mul F), norm_tB]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tB_mul F)]; exact norm_tP_mul _ (norm_tB_mul F) x)

instance (n : ℕ) : IsTateRing (PC F n) :=
  isTateRing_of_scale (polyToP (MvPolynomial.C (tC F)))
    (isUnit_tP _ (isUnit_tC F))
    (by rw [norm_tP _ (norm_tC_mul F), norm_tC]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tC_mul F), norm_tC]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tC_mul F)]; exact norm_tP_mul _ (norm_tC_mul F) x)

instance (n : ℕ) : IsTateRing (PD F n) :=
  isTateRing_of_scale (polyToP (MvPolynomial.C (tD F)))
    (isUnit_tP _ (isUnit_tD F))
    (by rw [norm_tP _ (norm_tD_mul F), norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tD_mul F), norm_tD]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tD_mul F)]; exact norm_tP_mul _ (norm_tD_mul F) x)

noncomputable instance (n : ℕ) : PlusSubring (PA F n) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (PA F n)⟩
noncomputable instance (n : ℕ) : PlusSubring (PB F n) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (PB F n)⟩
noncomputable instance (n : ℕ) : PlusSubring (PC F n) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (PC F n)⟩
noncomputable instance (n : ℕ) : PlusSubring (PD F n) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (PD F n)⟩

instance (n : ℕ) : IsRingOfIntegralElements ((PA F n)⁺ : Subring (PA F n)) :=
  isRingOfIntegralElements_powerBounded
instance (n : ℕ) : IsRingOfIntegralElements ((PB F n)⁺ : Subring (PB F n)) :=
  isRingOfIntegralElements_powerBounded
instance (n : ℕ) : IsRingOfIntegralElements ((PC F n)⁺ : Subring (PC F n)) :=
  isRingOfIntegralElements_powerBounded
instance (n : ℕ) : IsRingOfIntegralElements ((PD F n)⁺ : Subring (PD F n)) :=
  isRingOfIntegralElements_powerBounded

instance (n : ℕ) : @CompleteSpace (PA F n)
    (IsTopologicalAddGroup.rightUniformSpace (PA F n)) := by
  have : IsUniformAddGroup (PA F n) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

instance (n : ℕ) : @CompleteSpace (PB F n)
    (IsTopologicalAddGroup.rightUniformSpace (PB F n)) := by
  have : IsUniformAddGroup (PB F n) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

instance (n : ℕ) : @CompleteSpace (PC F n)
    (IsTopologicalAddGroup.rightUniformSpace (PC F n)) := by
  have : IsUniformAddGroup (PC F n) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

instance (n : ℕ) : @CompleteSpace (PD F n)
    (IsTopologicalAddGroup.rightUniformSpace (PD F n)) := by
  have : IsUniformAddGroup (PD F n) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

instance (n : ℕ) : HasLocLiftPowerBounded (PA F n) := hasLocLiftPowerBounded_faithful
instance (n : ℕ) : HasLocLiftPowerBounded (PB F n) := hasLocLiftPowerBounded_faithful
instance (n : ℕ) : HasLocLiftPowerBounded (PC F n) := hasLocLiftPowerBounded_faithful
instance (n : ℕ) : HasLocLiftPowerBounded (PD F n) := hasLocLiftPowerBounded_faithful

end Instances

/-! ### The extended pinch and its noetherian pack -/

section Package

variable (F : Type*) [Field F] (n : ℕ)

/-- **The `⟨V⟩`-extended finite-jet square as an abstract pinch** (T626): the
corners are the Gauss-normed Tate extensions and the package facts are the
`StrictLoc` `ext•` lemmas at arity `n`. -/
noncomputable def extPinch : Pinch (PA F n) (PB F n) (PC F n) (PD F n) where
  φB := extJB F n
  φC := extIotaC F n
  ψB := extRhoB F n
  ψC := extRhoC F n
  norm_φB_le := fun p => norm_mapRestricted_le _ _ _ p
  norm_φC := fun p => norm_mapRestricted_eq (JetA F) (iotaC F) (norm_iotaC F) p
  norm_ψB := fun p => norm_mapRestricted_eq (JetB F) (rhoB F) (norm_rhoB F) p
  norm_ψC_le := fun p => norm_mapRestricted_le _ _ _ p
  square := ext_square_commutes F n
  row := ext_milnorRow_exact F n
  max_norm := ext_max_norm_eq F n
  secD := fun d => (extRhoC_strict_surjective F n d).choose
  ψC_secD := fun d => (extRhoC_strict_surjective F n d).choose_spec.1
  norm_secD := fun d => (extRhoC_strict_surjective F n d).choose_spec.2
  tB := polyToP (MvPolynomial.C (tB F))
  tB_isUnit := isUnit_tP _ (isUnit_tB F)
  norm_tB_lt_one := by
    rw [norm_tP _ (norm_tB_mul F), norm_tB]; exact norm_t_lt_one F
  norm_tB_pos := by
    rw [norm_tP _ (norm_tB_mul F), norm_tB]; exact norm_t_pos F
  norm_tB_mul := fun x => by
    rw [norm_tP _ (norm_tB_mul F)]; exact norm_tP_mul _ (norm_tB_mul F) x
  tC := polyToP (MvPolynomial.C (tC F))
  tC_isUnit := isUnit_tP _ (isUnit_tC F)
  norm_tC_lt_one := by
    rw [norm_tP _ (norm_tC_mul F), norm_tC]; exact norm_t_lt_one F
  norm_tC_pos := by
    rw [norm_tP _ (norm_tC_mul F), norm_tC]; exact norm_t_pos F
  norm_tC_mul := fun x => by
    rw [norm_tP _ (norm_tC_mul F)]; exact norm_tP_mul _ (norm_tC_mul F) x
  tD := polyToP (MvPolynomial.C (tD F))
  tD_isUnit := isUnit_tP _ (isUnit_tD F)
  norm_tD_lt_one := by
    rw [norm_tP _ (norm_tD_mul F), norm_tD]; exact norm_t_lt_one F
  norm_tD_pos := by
    rw [norm_tP _ (norm_tD_mul F), norm_tD]; exact norm_t_pos F
  norm_tD_mul := fun x => by
    rw [norm_tP _ (norm_tD_mul F)]; exact norm_tP_mul _ (norm_tD_mul F) x

/-- The noetherian pack of the extended square at every arity, through the
ring-level Fubini `flattenPP` and the base tower facts at arity `n + m`. -/
theorem extNoethPack (m : ℕ) : NoethPack (PB F n) (PC F n) (PD F n) m := by
  obtain ⟨eB, heB⟩ := exists_flattenPP (JetB F) n m
  obtain ⟨eC, heC⟩ := exists_flattenPP (JetC F) n m
  obtain ⟨eD, heD⟩ := exists_flattenPP (JetD F) n m
  have hb := isNoetherianRing_PB F (n + m)
  have hc := isNoetherianRing_PC F (n + m)
  have hd := isNoetherianRing_PD F (n + m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isNoetherianRing_of_surjective (PB F (n + m)) _
      eB.symm.toRingHom eB.symm.surjective
  · exact isNoetherianRing_of_surjective (PC F (n + m)) _
      eC.symm.toRingHom eC.symm.surjective
  · exact isNoetherianRing_of_surjective (PD F (n + m)) _
      eD.symm.toRingHom eD.symm.surjective
  · exact isNoetherianRing_unitBall_of_isometry eB.symm
      (fun g => by
        conv_rhs => rw [← eB.apply_symm_apply g]
        rw [heB]) (isNoetherianRing_unitBall_PB F (n + m))
  · exact isNoetherianRing_unitBall_of_isometry eC.symm
      (fun g => by
        conv_rhs => rw [← eC.apply_symm_apply g]
        rw [heC]) (isNoetherianRing_unitBall_PC F (n + m))
  · exact isNoetherianRing_unitBall_of_isometry eD.symm
      (fun g => by
        conv_rhs => rw [← eD.apply_symm_apply g]
        rw [heD]) (isNoetherianRing_unitBall_PD F (n + m))
  · exact isNoetherianRing_unitBall_PD F n

end Package

end FiniteJet
