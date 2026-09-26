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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicCompletionTransfer
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf

/-!
# Presheaf Value via Adic Completion of the Subring

For a rational localization datum `D`, the ring of definition `locSubring`
with ideal of definition `locIdeal` carries the `locIdeal`-adic topology.
By the bridge (`AdicCompletionBridge`), the completion of `locSubring`
is isomorphic to `AdicCompletion locIdeal locSubring`, and by the transfer
(`AdicCompletionTransfer`), this completion is flat over `locSubring`.

The full presheaf value `presheafValue D = Completion(Localization.Away D.s)`
is obtained from `Completion(locSubring)` by inverting the Tate unit.

## Main definitions

* `locSubringTopology` : The `locIdeal`-adic topology on `locSubring`.
* `locSubringIsAdic` : `IsAdic locIdeal` (by definition).
* `locSubring_completion_flat` : The completion of `locSubring` is flat.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

section LocSubringCompletion

variable (D : RationalLocData A)

/-- The `locIdeal`-adic topology on `locSubring`. -/
@[reducible]
noncomputable def locSubringTopology :
    TopologicalSpace (locSubring D.P D.T D.s) :=
  (locIdeal D.P D.T D.s).adicTopology

/-- The `locIdeal`-adic topology is a ring topology. -/
@[reducible]
noncomputable def locSubringIsTopologicalRing :
    @IsTopologicalRing (locSubring D.P D.T D.s) (locSubringTopology D) _ := by
  infer_instance

/-- `IsAdic locIdeal` on `locSubring` with the adic topology. By definition. -/
theorem locSubringIsAdic :
    @IsAdic (locSubring D.P D.T D.s) _ (locSubringTopology D) (locIdeal D.P D.T D.s) :=
  rfl

/-- The completion of `locSubring` (with `locIdeal`-adic topology) is flat
over `locSubring`, when `locSubring` is noetherian. -/
theorem locSubring_completion_flat [IsNoetherianRing (locSubring D.P D.T D.s)] :
    let J := locIdeal D.P D.T D.s
    letI : TopologicalSpace (locSubring D.P D.T D.s) := J.adicTopology
    letI : IsTopologicalRing (locSubring D.P D.T D.s) := inferInstance
    letI : UniformSpace (locSubring D.P D.T D.s) :=
      IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup (locSubring D.P D.T D.s) :=
      isUniformAddGroup_of_addCommGroup
    Module.Flat (locSubring D.P D.T D.s)
      (UniformSpace.Completion (locSubring D.P D.T D.s)) := by
  letI : TopologicalSpace (locSubring D.P D.T D.s) := (locIdeal D.P D.T D.s).adicTopology
  letI : IsTopologicalRing (locSubring D.P D.T D.s) := inferInstance
  letI : UniformSpace (locSubring D.P D.T D.s) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (locSubring D.P D.T D.s) := isUniformAddGroup_of_addCommGroup
  exact AdicCompletionBridge.completion_flat (locIdeal D.P D.T D.s) rfl

/-! ### Flatness of presheafValue over A (Wedhorn Proposition 8.30)

For the localization topology: `presheafValue D = Completion(Localization.Away s)`.

**Proof route (via TopologyComparison):**
1. `A⟨X⟩` is flat over `A` (restricted power series of noetherian ring)
2. `1-sX` is universally regular in `A⟨X⟩` → `A⟨X⟩/(1-sX)` flat over `A`
   (`flat_quotient_oneSubfX_general` in `TateAlgebra.lean`, sorry-free)
3. `presheafValue D ≃+* A⟨X⟩/(1-sX)` (TopologyComparison, sorry-free)
4. Transfer flatness via the A-compatible ring isomorphism

The flatness theorems live downstream in `StructureSheaf.lean`, guarded by the
TopologyComparison hypotheses:

* `presheafValue_flat_of_tateQuotient`   — via the T-topology equivalence
  (5 hypotheses including the T-topology completeness/closedness).
* `presheafValue_flat_of_canonical`      — via the canonical-topology
  equivalence `presheafValueCanonicalQuotientEquiv` (5 hypotheses where the
  T-topology residuals are traded for `hA_complete`, `hnoeth`, `hT_pb`, and
  `hcont_eval`; the first three hold automatically for strongly noetherian Tate
  affinoid rings with a chosen pair of definition).

Both statements feed into Wedhorn's Cor 8.32 faithful-flatness argument via the
Laurent-refinement route in `LaurentRefinement.lean`.
-/

end LocSubringCompletion

end ValuationSpectrum
