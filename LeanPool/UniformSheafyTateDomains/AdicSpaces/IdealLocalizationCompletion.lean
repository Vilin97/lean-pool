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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.IdealLocalization
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafTateStructure
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletionLocalization
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicCompletionFaithfullyFlat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Ideal Closedness Transfer via the Completion Ring of Definition
(T-IDEAL-2 / Route B support lemmas)

Noncontroversial support lemmas for the Route B approach to
`coeRingHom_preserves_proper`: instead of requiring the (false-in-general)
`IsAdicComplete (locIdeal) (locSubring)`, we work at the completion side
using `presheafValue_ringOfDef D₀`, which **is** adic-complete
(`Cor832.presheafValue_isAdicComplete`).

## Main support lemmas

* `Ideal.isClosed_in_ringOfDef_subspace_of_isAdicComplete` — every ideal
  of `presheafValue_ringOfDef D₀` is closed in its subspace topology
  (from `presheafValue D₀`), given `[IsNoetherianRing (presheafValue_ringOfDef D₀)]`.
  Direct consequence of `Ideal.isClosed_of_isAdicComplete` at the
  completion level.
* `Ideal.isClosed_in_presheafValue_of_isClosed_in_ringOfDef` — a subset of
  `presheafValue D₀` contained in `presheafValue_ringOfDef D₀` and closed
  in the subspace lifts to closed in `presheafValue D₀` (open-subring bridge).
* `IsClosed.preimage_coeRingHom` — preimages of closed sets in
  `presheafValue D₀` are closed in `Localization.Away D₀.s` under
  `locTopology` (continuity of `D₀.coeRingHom`).

## Residual — explicit math gap, NOT bypassed by Route B

The step **"`(locSubringToRingOfDef)⁻¹(Ideal.map locSubringToRingOfDef q_D) = q_D`
in `locSubring`"** requires **faithful flatness** of `locSubringToRingOfDef`,
equivalent (under Noetherianness) to `locIdeal ≤ Jacobson ⊥` in `locSubring`
(S-IDEAL-JAC). The completion route gives closedness at the
`presheafValue_ringOfDef` level, but pulling closedness back to `locSubring`
needs this contraction identity.

No false `IsAdicComplete (locIdeal) (locSubring)` hypothesis appears here;
the residual is an ideal-theoretic statement about the Noetherian ring
`locSubring`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Thm 8.28(b), Cor 8.32.
* `Cor832.presheafValue_isAdicComplete:896`.
* `PresheafTateStructure.presheafValue_isAdic:804`,
  `presheafValue_ringOfDef_isOpen:84`.
* Mathlib `Ideal.isClosed_of_isAdicComplete` (`IdealClosedness.lean:128`),
  `IsClosed.of_isClosed_subspace_of_isOpen_subring` (`IdealClosedness.lean:227`).
-/

@[expose] public section

open Topology Filter

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **Closedness of ideals in `presheafValue_ringOfDef D₀` (subspace topology).**

Given `[IsNoetherianRing (presheafValue_ringOfDef D₀)]` and
`[IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]`, every ideal of
`presheafValue_ringOfDef D₀` is closed in the subspace topology
inherited from `presheafValue D₀`.

The Noetherian hypothesis on `presheafValue_ringOfDef D₀` is a classical
Zariski/Cohen result (I-adic completion of a Noetherian ring is
Noetherian). Not yet in Mathlib; adopted as a typeclass assumption here. -/
theorem Ideal.isClosed_in_ringOfDef_subspace_of_isAdicComplete
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [IsNoetherianRing (presheafValue_ringOfDef D₀)]
    [IsAdicComplete (presheafValue_idealOfDef D₀)
      (presheafValue_ringOfDef D₀)]
    (J : Ideal (presheafValue_ringOfDef D₀)) :
    IsClosed (J : Set (presheafValue_ringOfDef D₀)) := by
  haveI : IsTopologicalRing (presheafValue_ringOfDef D₀) :=
    Subring.instIsTopologicalRing _
  exact Ideal.isClosed_of_isAdicComplete (presheafValue_idealOfDef D₀)
    (presheafValue_isAdic D₀) J

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **Open-subring bridge from `ringOfDef` to `presheafValue`.**

A subset of `presheafValue D₀` contained in `presheafValue_ringOfDef D₀`
that is closed in the subspace topology of `ringOfDef` lifts to a closed
subset of `presheafValue D₀`. Uses `presheafValue_ringOfDef_isOpen`
(`PresheafTateStructure.lean:84`) +
`IsClosed.of_isClosed_subspace_of_isOpen_subring` (`IdealClosedness.lean`). -/
theorem Ideal.isClosed_in_presheafValue_of_isClosed_in_ringOfDef
    (D₀ : RationalLocData A)
    {C : Set (presheafValue D₀)}
    (hC_sub : C ⊆ (presheafValue_ringOfDef D₀ :
      Set (presheafValue D₀)))
    (hC_closed_sub : IsClosed
      ((presheafValue_ringOfDef D₀).subtype ⁻¹' C :
        Set (presheafValue_ringOfDef D₀))) :
    IsClosed C :=
  IsClosed.of_isClosed_subspace_of_isOpen_subring
    (presheafValue_ringOfDef_isOpen D₀) hC_sub hC_closed_sub

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **End-to-end: ideals of `presheafValue_ringOfDef D₀` are closed in
`presheafValue D₀`.** Composition of the two preceding lemmas. -/
theorem Ideal.isClosed_in_presheafValue_of_ringOfDef_ideal
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [IsNoetherianRing (presheafValue_ringOfDef D₀)]
    [IsAdicComplete (presheafValue_idealOfDef D₀)
      (presheafValue_ringOfDef D₀)]
    (J : Ideal (presheafValue_ringOfDef D₀)) :
    IsClosed (((presheafValue_ringOfDef D₀).subtype ''
        (J : Set (presheafValue_ringOfDef D₀))) :
      Set (presheafValue D₀)) := by
  have hJ_closed := Ideal.isClosed_in_ringOfDef_subspace_of_isAdicComplete D₀ J
  have heq : (presheafValue_ringOfDef D₀).subtype ⁻¹'
      ((presheafValue_ringOfDef D₀).subtype ''
        (J : Set (presheafValue_ringOfDef D₀))) =
      (J : Set (presheafValue_ringOfDef D₀)) := by
    ext ⟨x, hx⟩
    simp only [Set.mem_preimage, Set.mem_image, Subring.coe_subtype, SetLike.mem_coe]
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ (Subtype.ext hyx : y = ⟨x, hx⟩) ▸ hy,
      fun h ↦ ⟨⟨x, hx⟩, h, rfl⟩⟩
  refine Ideal.isClosed_in_presheafValue_of_isClosed_in_ringOfDef D₀ ?_ ?_
  · rintro _ ⟨x, _, rfl⟩; exact x.property
  · rwa [heq]

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Preimage descent**: a closed subset of `presheafValue D₀` pulls back to
a closed subset of `Localization.Away D₀.s` under the continuous
`D₀.coeRingHom`. -/
theorem IsClosed.preimage_coeRingHom
    (D₀ : RationalLocData A)
    {C : Set (presheafValue D₀)}
    (hC : IsClosed C) :
    @IsClosed _ D₀.topology
      ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ⁻¹' C) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  haveI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  haveI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  exact hC.preimage UniformSpace.Completion.continuous_coeRingHom

/-! ### T-COMP-FF scaffold: identify `presheafValue_ringOfDef D` with
`AdicCompletion (locIdeal) (locSubring)`

**Goal.** Identify `presheafValue_ringOfDef D` as the standard adic
completion of `locSubring D.P D.T D.s` at `locIdeal D.P D.T D.s`. The chain
of ring isomorphisms:

```
  AdicCompletion(locIdeal, locSubring)
      ≃+*     [via AdicCompletionBridge + locSubring_topology_eq_adic]
  UniformSpace.Completion(locSubring)
      ≃+*     [via CompletionLocalization.completionLocSubringEquiv]
  D.completedLocSubring
      =       [as Subrings of presheafValue D, via set equality]
  presheafValue_ringOfDef D
```

This identification unlocks Mathlib's adic-completion theorems
(`AdicCompletion.flat_of_isNoetherian`, and the Stacks 00MA faithful-flat
theorem when it lands) for the concrete Tate setting. -/

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **Subring equality** (upgrade of the set equality from `Cor832.lean`):
`D.completedLocSubring = presheafValue_ringOfDef D` as Subrings of
`presheafValue D`. Both are topological closures of the same dense image
of `locSubring` in the completion. -/
theorem completedLocSubring_eq_ringOfDef_subring (D : RationalLocData A) :
    D.completedLocSubring = presheafValue_ringOfDef D := by
  refine SetLike.ext' ?_
  unfold RationalLocData.completedLocSubring presheafValue_ringOfDef
  have h_sub_eq : (Subring.map D.coeRingHom (locSubring D.P D.T D.s) :
      Set (presheafValue D)) =
    ((D.coeRingHom.comp (locSubring D.P D.T D.s).subtype).range :
      Set (presheafValue D)) := by
    ext y
    simp only [Subring.coe_map, RingHom.coe_range, Set.mem_image, Set.mem_range]
    exact ⟨fun ⟨x, hx, h⟩ ↦ ⟨⟨x, hx⟩, h⟩, fun ⟨⟨x, hx⟩, h⟩ ↦ ⟨x, hx, h⟩⟩
  exact Set.Subset.antisymm (closure_mono h_sub_eq.le) (closure_mono h_sub_eq.ge)

omit [HasLocLiftPowerBounded A] in
/-- **Ring iso `D.completedLocSubring ≃+* presheafValue_ringOfDef D`** via
the Subring equality (identity carrier, inherited ring structure). -/
noncomputable def completedLocSubring_ringEquiv_ringOfDef (D : RationalLocData A) :
    D.completedLocSubring ≃+* presheafValue_ringOfDef D where
  toFun x := ⟨x.val, by
    rw [← completedLocSubring_eq_ringOfDef_subring]; exact x.property⟩
  invFun y := ⟨y.val, by
    rw [completedLocSubring_eq_ringOfDef_subring]; exact y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **Main T-COMP-FF identification theorem**: `presheafValue_ringOfDef D`
is ring-isomorphic to the standard adic completion `AdicCompletion (locIdeal
D.P D.T D.s) (locSubring D.P D.T D.s)`.

Obtained by composing the three existing bridges:
* `CompletionLocalization.locSubringCompletionEquivAdicCompletion`
* `CompletionLocalization.completionLocSubringEquiv`
* `completedLocSubring_ringEquiv_ringOfDef` (above).

This identification is the key algebraic content of Wedhorn Prop 8.15 at
the ring-of-definition level, and the bridge that lets Mathlib's adic
completion machinery apply directly to `presheafValue_ringOfDef D`. -/
noncomputable def presheafValue_ringOfDef_ringEquiv_adicCompletion
    (D : RationalLocData A) :
    presheafValue_ringOfDef D ≃+*
      AdicCompletion (locIdeal D.P D.T D.s) (locSubring D.P D.T D.s) :=
  (completedLocSubring_ringEquiv_ringOfDef D).symm.trans
    ((CompletionLocalization.completionLocSubringEquiv D).symm.trans
      (CompletionLocalization.locSubringCompletionEquivAdicCompletion D))

/-! ### T-COMP-FF: faithful-flatness of `locSubringToRingOfDef D`

**Residual (Stacks 00MA)**: the standard Noetherian adic-completion
faithful-flatness theorem — for Noetherian `R` with `I ⊆ Ideal.jacobson ⊥`,
`Module.FaithfullyFlat R (AdicCompletion I R)`. **Not in Mathlib yet.**

With this residual + the identification
`presheafValue_ringOfDef_ringEquiv_adicCompletion`, faithful flatness of
the structural ring-hom `locSubringToRingOfDef D` follows by transporting
across the ring iso. The chain:

```
  locSubring --AdicCompletion.of--> AdicCompletion(locIdeal, locSubring)
      |                                    ≃+* (iso.symm)
      |                                    v
      +--locSubringToRingOfDef-->    presheafValue_ringOfDef D
```

If the triangle commutes (which it does by construction of the bridges),
then FF of `AdicCompletion.of` (Stacks 00MA) transports to FF of
`locSubringToRingOfDef`. -/

/-- **T-COMP-FF: Stacks 00MA named residual**. The Noetherian
adic-completion faithful-flatness theorem — **not yet in Mathlib** — is
the single remaining gap for discharging `RingHom.FaithfullyFlat
(locSubringToRingOfDef D)`.

Statement (precise form needed):

```
theorem AdicCompletion.faithfullyFlat_of_le_jacobson
    {R : Type*} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) :
    Module.FaithfullyFlat R (AdicCompletion I R)
```

**Reference**: Stacks 00MA. The hypothesis `I ⊆ Jacobson ⊥` is the
Zariski-ring condition that makes the adic completion conservative.

Current status: Mathlib has `AdicCompletion.flat_of_isNoetherian`
(adic-complete Noetherian ring gives flatness, no Jacobson required), but
**does not** have the faithful-flat upgrade. Wiring this up — once the
Mathlib theorem lands — is a straightforward composition via
`presheafValue_ringOfDef_ringEquiv_adicCompletion` and
`RingHom.FaithfullyFlat.of_bijective` / `stableUnderComposition`. -/
def AdicCompletion_faithfullyFlat_of_le_jacobson_residual : Prop :=
  ∀ {R : Type*} [CommRing R] [IsNoetherianRing R] {I : Ideal R},
    I ≤ Ideal.jacobson ⊥ → Module.FaithfullyFlat R (AdicCompletion I R)

/-! ### Commutativity of the bridge triangle

The key algebraic identity needed to transport faithful-flatness from
the `AdicCompletion` side to `presheafValue_ringOfDef D`: the ring-hom
diagram commutes.

```
  locSubring --AdicCompletion.of--> AdicCompletion(locIdeal, locSubring)
      |                                    ≃+* (iso.symm)
      |                                    v
      +--locSubringToRingOfDef-->    presheafValue_ringOfDef D
```

Both paths land in `presheafValue_ringOfDef D` and — by construction of
the bridge chain through `UniformSpace.Completion.coeRingHom` — coincide
on the underlying `presheafValue D` element `D.coeRingHom r.val`. -/

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **Triangle commutativity** (routine transport): `locSubringToRingOfDef D`
equals `(presheafValue_ringOfDef_ringEquiv_adicCompletion D).symm` post-composed
with `AdicCompletion.of _ _`, on any `r : locSubring D.P D.T D.s`.

This is a `.val`-level equality in `presheafValue D`: both sides evaluate
to `D.coeRingHom r.val` (with `r.val ∈ Localization.Away D.s`). The
proof chains through `extensionHom_coe` (for `completionLocSubringEquiv`),
`AbstractCompletion.compare_coe` (for `locSubringCompletionEquivAdicCompletion`),
and `Subtype.ext` for the Subring projection. -/
theorem locSubringToRingOfDef_val_eq_symm_comp_of (D : RationalLocData A)
    (r : locSubring D.P D.T D.s) :
    ((locSubringToRingOfDef D r) : presheafValue D) =
      ((presheafValue_ringOfDef_ringEquiv_adicCompletion D).symm
        (AdicCompletion.of (locIdeal D.P D.T D.s) (locSubring D.P D.T D.s) r) :
          presheafValue D) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  haveI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  haveI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (locSubring D.P D.T D.s) :=
    CompletionLocalization.locSubringUniformSpace D
  have hadic : IsAdic (locIdeal D.P D.T D.s) :=
    locSubring_topology_eq_adic D.P D.T D.s D.hopen
  have h1 : (CompletionLocalization.locSubringCompletionEquivAdicCompletion D).symm
      (AdicCompletion.of (locIdeal D.P D.T D.s) (locSubring D.P D.T D.s) r) =
      (r : UniformSpace.Completion (locSubring D.P D.T D.s)) := by
    rw [RingEquiv.symm_apply_eq]
    exact (AdicCompletionBridge.adicCompletionRingEquiv_coe
      (locIdeal D.P D.T D.s) hadic r).symm
  have h2 : (CompletionLocalization.completionLocSubringEquiv D)
      (r : UniformSpace.Completion (locSubring D.P D.T D.s)) =
      D.locSubringToCompleted r := by
    have hcont : Continuous D.locSubringToCompleted :=
      Continuous.subtype_mk
        (CompletionLocalization.locSubringToPresheafValue_continuous D) _
    haveI : IsClosed (D.completedLocSubring : Set (presheafValue D)) :=
      Subring.isClosed_topologicalClosure _
    haveI : CompleteSpace D.completedLocSubring :=
      (Subring.isClosed_topologicalClosure _).completeSpace_coe
    haveI : IsTopologicalRing D.completedLocSubring := Subring.instIsTopologicalRing _
    haveI : IsUniformAddGroup D.completedLocSubring :=
      IsUniformAddGroup.comap D.completedLocSubring.subtype.toAddMonoidHom
    have hui : IsUniformInducing D.locSubringToCompleted := by
      refine isUniformEmbedding_subtype_val.isUniformInducing.of_comp_iff.mp ?_
      change IsUniformInducing (Subtype.val ∘ ⇑D.locSubringToCompleted)
      exact CompletionLocalization.locSubringToPresheafValue_isUniformInducing D
    have hdense : DenseRange D.locSubringToCompleted := by
      intro ⟨x, hx⟩
      rw [mem_closure_iff_nhds]
      intro U hU
      rw [nhds_induced, Filter.mem_comap] at hU
      obtain ⟨V, hV, hVU⟩ := hU
      obtain ⟨y, hyV, z, hz, rfl⟩ := mem_closure_iff_nhds.mp hx V hV
      exact ⟨⟨D.coeRingHom z, D.coeRingHom_mem_completedLocSubring hz⟩,
        hVU hyV, ⟨⟨z, hz⟩, rfl⟩⟩
    change AdicCompletionBridge.completionRingEquiv _ hcont hui hdense (↑r) = _
    exact AdicCompletionBridge.completionRingEquiv_coe _ hcont hui hdense r
  change ((locSubringToRingOfDef D r) : presheafValue D) = _
  unfold presheafValue_ringOfDef_ringEquiv_adicCompletion
  rw [RingEquiv.symm_trans_apply, RingEquiv.symm_trans_apply,
      RingEquiv.symm_symm, RingEquiv.symm_symm, h1, h2]
  rfl

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **Final T-COMP-FF interface (conditional)**: given the specialized
Stacks 00MA result `Module.FaithfullyFlat locSubring (AdicCompletion
locIdeal locSubring)` as an explicit hypothesis, the target
`RingHom.FaithfullyFlat (locSubringToRingOfDef D)` follows via ring-iso
transport.

**Hypothesis:** `h_stacks00MA_instance` — the specialization of
`AdicCompletion_faithfullyFlat_of_le_jacobson_residual` to the concrete
`locSubring / locIdeal` setup. A universe-polymorphic callsite can
specialize the generic Mathlib residual; a monomorphic callsite can
provide this directly.

**Proof structure:** converts the `Module.FaithfullyFlat` hypothesis to
`RingHom.FaithfullyFlat` of `algebraMap` via `faithfullyFlat_algebraMap_iff`;
obtains `RingHom.FaithfullyFlat` of the ring-iso inverse via
`RingHom.FaithfullyFlat.of_bijective`; composes via `stableUnderComposition`;
identifies the composite with `locSubringToRingOfDef D` via the triangle
commutativity residual `locSubringToRingOfDef_val_eq_symm_comp_of`. -/
theorem locSubringToRingOfDef_faithfullyFlat_of_residual
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)]
    (h_stacks00MA_instance : Module.FaithfullyFlat (locSubring D.P D.T D.s)
      (AdicCompletion (locIdeal D.P D.T D.s) (locSubring D.P D.T D.s))) :
    RingHom.FaithfullyFlat (locSubringToRingOfDef D) := by
  have h_adic_of_ff : RingHom.FaithfullyFlat
      (algebraMap (locSubring D.P D.T D.s)
        (AdicCompletion (locIdeal D.P D.T D.s) (locSubring D.P D.T D.s))) :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr h_stacks00MA_instance
  have h_iso_ff : RingHom.FaithfullyFlat
      ((presheafValue_ringOfDef_ringEquiv_adicCompletion D).symm.toRingHom) :=
    RingHom.FaithfullyFlat.of_bijective
      (presheafValue_ringOfDef_ringEquiv_adicCompletion D).symm.bijective
  have h_eq : locSubringToRingOfDef D =
      ((presheafValue_ringOfDef_ringEquiv_adicCompletion D).symm.toRingHom).comp
        (algebraMap (locSubring D.P D.T D.s)
          (AdicCompletion (locIdeal D.P D.T D.s) (locSubring D.P D.T D.s))) :=
    RingHom.ext fun r ↦ Subtype.ext (locSubringToRingOfDef_val_eq_symm_comp_of D r)
  rw [h_eq]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ h_adic_of_ff h_iso_ff

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **T-COMP-FF via Jacobson hypothesis** (cleaner entry-point composition).

Given the cleanest local algebraic hypothesis `locIdeal ≤ Jacobson ⊥` in
`locSubring` (equivalent to the classical Zariski-ring condition), produces
`RingHom.FaithfullyFlat (locSubringToRingOfDef D)`. Composes the generic
Stacks 00MA (`AdicCompletion.faithfullyFlat_of_le_jacobson_bot` from
`AdicCompletionFaithfullyFlat.lean`) with the T-COMP-FF residual chain
(`locSubringToRingOfDef_faithfullyFlat_of_residual` above).

This is the **cleaner conditional** replacing the raw
`Module.FaithfullyFlat locSubring (AdicCompletion …)` instance by the
purely algebraic Jacobson hypothesis on `locSubring`. Downstream
consumers (`Cor832.coeRingHom_preserves_proper_of_*`) can use either
form; this form is preferable when the Jacobson condition is the
natural algebraic content.

**The Jacobson hypothesis is NOT asserted unconditionally** — it is an
external input supplied by the caller. The project has two conditional
paths to this hypothesis (`locIdeal_le_jacobson_bot_of_isAdicComplete`,
`locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat`), but an
unconditional proof for uncompleted Tate localization rings remains
open (see `AdicCompletionFaithfullyFlat.lean` boundary documentation). -/
theorem locSubringToRingOfDef_faithfullyFlat_of_locIdeal_le_jacobson
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)]
    (h_jac : locIdeal D.P D.T D.s ≤
      Ideal.jacobson (⊥ : Ideal (locSubring D.P D.T D.s))) :
    RingHom.FaithfullyFlat (locSubringToRingOfDef D) :=
  locSubringToRingOfDef_faithfullyFlat_of_residual P D
    (AdicCompletion.faithfullyFlat_of_le_jacobson_bot _ h_jac)

end ValuationSpectrum
