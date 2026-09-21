/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentOverlap

/-!
# Lane-C caller-ready overlap consumer (T-OVERLAP-COMPAT end-to-end closure)

Top-level `_via_primary` caller-ready theorems for Lane C, composing
Primary's exported Lane-A finish theorem
`laurentOverlapBridge_exists_compatible_via_primary`
(`LaurentOverlap.lean:3764`, commit `7b6dccd`) with the four
`_via_compatible_bridge` consumers in `LaurentRefinement.lean`. Each
takes Primary's Lane-A raw inputs (`τ_preBiv` + two intertwining
identities) directly and returns the downstream conclusion without
caller-visible unpacking of `(τ₁₂, hcompat_bridge)`.

## Caller tower (end-to-end view, post-Lane-A)

* `V_cover_gluing_via_primary`: consumes `τ_preBiv`, two intertwinings, and
  V-cover data; returns the V-cover gluing existential.
* `laurentCover_gluing_presheaf_via_primary`: consumes the same overlap data
  and Laurent-pair data; returns Laurent-pair gluing.
* `laurentBridge_delta_eq_zero_via_primary`: consumes the overlap data and
  half-sections; returns algebraic `deltaMap_gen = 0`.
* `laurentAndVCover_gluing_unified_via_primary`: combines the Laurent-pair
  and V-cover conclusions into one single-witness smoke test.

Each `_via_primary` theorem is a two-step composition:

1. `laurentOverlapBridge_exists_compatible_via_primary` obtains
   `(τ₁₂, hcompat_bridge)` from the caller's τ_preBiv + intertwinings.
2. The corresponding `_via_compatible_bridge` wrapper consumes the bridge
   and returns the downstream conclusion.

The unified smoke test wraps `V_cover_gluing_via_primary`'s underlying
single-witness behaviour in an explicit Laurent-pair-AND-V-cover
existential, so callers needing both half-section recoveries and V-piece
restrictions from the same `x` get one call instead of three.

## Lane-C residual: none

The caller supplies `τ_preBiv` + intertwinings, which are Primary's
Step-A / S-OV-GLUE content. From the Lane-C geometry side, there are no
further sorries or missing bridges.

## Build status

`LaurentOverlap.lean` now builds and this consumer layer compiles on top of
it. The theorems in this file are pure structural composition over the
already-landed overlap primitives; remaining acyclicity work is downstream
geometric/final assembly, not this compatibility layer.

## References

* `Adic spaces/LaurentOverlap.lean:3764` —
  `laurentOverlapBridge_exists_compatible_via_primary` (Lane-A finish).
* `Adic spaces/LaurentRefinement.lean` — `_via_compatible_bridge`
  primitives:
  `laurentBridge_delta_eq_zero_via_compatible_bridge` (line 3743),
  `laurentCover_gluing_presheaf_via_compatible_bridge` (line 3841),
  `V_cover_gluing_from_laurentPair_via_compatible_bridge` (line 3952),
  `laurentAndVCover_gluing_unified_via_compatible_bridge` (line 4069).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- V-cover gluing from `τ_preBiv` + two intertwinings + V-cover data —
the **single call point** for Lane C inductive steps. Composes
`laurentOverlapBridge_exists_compatible_via_primary` (extracts the
compatible overlap bridge) with
`V_cover_gluing_from_laurentPair_via_compatible_bridge` (turns the bridge
into V-cover gluing). -/
theorem V_cover_gluing_via_primary
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus))
    (V_covers : Finset (RationalLocData A))
    (hV_subset_base : ∀ D ∈ V_covers,
      rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (hrefine : ∀ D : { D // D ∈ V_covers },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s))
    (u_plus : presheafValue (laurentPlusDatum D₀ f))
    (u_minus : presheafValue (laurentMinusDatum D₀ f))
    (fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1)
    (hfV_plus : ∀ (D : { D // D ∈ V_covers })
      (hD_plus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D.1 hD_plus u_plus = fV D)
    (hfV_minus : ∀ (D : { D // D ∈ V_covers })
      (hD_minus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentMinusDatum D₀ f) D.1 hD_minus u_minus = fV D)
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p u_plus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m u_minus) :
    ∃ x : presheafValue D₀,
      ∀ D : { D // D ∈ V_covers },
        restrictionMap D₀ D.1 (hV_subset_base D.1 D.2) x = fV D := by
  obtain ⟨τ₁₂, hcompat_bridge⟩ :=
    laurentOverlapBridge_exists_compatible_via_primary P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
      hcont_forward_B hcont_eval_B τ_preBiv h_plus_compat h_minus_compat
  exact V_cover_gluing_from_laurentPair_via_compatible_bridge P D₀ f
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
    hcont_forward_B hcont_eval_B τ₁₂ hcompat_bridge
    V_covers hV_subset_base hrefine
    u_plus u_minus fV hfV_plus hfV_minus hcompat

/-- Laurent-pair gluing from `τ_preBiv` + two intertwinings + Laurent-pair
data. Caller variant of `laurentCover_gluing_presheaf_via_compatible_bridge`
that obtains `(τ₁₂, hcompat_bridge)` internally via Primary's Lane-A finish. -/
theorem laurentCover_gluing_presheaf_via_primary
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p uplus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m uminus) :
    ∃ x : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = uplus ∧
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = uminus := by
  obtain ⟨τ₁₂, hcompat_bridge⟩ :=
    laurentOverlapBridge_exists_compatible_via_primary P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
      hcont_forward_B hcont_eval_B τ_preBiv h_plus_compat h_minus_compat
  exact laurentCover_gluing_presheaf_via_compatible_bridge P D₀ f
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
    hcont_forward_B hcont_eval_B τ₁₂ hcompat_bridge
    hplus hminus uplus uminus hcompat

/-- Algebraic `deltaMap_gen = 0` from `τ_preBiv` + two intertwinings +
compatible half-sections. Caller variant of
`laurentBridge_delta_eq_zero_via_compatible_bridge` that obtains
`(τ₁₂, hcompat_bridge)` internally via Primary's Lane-A finish. Useful
when only the algebraic vanishing is needed (e.g. inside a larger
gluing proof with its own reconstruction strategy). -/
theorem laurentBridge_delta_eq_zero_via_primary
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus))
    (uplus : presheafValue (laurentPlusDatum D₀ f))
    (uminus : presheafValue (laurentMinusDatum D₀ f))
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p uplus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m uminus) :
    LaurentCover.deltaMap_gen (D₀.canonicalMap f)
      (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
          hnoeth_B hcont_forward_B uplus,
        laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus) = 0 := by
  obtain ⟨τ₁₂, hcompat_bridge⟩ :=
    laurentOverlapBridge_exists_compatible_via_primary P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
      hcont_forward_B hcont_eval_B τ_preBiv h_plus_compat h_minus_compat
  exact laurentBridge_delta_eq_zero_via_compatible_bridge P D₀ f
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
    hcont_forward_B hcont_eval_B τ₁₂ hcompat_bridge
    uplus uminus hcompat

/-- **Unified smoke test**: combined Laurent-pair-AND-V-cover existential
from `τ_preBiv` + two intertwinings + Laurent-pair + V-cover data, with
single shared witness `x`. Caller variant of
`laurentAndVCover_gluing_unified_via_compatible_bridge` that obtains
`(τ₁₂, hcompat_bridge)` internally via Primary's Lane-A finish.

Verifies the post-Lane-A tower closes coherently: every `_via_primary`
conclusion is recoverable from the same `x`, not three different ones.
The intended consumer is anyone needing both half-section recoveries
and V-piece restrictions in a single call. -/
theorem laurentAndVCover_gluing_unified_via_primary
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus))
    (V_covers : Finset (RationalLocData A))
    (hV_subset_base : ∀ D ∈ V_covers,
      rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (hrefine : ∀ D : { D // D ∈ V_covers },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s))
    (u_plus : presheafValue (laurentPlusDatum D₀ f))
    (u_minus : presheafValue (laurentMinusDatum D₀ f))
    (fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1)
    (hfV_plus : ∀ (D : { D // D ∈ V_covers })
      (hD_plus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D.1 hD_plus u_plus = fV D)
    (hfV_minus : ∀ (D : { D // D ∈ V_covers })
      (hD_minus : rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentMinusDatum D₀ f) D.1 hD_minus u_minus = fV D)
    (hcompat : ∀ (D₃ : RationalLocData A)
      (h₃p : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)
      (h₃m : rationalOpen D₃.T D₃.s ⊆
        rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s),
      restrictionMap (laurentPlusDatum D₀ f) D₃ h₃p u_plus =
        restrictionMap (laurentMinusDatum D₀ f) D₃ h₃m u_minus) :
    ∃ x : presheafValue D₀,
      restrictionMap D₀ (laurentPlusDatum D₀ f)
          (laurentPlus_subset D₀ f) x = u_plus ∧
      restrictionMap D₀ (laurentMinusDatum D₀ f)
          (laurentMinus_subset D₀ f) x = u_minus ∧
      ∀ D : { D // D ∈ V_covers },
        restrictionMap D₀ D.1 (hV_subset_base D.1 D.2) x = fV D := by
  obtain ⟨τ₁₂, hcompat_bridge⟩ :=
    laurentOverlapBridge_exists_compatible_via_primary P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
      hcont_forward_B hcont_eval_B τ_preBiv h_plus_compat h_minus_compat
  exact laurentAndVCover_gluing_unified_via_compatible_bridge P D₀ f
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
    hcont_forward_B hcont_eval_B τ₁₂ hcompat_bridge
    V_covers hV_subset_base hrefine
    u_plus u_minus fV hfV_plus hfV_minus hcompat

end ValuationSpectrum
