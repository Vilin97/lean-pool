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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.BivariateContinuity
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.IteratedOverlapEquiv
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.QuotientTate

/-!
# Lane A reverse round trip: construction of `τ_preBiv`

This file constructs the presheaf-level bivariate iso `τ_preBiv` consumed by
`laurentOverlapBridge_exists_compatible_via_primary` (LaurentOverlap.lean line
3289). The target signature is

```
τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
    TateAlgebra₂ (presheafValue D₀) ⧸ bivariateOverlapIdeal (D₀.canonicalMap f)
```

## Mathematical route (T-OV-1-DENSITY)

The construction composes three equivalences, with the only residual a
**presheaf-level Wedhorn 2.13 transport** for the overlap shape:

1. `example638Bivariate_equiv (presheafValue D₀) P_B (D₀.canonicalMap f) …`
   (LaurentOverlap.lean:1472) gives the **B-side bivariate iso**
   ```
   TateAlgebra₂ B ⧸ bivariateOverlapIdeal (D₀.canonicalMap f) ≃+*
     presheafValue (overlapDatum B P_B (D₀.canonicalMap f))
   ```
   where `B := presheafValue D₀`, `P_B := presheafValue_pairOfDefinition_concrete P D₀`.

2. **Wedhorn 2.13 for the overlap (residual)**: a presheaf-level identification
   ```
   presheafValue (laurentOverlapDatum D₀ f) ≃+*
     presheafValue (overlapDatum (presheafValue D₀) P_B (D₀.canonicalMap f))
   ```
   This is the residual input. Mathematically: both presheaf values are
   completions of the same underlying ring (`Loc_A(D₀.s · f) = Loc_B(canonicalMap f)`
   via `iteratedOverlap_forwardLocHom`); the residual states that the two
   topologies (A-side overlap-from-laurentMinus-of-laurentPlus, B-side overlap
   on `presheafValue D₀` at `D₀.canonicalMap f`) yield ring-isomorphic
   completions.

3. The composition `τ_preBiv := (residual_overlap_bridge).trans
   (example638Bivariate_equiv … |>.symm)` matches the required signature.

## Status

* **Construction produced** (this file): `laneA_τ_preBiv` builds `τ_preBiv` from
  the residual overlap bridge via the composition above.
* **Residual**: `laurentOverlap_to_BSideOverlap_equiv`, the presheaf-level
  Wedhorn 2.13 transport for the overlap shape. This is the single named
  hypothesis the caller must supply (or that will be discharged in a
  follow-up T-OV-1-DENSITY ticket via `UniformSpace.Completion.extensionHom`
  + polynomial density `tateAlgebra_polynomials_dense_canonical`).

The forward and backward (Step A) maps and the `B`-side Tate-ring structure
(via `IsTateRing.quotient`) are landed: only the presheaf-level transport for
the *overlap* (vs the minus-only `presheafValue_iteratedMinus_equiv` already
in `LaurentRefinement.lean`) remains.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Example 6.39, Lemma 2.13.
* `Adic spaces/QuotientTate.lean` — T-QTATE-1 + T-QTATE-2 sources.
* `Adic spaces/LaurentOverlap.lean` — `example638Bivariate_equiv`,
  `bivariateOverlap_equiv_B₁₂gen`, `iteratedOverlap_forwardLocHom` /
  `iteratedOverlap_backwardLocHom` and round-trip lemma.
-/

@[expose] public section

universe u

namespace ValuationSpectrum

open UniformSpace TateAlgebra LaurentCover

/-! ### Construction of `τ_preBiv`

`laneA_τ_preBiv` constructs the bivariate-quotient bridge UNCONDITIONALLY
(no parametric witnesses). Both residuals are discharged internally:

* `hcont_forward_overlap` — discharged via
  `example638Bivariate_forwardHom_continuous_canonical` (T-NEW-2,
  `BivariateContinuity.lean`).
* `overlapBridge_eq` — discharged via
  `presheafValue_iteratedOverlap_equiv` (T-NEW-1,
  `IteratedOverlapEquiv.lean`). The overlap-shape Wedhorn 2.13 iterated
  rational identification for `T = {1, b, b²}`.

The composition is:
```
presheafValue (laurentOverlapDatum D₀ f)
  --[presheafValue_iteratedOverlap_equiv]→ presheafValue (iteratedOverlapDatum_B …)
  --[example638Bivariate_equiv.symm]→ TateAlgebra₂ B ⧸ bivariateOverlapIdeal …
```

Both factors are now landed sorry-free. -/

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- **Lane A `τ_preBiv` construction**: given a presheaf-level overlap bridge
between the A-side iterated overlap and the B-side overlap-shaped datum (the
single named residual for T-OV-1-DENSITY), this produces the bivariate
factorization input `τ_preBiv` required by
`laurentOverlapBridge_exists_compatible_via_primary`.

The composition is:
```
presheafValue (laurentOverlapDatum D₀ f)
  --[overlapBridge_eq]→ presheafValue (overlapDatum B P_B (D₀.canonicalMap f))
  --[example638Bivariate_equiv.symm]→ TateAlgebra₂ B ⧸ bivariateOverlapIdeal …
```

where `B := presheafValue D₀`, `P_B := presheafValue_pairOfDefinition_concrete P D₀`.

The `example638Bivariate_equiv` factor's continuity hypothesis is now
discharged unconditionally by
`example638Bivariate_forwardHom_continuous_canonical` (BivariateContinuity.lean),
the bivariate analog of `tateEvalPresheafHom_continuous_canonical`. -/
noncomputable def laneA_τ_preBiv
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
      IsNoetherianRing ↥(TateAlgebra.pairSubring₂
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition)) :
    presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
  -- Discharge the bivariate-side continuity unconditionally (T-NEW-2).
  have hcont_forward_overlap :
      @Continuous _ _
        (TateAlgebra.quotientBivariateOverlapIdealTopology (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (overlapDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Bivariate_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)) :=
    example638Bivariate_forwardHom_continuous_canonical (presheafValue D₀)
      P_B (D₀.canonicalMap f)
  -- Discharge the Wedhorn 2.13 overlap-shape transport unconditionally (T-NEW-1).
  -- `iteratedOverlapDatum_B P D₀ f hLocLift_B` IS definitionally
  -- `overlapDatum (presheafValue D₀) P_B (D₀.canonicalMap f)`.
  have overlapBridge_eq :
      presheafValue (laurentOverlapDatum D₀ f) ≃+*
        presheafValue (overlapDatum (presheafValue D₀) P_B (D₀.canonicalMap f)) :=
    presheafValue_iteratedOverlap_equiv P D₀ f hLocLift_B
  -- B-side Step A: `TateAlgebra₂ B ⧸ … ≃+* presheafValue (overlapDatum …)`
  -- via `example638Bivariate_equiv` at `B := presheafValue D₀`, `b := D₀.canonicalMap f`.
  have biv_equiv :
      ↥(TateAlgebra₂ (presheafValue D₀)) ⧸
          TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f) ≃+*
        presheafValue (overlapDatum (presheafValue D₀) P_B (D₀.canonicalMap f)) :=
    example638Bivariate_equiv (presheafValue D₀) P_B (D₀.canonicalMap f)
      hA_complete_B hnoeth_B hcont_forward_overlap
  -- Compose: presheafValue(laurentOverlap) → presheafValue(overlapDatum B P_B …) →
  -- TateAlgebra₂ B ⧸ bivariateOverlapIdeal.
  exact overlapBridge_eq.trans biv_equiv.symm

/-! ### Compatibility check: `laneA_τ_preBiv` feeds
`laurentOverlapBridge_exists_compatible_via_primary`

The next theorem demonstrates that `laneA_τ_preBiv` produces a `τ_preBiv` of the
**exact type** required by `laurentOverlapBridge_exists_compatible_via_primary`
in `LaurentOverlap.lean:3289`. The theorem is a wrapper that pipes the
construction through to obtain the compatible-bridge existence — assuming the
caller still supplies the two intertwining identities `h_plus_compat` and
`h_minus_compat`, which are predicates depending on `τ_preBiv` and hence
unavoidable inputs at this point in the pipeline.

The wrapper's signature shows that `laneA_τ_preBiv` plugs directly into
`laurentOverlapBridge_exists_compatible_via_primary`'s `τ_preBiv` argument.
-/

/-- **Compatibility wrapper**: `laneA_τ_preBiv` feeds the
Lane A finish theorem `laurentOverlapBridge_exists_compatible_via_primary`
(LaurentOverlap.lean:3289) directly. The wrapper:

* binds `τ_preBiv := laneA_τ_preBiv … overlapBridge_eq`,
* forwards the compatibility hypotheses `h_plus_compat`, `h_minus_compat`
  (these depend on the chosen `τ_preBiv` and cannot be discharged without
  the residual overlap bridge plus a forward-naturality check),
* produces the bivariate-factored compatible bridge.

This concretely demonstrates that the construction's type unifies with the
expected signature. -/
theorem laneA_τ_preBiv_compatible_bridge_exists
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
      IsNoetherianRing ↥(TateAlgebra.pairSubring₂
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    -- Univariate `hnoeth_B` for `laurentOverlapBridge_exists_compatible_via_primary`:
    (hnoethUni_B : letI : IsTateRing (presheafValue D₀) :=
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
    -- The two intertwining identities (caller still supplies, depending on
    -- the chosen `τ_preBiv` = `laneA_τ_preBiv …`):
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (laneA_τ_preBiv P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
              hnoeth_B
            (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoethUni_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (laneA_τ_preBiv P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
              hnoeth_B
            (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoethUni_B hcont_eval_B uminus)) :
    ∃ τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
            LaurentCover.B₁₂_gen (D₀.canonicalMap f),
      LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
        hA₀Noeth_B hA_complete_B hnoethUni_B hcont_forward_B hcont_eval_B τ₁₂ :=
  laurentOverlapBridge_exists_compatible_via_primary P D₀ f hNoeth_B hLocLift_B
    hA₀Noeth_B hA_complete_B hnoethUni_B hcont_forward_B hcont_eval_B
    (laneA_τ_preBiv P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
      hnoeth_B)
    h_plus_compat h_minus_compat

end ValuationSpectrum
