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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinement

/-!
# Lifting algebraic Laurent separation to the presheafValue level (R2)

The companion to `laurentCover_gluing_presheaf_viaRow3`
(`LaurentRefinement.lean:3527`) for the **separation** direction of the
Laurent row.

## What this gives

`LaurentCoverExact.lean:380` proves the algebraic Laurent diagonal
`ε : A → B₁_gen f × B₂_gen f` is injective whenever
`⨅ n, span {f}^n = ⊥` in `A` (Krull intersection at `f`). This file
applies that result at `A := presheafValue D₀, f := D₀.canonicalMap f`,
threading the same `(τ_plus, τ_minus, htau_plus, htau_minus)` bridge
data the gluing companion uses, to derive presheafValue-level Laurent
separation:

  Two `presheafValue D₀` sections agreeing on both `presheafValue
  (laurentPlusDatum D₀ f)` and `presheafValue (laurentMinusDatum D₀ f)`
  via restriction must be equal.

The single new caller residual versus the gluing companion is the
**Krull intersection hypothesis** `hInf` at the presheafValue base —
discharged downstream from completion / topological-nilpotence inputs.

## Why this is the R2 direction

Wedhorn's Lemma 8.33 row `0 → A →ε B₁ × B₂ →δ B₁₂ → 0` decomposes into:
- δ-surjectivity + ker-δ ⊆ im-ε → **gluing** (Lane A's existing
  `laurentCover_gluing_presheaf_via*` chain via `row3_exact`).
- ε-injectivity → **separation** (this file).

Both halves use the same `(τ_plus, τ_minus)` bridges, so the cost of
this file is just the Krull-intersection hypothesis. No new
faithful-flatness / Cor 8.32 / Jacobson content; ε-injectivity is the
purely algebraic Krull route.

## References

* `Adic spaces/LaurentCoverExact.lean:380` —
  `LaurentCover.epsilonHom_gen_injective_of_iInf_pow_eq_bot`
  (the algebraic separation core consumed here).
* `Adic spaces/LaurentRefinement.lean:3527` —
  `laurentCover_gluing_presheaf_viaRow3`
  (gluing companion, mirror structure).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **R2 / presheafValue Laurent separation companion** to
`laurentCover_gluing_presheaf_viaRow3`.

Given the same `(τ_plus, τ_minus, htau_plus, htau_minus)` bridge data
plus a Krull-intersection hypothesis `hInf` on `D₀.canonicalMap f` in
`presheafValue D₀`, two `presheafValue D₀` sections that agree after
restriction to both Laurent halves must be equal.

The proof composes:

1. `htau_plus` / `htau_minus` — translate the restriction equalities
   into equalities of the first / second components of
   `LaurentCover.epsilonHom_gen (D₀.canonicalMap f)` at `a, b`.
2. `LaurentCover.epsilonHom_gen_injective_of_iInf_pow_eq_bot` — the
   algebraic ε-injectivity, applied at `A := presheafValue D₀`,
   `f := D₀.canonicalMap f`.

No new sorries, no faithful-flatness, no Cor 8.32. The Krull
hypothesis `hInf` is the single explicit residual; it is the analytic
content already isolated as the "R2" content in
`LaurentCoverExact.lean:1890-1908`. -/
theorem laurentCover_separation_presheaf_viaRow3
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (τ_plus : presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f))
    (τ_minus : presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f))
    (htau_plus : ∀ x : presheafValue D₀,
      τ_plus (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1)
    (htau_minus : ∀ x : presheafValue D₀,
      τ_minus (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2)
    (hInf : (⨅ n : ℕ,
        Ideal.span ({D₀.canonicalMap f} : Set (presheafValue D₀)) ^ n) = ⊥)
    {a b : presheafValue D₀}
    (h_plus : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus a =
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus b)
    (h_minus : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus a =
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus b) :
    a = b := by
  apply LaurentCover.epsilonHom_gen_injective_of_iInf_pow_eq_bot
    (A := presheafValue D₀) (D₀.canonicalMap f) hInf
  apply Prod.ext
  · rw [← htau_plus a, ← htau_plus b, h_plus]
  · rw [← htau_minus a, ← htau_minus b, h_minus]

/-- **Caller-friendly companion** to `laurentCover_separation_presheaf_viaRow3`
that constructs the `(τ_plus, τ_minus, htau_plus, htau_minus)` bridge
arguments from the existing `laurentPlusBridge` / `laurentMinusBridge`
infrastructure (`LaurentRefinement.lean:2480, :2548, :2734`).

Mirrors the structure of
`laurentCover_gluing_presheaf_via_compatible_bridge`
(`LaurentRefinement.lean:3911`) on the gluing side, exposing only the
standard Tate bundle plus the explicit Krull-intersection hypothesis
`hInf` to the caller.

The `hInf` hypothesis is **not discharged** in this wrapper — it
remains the single explicit residual at the manager-target shape. -/
theorem laurentCover_separation_presheaf_via_compatible_bridge
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
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hInf : (⨅ n : ℕ,
        Ideal.span ({D₀.canonicalMap f} : Set (presheafValue D₀)) ^ n) = ⊥)
    {a b : presheafValue D₀}
    (h_plus : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus a =
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus b)
    (h_minus : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus a =
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus b) :
    a = b :=
  laurentCover_separation_presheaf_viaRow3 D₀ f hplus hminus
    (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
        hnoeth_B hcont_forward_B)
    (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B)
    (laurentPlusBridge_restrictionMap P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
        hA_complete_B hnoeth_B hcont_forward_B hplus)
    (laurentMinusBridge_restrictionMap P D₀ f hnoeth_B hcont_eval_B hminus)
    hInf h_plus h_minus

end ValuationSpectrum
