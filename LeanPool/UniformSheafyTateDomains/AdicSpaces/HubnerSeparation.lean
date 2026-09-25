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
# Hübner-route separation (Hübner Lemma 3.8 / Wedhorn Thm 8.28 Part 1)

This file provides the **Hübner-route** analogue of
`laurentCover_gluing_presheaf` for the **separation** part (Part 1) of
`tateAcyclicity`. The Hübner route decouples Part 1 from Cor 8.32
(`productRestriction_injective_tate` / T-IDEAL-2 Lane B faithful flatness)
by routing through the simpler **algebraic Laurent-pair injectivity**
`LaurentCover.epsilonHom_gen_injective` plus the existing Route B bridges.

## Key results — scope split (2026-04-20)

* `laurentCover_separation_presheaf_viaRow3_domain` (H1-domain): **LANDED
  sorry-free**. Laurent-pair separation at presheafValue level **under
  `[IsDomain (presheafValue D₀)]`**. Proved via
  `epsilonHom_gen_injective` + bridges.
* `laurentCover_separation_presheaf_viaRow3_of_iInf_pow_eq_bot` (H1-core):
  **LANDED sorry-free**. This removes the domain assumption but exposes the
  exact algebraic input `⋂ n, (D₀.canonicalMap f)^n = 0`.
* H1-general (non-domain): **TARGET NOT LANDED**. Documented as a
  comment-only target (see bottom of file). The direct Hübner-route
  proof attempt encountered a fundamental Tate-topology obstruction at
  step 5 (see block at end of file). Escalation packet at
  `.mathlib-quality/chatgpt-packet-hubner-nondomain.md`.

**Domain caveat recognised**. The final `ValuationSpectrum.tateAcyclicity`
does NOT assume `[IsDomain]`, so the domain-only H1 cannot close the
final theorem directly. The non-domain H1 requires a new general
injectivity result that replaces `epsilonHom_gen_injective` (which
currently needs `[IsDomain]` because its proof goes through
`Ideal.iInf_pow_eq_bot_of_isDomain` = Krull intersection in domains).
Per reviewer instruction (2026-04-20), we DO NOT import a `sorry` for
the non-domain target; instead it remains as a documentation block
+ escalation packet until the obstruction is resolved.

## Route audit (2026-04-20 post-Cor-8.32-pivot)

Current `tateAcyclicity` Part 1 (LaurentRefinement.lean:3695) uses the
retired-as-false `ValuationSpectrum.restrictionMapHom_injective`, which
is pinned to Cor 8.32 (Wedhorn Thm 8.32) faithful flatness via
`restrictionMapHom_injective_via_iso` / Lane B. The Hübner route bypasses
this entirely at the simple-Laurent level in the **domain case**:
`epsilonHom_gen_injective` is already sorry-free, and `laurentPlusBridge` /
`laurentMinusBridge` plus intertwining lemmas lift it to `presheafValue`
level.

**Non-domain gap**. For general noetherian Tate rings, the Laurent-pair
injectivity requires a combined algebraic-topological argument:

1. First projection `ε(a).1 = 0` gives `a ∈ ⋂_n (f)^n` (coefficient
   recurrence, no domain needed).
2. Second projection `ε(a).2 = 0` gives `f^n · a → 0` in A's topology
   (from `c'' ∈ A⟨X⟩` = restricted power series).
3. By Mathlib `Ideal.mem_iInf_smul_pow_eq_bot_iff` (general Krull,
   non-domain version): `∃ r ∈ (f), (1-r) · a = 0`, i.e.,
   `a = fc · a` for some `c ∈ A`.
4. Iterate: `a = c^N · f^N · a` for all N.
5. For each basic open `I^k` (from Tate pair-of-definition ideal I):
   `f^N · a ∈ I^k` eventually (from step 2), so `a = c^N · f^N · a ∈ I^k`
   (I^k is an ideal).
6. `a ∈ ⋂_k I^k = 0` (Hausdorffness via `T2Space` + basic-open nhd basis).

This argument works in principle but requires technical infrastructure
for the Tate topology on `presheafValue D₀` — translating the
`IsRestricted` condition on `c''` into explicit `f^n · a ∈ I^k`
membership, and linking to `T2Space`-based Hausdorffness for the
`⋂ I^k = 0` conclusion.

Next session should either close this technical gap or formalize it as
a named external residual (analogous to Stacks 00MA in the Cor 8.32
route) — escalation packet in `.mathlib-quality/chatgpt-packet-hubner-nondomain.md`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Theorem 8.28(b), Lemma 8.33.
* [Hübner, *Sheafiness of Huber's valuation spectrum*][arXiv:2405.06435], Lemma 3.8.
* `Adic spaces/LaurentCoverExact.lean` — `epsilonHom_gen_injective`
  (Krull-intersection argument at algebraic level, `[IsDomain]` required).
* `Adic spaces/LaurentRefinement.lean` — `laurentCover_gluing_presheaf_viaRow3`
  (the gluing analog, template for this file).
* Mathlib `Ideal.mem_iInf_smul_pow_eq_bot_iff` — general Krull without
  `[IsDomain]`, only `[IsNoetherianRing R]` + `[Module.Finite R M]`.
-/

@[expose] public section

namespace ValuationSpectrum

open LaurentCover

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **H1-core: Laurent-pair separation from an explicit Krull-intersection input.**

This is the non-domain-ready core of the Hübner/Wedhorn simple-Laurent
separation argument. Instead of assuming `[IsDomain (presheafValue D₀)]`, it
takes exactly the algebraic input needed by the first projection of the Laurent
row:

`⋂ n, (D₀.canonicalMap f)^n = 0` in `presheafValue D₀`.

The domain theorem below is now just the specialization of this statement via
`Ideal.iInf_pow_eq_bot_of_isDomain`. -/
theorem laurentCover_separation_presheaf_viaRow3_of_iInf_pow_eq_bot
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ : RationalLocData A)
    (f : A)
    (hInf : (⨅ n : ℕ,
      Ideal.span ({D₀.canonicalMap f} : Set (presheafValue D₀)) ^ n) = ⊥)
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
    (x : presheafValue D₀)
    (hplus0 : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = 0)
    (hminus0 : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = 0) :
    x = 0 := by
  apply LaurentCover.epsilonHom_gen_injective_of_iInf_pow_eq_bot
    (D₀.canonicalMap f) hInf
  rw [map_zero]
  refine Prod.ext ?_ ?_
  · rw [← htau_plus x, hplus0, map_zero, Prod.fst_zero]
  · rw [← htau_minus x, hminus0, map_zero, Prod.snd_zero]

/-- **H1-Jacobson: Laurent-pair separation when `(D₀.canonicalMap f)` is
contained in the Jacobson radical.**

This is the main no-domain specialization currently available: Mathlib's
Krull intersection theorem gives `⋂ n, (D₀.canonicalMap f)^n = 0` from the
Jacobson containment, and the H1-core theorem above handles the Laurent
bridge transport. -/
theorem laurentCover_separation_presheaf_viaRow3_of_span_le_jacobson
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ : RationalLocData A) [IsNoetherianRing (presheafValue D₀)]
    (f : A)
    (hf_jac : Ideal.span ({D₀.canonicalMap f} : Set (presheafValue D₀)) ≤
      Ideal.jacobson (⊥ : Ideal (presheafValue D₀)))
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
    (x : presheafValue D₀)
    (hplus0 : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = 0)
    (hminus0 : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = 0) :
    x = 0 :=
  laurentCover_separation_presheaf_viaRow3_of_iInf_pow_eq_bot D₀ f
    (LaurentCover.span_singleton_iInf_pow_eq_bot_of_le_jacobson
      (D₀.canonicalMap f) hf_jac)
    hplus hminus τ_plus τ_minus htau_plus htau_minus x hplus0 hminus0

/-- **H1-domain: Hübner Lemma 8.33(a) / Laurent-pair separation at
`presheafValue` level — DOMAIN case only.**

Given ring isos `τ_plus`, `τ_minus` identifying the two Laurent pieces
with the algebraic quotient rings `B₁_gen`, `B₂_gen` (same as in
`laurentCover_gluing_presheaf_viaRow3`), plus the intertwining
conditions connecting `restrictionMap D₀ plus/minus` to
`LaurentCover.epsilonHom_gen`, if `x ∈ presheafValue D₀` restricts to
zero on both Laurent pieces then `x = 0`.

**Scope caveat: requires `[IsDomain (presheafValue D₀)]`.** This comes
from the underlying `LaurentCover.epsilonHom_gen_injective` which uses
`Ideal.iInf_pow_eq_bot_of_isDomain` (Krull intersection for domains).
The general noetherian Tate case requires the companion theorem
`laurentCover_separation_presheaf_viaRow3_noetherian` below (currently
`sorry` pending escalation).

**Proof strategy** (mirror of the gluing version):
* Unfold both `hplus0`, `hminus0` through the intertwining conditions
  to show `(epsilonHom_gen (D₀.canonicalMap f) x).1 = 0` and
  `(epsilonHom_gen (D₀.canonicalMap f) x).2 = 0`.
* Combine to show `epsilonHom_gen (D₀.canonicalMap f) x = 0`.
* Apply `epsilonHom_gen_injective` to conclude `x = 0`.

**No Cor 8.32 / Stacks 00MA / faithful flatness needed**:
`epsilonHom_gen_injective` is proved at the algebraic level via
Krull intersection and is fully sorry-free (under `[IsDomain]`). -/
theorem laurentCover_separation_presheaf_viaRow3_domain
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ : RationalLocData A) [IsNoetherianRing (presheafValue D₀)]
    [IsDomain (presheafValue D₀)]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
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
    (x : presheafValue D₀)
    (hplus0 : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = 0)
    (hminus0 : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = 0) :
    x = 0 :=
  laurentCover_separation_presheaf_viaRow3_of_iInf_pow_eq_bot D₀ f
    (Ideal.iInf_pow_eq_bot_of_isDomain _ (by rwa [Ne, Ideal.span_singleton_eq_top]))
    hplus hminus τ_plus τ_minus htau_plus htau_minus x hplus0 hminus0

/-- **Hübner simple-Laurent separation via the named Route-B bridges.**

This is the separation analogue of
`laurentCover_gluing_presheaf_viaBridges`: it packages the concrete
`laurentPlusBridge`/`laurentMinusBridge` identifications and their
restriction-map compatibility lemmas, leaving only the explicit algebraic
Krull-intersection input
`⋂ n, (D₀.canonicalMap f)^n = 0`.

This theorem is deliberately not a final acyclicity theorem. Its purpose is to
make the simple-Laurent **separation** supplier as callable as the existing
simple-Laurent gluing supplier, without routing through Corollary 8.32. -/
theorem laurentCover_separation_presheaf_viaBridges_of_iInf_pow_eq_bot
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hInf : (⨅ n : ℕ,
      Ideal.span ({D₀.canonicalMap f} : Set (presheafValue D₀)) ^ n) = ⊥)
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
    (x : presheafValue D₀)
    (hplus0 : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = 0)
    (hminus0 : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = 0) :
    x = 0 :=
  laurentCover_separation_presheaf_viaRow3_of_iInf_pow_eq_bot D₀ f hInf
    hplus hminus
    (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
      hnoeth_B hcont_forward_B)
    (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B)
    (laurentPlusBridge_restrictionMap P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
      hA_complete_B hnoeth_B hcont_forward_B hplus)
    (laurentMinusBridge_restrictionMap P D₀ f hnoeth_B hcont_eval_B hminus)
    x hplus0 hminus0

/-- **Jacobian specialization of bridge-packaged simple-Laurent separation.**

If the Laurent parameter lies in the Jacobson radical of the completed base
ring, Mathlib's Krull-intersection theorem supplies the explicit
`iInf_pow_eq_bot` input required by
`laurentCover_separation_presheaf_viaBridges_of_iInf_pow_eq_bot`. -/
theorem laurentCover_separation_presheaf_viaBridges_of_span_le_jacobson
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hf_jac : Ideal.span ({D₀.canonicalMap f} : Set (presheafValue D₀)) ≤
      Ideal.jacobson (⊥ : Ideal (presheafValue D₀)))
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
    (x : presheafValue D₀)
    (hplus0 : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = 0)
    (hminus0 : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = 0) :
    x = 0 := by
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  exact laurentCover_separation_presheaf_viaBridges_of_iInf_pow_eq_bot
    P D₀ f
    (LaurentCover.span_singleton_iInf_pow_eq_bot_of_le_jacobson
      (D₀.canonicalMap f) hf_jac)
    hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
    hcont_forward_B hcont_eval_B hplus hminus x hplus0 hminus0

/-! ### H1-general (non-domain) — TARGET, NOT LANDED

The general noetherian Tate analog of `laurentCover_separation_presheaf_viaRow3_domain`
— removing the `[IsDomain (presheafValue D₀)]` hypothesis — is **not landed
this session**. It requires a new injectivity theorem replacing
`LaurentCover.epsilonHom_gen_injective`:

```lean
-- WANTED: helper in LaurentCoverExact.lean or new Tate-topology module
theorem epsilonHom_gen_injective_noetherian_tate
    {B : Type*} [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
    [T2Space B] [IsNoetherianRing B] [IsTateRing B]
    (g : B) (hg : ¬IsUnit g) :
    Function.Injective (LaurentCover.epsilonHom_gen g)
```

**Identified obstruction** (discovered during direct proof attempt this
session): the proposed proof sketch (coefficient recurrence + general
Krull + iteration + `IsRestricted`-convergence + Tate-ideal-basis ⋂ = 0)
BREAKS at the final step because:

* In a **Tate ring** B with pair of definition (B₀, I₀), the 0-nhd basis
  `{I₀^k}_k` consists of ideals of **B₀**, not of B itself.
* Extending to `I₀^k · B` makes these ideals of B, but they become all
  of B (since the topologically-nilpotent unit π ∈ I₀ is a unit in B:
  `I₀ · B = π · B₀ · B = B`).
* The iteration step `a = c^N · f^N · a ∈ c^N · I₀^k ⊆ I₀^k` requires
  `c · I₀^k ⊆ I₀^k`, i.e., `c ∈ B₀` (power-bounded). But the witness `c`
  from general Krull `Ideal.mem_iInf_smul_pow_eq_bot_iff` is an arbitrary
  element of B, not necessarily in B₀.

**Conclusion**: the direct Hübner-route proof of Laurent-pair injectivity
without `[IsDomain]` for Tate rings appears to require either (a) a
refined Krull giving `c ∈ B₀`, or (b) a different argument (e.g., via
flatness of the Laurent quotients + spectrum surjectivity), or (c) the
faithful-flatness route (Stacks 00MA / Cor 8.32) we were trying to avoid.

See `.mathlib-quality/chatgpt-packet-hubner-nondomain.md` for the full
context, Lean signatures, and five acceptable response forms (A-E) to
ChatGPT Pro. The packet captures the exact formalization boundary and
open mathematical question.

**Downstream impact**: H2/H3/H4 (iterated Laurent separation, final
Hübner Part 1 wrapper, per-E Laurent Lane B) all wait on the non-domain
general case. If the non-domain version truly requires Stacks 00MA,
then the Hübner route does NOT decouple `tateAcyclicity` from Cor 8.32,
and Lane B (T-COMP-FF / T-IDEAL-2) remains the critical path. -/

end ValuationSpectrum
