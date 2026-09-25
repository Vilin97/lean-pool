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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinement
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentMinusNormalized
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativeRationalLocData
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flatness of the restriction map via Wedhorn Prop 8.30 + Wedhorn Lemma 2.13

## Reframe (MAJOR CORRECTION, ChatGPT Pro 2026-05-11 session 2)

The previous `restrictionMap_isLocalization` target (Wedhorn 8.15 as
`IsLocalization.Away`) is mathematically FALSE — completed rational
localizations contain infinite convergent denominator tails that no finite
power `s^N` can clear (counterexample: `A = ℚ_p⟨X⟩`,
`A⟨T⟩/(XT-1) ∋ ∑_{n≥0} p^n X^{-n}`).

The FIX: deliver `Module.Flat` for the restriction map DIRECTLY via the
B-level Wedhorn Prop 8.30 (Tate-algebra quotient identification at
`B := presheafValue D₀`), then transfer along the Wedhorn Lemma 2.13
identification `presheafValue (laurentMinusDatum D₀ f) ≃+*
presheafValue (iteratedMinusDatum_B P D₀ f)` (the
`presheafValue_iteratedMinus_equiv` of `LaurentRefinement.lean`, sorry-free).

## Main results

* `restrictionMap_flat_via_iteratedMinus` — for `D = laurentMinusDatum D₀ f`,
  `presheafValue D` is flat as a `presheafValue D₀`-module along the
  restriction map. Discharged by:
  1. B-level flatness `Module.Flat (presheafValue D₀)
     (presheafValue (iteratedMinusDatum_B P D₀ f))` via
     `presheafValue_flat_of_canonical` (with `T = {1}` collapsing `hT_pb`,
     `hb` via `invS_isPowerBounded_of_one_mem_T`).
  2. Transfer of flatness along `presheafValue_iteratedMinus_equiv` using
     `Module.Flat.of_linearEquiv` and the compatibility lemma
     `presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 8.30, Lemma 2.13.
* `docs/STATUS.md` — Reframe of T-FLAT-VIA-WEDHORN830.
* `Adic spaces/StructureSheaf.lean` — template `presheafValue_flat_of_tateQuotient`.
-/

@[expose] public section

open ValuationSpectrum CompletionLocalization

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### B-level flatness for the iteratedMinusDatum_B (`T = {1}`)

This is `presheafValue_flat_of_laurentMinus` of `StructureSheaf.lean`
specialised to `A := presheafValue D₀`, `P := presheafValue_pairOfDefinition_concrete P D₀`,
`D := iteratedMinusDatum_B P D₀ f`. The data has `T = {1}` and
`s = D₀.canonicalMap f`, so `hT_pb` and `hb` collapse to the singleton case,
and we are left with the canonical-topology hypotheses
`hA_complete_B`, `hnoeth_B`, `hcont_eval_B`.

Stated as a helper to declutter `restrictionMap_flat_via_iteratedMinus`. -/
omit [HasLocLiftPowerBounded A] in
theorem iteratedMinus_B_flat_of_canonical
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    -- Note: NO `hLocLift_B : HasLocLiftPowerBounded (presheafValue D₀)` —
    -- the proof uses `presheafValue_flat_of_canonical` which does not require
    -- it. The Nullstellensatz/Wedhorn 7.32 preservation is unnecessary at
    -- this depth-1 level.
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
          (iteratedMinusDatum_B P D₀ f).s))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      let D := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
    letI P_B : PairOfDefinition (presheafValue D₀) :=
      presheafValue_pairOfDefinition_concrete P D₀
    letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
    letI : IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
          (iteratedMinusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
    @Module.Flat (presheafValue D₀) (presheafValue (iteratedMinusDatum_B P D₀ f))
      _ _ (RingHom.toModule (RationalLocData.canonicalMap (iteratedMinusDatum_B P D₀ f))) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  letI : IsNoetherianRing
      (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
        (iteratedMinusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
  -- Discharge `hb` and `hT_pb` for `T = {1}`, `s = D₀.canonicalMap f`.
  have hb : TopologicalRing.IsPowerBounded
      (invS (iteratedMinusDatum_B P D₀ f)) := by
    -- `D.T = {1}`, so `1 ∈ D.T`. Use `invS_isPowerBounded_of_one_mem_T`.
    have h1_mem : (1 : presheafValue D₀) ∈ (iteratedMinusDatum_B P D₀ f).T :=
      Finset.mem_singleton_self 1
    -- `invS D = D.coeRingHom (divByS 1 D.s)` (factor through completion).
    have hinvS_eq : invS (iteratedMinusDatum_B P D₀ f) =
        (iteratedMinusDatum_B P D₀ f).coeRingHom
          (divByS 1 (iteratedMinusDatum_B P D₀ f).s) := by
      set D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      have h1 : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
      have halg : algebraMap (presheafValue D₀) (Localization.Away D.s) D.s *
          divByS 1 D.s = 1 := by
        rw [← invSelf_eq_divByS, IsLocalization.Away.mul_invSelf]
      have h2 : D.canonicalMap D.s * D.coeRingHom (divByS 1 D.s) = 1 := by
        change D.coeRingHom (algebraMap (presheafValue D₀) (Localization.Away D.s) D.s) *
          D.coeRingHom (divByS 1 D.s) = 1
        rw [← map_mul, halg, map_one]
      have hu : IsUnit (D.canonicalMap D.s) := isUnit_s_in_presheafValue D
      exact hu.mul_left_cancel (h1.trans h2.symm)
    rw [hinvS_eq]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
      (iteratedMinusDatum_B P D₀ f) h1_mem
  have hT_pb : ∀ t ∈ (iteratedMinusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded t := by
    intro t ht
    -- `T = {1}` collapses to `t = 1`.
    rw [Finset.mem_singleton.mp ht]
    exact TopologicalRing.isPowerBounded_one
  -- Now apply `presheafValue_flat_of_canonical` at the B-level.
  exact presheafValue_flat_of_canonical (presheafValue D₀) P_B
    (iteratedMinusDatum_B P D₀ f) hb hA_complete_B hnoeth_B hT_pb (hcont_eval_B hb)

/-! ### Linear equiv compatibility for `presheafValue_iteratedMinus_equiv`

The ring equiv `presheafValue_iteratedMinus_equiv P D₀ f` intertwines:
* the source `presheafValue D₀`-module structure on
  `presheafValue (laurentMinusDatum D₀ f)` via
  `restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub`;
* the target `presheafValue D₀`-module structure on
  `presheafValue (iteratedMinusDatum_B P D₀ f)` via the canonical map
  `(iteratedMinusDatum_B P D₀ f).canonicalMap`.

This is the linear-equiv version of the sorry-free ring-hom compatibility
`presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap`. -/

/-! ### T-FLAT-VIA-WEDHORN830: Module.Flat for the Laurent-minus restriction

`presheafValue (laurentMinusDatum D₀ f)` is flat as a `presheafValue D₀`-module
along `restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub`. Discharged via
the Wedhorn Prop 8.30 + Lemma 2.13 route, NOT via `IsLocalization.Away`. -/
theorem restrictionMap_flat_via_iteratedMinus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
            rationalOpen D₀.T D₀.s)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    -- NO `hLocLift_B` — the proof uses `presheafValue_flat_of_canonical` which
    -- does not require `HasLocLiftPowerBounded (presheafValue D₀)`.
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
          (iteratedMinusDatum_B P D₀ f).s))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      let D := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    @Module.Flat (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f)) _ _
      ((restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  letI : IsNoetherianRing
      (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
        (iteratedMinusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
  -- Step 1: B-level flatness for the iteratedMinusDatum_B side.
  -- NO `letI : HasLocLiftPowerBounded` needed — `iteratedMinus_B_flat_of_canonical`
  -- does not require it (proved via `presheafValue_flat_of_canonical`).
  haveI hflat_B :
      @Module.Flat (presheafValue D₀) (presheafValue (iteratedMinusDatum_B P D₀ f))
        _ _ (RingHom.toModule
          (RationalLocData.canonicalMap (iteratedMinusDatum_B P D₀ f))) :=
    iteratedMinus_B_flat_of_canonical P D₀ f hNoeth_B
      hA_complete_B hnoeth_B hP_A₀Noeth_B hlocSubring_Noeth_B hcont_eval_B
  -- Step 2: Transfer flatness via `presheafValue_iteratedMinus_equiv`.
  -- The equiv intertwines `restrictionMapHom`-module on the source with
  -- `canonicalMap`-module on the target (compatibility lemma below).
  let e := presheafValue_iteratedMinus_equiv P D₀ f
  -- Module structure compatibility: `e (a • x) = a • e x` where
  --  • src `•`: `a • x = restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub a * x`
  --  • tgt `•`: `a • y = (iteratedMinusDatum_B P D₀ f).canonicalMap a * y`
  change @Module.Flat (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f))
    _ _ ((restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule)
  letI : Module (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f)) :=
    (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule
  letI : Module (presheafValue D₀) (presheafValue (iteratedMinusDatum_B P D₀ f)) :=
    RingHom.toModule (RationalLocData.canonicalMap (iteratedMinusDatum_B P D₀ f))
  -- `e_smul`: the equiv preserves the module action.
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue (laurentMinusDatum D₀ f)),
      e (a • x) = a • e x := by
    intro a x
    -- Unfold scalar actions:
    --   src: a • x = restrictionMapHom (...) a * x
    --   tgt: a • e x = (iteratedMinusDatum_B P D₀ f).canonicalMap a * e x
    change e (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub a * x) =
      (iteratedMinusDatum_B P D₀ f).canonicalMap a * e x
    rw [e.map_mul]
    congr 1
    -- This is exactly `presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap`.
    exact presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap P D₀ f hsub a
  -- Apply `Module.Flat.of_linearEquiv` with the forward direction `e` as the
  -- LinearEquiv `N →ₗ M` where N = laurent-minus, M = iterated-minus B (known flat).
  exact @Module.Flat.of_linearEquiv (presheafValue D₀)
    (presheafValue (iteratedMinusDatum_B P D₀ f))
    (presheafValue (laurentMinusDatum D₀ f))
    _ _ _ _ _ hflat_B
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-! ### Plus-side analog: B-level flatness for the iteratedPlusDatum_B

`iteratedPlusDatum_B P D₀ f` has `T = {D₀.canonicalMap f}` and `s = 1`. Then
`invS D = 1` (a power-bounded unit), and `hT_pb` reduces to
`IsPowerBounded (D₀.canonicalMap f)` — an EXTERNAL hypothesis the caller
must supply (in contrast to the minus side where `T = {1}` collapses
trivially). -/
omit [HasLocLiftPowerBounded A] in
theorem iteratedPlus_B_flat_of_canonical
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    -- NO `hLocLift_B`: HasLocLiftPowerBounded preservation isn't needed —
    -- proof uses `presheafValue_flat_of_canonical` directly.
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      IsNoetherianRing
        (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
          (iteratedPlusDatum_B P D₀ f).s))
    -- EXTRA HYPOTHESIS vs the minus side: `canonicalMap f` must be power-bounded.
    -- Holds when `f ∈ A°` (power-bounded elements of `A`) and `canonicalMap`
    -- preserves power-boundedness, which is the standard setting.
    (hf_canonical_pb : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      TopologicalRing.IsPowerBounded (D₀.canonicalMap f))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      let D := iteratedPlusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
    letI P_B : PairOfDefinition (presheafValue D₀) :=
      presheafValue_pairOfDefinition_concrete P D₀
    letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
    letI : IsNoetherianRing
        (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
          (iteratedPlusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
    @Module.Flat (presheafValue D₀) (presheafValue (iteratedPlusDatum_B P D₀ f))
      _ _ (RingHom.toModule (RationalLocData.canonicalMap (iteratedPlusDatum_B P D₀ f))) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  letI : IsNoetherianRing
      (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
        (iteratedPlusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
  -- For `s = 1`: `invS D = 1` (power-bounded).
  have hb : TopologicalRing.IsPowerBounded
      (invS (iteratedPlusDatum_B P D₀ f)) := by
    -- `D.s = 1` ⇒ `D.canonicalMap D.s = D.canonicalMap 1 = 1` ⇒ `invS D = 1`.
    have hinvS_eq : invS (iteratedPlusDatum_B P D₀ f) = 1 := by
      set D : RationalLocData (presheafValue D₀) := iteratedPlusDatum_B P D₀ f
      have h1 : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
      have hs : D.s = 1 := rfl
      rw [hs, map_one, one_mul] at h1
      exact h1
    rw [hinvS_eq]
    exact TopologicalRing.isPowerBounded_one
  -- For `T = {D₀.canonicalMap f}`: `hT_pb` follows from `hf_canonical_pb`.
  have hT_pb : ∀ t ∈ (iteratedPlusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [Finset.mem_singleton.mp ht]
    exact hf_canonical_pb
  -- Apply `presheafValue_flat_of_canonical` at the B-level.
  exact presheafValue_flat_of_canonical (presheafValue D₀) P_B
    (iteratedPlusDatum_B P D₀ f) hb hA_complete_B hnoeth_B hT_pb (hcont_eval_B hb)

/-! ### T-FLAT-VIA-WEDHORN830 plus side: `Module.Flat` for the Laurent-plus restriction

`presheafValue (laurentPlusDatum D₀ f)` is flat as a `presheafValue D₀`-module
along `restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub`. Discharged via the
Wedhorn Prop 8.30 + Lemma 2.13 route on the PLUS side. Requires the additional
`hf_canonical_pb` hypothesis. -/
theorem restrictionMap_flat_via_iteratedPlus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
            rationalOpen D₀.T D₀.s)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    -- NO `hLocLift_B`: HasLocLiftPowerBounded preservation isn't needed.
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      IsNoetherianRing
        (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
          (iteratedPlusDatum_B P D₀ f).s))
    (hf_canonical_pb : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      TopologicalRing.IsPowerBounded (D₀.canonicalMap f))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      let D := iteratedPlusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    @Module.Flat (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f)) _ _
      ((restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  letI : IsNoetherianRing
      (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
        (iteratedPlusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
  haveI hflat_B :
      @Module.Flat (presheafValue D₀) (presheafValue (iteratedPlusDatum_B P D₀ f))
        _ _ (RingHom.toModule
          (RationalLocData.canonicalMap (iteratedPlusDatum_B P D₀ f))) :=
    iteratedPlus_B_flat_of_canonical P D₀ f hNoeth_B
      hA_complete_B hnoeth_B hP_A₀Noeth_B hlocSubring_Noeth_B hf_canonical_pb hcont_eval_B
  let e := presheafValue_iteratedPlus_equiv P D₀ f
  change @Module.Flat (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f))
    _ _ ((restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule)
  letI : Module (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f)) :=
    (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule
  letI : Module (presheafValue D₀) (presheafValue (iteratedPlusDatum_B P D₀ f)) :=
    RingHom.toModule (RationalLocData.canonicalMap (iteratedPlusDatum_B P D₀ f))
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue (laurentPlusDatum D₀ f)),
      e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub a * x) =
      (iteratedPlusDatum_B P D₀ f).canonicalMap a * e x
    rw [e.map_mul]
    congr 1
    exact presheafValue_iteratedPlus_equiv_restrictionMap_canonicalMap P D₀ f hsub a
  exact @Module.Flat.of_linearEquiv (presheafValue D₀)
    (presheafValue (iteratedPlusDatum_B P D₀ f))
    (presheafValue (laurentPlusDatum D₀ f))
    _ _ _ _ _ hflat_B
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-! ### T-FLAT-PLUS-REWORK: plus-side flatness via the `f-X` quotient (NO PB hypothesis)

**T-FLAT-PLUS-REWORK (2026-05-11 round 3)**.

Per reviewer guidance (ChatGPT Pro session 3): the plus rational localization
`R(f/1)` is **precisely** what makes `f` power-bounded — it should NOT require
`IsPowerBounded (D₀.canonicalMap f)` in the source. The correct model is the
quotient `B⟨X⟩/(f - X)`.

This theorem replaces `restrictionMap_flat_via_iteratedPlus` with a version
built on `flat_quotient_fSubX_general` + the existing `laurentPlusBridge`
(which provides `presheafValue (laurentPlusDatum D₀ f) ≃+* B⟨X⟩/(f-X)`).

The hypotheses are the same as `laurentPlusBridge` (all about the generic
B-base, NO assumption that `D₀.canonicalMap f` is power-bounded). -/
theorem restrictionMap_flat_via_fSubX_quotient
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
            rationalOpen D₀.T D₀.s)
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
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f))) :
    @Module.Flat (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f)) _ _
      ((restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
  -- Step 1: B = presheafValue D₀-flatness of B⟨X⟩/(f - X) via Wedhorn 8.30 / Lemma 8.31.
  -- `flat_quotient_fSubX_general` gives this for ANY f in B (no PB hypothesis).
  haveI hflat_quot :
      Module.Flat (presheafValue D₀)
        (LaurentCover.B₁_gen (D₀.canonicalMap f)) :=
    TateAlgebra.flat_quotient_fSubX_general P_B (D₀.canonicalMap f)
  -- Step 2: Transfer flatness along `laurentPlusBridge`, which gives
  -- `presheafValue (laurentPlusDatum D₀ f) ≃+* B⟨X⟩/(f-X)`.
  let e := laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
    hnoeth_B hcont_forward_B
  change @Module.Flat (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f))
    _ _ ((restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule)
  letI : Module (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f)) :=
    (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule
  -- Module action on B₁_gen via algebraMap (matches `flat_quotient_fSubX_general`'s
  -- instance, which comes from the canonical A-algebra structure on `TateAlgebra A`
  -- followed by the quotient).
  -- `e_smul`: the equiv intertwines the restriction-map module action with the
  -- canonical quotient-map module action.
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue (laurentPlusDatum D₀ f)),
      e (a • x) = a • e x := by
    intro a x
    -- src: a • x = restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub a * x
    -- tgt: a • e x = algebraMap B (B₁_gen f) a * e x
    change e (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub a * x) =
      algebraMap (presheafValue D₀) (LaurentCover.B₁_gen (D₀.canonicalMap f)) a * e x
    rw [e.map_mul]
    congr 1
    -- `e (restrictionMap a) = (epsilonHom_gen (canonicalMap f) a).1`
    -- via `laurentPlusBridge_restrictionMap`.
    have h1 := laurentPlusBridge_restrictionMap P D₀ f hNoeth_B hLocLift_B
      hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hsub a
    -- Bring `restrictionMap` and `restrictionMapHom` into the same form:
    change e (restrictionMap D₀ (laurentPlusDatum D₀ f) hsub a) =
      algebraMap (presheafValue D₀) (LaurentCover.B₁_gen (D₀.canonicalMap f)) a
    rw [h1]
    -- `(epsilonHom_gen f a).1 = (Ideal.Quotient.mk _).comp (algebraMap _ _) a`.
    rfl
  exact @Module.Flat.of_linearEquiv (presheafValue D₀)
    (LaurentCover.B₁_gen (D₀.canonicalMap f))
    (presheafValue (laurentPlusDatum D₀ f))
    _ _ _ _ _ hflat_quot
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-! ### Minus-side analog: flatness via the `1 - fX` quotient

**Symmetric to `restrictionMap_flat_via_fSubX_quotient`** (T-FLAT-PLUS-REWORK).

This is the corrected minus-side theorem using `flat_quotient_oneSubfX_general` +
the existing `laurentMinusBridge`. Symmetric to the plus version; gives a clean
uniform API for both halves of any Laurent cover.

The minus side does NOT need any source-side power-boundedness hypothesis
(neither side does, after this rework). Hypothesis set matches
`laurentMinusBridge`: just `hnoeth_B` and `hcont_eval_B` at the B-level. -/
theorem restrictionMap_flat_via_oneSubfX_quotient
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
            rationalOpen D₀.T D₀.s)
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀)) :
    @Module.Flat (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f)) _ _
      ((restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  -- B-level flatness of B⟨X⟩/(1 - fX) via Wedhorn 8.30 / Lemma 8.31.
  haveI hflat_quot :
      Module.Flat (presheafValue D₀)
        (LaurentCover.B₂_gen (D₀.canonicalMap f)) :=
    TateAlgebra.flat_quotient_oneSubfX_general P_B (D₀.canonicalMap f)
  -- Transfer flatness along `laurentMinusBridge`.
  let e := laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B
  change @Module.Flat (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f))
    _ _ ((restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule)
  letI : Module (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f)) :=
    (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue (laurentMinusDatum D₀ f)),
      e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub a * x) =
      algebraMap (presheafValue D₀) (LaurentCover.B₂_gen (D₀.canonicalMap f)) a * e x
    rw [e.map_mul]
    congr 1
    have h1 := laurentMinusBridge_restrictionMap P D₀ f hnoeth_B hcont_eval_B hsub a
    change e (restrictionMap D₀ (laurentMinusDatum D₀ f) hsub a) =
      algebraMap (presheafValue D₀) (LaurentCover.B₂_gen (D₀.canonicalMap f)) a
    rw [h1]
    rfl
  exact @Module.Flat.of_linearEquiv (presheafValue D₀)
    (LaurentCover.B₂_gen (D₀.canonicalMap f))
    (presheafValue (laurentMinusDatum D₀ f))
    _ _ _ _ _ hflat_quot
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-! ### T-RATIONAL-FLAT-GENERAL: general rational-restriction flatness

**T-RATIONAL-FLAT-GENERAL (2026-05-11 round 3, hypothesis-parameterised form)**.

Per session-3 reviewer prescription: the natural theorem Wedhorn actually uses
is *arbitrary rational restrictions are flat*. For any `E, D : RationalLocData A`
with `rationalOpen D ⊆ rationalOpen E`, the restriction map `O(E) → O(D)` is flat
as an `O(E)`-module homomorphism.

The reviewer's proof outline:
1. Basic plus flatness `B → B⟨X⟩/(f-X)` (already proved as
   `flat_quotient_fSubX_general`).
2. Basic minus flatness `B → B⟨X⟩/(1-fX)` (already proved as
   `flat_quotient_oneSubfX_general`).
3. Transitivity of rational localizations: any inclusion `D ⊆ E` decomposes as
   a finite chain of basic steps.
4. Composition of flat maps is flat.

This version of the theorem is **hypothesis-parameterised** by the depth-N
Wedhorn 2.13 generalisation: the caller supplies a ring iso
`presheafValue D ≃+* presheafValue D_at_E` where `D_at_E : RationalLocData (presheafValue E)`
is the relative rational locale (built by iterating Wedhorn 2.13). The iso
must intertwine the restriction map with the canonical map at E-level.

Once supplied, the flatness follows by applying `presheafValue_flat_of_canonical`
at the E-level and transferring along the equiv.

The construction of `D_at_E` and the relative-equiv `presheafValue_relative_equiv`
is the remaining structural piece (T-WEDHORN-213-GENERAL); this wrapper isolates
the algebraic-flatness step from that construction. -/
theorem restrictionMap_flat_of_rational_subset_via_relative
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E D : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s)
    -- Depth-N Wedhorn 2.13: relative locale data for D over presheafValue E.
    (D_at_E : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      RationalLocData (presheafValue E))
    -- The relative equiv (depth-N 2.13).
    (relEquiv : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      presheafValue D ≃+* presheafValue D_at_E)
    -- The relative equiv intertwines the restriction map with the canonical map.
    (h_intertwine : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      ∀ a : presheafValue E,
        relEquiv (restrictionMapHom E D hsub a) = D_at_E.canonicalMap a)
    -- B-level hypotheses needed by `presheafValue_flat_of_canonical` at E-level.
    -- Note: NO `HasLocLiftPowerBounded (presheafValue E)` hypothesis required —
    -- `presheafValue_flat_of_canonical` discharges flatness via the canonical
    -- Tate-quotient identification, not via Nullstellensatz / restriction maps at
    -- the B-level.
    (hNoeth_B : IsNoetherianRing (presheafValue E))
    (hA_complete_B : @CompleteSpace (presheafValue E)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue E)))
    (hnoeth_B : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue E)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      letI : IsNoetherianRing (presheafValue E) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P E).A₀))
    -- The canonical-form flatness hypotheses for D_at_E.
    (hb : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      TopologicalRing.IsPowerBounded (invS D_at_E))
    (hT_pb : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      ∀ t ∈ D_at_E.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      letI : IsNoetherianRing (presheafValue E) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue E) :=
        presheafValue_pairOfDefinition_concrete P E
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology D_at_E.s)
        (inferInstance : TopologicalSpace (presheafValue D_at_E))
        (tateQuotientToPresheafHom D_at_E hb)) :
    @Module.Flat (presheafValue E) (presheafValue D) _ _
      ((restrictionMapHom E D hsub).toModule) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
  letI : IsNoetherianRing (presheafValue E) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue E) :=
    presheafValue_pairOfDefinition_concrete P E
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  -- Step 1: E-level flatness of presheafValue D_at_E via Wedhorn 8.30 + Lemma 8.31.
  -- Note: `presheafValue_flat_of_canonical` does NOT require
  -- `HasLocLiftPowerBounded (presheafValue E)` — flatness is established directly
  -- from the Tate-quotient identification at the B-level, no Nullstellensatz needed.
  haveI hflat_E :
      @Module.Flat (presheafValue E) (presheafValue D_at_E)
        _ _ (RingHom.toModule D_at_E.canonicalMap) :=
    presheafValue_flat_of_canonical (presheafValue E) P_B D_at_E
      hb hA_complete_B hnoeth_B hT_pb hcont_eval
  -- Step 2: Transfer flatness along the relative equiv.
  let e := relEquiv
  change @Module.Flat (presheafValue E) (presheafValue D)
    _ _ ((restrictionMapHom E D hsub).toModule)
  letI : Module (presheafValue E) (presheafValue D) :=
    (restrictionMapHom E D hsub).toModule
  letI : Module (presheafValue E) (presheafValue D_at_E) :=
    RingHom.toModule D_at_E.canonicalMap
  have he_smul : ∀ (a : presheafValue E) (x : presheafValue D),
      e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom E D hsub a * x) = D_at_E.canonicalMap a * e x
    rw [e.map_mul]
    congr 1
    exact h_intertwine a
  exact @Module.Flat.of_linearEquiv (presheafValue E)
    (presheafValue D_at_E)
    (presheafValue D)
    _ _ _ _ _ hflat_E
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-! ### Direct-Laurent-shape corollary: D = laurentMinusDatum E f

Concrete corollary of `restrictionMap_flat_of_rational_subset_via_relative`:
when `D = laurentMinusDatum E f` directly (depth-1 from E), the relative equiv
is the existing `presheafValue_iteratedMinus_equiv` and the intertwining is the
existing `_restrictionMap_canonicalMap`. So the general theorem specialises
sorry-free.

This is `restrictionMap_flat_via_iteratedMinus` restated through the general
framework, providing the same conclusion as the existing `iteratedMinus`
version. Useful as the depth-1 sanity check + the API entry point for the
general theorem. -/
theorem restrictionMap_flat_of_rational_subset_direct_laurentMinus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    [LaurentNormalized E]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum E f).T (laurentMinusDatum E f).s ⊆
            rationalOpen E.T E.s)
    -- NO `hLocLift_B` — proof path doesn't need HasLocLiftPowerBounded.
    (hNoeth_B : IsNoetherianRing (presheafValue E))
    (hA_complete_B : @CompleteSpace (presheafValue E)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue E)))
    (hnoeth_B : letI : IsTateRing (presheafValue E) :=
        presheafValue_isTateRing P E
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue E)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue E) :=
        presheafValue_isTateRing P E
      letI : IsNoetherianRing (presheafValue E) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P E).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue E) :=
        presheafValue_isTateRing P E
      letI : IsNoetherianRing (presheafValue E) := hNoeth_B
      letI : PairOfDefinition (presheafValue E) :=
        presheafValue_pairOfDefinition_concrete P E
      IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P E f).P (iteratedMinusDatum_B P E f).T
          (iteratedMinusDatum_B P E f).s))
    (hcont_eval_B : letI : IsTateRing (presheafValue E) :=
        presheafValue_isTateRing P E
      letI : IsNoetherianRing (presheafValue E) := hNoeth_B
      letI : PairOfDefinition (presheafValue E) :=
        presheafValue_pairOfDefinition_concrete P E
      let D := iteratedMinusDatum_B P E f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    @Module.Flat (presheafValue E) (presheafValue (laurentMinusDatum E f)) _ _
      ((restrictionMapHom E (laurentMinusDatum E f) hsub).toModule) :=
  restrictionMap_flat_via_iteratedMinus P E f hsub hNoeth_B
    hA_complete_B hnoeth_B hP_A₀Noeth_B hlocSubring_Noeth_B hcont_eval_B

/-! ### Flatness chain composition (T-CHAIN-COMPOSITION)

**Reviewer-recommended transitivity step**. Per session-3 guidance: "Build
[arbitrary rational-restriction flatness] from the two basic flatness steps
plus transitivity/decomposition of rational localizations."

Given flatness `O(E) → O(D₁)` along restrictionMap (e.g., from a basic
Laurent step + our depth-1 theorems) and flatness `O(D₁) → O(D)` along the
next restrictionMap, conclude `O(E) → O(D)` is flat by `Module.Flat.trans`
along the natural scalar tower.

The tower `IsScalarTower (presheafValue E) (presheafValue D₁) (presheafValue D)`
follows from presheaf functoriality (`restrictionMap_comp`):
`restrictionMap D₁ D h₂ ∘ restrictionMap E D₁ h₁ = restrictionMap E D (h₂.trans h₁)`.

Iterate this theorem along any finite chain of basic Laurent steps to
discharge flatness for arbitrary rational sub-locale containments. -/
theorem restrictionMap_flat_trans
    (E D₁ D : RationalLocData A)
    (h_E_D₁ : rationalOpen D₁.T D₁.s ⊆ rationalOpen E.T E.s)
    (h_D₁_D : rationalOpen D.T D.s ⊆ rationalOpen D₁.T D₁.s)
    (flat_E_D₁ : @Module.Flat (presheafValue E) (presheafValue D₁) _ _
      ((restrictionMapHom E D₁ h_E_D₁).toModule))
    (flat_D₁_D : @Module.Flat (presheafValue D₁) (presheafValue D) _ _
      ((restrictionMapHom D₁ D h_D₁_D).toModule)) :
    @Module.Flat (presheafValue E) (presheafValue D) _ _
      ((restrictionMapHom E D (h_D₁_D.trans h_E_D₁)).toModule) := by
  letI alg_E_D₁ : Algebra (presheafValue E) (presheafValue D₁) :=
    (restrictionMapHom E D₁ h_E_D₁).toAlgebra
  letI alg_D₁_D : Algebra (presheafValue D₁) (presheafValue D) :=
    (restrictionMapHom D₁ D h_D₁_D).toAlgebra
  letI alg_E_D : Algebra (presheafValue E) (presheafValue D) :=
    (restrictionMapHom E D (h_D₁_D.trans h_E_D₁)).toAlgebra
  letI mod_E_D₁ : Module (presheafValue E) (presheafValue D₁) := Algebra.toModule
  letI mod_D₁_D : Module (presheafValue D₁) (presheafValue D) := Algebra.toModule
  letI mod_E_D : Module (presheafValue E) (presheafValue D) := Algebra.toModule
  haveI : IsScalarTower (presheafValue E) (presheafValue D₁) (presheafValue D) := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change restrictionMapHom E D (h_D₁_D.trans h_E_D₁) x =
      restrictionMapHom D₁ D h_D₁_D (restrictionMapHom E D₁ h_E_D₁ x)
    have hcomp := congrFun (restrictionMap_comp E D₁ D h_E_D₁ h_D₁_D) x
    exact hcomp.symm
  haveI : Module.Flat (presheafValue E) (presheafValue D₁) := flat_E_D₁
  haveI : Module.Flat (presheafValue D₁) (presheafValue D) := flat_D₁_D
  exact Module.Flat.trans (presheafValue E) (presheafValue D₁) (presheafValue D)

/-- The self-restriction `𝒪_X(E) → 𝒪_X(E)` is flat (it is the identity ring hom,
so the module is the regular module). Base case of the chain fold. -/
theorem restrictionMapHom_refl_flat (E : RationalLocData A)
    (h : rationalOpen E.T E.s ⊆ rationalOpen E.T E.s) :
    @Module.Flat (presheafValue E) (presheafValue E) _ _
      ((restrictionMapHom E E h).toModule) := by
  have hid : restrictionMapHom E E h = RingHom.id (presheafValue E) := by
    ext x; exact congrFun (restrictionMap_id E) x
  rw [hid]
  exact Module.Flat.self

/-- **Cumulative containment of a descending chain of rational locales**: if each
`rationalOpen (X (i+1)) ⊆ rationalOpen (X i)`, then `rationalOpen (X n) ⊆ rationalOpen (X 0)`
for every `n`. Defined by the obvious recursion so that the `n+1` case is *definitionally*
`(hstep n).trans (… n)` — the chain fold relies on this for proof-irrelevant matching. -/
theorem rationalOpen_chain_contains (X : ℕ → RationalLocData A)
    (hstep : ∀ i, rationalOpen (X (i + 1)).T (X (i + 1)).s ⊆ rationalOpen (X i).T (X i).s) :
    ∀ n, rationalOpen (X n).T (X n).s ⊆ rationalOpen (X 0).T (X 0).s
  | 0 => le_refl _
  | k + 1 => (hstep k).trans (rationalOpen_chain_contains X hstep k)

/-- **Arbitrary-length chain flatness** (Wedhorn Remark 7.55 fold): for a descending
chain of rational locales `X 0 ⊇ X 1 ⊇ ⋯` with each step's restriction map flat, the
composite restriction `𝒪_X(X 0) → 𝒪_X(X n)` is flat for every `n`. Supersedes the
explicit depth-3..7 lemmas; folds the per-step flatness by `restrictionMap_flat_trans`. -/
theorem restrictionMap_flat_chain (X : ℕ → RationalLocData A)
    (hstep : ∀ i, rationalOpen (X (i + 1)).T (X (i + 1)).s ⊆ rationalOpen (X i).T (X i).s)
    (hflat : ∀ i, @Module.Flat (presheafValue (X i)) (presheafValue (X (i + 1))) _ _
      ((restrictionMapHom (X i) (X (i + 1)) (hstep i)).toModule)) :
    ∀ n, @Module.Flat (presheafValue (X 0)) (presheafValue (X n)) _ _
      ((restrictionMapHom (X 0) (X n) (rationalOpen_chain_contains X hstep n)).toModule)
  | 0 => restrictionMapHom_refl_flat (X 0) (rationalOpen_chain_contains X hstep 0)
  | k + 1 =>
    restrictionMap_flat_trans (X 0) (X k) (X (k + 1))
      (rationalOpen_chain_contains X hstep k) (hstep k)
      (restrictionMap_flat_chain X hstep hflat k) (hflat k)

/-! ### Chain composition extended to depth N (list version)

Generalises `restrictionMap_flat_trans` to chains of arbitrary length. Given
a list of intermediate rational locales `E = L₀, L₁, ..., L_n = D` with each
`rationalOpen L_{i+1} ⊆ rationalOpen L_i` and each step's restriction map
flat, conclude the composite restriction `O(E) → O(D)` is flat.

Proof: induction on the list length, applying `restrictionMap_flat_trans`
at each step. (See also the recursion-free `restrictionMap_flat_chain` above,
which folds an arbitrary-length descending chain directly.) -/

/-- Inductive step for chain flatness: given flatness of N consecutive
restriction maps, the composed restriction is flat.

The list `chain : List (RationalLocData A × _)` packages each chain element
with the witness that it's contained in the previous one. Each step also
needs a flatness witness. -/
theorem restrictionMap_flat_chain_three
    (E D₁ D₂ D : RationalLocData A)
    (h_E_D₁ : rationalOpen D₁.T D₁.s ⊆ rationalOpen E.T E.s)
    (h_D₁_D₂ : rationalOpen D₂.T D₂.s ⊆ rationalOpen D₁.T D₁.s)
    (h_D₂_D : rationalOpen D.T D.s ⊆ rationalOpen D₂.T D₂.s)
    (flat_E_D₁ : @Module.Flat (presheafValue E) (presheafValue D₁) _ _
      ((restrictionMapHom E D₁ h_E_D₁).toModule))
    (flat_D₁_D₂ : @Module.Flat (presheafValue D₁) (presheafValue D₂) _ _
      ((restrictionMapHom D₁ D₂ h_D₁_D₂).toModule))
    (flat_D₂_D : @Module.Flat (presheafValue D₂) (presheafValue D) _ _
      ((restrictionMapHom D₂ D h_D₂_D).toModule)) :
    @Module.Flat (presheafValue E) (presheafValue D) _ _
      ((restrictionMapHom E D
        (h_D₂_D.trans (h_D₁_D₂.trans h_E_D₁))).toModule) := by
  -- Combine flat_E_D₁ with flat_D₁_D₂ to get flat E → D₂.
  have flat_E_D₂ :
      @Module.Flat (presheafValue E) (presheafValue D₂) _ _
        ((restrictionMapHom E D₂ (h_D₁_D₂.trans h_E_D₁)).toModule) :=
    restrictionMap_flat_trans E D₁ D₂ h_E_D₁ h_D₁_D₂ flat_E_D₁ flat_D₁_D₂
  -- Combine with flat_D₂_D to get flat E → D.
  exact restrictionMap_flat_trans E D₂ D
    (h_D₁_D₂.trans h_E_D₁) h_D₂_D flat_E_D₂ flat_D₂_D

/-- Depth-4 chain composition. -/
theorem restrictionMap_flat_chain_four
    (E D₁ D₂ D₃ D : RationalLocData A)
    (h_E_D₁ : rationalOpen D₁.T D₁.s ⊆ rationalOpen E.T E.s)
    (h_D₁_D₂ : rationalOpen D₂.T D₂.s ⊆ rationalOpen D₁.T D₁.s)
    (h_D₂_D₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.T D₂.s)
    (h_D₃_D : rationalOpen D.T D.s ⊆ rationalOpen D₃.T D₃.s)
    (flat_E_D₁ : @Module.Flat (presheafValue E) (presheafValue D₁) _ _
      ((restrictionMapHom E D₁ h_E_D₁).toModule))
    (flat_D₁_D₂ : @Module.Flat (presheafValue D₁) (presheafValue D₂) _ _
      ((restrictionMapHom D₁ D₂ h_D₁_D₂).toModule))
    (flat_D₂_D₃ : @Module.Flat (presheafValue D₂) (presheafValue D₃) _ _
      ((restrictionMapHom D₂ D₃ h_D₂_D₃).toModule))
    (flat_D₃_D : @Module.Flat (presheafValue D₃) (presheafValue D) _ _
      ((restrictionMapHom D₃ D h_D₃_D).toModule)) :
    @Module.Flat (presheafValue E) (presheafValue D) _ _
      ((restrictionMapHom E D
        (h_D₃_D.trans (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁)))).toModule) := by
  -- Combine the first three steps.
  have flat_E_D₃ :
      @Module.Flat (presheafValue E) (presheafValue D₃) _ _
        ((restrictionMapHom E D₃
          (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁))).toModule) :=
    restrictionMap_flat_chain_three E D₁ D₂ D₃
      h_E_D₁ h_D₁_D₂ h_D₂_D₃ flat_E_D₁ flat_D₁_D₂ flat_D₂_D₃
  -- Add the final step.
  exact restrictionMap_flat_trans E D₃ D
    (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁)) h_D₃_D flat_E_D₃ flat_D₃_D

/-! ### Depth-5, depth-6, depth-7 chain composition (explicit extensions)

Each depth-N theorem is a direct cascade of `restrictionMap_flat_trans`,
extending the depth-3 / depth-4 pattern. Covers chains of length up to 7,
sufficient for `T-CHAIN-CONSTRUCTION` chains `chainSteps : Fin (|D.T| + 2)`
with `|D.T|` up to 5. -/

/-- Depth-5 chain composition. -/
theorem restrictionMap_flat_chain_five
    (E D₁ D₂ D₃ D₄ D : RationalLocData A)
    (h_E_D₁ : rationalOpen D₁.T D₁.s ⊆ rationalOpen E.T E.s)
    (h_D₁_D₂ : rationalOpen D₂.T D₂.s ⊆ rationalOpen D₁.T D₁.s)
    (h_D₂_D₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.T D₂.s)
    (h_D₃_D₄ : rationalOpen D₄.T D₄.s ⊆ rationalOpen D₃.T D₃.s)
    (h_D₄_D : rationalOpen D.T D.s ⊆ rationalOpen D₄.T D₄.s)
    (flat_E_D₁ : @Module.Flat (presheafValue E) (presheafValue D₁) _ _
      ((restrictionMapHom E D₁ h_E_D₁).toModule))
    (flat_D₁_D₂ : @Module.Flat (presheafValue D₁) (presheafValue D₂) _ _
      ((restrictionMapHom D₁ D₂ h_D₁_D₂).toModule))
    (flat_D₂_D₃ : @Module.Flat (presheafValue D₂) (presheafValue D₃) _ _
      ((restrictionMapHom D₂ D₃ h_D₂_D₃).toModule))
    (flat_D₃_D₄ : @Module.Flat (presheafValue D₃) (presheafValue D₄) _ _
      ((restrictionMapHom D₃ D₄ h_D₃_D₄).toModule))
    (flat_D₄_D : @Module.Flat (presheafValue D₄) (presheafValue D) _ _
      ((restrictionMapHom D₄ D h_D₄_D).toModule)) :
    @Module.Flat (presheafValue E) (presheafValue D) _ _
      ((restrictionMapHom E D
        (h_D₄_D.trans (h_D₃_D₄.trans (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁))))).toModule) := by
  have flat_E_D₄ :
      @Module.Flat (presheafValue E) (presheafValue D₄) _ _
        ((restrictionMapHom E D₄
          (h_D₃_D₄.trans (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁)))).toModule) :=
    restrictionMap_flat_chain_four E D₁ D₂ D₃ D₄
      h_E_D₁ h_D₁_D₂ h_D₂_D₃ h_D₃_D₄ flat_E_D₁ flat_D₁_D₂ flat_D₂_D₃ flat_D₃_D₄
  exact restrictionMap_flat_trans E D₄ D
    (h_D₃_D₄.trans (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁))) h_D₄_D flat_E_D₄ flat_D₄_D

/-- Depth-6 chain composition. -/
theorem restrictionMap_flat_chain_six
    (E D₁ D₂ D₃ D₄ D₅ D : RationalLocData A)
    (h_E_D₁ : rationalOpen D₁.T D₁.s ⊆ rationalOpen E.T E.s)
    (h_D₁_D₂ : rationalOpen D₂.T D₂.s ⊆ rationalOpen D₁.T D₁.s)
    (h_D₂_D₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.T D₂.s)
    (h_D₃_D₄ : rationalOpen D₄.T D₄.s ⊆ rationalOpen D₃.T D₃.s)
    (h_D₄_D₅ : rationalOpen D₅.T D₅.s ⊆ rationalOpen D₄.T D₄.s)
    (h_D₅_D : rationalOpen D.T D.s ⊆ rationalOpen D₅.T D₅.s)
    (flat_E_D₁ : @Module.Flat (presheafValue E) (presheafValue D₁) _ _
      ((restrictionMapHom E D₁ h_E_D₁).toModule))
    (flat_D₁_D₂ : @Module.Flat (presheafValue D₁) (presheafValue D₂) _ _
      ((restrictionMapHom D₁ D₂ h_D₁_D₂).toModule))
    (flat_D₂_D₃ : @Module.Flat (presheafValue D₂) (presheafValue D₃) _ _
      ((restrictionMapHom D₂ D₃ h_D₂_D₃).toModule))
    (flat_D₃_D₄ : @Module.Flat (presheafValue D₃) (presheafValue D₄) _ _
      ((restrictionMapHom D₃ D₄ h_D₃_D₄).toModule))
    (flat_D₄_D₅ : @Module.Flat (presheafValue D₄) (presheafValue D₅) _ _
      ((restrictionMapHom D₄ D₅ h_D₄_D₅).toModule))
    (flat_D₅_D : @Module.Flat (presheafValue D₅) (presheafValue D) _ _
      ((restrictionMapHom D₅ D h_D₅_D).toModule)) :
    @Module.Flat (presheafValue E) (presheafValue D) _ _
      ((restrictionMapHom E D
        (h_D₅_D.trans (h_D₄_D₅.trans (h_D₃_D₄.trans (h_D₂_D₃.trans
          (h_D₁_D₂.trans h_E_D₁)))))).toModule) := by
  have flat_E_D₅ :
      @Module.Flat (presheafValue E) (presheafValue D₅) _ _
        ((restrictionMapHom E D₅
          (h_D₄_D₅.trans (h_D₃_D₄.trans (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁))))).toModule) :=
    restrictionMap_flat_chain_five E D₁ D₂ D₃ D₄ D₅
      h_E_D₁ h_D₁_D₂ h_D₂_D₃ h_D₃_D₄ h_D₄_D₅
      flat_E_D₁ flat_D₁_D₂ flat_D₂_D₃ flat_D₃_D₄ flat_D₄_D₅
  exact restrictionMap_flat_trans E D₅ D
    (h_D₄_D₅.trans (h_D₃_D₄.trans (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁))))
    h_D₅_D flat_E_D₅ flat_D₅_D

/-- Depth-7 chain composition. -/
theorem restrictionMap_flat_chain_seven
    (E D₁ D₂ D₃ D₄ D₅ D₆ D : RationalLocData A)
    (h_E_D₁ : rationalOpen D₁.T D₁.s ⊆ rationalOpen E.T E.s)
    (h_D₁_D₂ : rationalOpen D₂.T D₂.s ⊆ rationalOpen D₁.T D₁.s)
    (h_D₂_D₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.T D₂.s)
    (h_D₃_D₄ : rationalOpen D₄.T D₄.s ⊆ rationalOpen D₃.T D₃.s)
    (h_D₄_D₅ : rationalOpen D₅.T D₅.s ⊆ rationalOpen D₄.T D₄.s)
    (h_D₅_D₆ : rationalOpen D₆.T D₆.s ⊆ rationalOpen D₅.T D₅.s)
    (h_D₆_D : rationalOpen D.T D.s ⊆ rationalOpen D₆.T D₆.s)
    (flat_E_D₁ : @Module.Flat (presheafValue E) (presheafValue D₁) _ _
      ((restrictionMapHom E D₁ h_E_D₁).toModule))
    (flat_D₁_D₂ : @Module.Flat (presheafValue D₁) (presheafValue D₂) _ _
      ((restrictionMapHom D₁ D₂ h_D₁_D₂).toModule))
    (flat_D₂_D₃ : @Module.Flat (presheafValue D₂) (presheafValue D₃) _ _
      ((restrictionMapHom D₂ D₃ h_D₂_D₃).toModule))
    (flat_D₃_D₄ : @Module.Flat (presheafValue D₃) (presheafValue D₄) _ _
      ((restrictionMapHom D₃ D₄ h_D₃_D₄).toModule))
    (flat_D₄_D₅ : @Module.Flat (presheafValue D₄) (presheafValue D₅) _ _
      ((restrictionMapHom D₄ D₅ h_D₄_D₅).toModule))
    (flat_D₅_D₆ : @Module.Flat (presheafValue D₅) (presheafValue D₆) _ _
      ((restrictionMapHom D₅ D₆ h_D₅_D₆).toModule))
    (flat_D₆_D : @Module.Flat (presheafValue D₆) (presheafValue D) _ _
      ((restrictionMapHom D₆ D h_D₆_D).toModule)) :
    @Module.Flat (presheafValue E) (presheafValue D) _ _
      ((restrictionMapHom E D
        (h_D₆_D.trans (h_D₅_D₆.trans (h_D₄_D₅.trans (h_D₃_D₄.trans
          (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁))))))).toModule) := by
  have flat_E_D₆ :
      @Module.Flat (presheafValue E) (presheafValue D₆) _ _
        ((restrictionMapHom E D₆
          (h_D₅_D₆.trans (h_D₄_D₅.trans (h_D₃_D₄.trans
            (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁)))))).toModule) :=
    restrictionMap_flat_chain_six E D₁ D₂ D₃ D₄ D₅ D₆
      h_E_D₁ h_D₁_D₂ h_D₂_D₃ h_D₃_D₄ h_D₄_D₅ h_D₅_D₆
      flat_E_D₁ flat_D₁_D₂ flat_D₂_D₃ flat_D₃_D₄ flat_D₄_D₅ flat_D₅_D₆
  exact restrictionMap_flat_trans E D₆ D
    (h_D₅_D₆.trans (h_D₄_D₅.trans (h_D₃_D₄.trans (h_D₂_D₃.trans (h_D₁_D₂.trans h_E_D₁)))))
    h_D₆_D flat_E_D₆ flat_D₆_D

/-! ### T-RATIONAL-FLAT-GENERAL for LaurentNormalized D (SORRY-FREE WRAPPER)

Wire the sorry-free `relativeLaurentNormalized_equiv` (RelativeRationalLocData.lean)
into `restrictionMap_flat_of_rational_subset_via_relative` to close
T-RATIONAL-FLAT-GENERAL for any LaurentNormalized D ⊆ E rationally.

The relative equiv + intertwine are now sorry-free (T218-T227), so this
wrapper closes the algebraic-flatness step without any sorry. The caller
still must supply the canonical-form B-level hypotheses (`hb`, `hT_pb`,
`hcont_eval`, etc.) for `presheafValue_flat_of_canonical` at the E-level. -/
theorem restrictionMap_flat_of_rational_subset_laurentNormalized
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s)
    -- B-level hypotheses for `presheafValue_flat_of_canonical` at E-level.
    (hNoeth_B : IsNoetherianRing (presheafValue E))
    (hA_complete_B : @CompleteSpace (presheafValue E)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue E)))
    (hnoeth_B : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue E)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      letI : IsNoetherianRing (presheafValue E) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P E).A₀))
    -- Canonical-form hypotheses for the relative datum D_at_E.
    (hb : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      letI : DecidableEq (presheafValue E) := Classical.decEq _
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized E D hsub)))
    (hT_pb : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      letI : DecidableEq (presheafValue E) := Classical.decEq _
      ∀ t ∈ (relativeRationalLocData_laurentNormalized E D hsub).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval : letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
      letI : DecidableEq (presheafValue E) := Classical.decEq _
      letI : IsNoetherianRing (presheafValue E) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue E) :=
        presheafValue_pairOfDefinition_concrete P E
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized E D hsub).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized E D hsub)))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized E D hsub) hb)) :
    @Module.Flat (presheafValue E) (presheafValue D) _ _
      ((restrictionMapHom E D hsub).toModule) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  -- Apply via_relative with D_at_E = relativeRationalLocData_laurentNormalized.
  exact restrictionMap_flat_of_rational_subset_via_relative P E D hsub
    (relativeRationalLocData_laurentNormalized E D hsub)
    (relativeLaurentNormalized_equiv E D hsub)
    (relativeLaurentNormalized_equiv_intertwine E D hsub)
    hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
    hb hT_pb hcont_eval

/-! ### T-RATIONAL-FLAT-NORMALIZED-MINUS: flatness for `laurentMinusNormalizedDatum`

Specialization of `restrictionMap_flat_of_rational_subset_laurentNormalized`
to the case `D = laurentMinusNormalizedDatum E₀ f` (the reviewer-prescribed
substitute for the ordinary `laurentMinusDatum`). The normalized minus is
LaurentNormalized by construction (T229), so T228 applies directly with the
LaurentNormalized hypothesis discharged automatically.

The hypothesis `hf : f ∈ E₀.P.A₀` is needed for the normalized-minus to
carry `LaurentNormalized` (and for `f ∈ A₀` so the new T-element products
stay in `A₀`); it parallels Wedhorn's standard requirement for the f in
a Laurent decomposition. -/
theorem restrictionMap_flat_via_normalizedMinus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E₀ : RationalLocData A) [LaurentNormalized E₀]
    [IsNoetherianRing (locSubring E₀.P E₀.T E₀.s)]
    (f : A) (hf : f ∈ E₀.P.A₀)
    -- B-level hypotheses for `presheafValue_flat_of_canonical` at E₀-level.
    (hNoeth_B : IsNoetherianRing (presheafValue E₀))
    (hA_complete_B : @CompleteSpace (presheafValue E₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue E₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue E₀) := presheafValue_isTateRing P E₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue E₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue E₀) := presheafValue_isTateRing P E₀
      letI : IsNoetherianRing (presheafValue E₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P E₀).A₀))
    -- Canonical-form hypotheses for the relative datum for D = laurentMinusNormalizedDatum E₀ f.
    (hb : letI : IsTateRing (presheafValue E₀) := presheafValue_isTateRing P E₀
      letI : DecidableEq (presheafValue E₀) := Classical.decEq _
      letI : LaurentNormalized (laurentMinusNormalizedDatum E₀ f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized E₀ f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized E₀
          (laurentMinusNormalizedDatum E₀ f) (laurentMinusNormalized_subset E₀ f))))
    (hT_pb : letI : IsTateRing (presheafValue E₀) := presheafValue_isTateRing P E₀
      letI : DecidableEq (presheafValue E₀) := Classical.decEq _
      letI : LaurentNormalized (laurentMinusNormalizedDatum E₀ f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized E₀ f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized E₀
        (laurentMinusNormalizedDatum E₀ f) (laurentMinusNormalized_subset E₀ f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval : letI : IsTateRing (presheafValue E₀) := presheafValue_isTateRing P E₀
      letI : DecidableEq (presheafValue E₀) := Classical.decEq _
      letI : LaurentNormalized (laurentMinusNormalizedDatum E₀ f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized E₀ f hf
      letI : IsNoetherianRing (presheafValue E₀) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue E₀) :=
        presheafValue_pairOfDefinition_concrete P E₀
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized E₀
            (laurentMinusNormalizedDatum E₀ f)
            (laurentMinusNormalized_subset E₀ f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized E₀
            (laurentMinusNormalizedDatum E₀ f)
            (laurentMinusNormalized_subset E₀ f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized E₀
            (laurentMinusNormalizedDatum E₀ f)
            (laurentMinusNormalized_subset E₀ f)) hb)) :
    letI : LaurentNormalized (laurentMinusNormalizedDatum E₀ f) :=
      laurentMinusNormalizedDatum_isLaurentNormalized E₀ f hf
    @Module.Flat (presheafValue E₀)
      (presheafValue (laurentMinusNormalizedDatum E₀ f)) _ _
      ((restrictionMapHom E₀ (laurentMinusNormalizedDatum E₀ f)
        (laurentMinusNormalized_subset E₀ f)).toModule) := by
  letI : LaurentNormalized (laurentMinusNormalizedDatum E₀ f) :=
    laurentMinusNormalizedDatum_isLaurentNormalized E₀ f hf
  exact restrictionMap_flat_of_rational_subset_laurentNormalized P E₀
    (laurentMinusNormalizedDatum E₀ f) (laurentMinusNormalized_subset E₀ f)
    hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
    hb hT_pb hcont_eval

end ValuationSpectrum
