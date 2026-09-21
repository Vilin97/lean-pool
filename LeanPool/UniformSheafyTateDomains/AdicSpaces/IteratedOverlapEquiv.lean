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
# `presheafValue_iteratedOverlap_equiv`: presheaf-level Wedhorn 2.13 for the overlap

This file constructs the **concrete ring equivalence**
```
presheafValue (laurentOverlapDatum D₀ f) ≃+*
  presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B)
```

This is the overlap-shape analog of `presheafValue_iteratedMinus_equiv`
(in `LaurentRefinement.lean`). The structure mirrors the iteratedMinus
chain exactly:

1. Forward / backward uncompleted loc homs (forward built here; backward
   from `LaurentOverlap.iteratedOverlap_backwardToCompletion`).
2. Power-boundedness of the forward map's generators.
3. Continuity of forward via `locTopology_continuous_lift`.
4. Power-boundedness of the backward map's generators.
5. Continuity of backward.
6. Forward / backward completion homs via `UniformSpace.Completion.extensionHom`.
7. Round-trip identities via `Completion.ext'`.
8. The packaged `≃+*` (main result).

## Type-transport convention

`(iteratedOverlapDatum_B P D₀ f).s = D₀.canonicalMap f` only propositionally
(via `iteratedOverlapDatum_B_s_eq`); the literal `.s` field is `1 * canonicalMap f`.
We therefore build the forward map landing in
`Localization.Away ((iteratedOverlapDatum_B).s)` directly via
`IsLocalization.Away.lift`, using the transported instance
`IsLocalization.Away (D₀.canonicalMap f) (Localization.Away ((iteratedOverlapDatum_B).s))`.

## Main result

* `presheafValue_iteratedOverlap_equiv` — the concrete `≃+*` ring
  equivalence; no parametric hypothesis-witnesses, no sorries, no axioms.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 2.13.
* `LaurentRefinement.lean` — `presheafValue_iteratedMinus_equiv` (template).
* `LaurentOverlap.lean` — overlap forward/backward loc homs and
  `canonicalMap_b_isPowerBounded_in_overlap` helper.
-/

universe u


open Classical

namespace ValuationSpectrum

open UniformSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-! ### Phase 0: target-side IsLocalization instance via transport -/

/-- IsLocalization instance for the target localization. -/
private theorem iteratedOverlap_isLocalization_target
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  rw [iteratedOverlapDatum_B_s_eq P D₀ f hLocLift_B]; infer_instance

/-! ### Phase 1: forward uncompleted hom landing in target localization -/

private theorem iteratedOverlap_baseHom_DsTimes_f_isUnit
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    IsUnit ((algebraMap (presheafValue D₀)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))).comp
      D₀.canonicalMap (D₀.s * f)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI := iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  rw [RingHom.comp_apply, map_mul, map_mul]
  exact ((isUnit_s_in_presheafValue D₀).map _).mul
    (IsLocalization.Away.algebraMap_isUnit (D₀.canonicalMap f))

/-- Forward uncompleted hom `Loc_A(D₀.s · f) →+* Loc_B((iteratedOverlapDatum_B).s)`. -/
noncomputable def iteratedOverlap_forwardLocHom_to_B
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    Localization.Away ((laurentOverlapDatum D₀ f).s) →+*
      Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s) := by
  haveI : IsLocalization.Away (D₀.s * f)
      (Localization.Away ((laurentOverlapDatum D₀ f).s)) := by
    change IsLocalization.Away (D₀.s * f) (Localization.Away (D₀.s * f))
    infer_instance
  exact IsLocalization.Away.lift (S := Localization.Away ((laurentOverlapDatum D₀ f).s))
    (R := A) (D₀.s * f)
    (iteratedOverlap_baseHom_DsTimes_f_isUnit P D₀ f hLocLift_B)

theorem iteratedOverlap_forwardLocHom_to_B_algebraMap
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (a : A) :
    iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
      (algebraMap A (Localization.Away ((laurentOverlapDatum D₀ f).s)) a) =
      algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
        (D₀.canonicalMap a) := by
  haveI : IsLocalization.Away (D₀.s * f)
      (Localization.Away ((laurentOverlapDatum D₀ f).s)) := by
    change IsLocalization.Away (D₀.s * f) (Localization.Away (D₀.s * f))
    infer_instance
  change IsLocalization.Away.lift (D₀.s * f)
    (iteratedOverlap_baseHom_DsTimes_f_isUnit P D₀ f hLocLift_B)
    (algebraMap A (Localization.Away ((laurentOverlapDatum D₀ f).s)) a) = _
  rw [IsLocalization.Away.lift_eq]
  rfl

/-! ### Phase 2: forward loc hom power-boundedness for the overlap T -/

/-- Source-level clearing identity: in `Loc_A(D₀.s * f)`,
`divByS p (D₀.s * f) * algebraMap q = algebraMap r` whenever `p * q = (D₀.s * f) * r`. -/
private theorem divByS_mul_algebraMap_clear (D₀ : RationalLocData A) (f p q r : A)
    (h : p * q = (D₀.s * f) * r) :
    divByS p (D₀.s * f) * algebraMap A (Localization.Away (D₀.s * f)) q =
      algebraMap A (Localization.Away (D₀.s * f)) r := by
  unfold divByS
  rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
        (S := Localization.Away (D₀.s * f)) q,
      ← IsLocalization.mk'_mul,
      ← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
        (S := Localization.Away (D₀.s * f)) r]
  exact IsLocalization.mk'_eq_of_eq
    (by simp only [Submonoid.coe_mul, Submonoid.coe_one]; rw [h]; ring)

/-- Target-level fact: `algebraMap_B (canMap f) * divByS 1 s_B = 1` (the canonical
unit `canMap f` is inverted in `Loc_B(s_B)`). -/
private theorem algebraMap_canMap_f_mul_divByS_one
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    [IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))]
    (hs_B_eq : (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f) :
    algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
        (D₀.canonicalMap f) *
      divByS (1 : presheafValue D₀) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = 1 := by
  rw [hs_B_eq]; unfold divByS
  rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.canonicalMap f))
        (S := Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap f),
      ← IsLocalization.mk'_mul, mul_one, one_mul]
  exact IsLocalization.mk'_self _ _

/-- Forward image of `divByS (x * D₀.s) (D₀.s * f)`: equals
`algebraMap_B (canMap x) * divByS 1 s_B`. Shared by the `(a, b = D₀.s)` cases. -/
private theorem forward_divByS_mul_s_eq
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    [IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))]
    (hforward_alg : ∀ x : A, iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) x) =
        algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
          (D₀.canonicalMap x))
    (hs_B_eq : (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f)
    (x : A) :
    iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (divByS (x * D₀.s) (D₀.s * f)) =
      algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
        (D₀.canonicalMap x) *
      divByS (1 : presheafValue D₀) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s := by
  have hcm := congrArg (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B)
    (divByS_mul_algebraMap_clear D₀ f (x * D₀.s) f x (by ring))
  have h_mul_forward : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
      (divByS (x * D₀.s) (D₀.s * f) * algebraMap A (Localization.Away (D₀.s * f)) f) =
      iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B (divByS (x * D₀.s) (D₀.s * f)) *
      iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) f) := map_mul _ _ _
  rw [h_mul_forward, hforward_alg, hforward_alg] at hcm
  have hmm := congrArg
    (· * divByS (1 : presheafValue D₀) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s) hcm
  rwa [mul_assoc, algebraMap_canMap_f_mul_divByS_one P D₀ f hLocLift_B hs_B_eq, mul_one] at hmm

/-- Forward image of `divByS (f * f) (D₀.s * f)`: equals
`algebraMap_B (canMap f) * algebraMap_B (invS D₀)`. -/
private theorem forward_divByS_ff_eq
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    [IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))]
    (hforward_alg : ∀ x : A, iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) x) =
        algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
          (D₀.canonicalMap x))
    (hu_s_tgt : IsUnit (algebraMap (presheafValue D₀)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
      (D₀.canonicalMap D₀.s))) :
    iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (divByS (f * f) (D₀.s * f)) =
      algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
        (D₀.canonicalMap f) *
      algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) (invS D₀) := by
  set B := presheafValue D₀
  have hcm := congrArg (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B)
    (divByS_mul_algebraMap_clear D₀ f (f * f) D₀.s f (by ring))
  have h_mul_forward : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
      (divByS (f * f) (D₀.s * f) * algebraMap A (Localization.Away (D₀.s * f)) D₀.s) =
      iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B (divByS (f * f) (D₀.s * f)) *
      iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) D₀.s) := map_mul _ _ _
  rw [h_mul_forward, hforward_alg, hforward_alg] at hcm
  -- The inverse of `algebraMap_B (canMap D₀.s)` in target is `algebraMap_B (invS D₀)`.
  have hinv_canSs : D₀.canonicalMap D₀.s * invS D₀ = 1 := canonicalMap_s_mul_invS D₀
  apply hu_s_tgt.mul_right_cancel
  rw [hcm]
  -- Goal: alg(canF) * alg(canDs) = (alg(canF) * alg(invS D₀)) * alg(canDs).
  rw [mul_assoc (algebraMap B _ (D₀.canonicalMap f)) (algebraMap B _ (invS D₀))
        (algebraMap B _ (D₀.canonicalMap D₀.s)),
      mul_comm (algebraMap B _ (invS D₀)) (algebraMap B _ (D₀.canonicalMap D₀.s)),
      ← map_mul, hinv_canSs, map_one, mul_one]

/-- Forward image of `divByS (a * f) (D₀.s * f)`: equals
`algebraMap_B (coeRingHom (divByS a D₀.s))`. -/
private theorem forward_divByS_mul_f_eq
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    [IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))]
    (hforward_alg : ∀ x : A, iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) x) =
        algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
          (D₀.canonicalMap x))
    (hu_s_tgt : IsUnit (algebraMap (presheafValue D₀)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
      (D₀.canonicalMap D₀.s)))
    (a : A) :
    iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (divByS (a * f) (D₀.s * f)) =
      algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
        (D₀.coeRingHom (divByS a D₀.s)) := by
  have hcm := congrArg (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B)
    (divByS_mul_algebraMap_clear D₀ f (a * f) D₀.s a (by ring))
  have h_mul_forward : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
      (divByS (a * f) (D₀.s * f) * algebraMap A (Localization.Away (D₀.s * f)) D₀.s) =
      iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B (divByS (a * f) (D₀.s * f)) *
      iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) D₀.s) := map_mul _ _ _
  rw [h_mul_forward, hforward_alg, hforward_alg] at hcm
  have hcoeB : D₀.canonicalMap D₀.s * D₀.coeRingHom (divByS a D₀.s) = D₀.canonicalMap a := by
    change D₀.coeRingHom (algebraMap A _ D₀.s) * D₀.coeRingHom (divByS a D₀.s) =
      D₀.coeRingHom (algebraMap A _ a)
    rw [← map_mul]
    congr 1
    unfold divByS
    rw [← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
          (S := Localization.Away D₀.s) D₀.s,
        ← IsLocalization.mk'_mul,
        ← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
          (S := Localization.Away D₀.s) a]
    exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
  apply hu_s_tgt.mul_right_cancel
  rw [hcm, ← hcoeB, map_mul]; ring

/-- Generator case `a = D₀.s`: for `b ∈ {D₀.s, f}`, the forward image of
`divByS (D₀.s * b) (laurentOverlap).s` lies in the target `locSubring`. -/
private theorem iteratedOverlap_forwardLocHom_to_B_genPB_s
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    [IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))]
    (hforward_alg : ∀ x : A, iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) x) =
        algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
          (D₀.canonicalMap x))
    (hs_B_eq : (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f)
    (h1_mem_T_B : (1 : presheafValue D₀) ∈ (iteratedOverlapDatum_B P D₀ f hLocLift_B).T)
    (b : A) (hb : b ∈ ({D₀.s, f} : Finset A)) :
    iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (divByS (D₀.s * b) (laurentOverlapDatum D₀ f).s) ∈
      locSubring (iteratedOverlapDatum_B P D₀ f hLocLift_B).P
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).T
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).s := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hb_s | hb_f
  · -- `a = D₀.s, b = D₀.s`: forward = `algebraMap(canMap D₀.s) * divByS 1 s_B`.
    subst hb_s
    rw [show divByS (D₀.s * D₀.s) (laurentOverlapDatum D₀ f).s =
          divByS (D₀.s * D₀.s) (D₀.s * f) from rfl,
        forward_divByS_mul_s_eq P D₀ f hLocLift_B hforward_alg hs_B_eq D₀.s]
    refine (locSubring _ _ _).mul_mem (algebraMap_mem_locSubring _ _ _
      (canonicalMap_mem_ringOfDef D₀ (LaurentNormalized.insert_s_T_subset_A₀ D₀.s
        (Finset.mem_insert_self _ _)))) ?_
    rw [hs_B_eq]; exact divByS_mem_locSubring _ _ _ h1_mem_T_B
  · -- `a = D₀.s, b = f`: trivial (`divByS (D₀.s · f) (D₀.s · f) = 1`).
    rw [show D₀.s * b = D₀.s * f from by rw [hb_f],
        show divByS (D₀.s * f) (laurentOverlapDatum D₀ f).s = 1 from by
          unfold divByS; exact IsLocalization.mk'_self _ _, map_one]
    exact (locSubring _ _ _).one_mem

/-- Generator case `a = f`: for `b ∈ {D₀.s, f}`, the forward image of
`divByS (f * b) (laurentOverlap).s` lies in the target `locSubring`. The
`b = f` sub-case is new relative to `iteratedMinus`. -/
private theorem iteratedOverlap_forwardLocHom_to_B_genPB_f
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    [IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))]
    (hforward_alg : ∀ x : A, iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) x) =
        algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
          (D₀.canonicalMap x))
    (hs_B_eq : (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f)
    (hb_sq_mem_T_B : (D₀.canonicalMap f) * (D₀.canonicalMap f) ∈
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).T)
    (hu_s_tgt : IsUnit (algebraMap (presheafValue D₀)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
      (D₀.canonicalMap D₀.s)))
    (b : A) (hb : b ∈ ({D₀.s, f} : Finset A)) :
    iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (divByS (f * b) (laurentOverlapDatum D₀ f).s) ∈
      locSubring (iteratedOverlapDatum_B P D₀ f hLocLift_B).P
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).T
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).s := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hb_s | hb_f
  · -- `a = f, b = D₀.s`: trivial (`divByS (f · D₀.s) (D₀.s · f) = 1`).
    rw [show f * b = f * D₀.s from by rw [hb_s],
        show divByS (f * D₀.s) (laurentOverlapDatum D₀ f).s = 1 from by
          rw [show f * D₀.s = D₀.s * f from mul_comm _ _]
          unfold divByS; exact IsLocalization.mk'_self _ _, map_one]
    exact (locSubring _ _ _).one_mem
  · -- `a = f, b = f`: NEW case. forward = `algebraMap(canMap f) * algebraMap(invS D₀)`.
    rw [show f * b = f * f from by rw [hb_f],
        show divByS (f * f) (laurentOverlapDatum D₀ f).s = divByS (f * f) (D₀.s * f) from rfl,
        forward_divByS_ff_eq P D₀ f hLocLift_B hforward_alg hu_s_tgt]
    refine (locSubring _ _ _).mul_mem ?_ (algebraMap_mem_locSubring _ _ _ ?_)
    · -- `algebraMap_B (canMap f) = divByS (b · b) b ∈ locSubring`.
      rw [show algebraMap (presheafValue D₀) _ (D₀.canonicalMap f) =
            divByS (D₀.canonicalMap f * D₀.canonicalMap f)
              (iteratedOverlapDatum_B P D₀ f hLocLift_B).s from by
          rw [hs_B_eq]; unfold divByS
          rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.canonicalMap f))
                (S := Localization.Away (D₀.canonicalMap f)) (D₀.canonicalMap f)]
          exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_one, one_mul])]
      exact divByS_mem_locSubring _ _ _ hb_sq_mem_T_B
    · -- `invS D₀ ∈ P_B.A₀` via `1 ∈ D₀.T`.
      rw [invS_eq_coeRingHom_divByS_one]
      exact Subring.le_topologicalClosure _ ⟨⟨divByS (1 : A) D₀.s,
        divByS_mem_locSubring _ _ _ LaurentNormalized.one_mem_T⟩, rfl⟩

/-- Generator case `a ∈ D₀.T`: for `b ∈ {D₀.s, f}`, the forward image of
`divByS (a * b) (laurentOverlap).s` lies in the target `locSubring`. -/
private theorem iteratedOverlap_forwardLocHom_to_B_genPB_T
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    [IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))]
    (hforward_alg : ∀ x : A, iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (algebraMap A (Localization.Away (D₀.s * f)) x) =
        algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
          (D₀.canonicalMap x))
    (hs_B_eq : (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f)
    (h1_mem_T_B : (1 : presheafValue D₀) ∈ (iteratedOverlapDatum_B P D₀ f hLocLift_B).T)
    (hu_s_tgt : IsUnit (algebraMap (presheafValue D₀)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
      (D₀.canonicalMap D₀.s)))
    (a : A) (ha_T : a ∈ D₀.T)
    (b : A) (hb : b ∈ ({D₀.s, f} : Finset A)) :
    iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
        (divByS (a * b) (laurentOverlapDatum D₀ f).s) ∈
      locSubring (iteratedOverlapDatum_B P D₀ f hLocLift_B).P
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).T
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).s := by
  have hcan_a : D₀.canonicalMap a ∈ (iteratedOverlapDatum_B P D₀ f hLocLift_B).P.A₀ :=
    canonicalMap_mem_ringOfDef D₀ (LaurentNormalized.insert_s_T_subset_A₀ a
      (Finset.mem_insert_of_mem ha_T))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hb_s | hb_f
  · -- `a ∈ D₀.T, b = D₀.s`: forward = `algebraMap(canMap a) * divByS 1 s_B`.
    subst hb_s
    rw [show divByS (a * D₀.s) (laurentOverlapDatum D₀ f).s =
          divByS (a * D₀.s) (D₀.s * f) from rfl,
        forward_divByS_mul_s_eq P D₀ f hLocLift_B hforward_alg hs_B_eq a]
    refine (locSubring _ _ _).mul_mem (algebraMap_mem_locSubring _ _ _ hcan_a) ?_
    rw [hs_B_eq]; exact divByS_mem_locSubring _ _ _ h1_mem_T_B
  · -- `a ∈ D₀.T, b = f`: forward = `algebraMap(coeRingHom(divByS a D₀.s))`.
    rw [show a * b = a * f from by rw [hb_f],
        show divByS (a * f) (laurentOverlapDatum D₀ f).s =
          divByS (a * f) (D₀.s * f) from rfl,
        forward_divByS_mul_f_eq P D₀ f hLocLift_B hforward_alg hu_s_tgt a]
    refine algebraMap_mem_locSubring _ _ _ (Subring.le_topologicalClosure _ ?_)
    exact ⟨⟨divByS a D₀.s, divByS_mem_locSubring _ _ _ ha_T⟩, rfl⟩

/-- **Forward loc hom power-boundedness, overlap case.**

For each `t ∈ (laurentOverlapDatum D₀ f).T`, `iteratedOverlap_forwardLocHom_to_B`
sends `divByS t (D₀.s * f)` to an element power-bounded in
`(iteratedOverlapDatum_B P D₀ f hLocLift_B).topology`.

The overlap T = `(insert D₀.s (insert f D₀.T)) × {D₀.s, f}` decomposes elements
as `t = a * b`. Cases:

* `a = D₀.s, b = D₀.s`: forward = `algebraMap(canMap D₀.s) * divByS 1 s_B`,
  both in `locSubring`.
* `a = D₀.s, b = f`: trivial (`divByS (D₀.s · f) (D₀.s · f) = 1`).
* `a = f, b = D₀.s`: trivial (`divByS (f · D₀.s) (D₀.s · f) = 1`).
* `a = f, b = f`: NEW case. forward = `algebraMap(canMap f) * algebraMap(invS D₀)`,
  using `1 ∈ D₀.T` (via `LaurentNormalized.one_mem_T`) to put `invS D₀ ∈ P_B.A₀`.
* `a ∈ D₀.T, b = D₀.s`: forward = `algebraMap(canMap a) * divByS 1 s_B`.
* `a ∈ D₀.T, b = f`: forward = `algebraMap(coeRingHom(divByS a D₀.s))`. -/
private theorem iteratedOverlap_forwardLocHom_to_B_generators_powerBounded
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    ∀ t ∈ (laurentOverlapDatum D₀ f).T,
      @TopologicalRing.IsPowerBounded _ _
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology
        (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
          (divByS t (laurentOverlapDatum D₀ f).s)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI hloc_src : IsLocalization.Away (D₀.s * f)
      (Localization.Away ((laurentOverlapDatum D₀ f).s)) := by
    change IsLocalization.Away (D₀.s * f) (Localization.Away (D₀.s * f))
    infer_instance
  haveI hloc_tgt : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  intro t ht
  obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := Finset.mem_image.mp ht
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab_mem
  change a ∈ insert D₀.s (insert f D₀.T) at ha
  change b ∈ ({D₀.s, f} : Finset A) at hb
  change a * b = t at hab_eq
  subst hab_eq
  apply isPowerBounded_of_mem_locSubring (iteratedOverlapDatum_B P D₀ f hLocLift_B)
  -- Shared facts dispatched to the per-generator case helpers.
  have hu_s_tgt : IsUnit (algebraMap (presheafValue D₀)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
      (D₀.canonicalMap D₀.s)) := (isUnit_s_in_presheafValue D₀).map _
  have hforward_alg : ∀ x : A, iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
      (algebraMap A (Localization.Away (D₀.s * f)) x) =
      algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
        (D₀.canonicalMap x) := fun x =>
    iteratedOverlap_forwardLocHom_to_B_algebraMap P D₀ f hLocLift_B x
  -- `s_B = canonicalMap f` (propositionally).
  have hs_B_eq : (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f :=
    iteratedOverlapDatum_B_s_eq P D₀ f hLocLift_B
  have h1_mem_T_B : (1 : presheafValue D₀) ∈ (iteratedOverlapDatum_B P D₀ f hLocLift_B).T :=
    one_mem_overlapDatum_T (presheafValue D₀)
      (presheafValue_pairOfDefinition_concrete P D₀) (D₀.canonicalMap f)
  have hb_sq_mem_T_B : (D₀.canonicalMap f) * (D₀.canonicalMap f) ∈
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).T :=
    b_sq_mem_overlapDatum_T (presheafValue D₀)
      (presheafValue_pairOfDefinition_concrete P D₀) (D₀.canonicalMap f)
  -- Split by `a`, dispatching to the three generator-case helpers.
  rcases Finset.mem_insert.mp ha with ha_s | ha_rest
  · subst ha_s
    exact iteratedOverlap_forwardLocHom_to_B_genPB_s P D₀ f hLocLift_B
      hforward_alg hs_B_eq h1_mem_T_B b hb
  · rcases Finset.mem_insert.mp ha_rest with ha_f | ha_T
    · rw [show a = f from ha_f]
      exact iteratedOverlap_forwardLocHom_to_B_genPB_f P D₀ f hLocLift_B
        hforward_alg hs_B_eq hb_sq_mem_T_B hu_s_tgt b hb
    · exact iteratedOverlap_forwardLocHom_to_B_genPB_T P D₀ f hLocLift_B
        hforward_alg hs_B_eq h1_mem_T_B hu_s_tgt a ha_T b hb

/-! ### Phase 3: forward hom to completion (uncompleted) and continuity -/

/-- Forward uncompleted hom from `Loc_A((laurentOverlap).s)` to the completion
of `iteratedOverlapDatum_B`. -/
noncomputable def iteratedOverlap_forwardToCompletion
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    Localization.Away ((laurentOverlapDatum D₀ f).s) →+*
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
  (iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom.comp
    (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B)

/-- Continuity of `iteratedOverlap_forwardToCompletion` from `(laurentOverlap).topology`
to the completion. -/
theorem iteratedOverlap_forwardToCompletion_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    @Continuous _ _ (laurentOverlapDatum D₀ f).topology _
      (iteratedOverlap_forwardToCompletion P D₀ f hLocLift_B) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  letI : TopologicalSpace (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).topology
  letI : IsTopologicalRing (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isTopologicalAddGroup
  letI topB : TopologicalSpace
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology
  letI : IsTopologicalRing
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isTopologicalRing
  letI : IsTopologicalAddGroup
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isTopologicalAddGroup
  letI : UniformSpace (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).uniformSpace
  letI : IsUniformAddGroup
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isUniformAddGroup
  haveI : @NonarchimedeanRing
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) _
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology :=
    (locBasis (iteratedOverlapDatum_B P D₀ f hLocLift_B).P
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).T
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).s
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).hopen).nonarchimedean
  -- Factor: forward_to_completion = coeRingHom ∘ forward_loc_to_B.
  change @Continuous _ _ (laurentOverlapDatum D₀ f).topology _
    ((iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom.comp
      (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B))
  have hcoe : @Continuous _ _ (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology _
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom :=
    @UniformSpace.Completion.continuous_coe _
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).uniformSpace
  -- Reduce to continuity of the loc hom.
  suffices hlift : @Continuous _ _ (laurentOverlapDatum D₀ f).topology
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology
      (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B) from
    hcoe.comp hlift
  -- Apply `locTopology_continuous_lift` to the forward loc hom.
  have hf_alg : @Continuous _ _ _ (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology
      ((iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B).comp
        (algebraMap A (Localization.Away ((laurentOverlapDatum D₀ f).s)))) := by
    -- composite equals `algebraMap_B ∘ canonicalMap A`.
    have heq : (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B).comp
        (algebraMap A (Localization.Away ((laurentOverlapDatum D₀ f).s))) =
        (algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))).comp
          D₀.canonicalMap := by
      ext a
      simp only [RingHom.comp_apply]
      exact iteratedOverlap_forwardLocHom_to_B_algebraMap P D₀ f hLocLift_B a
    rw [show ⇑((iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B).comp
        (algebraMap A (Localization.Away ((laurentOverlapDatum D₀ f).s)))) =
      ⇑((algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))).comp
          D₀.canonicalMap) from
      congr_arg _ heq]
    exact (algebraMap_continuous_loc (iteratedOverlapDatum_B P D₀ f hLocLift_B)).comp
      (canonicalMap_continuous D₀)
  exact locTopology_continuous_lift (laurentOverlapDatum D₀ f).P
    (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s
    (laurentOverlapDatum D₀ f).hopen
    (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B) hf_alg
    (iteratedOverlap_forwardLocHom_to_B_generators_powerBounded P D₀ f hLocLift_B)

/-! ### Phase 4: backward loc hom generator power-boundedness -/

omit [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] in
/-- `D₀.s ∈ (laurentOverlapDatum D₀ f).T`, witnessed by `(1, D₀.s)` with
`1 ∈ insert (laurentPlusDatum D₀ f).s (laurentPlusDatum D₀ f).T` (via
`LaurentNormalized.one_mem_T`) and `D₀.s ∈ {(laurentPlusDatum D₀ f).s, f}`. -/
private theorem D₀s_mem_laurentOverlap_T
    (D₀ : RationalLocData A) [LaurentNormalized D₀] (f : A) :
    D₀.s ∈ (laurentOverlapDatum D₀ f).T := by
  classical
  change D₀.s ∈ ((insert (laurentPlusDatum D₀ f).s (laurentPlusDatum D₀ f).T).product
      ({(laurentPlusDatum D₀ f).s, f} : Finset A)).image (fun p => p.1 * p.2)
  refine Finset.mem_image.mpr ⟨(1, D₀.s), ?_, one_mul _⟩
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · -- 1 ∈ insert (laurentPlusDatum.s) (laurentPlusDatum.T) = insert D₀.s (insert f D₀.T).
    change (1 : A) ∈ insert D₀.s (insert f D₀.T)
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem LaurentNormalized.one_mem_T)
  · -- D₀.s ∈ {(laurentPlusDatum.s), f} = {D₀.s, f}.
    change D₀.s ∈ ({D₀.s, f} : Finset A)
    exact Finset.mem_insert_self _ _

omit [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] in
/-- `f * f ∈ (laurentOverlapDatum D₀ f).T`, witnessed by `(f, f)` with
`f ∈ insert (laurentPlusDatum D₀ f).s (laurentPlusDatum D₀ f).T = insert D₀.s (insert f D₀.T)`
and `f ∈ {(laurentPlusDatum D₀ f).s, f}`. -/
private theorem f_sq_mem_laurentOverlap_T
    (D₀ : RationalLocData A) (f : A) :
    f * f ∈ (laurentOverlapDatum D₀ f).T := by
  classical
  change f * f ∈ ((insert (laurentPlusDatum D₀ f).s (laurentPlusDatum D₀ f).T).product
      ({(laurentPlusDatum D₀ f).s, f} : Finset A)).image (fun p => p.1 * p.2)
  refine Finset.mem_image.mpr ⟨(f, f), ?_, rfl⟩
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · change f ∈ insert D₀.s (insert f D₀.T)
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · change f ∈ ({D₀.s, f} : Finset A)
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **Backward loc hom power-boundedness, overlap case.**

For each `t ∈ (iteratedOverlapDatum_B P D₀ f hLocLift_B).T = {1, canonicalMap f,
(canonicalMap f)²}`, `iteratedOverlap_backwardToCompletion` sends
`divByS t (iteratedOverlapDatum_B).s` to a power-bounded element of
`presheafValue (laurentOverlapDatum D₀ f)`.

Cases:
* `t = 1`: backward = `((laurentOverlap).canMap f)⁻¹ = coeRingHom(divByS D₀.s (D₀.s · f))`;
  `D₀.s ∈ (laurentOverlap).T` (via `D₀s_mem_laurentOverlap_T`).
* `t = canonicalMap f`: backward = `(laurentOverlap).canMap f = coeRingHom(algebraMap_A f)`;
  `algebraMap_A f = divByS (f²) (D₀.s · f) · algebraMap_A D₀.s` with `f² ∈ T`.
* `t = (canonicalMap f)²`: same as above. -/
private theorem iteratedOverlap_backwardToCompletion_generators_powerBounded
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    ∀ t ∈ (iteratedOverlapDatum_B P D₀ f hLocLift_B).T,
      TopologicalRing.IsPowerBounded
        (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub
          (divByS t (iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI hloc_tgt : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  intro t ht
  -- `(iteratedOverlapDatum_B).T = (insert 1 {canMap f}) × {1, canMap f}` image.
  -- Unpack `t = x · y` with `x ∈ insert 1 {canMap f}`, `y ∈ {1, canMap f}`.
  set B := presheafValue D₀
  set b := D₀.canonicalMap f with hb_def
  -- Helper for membership: `ht` is in the explicit image-product form via unfolding.
  obtain ⟨⟨x, y⟩, hxy_mem, hxy_eq⟩ := Finset.mem_image.mp ht
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy_mem
  -- After unfolding, `x ∈ insert 1 {b}` and `y ∈ {1, b}` (where `b = canMap f`).
  change x ∈ (insert (1 : B) {b} : Finset B) at hx
  change y ∈ ({1, b} : Finset B) at hy
  -- `hxy_eq : (x, y).1 * (x, y).2 = t`. Simplify the prod projections.
  simp only at hxy_eq
  rw [← hxy_eq]
  clear hxy_eq
  -- `hs_B_eq : (iteratedOverlapDatum_B).s = canonicalMap f = b`.
  have hs_B_eq : (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = b :=
    iteratedOverlapDatum_B_s_eq P D₀ f hLocLift_B
  -- `divByS t s_B` is computed via algebraic identities.
  -- Key: the backward map sends `divByS t b` to `restrictionMap(t)` when `t ∈ A₀_B`.
  -- For `t = 1`: divByS 1 b = (algebraMap b)⁻¹; backward = ((laurentOverlap).canMap f)⁻¹.
  -- For `t = b`: divByS b b = algebraMap b; backward = (laurentOverlap).canMap f.
  -- For `t = b · b`: divByS (b·b) b = algebraMap b; backward = (laurentOverlap).canMap f.
  -- Useful: `algebraMap_A f = divByS (f²) (D₀.s · f) · algebraMap_A D₀.s` in Loc_A(D₀.s · f).
  have halg_A_f : algebraMap A (Localization.Away (D₀.s * f)) f =
      divByS (f * f) (D₀.s * f) * algebraMap A (Localization.Away (D₀.s * f)) D₀.s := by
    unfold divByS
    rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
          (S := Localization.Away (D₀.s * f)) D₀.s,
        ← IsLocalization.mk'_mul,
        ← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
          (S := Localization.Away (D₀.s * f)) f]
    exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
  -- Show `(laurentOverlap).canMap f ∈ coeRingHom '' locSubring(laurentOverlap)`,
  -- and similarly for the inverse.
  have hAlg_f_in_loc : algebraMap A (Localization.Away (D₀.s * f)) f ∈
      locSubring (laurentOverlapDatum D₀ f).P (laurentOverlapDatum D₀ f).T
        (laurentOverlapDatum D₀ f).s := by
    rw [halg_A_f]
    refine (locSubring _ _ _).mul_mem ?_ ?_
    · -- divByS (f²) (D₀.s · f) — uses `f² ∈ (laurentOverlap).T`.
      exact divByS_mem_locSubring _ _ _ (f_sq_mem_laurentOverlap_T D₀ f)
    · -- algebraMap D₀.s — uses `D₀.s ∈ D₀.P.A₀ = (laurentOverlap).P.A₀`.
      have hDs_A₀ : D₀.s ∈ D₀.P.A₀ := LaurentNormalized.insert_s_T_subset_A₀ D₀.s
        (Finset.mem_insert_self _ _)
      have hDs_A₀_overlap : D₀.s ∈ (laurentOverlapDatum D₀ f).P.A₀ := hDs_A₀
      exact algebraMap_mem_locSubring _ _ _ hDs_A₀_overlap
  have hCanF_pb : TopologicalRing.IsPowerBounded
      ((laurentOverlapDatum D₀ f).canonicalMap f) := by
    -- (laurentOverlap).canMap f = coeRingHom(algebraMap_A f); image lies in
    -- coeRingHom '' locSubring, a bounded subring (closed under powers).
    have hcoeF : (laurentOverlapDatum D₀ f).canonicalMap f =
        (laurentOverlapDatum D₀ f).coeRingHom
          (algebraMap A (Localization.Away (D₀.s * f)) f) := rfl
    rw [hcoeF]
    apply (CompletionLocalization.coeRingHom_image_locSubring_isBounded
      (laurentOverlapDatum D₀ f)).subset
    rintro _ ⟨n, rfl⟩
    change ((laurentOverlapDatum D₀ f).coeRingHom
      (algebraMap A (Localization.Away (D₀.s * f)) f)) ^ n ∈ _
    rw [← map_pow]
    exact ⟨_, (locSubring _ _ _).pow_mem hAlg_f_in_loc n, rfl⟩
  -- Inverse: `((laurentOverlap).canMap f)⁻¹ = coeRingHom (divByS D₀.s (D₀.s · f))`.
  have hDsDivMem : divByS D₀.s (D₀.s * f) ∈ locSubring
      (laurentOverlapDatum D₀ f).P (laurentOverlapDatum D₀ f).T
      (laurentOverlapDatum D₀ f).s :=
    divByS_mem_locSubring _ _ _ (D₀s_mem_laurentOverlap_T D₀ f)
  have hInvF_pb : TopologicalRing.IsPowerBounded
      ((laurentOverlapDatum D₀ f).coeRingHom (divByS D₀.s (D₀.s * f))) := by
    apply (CompletionLocalization.coeRingHom_image_locSubring_isBounded
      (laurentOverlapDatum D₀ f)).subset
    rintro _ ⟨n, rfl⟩
    change ((laurentOverlapDatum D₀ f).coeRingHom (divByS D₀.s (D₀.s * f))) ^ n ∈ _
    rw [← map_pow]
    exact ⟨_, (locSubring _ _ _).pow_mem hDsDivMem n, rfl⟩
  -- Useful: `backward(algebraMap_B b)` for `b : B`.
  have hbwd_algMap : ∀ z : B, iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub
      (algebraMap B (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) z) =
      restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub z := fun z =>
    iteratedOverlap_backwardToCompletion_algebraMap P D₀ f hLocLift_B hsub z
  -- Split by `x ∈ {1, b}`.
  rcases Finset.mem_insert.mp hx with hx_one | hx_b
  · subst hx_one
    -- `x = 1`.
    rcases Finset.mem_insert.mp hy with hy_one | hy_b
    · subst hy_one
      -- `x = 1, y = 1`: `t = 1 · 1 = 1`. divByS 1 s_B = inverse of algebraMap_B b.
      -- backward(divByS 1 s_B) = inverse of (laurentOverlap).canMap f.
      change TopologicalRing.IsPowerBounded
        (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub
          (divByS (1 * 1) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
      have hone : (1 : B) * 1 = 1 := mul_one _
      rw [hone]
      -- Show backward(divByS 1 s_B) = coeRingHom(divByS D₀.s (D₀.s·f)).
      have hinv_target : divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s *
          algebraMap B
            (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) b = 1 := by
        rw [hs_B_eq]; unfold divByS
        rw [mul_comm, ← IsLocalization.mk'_one (M := Submonoid.powers b)
              (S := Localization.Away b) b,
            ← IsLocalization.mk'_mul, mul_one, one_mul]
        exact IsLocalization.mk'_self _ _
      have hbwd_inv : iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub
          (divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s) *
          (laurentOverlapDatum D₀ f).canonicalMap f = 1 := by
        -- Apply backward to `hinv_target`.
        have := congrArg (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub) hinv_target
        rw [map_mul, map_one, hbwd_algMap, restrictionMapHom_canonicalMap] at this
        exact this
      -- backward(divByS 1 s_B) = ((laurentOverlap).canMap f)⁻¹.
      have hu_canF : IsUnit ((laurentOverlapDatum D₀ f).canonicalMap f) :=
        canonicalMap_f_isUnit_in_laurentOverlap D₀ f
      -- Apply mul_right_cancel: backward(divByS 1 s_B) = coeRingHom(divByS D₀.s (D₀.s·f)).
      have hinv_overlap : (laurentOverlapDatum D₀ f).coeRingHom (divByS D₀.s (D₀.s * f)) *
          (laurentOverlapDatum D₀ f).canonicalMap f = 1 := by
        -- `algebraMap f = mk' f 1`, `divByS D₀.s (D₀.s * f) = mk' D₀.s ⟨D₀.s * f, _⟩`.
        -- Their product is `mk' (D₀.s · f) ⟨D₀.s · f, _⟩ = 1`.
        have hsrc : divByS D₀.s (D₀.s * f) *
            algebraMap A (Localization.Away (D₀.s * f)) f = 1 := by
          have hu_Dsf : IsUnit (algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f)) :=
            IsLocalization.Away.algebraMap_isUnit _
          -- algebraMap f * algebraMap D₀.s = algebraMap (D₀.s · f); inverse = divByS 1.
          have hsf_inv : algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f) *
              divByS (1 : A) (D₀.s * f) = 1 := by
            unfold divByS
            rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
                  (S := Localization.Away (D₀.s * f)) (D₀.s * f),
                ← IsLocalization.mk'_mul, mul_one, one_mul]
            exact IsLocalization.mk'_self _ _
          -- divByS D₀.s (D₀.s · f) = algebraMap D₀.s · divByS 1 (D₀.s · f).
          have hDs_mul : algebraMap A (Localization.Away (D₀.s * f)) D₀.s *
              divByS (1 : A) (D₀.s * f) = divByS D₀.s (D₀.s * f) := by
            unfold divByS
            rw [← IsLocalization.mk'_one (M := Submonoid.powers (D₀.s * f))
                  (S := Localization.Away (D₀.s * f)) D₀.s,
                ← IsLocalization.mk'_mul, one_mul, mul_one]
          -- Goal: divByS D₀.s (D₀.s · f) · algebraMap f = 1.
          rw [← hDs_mul, mul_assoc, mul_comm (divByS (1 : A) (D₀.s * f)) _,
              ← mul_assoc, ← map_mul]
          change algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f) *
            divByS (1 : A) (D₀.s * f) = 1
          exact hsf_inv
        have h2 : (laurentOverlapDatum D₀ f).coeRingHom
            (divByS D₀.s (D₀.s * f) *
              algebraMap A (Localization.Away (D₀.s * f)) f) =
            (laurentOverlapDatum D₀ f).coeRingHom 1 :=
          congrArg _ hsrc
        rw [show (laurentOverlapDatum D₀ f).coeRingHom
            (divByS D₀.s (D₀.s * f) *
              algebraMap A (Localization.Away (D₀.s * f)) f) =
            (laurentOverlapDatum D₀ f).coeRingHom (divByS D₀.s (D₀.s * f)) *
            (laurentOverlapDatum D₀ f).coeRingHom
              (algebraMap A (Localization.Away (D₀.s * f)) f) from
          map_mul _ _ _, map_one] at h2
        exact h2
      have hbwd_eq : iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub
          (divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s) =
          (laurentOverlapDatum D₀ f).coeRingHom (divByS D₀.s (D₀.s * f)) := by
        apply hu_canF.mul_right_cancel
        rw [hbwd_inv, hinv_overlap]
      rw [hbwd_eq]
      exact hInvF_pb
    · -- `x = 1, y = b`: t = 1 · b = b. divByS b b = 1. Trivial.
      rw [show (1 : B) * y = y from one_mul y]
      simp only [Finset.mem_singleton] at hy_b
      subst hy_b
      have hdiv1 : divByS (b : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = 1 := by
        rw [hs_B_eq]; unfold divByS
        exact IsLocalization.mk'_self _ _
      rw [hdiv1, map_one]
      exact TopologicalRing.isPowerBounded_one
  · -- `x = b`.
    simp only [Finset.mem_singleton] at hx_b
    subst hx_b
    rcases Finset.mem_insert.mp hy with hy_one | hy_b
    · subst hy_one
      -- `x = b, y = 1`: t = b · 1 = b. divByS b b = 1.
      rw [show (b : B) * 1 = b from mul_one b]
      have hdiv1 : divByS (b : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = 1 := by
        rw [hs_B_eq]; unfold divByS
        exact IsLocalization.mk'_self _ _
      rw [hdiv1, map_one]
      exact TopologicalRing.isPowerBounded_one
    · -- `x = b, y = b`: t = b · b = b². divByS (b · b) b = algebraMap_B b.
      simp only [Finset.mem_singleton] at hy_b
      subst hy_b
      have halg_b_eq : divByS ((b : B) * b) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s =
          algebraMap B (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) b := by
        rw [hs_B_eq]; unfold divByS
        rw [← IsLocalization.mk'_one (M := Submonoid.powers b)
              (S := Localization.Away b) b]
        apply IsLocalization.mk'_eq_of_eq
        simp only [Submonoid.coe_one, one_mul]
      rw [halg_b_eq, hbwd_algMap, restrictionMapHom_canonicalMap]
      exact hCanF_pb

/-! ### Phase 5: backward loc hom continuity -/

/-- Continuity of `iteratedOverlap_backwardToCompletion` from
`(iteratedOverlapDatum_B).topology` to the completion of `laurentOverlapDatum`. -/
theorem iteratedOverlap_backwardToCompletion_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    @Continuous _ _ (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology _
      (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI hloc_tgt : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  letI : TopologicalSpace
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology
  letI : IsTopologicalRing
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isTopologicalRing
  haveI : NonarchimedeanRing (presheafValue (laurentOverlapDatum D₀ f)) :=
    presheafValueNonarchimedeanRing (laurentOverlapDatum D₀ f)
  -- Continuity of `backwardToCompletion ∘ algebraMap B`: equals `restrictionMapHom`.
  have hf_alg : @Continuous _ _ _ _
      ((iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)))) := by
    have heq : (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))) =
        restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub := by
      ext b
      simp only [RingHom.comp_apply]
      exact iteratedOverlap_backwardToCompletion_algebraMap P D₀ f hLocLift_B hsub b
    rw [show ⇑((iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub).comp
        (algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)))) =
      ⇑(restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub) from
      congr_arg _ heq]
    exact restrictionMapHom_continuous D₀ (laurentOverlapDatum D₀ f) hsub
  exact locTopology_continuous_lift (iteratedOverlapDatum_B P D₀ f hLocLift_B).P
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).T
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).s
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).hopen
    (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub) hf_alg
    (iteratedOverlap_backwardToCompletion_generators_powerBounded P D₀ f hLocLift_B hsub)

/-! ### Phase 5b: round trip at the uncompleted level for `_to_B` -/

/-- `backwardToCompletion ∘ forwardLocHom_to_B = (laurentOverlap).coeRingHom`. -/
private theorem iteratedOverlap_backwardToCompletion_comp_forwardLocHom_to_B
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub).comp
      (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B) =
      (laurentOverlapDatum D₀ f).coeRingHom := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI hloc_src : IsLocalization.Away (D₀.s * f)
      (Localization.Away ((laurentOverlapDatum D₀ f).s)) := by
    change IsLocalization.Away (D₀.s * f) (Localization.Away (D₀.s * f))
    infer_instance
  haveI hloc_tgt : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  apply IsLocalization.ringHom_ext (Submonoid.powers (D₀.s * f))
  ext a
  simp only [RingHom.comp_apply, iteratedOverlap_forwardLocHom_to_B_algebraMap,
    iteratedOverlap_backwardToCompletion_algebraMap, restrictionMapHom_canonicalMap]
  rfl

/-! ### Phase 6: forward and backward completion homs -/

/-- The forward completion hom (overlap branch): `extensionHom` of
`iteratedOverlap_forwardToCompletion`. -/
noncomputable def iteratedOverlap_forwardHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    presheafValue (laurentOverlapDatum D₀ f) →+*
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
  letI : UniformSpace (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isTopologicalRing
  UniformSpace.Completion.extensionHom
    (iteratedOverlap_forwardToCompletion P D₀ f hLocLift_B)
    (iteratedOverlap_forwardToCompletion_continuous P D₀ f hLocLift_B)

/-- The backward completion hom (overlap branch): `extensionHom` of
`iteratedOverlap_backwardToCompletion`. -/
noncomputable def iteratedOverlap_backwardHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) →+*
      presheafValue (laurentOverlapDatum D₀ f) :=
  letI : UniformSpace
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).uniformSpace
  letI : IsUniformAddGroup
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isUniformAddGroup
  letI : IsTopologicalRing
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isTopologicalRing
  UniformSpace.Completion.extensionHom
    (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub)
    (iteratedOverlap_backwardToCompletion_continuous P D₀ f hLocLift_B hsub)

/-- Forward completion hom on `coeRingHom a`. -/
theorem iteratedOverlap_forwardHom_coeRingHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (a : Localization.Away ((laurentOverlapDatum D₀ f).s)) :
    iteratedOverlap_forwardHom P D₀ f hLocLift_B
        ((laurentOverlapDatum D₀ f).coeRingHom a) =
      iteratedOverlap_forwardToCompletion P D₀ f hLocLift_B a := by
  letI : UniformSpace (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isTopologicalRing
  exact UniformSpace.Completion.extensionHom_coe _ _ a

/-- Backward completion hom on `coeRingHom b`. -/
theorem iteratedOverlap_backwardHom_coeRingHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (b : Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :
    iteratedOverlap_backwardHom P D₀ f hLocLift_B hsub
        ((iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom b) =
      iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub b := by
  letI : UniformSpace
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).uniformSpace
  letI : IsUniformAddGroup
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isUniformAddGroup
  letI : IsTopologicalRing
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isTopologicalRing
  exact UniformSpace.Completion.extensionHom_coe _ _ b

/-! ### Phase 7: round-trip identities -/

/-- Round-trip 1 (overlap branch): `backwardHom ∘ forwardHom = id`. -/
theorem iteratedOverlap_backwardHom_comp_forwardHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedOverlap_backwardHom P D₀ f hLocLift_B hsub).comp
      (iteratedOverlap_forwardHom P D₀ f hLocLift_B) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isTopologicalRing
  letI : UniformSpace
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).uniformSpace
  letI : IsUniformAddGroup
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isUniformAddGroup
  letI : IsTopologicalRing
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isTopologicalRing
  apply RingHom.ext
  intro x
  change iteratedOverlap_backwardHom P D₀ f hLocLift_B hsub
    (iteratedOverlap_forwardHom P D₀ f hLocLift_B x) = x
  refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro a
  change iteratedOverlap_backwardHom P D₀ f hLocLift_B hsub
      (iteratedOverlap_forwardHom P D₀ f hLocLift_B
        ((laurentOverlapDatum D₀ f).coeRingHom a)) =
    (laurentOverlapDatum D₀ f).coeRingHom a
  rw [iteratedOverlap_forwardHom_coeRingHom,
      show iteratedOverlap_forwardToCompletion P D₀ f hLocLift_B a =
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom
          (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B a) from rfl,
      iteratedOverlap_backwardHom_coeRingHom]
  exact congr_fun (congrArg DFunLike.coe
    (iteratedOverlap_backwardToCompletion_comp_forwardLocHom_to_B P D₀ f hLocLift_B hsub)) a

/-- Helper: `forwardHom ∘ restrictionMapHom = (iteratedOverlapDatum_B).canonicalMap`
as a continuous ring hom `presheafValue D₀ → presheafValue (iteratedOverlapDatum_B)`. -/
theorem iteratedOverlap_forwardHom_comp_restrictionMapHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedOverlap_forwardHom P D₀ f hLocLift_B).comp
        (restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub) =
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).canonicalMap := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI hloc_src : IsLocalization.Away (D₀.s * f)
      (Localization.Away ((laurentOverlapDatum D₀ f).s)) := by
    change IsLocalization.Away (D₀.s * f) (Localization.Away (D₀.s * f))
    infer_instance
  haveI hloc_tgt : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isTopologicalRing
  letI : UniformSpace
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).uniformSpace
  letI : IsUniformAddGroup
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isUniformAddGroup
  letI : IsTopologicalRing
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isTopologicalRing
  apply RingHom.ext
  intro b
  -- Apply Completion.ext' on b : presheafValue D₀.
  let lhsFun : presheafValue D₀ →
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
    fun y => iteratedOverlap_forwardHom P D₀ f hLocLift_B
      (restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub y)
  let rhsFun : presheafValue D₀ →
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
    fun y => (iteratedOverlapDatum_B P D₀ f hLocLift_B).canonicalMap y
  change lhsFun b = rhsFun b
  refine @UniformSpace.Completion.ext' (Localization.Away D₀.s) D₀.uniformSpace
    (presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B)) _ _ lhsFun rhsFun ?_ ?_ ?_ b
  · exact UniformSpace.Completion.continuous_extension.comp
      (restrictionMapHom_continuous D₀ (laurentOverlapDatum D₀ f) hsub)
  · exact canonicalMap_continuous (iteratedOverlapDatum_B P D₀ f hLocLift_B)
  intro a
  change lhsFun (D₀.coeRingHom a) = rhsFun (D₀.coeRingHom a)
  simp only [lhsFun, rhsFun]
  -- Reduce via IsLocalization.ringHom_ext on a : Loc(D₀.s).
  let lhsHom : Localization.Away D₀.s →+*
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
    (iteratedOverlap_forwardHom P D₀ f hLocLift_B).comp
      ((restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub).comp D₀.coeRingHom)
  let rhsHom : Localization.Away D₀.s →+*
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
    ((iteratedOverlapDatum_B P D₀ f hLocLift_B).canonicalMap).comp D₀.coeRingHom
  suffices h : lhsHom = rhsHom by
    have hcong := congr_fun (congrArg DFunLike.coe h) a
    change lhsHom a = rhsHom a
    exact hcong
  apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
  ext c
  change iteratedOverlap_forwardHom P D₀ f hLocLift_B
      (restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub
        (D₀.canonicalMap c)) =
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).canonicalMap (D₀.canonicalMap c)
  rw [restrictionMapHom_canonicalMap]
  change iteratedOverlap_forwardHom P D₀ f hLocLift_B
      ((laurentOverlapDatum D₀ f).coeRingHom (algebraMap A _ c)) =
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).canonicalMap (D₀.canonicalMap c)
  rw [iteratedOverlap_forwardHom_coeRingHom]
  change (iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom
      (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B (algebraMap A _ c)) =
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).canonicalMap (D₀.canonicalMap c)
  rw [iteratedOverlap_forwardLocHom_to_B_algebraMap]
  rfl

/-- Round-trip 2 (overlap branch): `forwardHom ∘ backwardHom = id`. -/
theorem iteratedOverlap_forwardHom_comp_backwardHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedOverlap_forwardHom P D₀ f hLocLift_B).comp
        (iteratedOverlap_backwardHom P D₀ f hLocLift_B hsub) =
      RingHom.id _ := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI hloc_tgt : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away ((laurentOverlapDatum D₀ f).s)) :=
    (laurentOverlapDatum D₀ f).isTopologicalRing
  letI : UniformSpace
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).uniformSpace
  letI : IsUniformAddGroup
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isUniformAddGroup
  letI : IsTopologicalRing
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).isTopologicalRing
  apply RingHom.ext
  intro x
  change iteratedOverlap_forwardHom P D₀ f hLocLift_B
    (iteratedOverlap_backwardHom P D₀ f hLocLift_B hsub x) = x
  refine @UniformSpace.Completion.ext'
    (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro y
  change iteratedOverlap_forwardHom P D₀ f hLocLift_B
      (iteratedOverlap_backwardHom P D₀ f hLocLift_B hsub
        ((iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom y)) =
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom y
  rw [iteratedOverlap_backwardHom_coeRingHom]
  -- Reduce to y = algebraMap b for b : presheafValue D₀.
  let lhsHom : Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s) →+*
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
    (iteratedOverlap_forwardHom P D₀ f hLocLift_B).comp
      (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub)
  let rhsHom : Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s) →+*
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom
  suffices h : lhsHom = rhsHom by
    have hcong := congr_fun (congrArg DFunLike.coe h) y
    change lhsHom y = rhsHom y
    exact hcong
  apply IsLocalization.ringHom_ext (Submonoid.powers (D₀.canonicalMap f))
  ext b
  change iteratedOverlap_forwardHom P D₀ f hLocLift_B
      (iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub
        (algebraMap (presheafValue D₀) _ b)) =
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).coeRingHom
      (algebraMap (presheafValue D₀) _ b)
  rw [iteratedOverlap_backwardToCompletion_algebraMap]
  -- Goal: forwardHom (restrictionMapHom b) = (iteratedOverlapDatum_B).canonicalMap b.
  exact congr_fun (congrArg DFunLike.coe
    (iteratedOverlap_forwardHom_comp_restrictionMapHom P D₀ f hLocLift_B hsub)) b

/-! ### Phase 8: the packaged ring equiv -/

/-- **Iterated rational identification, overlap branch (Wedhorn Lemma 2.13)**.

The concrete ring equivalence:
```
presheafValue (laurentOverlapDatum D₀ f) ≃+*
  presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B)
```

This is the overlap-shape analog of `presheafValue_iteratedMinus_equiv`. It is
the unconditional (sorry-free, axiom-free) construction discharging the
residual `overlapBridge_eq` hypothesis in `LaneAReverseRoundTrip.laneA_τ_preBiv`. -/
noncomputable def presheafValue_iteratedOverlap_equiv
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    presheafValue (laurentOverlapDatum D₀ f) ≃+*
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
  let hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s :=
    (laurentOverlap_subset_minus D₀ f).trans (laurentMinus_subset D₀ f)
  { toFun := iteratedOverlap_forwardHom P D₀ f hLocLift_B
    invFun := iteratedOverlap_backwardHom P D₀ f hLocLift_B hsub
    left_inv := fun x =>
      congr_fun (congrArg DFunLike.coe
        (iteratedOverlap_backwardHom_comp_forwardHom P D₀ f hLocLift_B hsub)) x
    right_inv := fun y =>
      congr_fun (congrArg DFunLike.coe
        (iteratedOverlap_forwardHom_comp_backwardHom P D₀ f hLocLift_B hsub)) y
    map_mul' := map_mul _
    map_add' := map_add _ }

end ValuationSpectrum
