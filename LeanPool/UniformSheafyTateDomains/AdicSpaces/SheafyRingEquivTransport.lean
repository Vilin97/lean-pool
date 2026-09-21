/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRing
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RingEquivPresheafTransport

/-!
# Public transport of sheafiness along a bicontinuous ring equivalence (T7)

The literature-facing endpoints of the ring-equivalence transport: for an
isomorphism of complete Tate topological rings `e : A ≃+* B` (a ring equivalence
continuous in both directions),

* `isSheafyFor_mapRingEquiv` — pair-level sheafiness pushes forward:
  `IsSheafyFor A Aplus → IsSheafyFor B (Aplus.map e)`;
* `isSheafyFor_equiv` — the two-sided form, an `↔` (via the plus-ring
  roundtrip `RingOfIntegralElements.map_symm_map`);
* `isSheafyComplete_congr` — ring-level sheafiness (every valid ring of
  integral elements) is invariant: `IsSheafyComplete A ↔ IsSheafyComplete B`.

Distinguish `isSheafyFor_equiv` from `isSheafyFor_congr`
(`RelativeStandardRefinement.lean`): the latter changes only the plus ring on
one fixed underlying ring; this file changes the ring itself.

The signatures carry only the two complete-Tate topological stacks and the
bicontinuous ring equivalence — no `PlusSubring`, no ambient
`IsRingOfIntegralElements` instance, no `HasLocLiftPowerBounded`, no
`CompatiblePlusSubring`, no `DecidableEq`, no noetherian hypotheses. The proofs
route through the internal criterion (`isSheafy_iff_isLimitSheaf` and the T6
transport `isSheafy_mapRingEquiv`); every legacy instance is installed `letI`/
`haveI`-locally inside the proof bodies.

This module sits *above* `SheafyRing.lean` — the low-level transport file
(`RingEquivPresheafTransport.lean`) deliberately does not import the sheafy-pair
layer, avoiding a foundational import cycle.
-/

noncomputable section

namespace ValuationSpectrum

universe u v

variable {A : Type u} {B : Type v}
  [CommRing A] [TopologicalSpace A] [IsTateRing A] [T2Space A]
  [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
  [CommRing B] [TopologicalSpace B] [IsTateRing B] [T2Space B]
  [NonarchimedeanRing B]
  [letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B; CompleteSpace B]

/-- **Pair-level sheafiness pushes forward along a bicontinuous ring
equivalence** (T7): if the genuine all-open structure presheaf of
`Spa (A, Aplus)` is a sheaf of topological rings, so is that of
`Spa (B, Aplus.map e)`. -/
theorem isSheafyFor_mapRingEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (Aplus : RingOfIntegralElements A)
    (h : IsSheafyFor A Aplus) :
    IsSheafyFor B (RingOfIntegralElements.map e he he' Aplus) := by
  classical
  -- 1–2: install the source pair and the mapped target pair
  letI := Aplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
  letI := (RingOfIntegralElements.map e he he' Aplus).toPlusSubring
  haveI : IsRingOfIntegralElements (B⁺ : Subring B) :=
    (RingOfIntegralElements.map e he he' Aplus).2
  -- 3: both faithful restriction-map packages, locally
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  haveI : HasLocLiftPowerBounded B := hasLocLiftPowerBounded_faithful
  -- 4: convert `IsLimitSheaf` to the internal criterion
  haveI : IsSheafy A := isSheafy_of_isLimitSheaf h
  -- 5: the T6 transport (the mapped plus ring is definitionally the image)
  haveI : IsSheafy B := isSheafy_mapRingEquiv e he he' rfl
  -- 6: convert back
  show IsLimitSheaf B
  exact isLimitSheaf_of_isSheafy

/-- **Pair-level sheafiness transports as an equivalence** (T7): sheafiness of
`(A, Aplus)` is equivalent to sheafiness of `(B, Aplus.map e)`. Both directions
are the one-way transport; the backward direction is normalized with the
plus-ring roundtrip `RingOfIntegralElements.map_symm_map`. -/
theorem isSheafyFor_equiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (Aplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus ↔
      IsSheafyFor B (RingOfIntegralElements.map e he he' Aplus) := by
  refine ⟨isSheafyFor_mapRingEquiv e he he' Aplus, fun h => ?_⟩
  have h' := isSheafyFor_mapRingEquiv e.symm he' he
    (RingOfIntegralElements.map e he he' Aplus) h
  rwa [RingOfIntegralElements.map_symm_map] at h'

/-- **Ring-level sheafiness is invariant under bicontinuous ring equivalences**
(T7): a complete Tate ring is sheafy for every valid ring of integral elements
iff its isomorphic image is. Arbitrary valid plus rings move in both directions
through `RingOfIntegralElements.congr`. -/
theorem isSheafyComplete_congr (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) :
    IsSheafyComplete A ↔ IsSheafyComplete B := by
  constructor
  · intro h Bplus
    have hB := (isSheafyFor_equiv e he he'
      ((RingOfIntegralElements.congr e he he').symm Bplus)).mp
      (h ((RingOfIntegralElements.congr e he he').symm Bplus))
    rwa [show RingOfIntegralElements.map e he he'
        ((RingOfIntegralElements.congr e he he').symm Bplus) = Bplus from
      (RingOfIntegralElements.congr e he he').apply_symm_apply Bplus] at hB
  · intro h Aplus
    exact (isSheafyFor_equiv e he he' Aplus).mpr
      (h (RingOfIntegralElements.map e he he' Aplus))

end ValuationSpectrum
