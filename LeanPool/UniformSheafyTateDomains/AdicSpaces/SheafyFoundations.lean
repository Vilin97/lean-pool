/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AffinoidRings

/-!
# Bundled rings of integral elements and pair-explicit adic spectra

Foundations for the literature-faithful sheafiness API (Wedhorn §7.3, §8.2):

* `ValuationSpectrum.RingOfIntegralElements A` — a subring of `A` bundled with the proof
  that it is a **ring of integral elements** (Wedhorn Definition 7.14(1): open, integrally
  closed in `A`, contained in `A°`). Pair-level sheafiness statements take this bundle,
  never a bare `Subring A`, so an invalid choice of `A⁺` cannot be supplied.
* `RingOfIntegralElements.toPlusSubring` — the local-instance bridge to the legacy
  instance-parametrized layer: `letI := Aplus.toPlusSubring` re-exposes the whole
  `Spa A A⁺` / `rationalOpen` / presheaf infrastructure at the selected valid choice,
  and `Aplus.instIsRingOfIntegralElements` supplies the validity instance the
  faithful theorems require.

The two chosen-pair notions this feeds (`IsSheafyFor`, `StandardSheafCondition`) live in
later files; this file is deliberately minimal so it can sit low in the import graph.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 7.14, Remark 7.15,
  Definition 7.23.
-/

namespace ValuationSpectrum

variable (A : Type*) [CommRing A] [TopologicalSpace A]

/-- A **ring of integral elements** of `A` (Wedhorn Definition 7.14(1)), bundled with its
validity proof: an open subring, integrally closed in `A`, consisting of power-bounded
elements. This is the explicit-parameter form of a valid `A⁺`; the literature-facing
pair-level sheafiness API quantifies over this type (never over bare `Subring A`). -/
def RingOfIntegralElements : Type _ :=
  {B : Subring A // IsRingOfIntegralElements B}

namespace RingOfIntegralElements

variable {A}

/-- The underlying subring of a bundled ring of integral elements. -/
@[coe] def toSubring (Aplus : RingOfIntegralElements A) : Subring A := Aplus.1

instance : CoeOut (RingOfIntegralElements A) (Subring A) := ⟨toSubring⟩

@[simp] theorem coe_mk (B : Subring A) (hB : IsRingOfIntegralElements B) :
    ((⟨B, hB⟩ : RingOfIntegralElements A) : Subring A) = B := rfl

/-- The bundled validity proof. -/
theorem isRingOfIntegralElements (Aplus : RingOfIntegralElements A) :
    IsRingOfIntegralElements (Aplus : Subring A) := Aplus.2

/-- Two bundled rings of integral elements with the same subring are equal. -/
@[ext] theorem ext {Aplus Bplus : RingOfIntegralElements A}
    (h : (Aplus : Subring A) = (Bplus : Subring A)) : Aplus = Bplus := Subtype.ext h

/-- The legacy `PlusSubring` structure selecting this bundled choice — the
local-instance bridge to the instance-parametrized layer: statements about a pair
`(A, Aplus)` install `letI := Aplus.toPlusSubring` and reuse the whole `A⁺`-based
infrastructure. Instance-reducible so `A⁺`-projections unfold under the bridge. -/
@[instance_reducible]
def toPlusSubring (Aplus : RingOfIntegralElements A) : PlusSubring A := ⟨Aplus.1⟩

/-- Under the bridge instance, the instance-chosen `A⁺` is the bundled subring. -/
theorem ringPlus_toPlusSubring (Aplus : RingOfIntegralElements A) :
    (letI := Aplus.toPlusSubring; (A⁺ : Subring A)) = (Aplus : Subring A) := rfl

/-- Under the bridge instance, the validity instance `IsRingOfIntegralElements (A⁺)`
holds — the hypothesis shape all faithful pair-level theorems consume. -/
theorem instIsRingOfIntegralElements (Aplus : RingOfIntegralElements A) :
    letI := Aplus.toPlusSubring
    IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2

/-- The **adic spectrum of the explicit pair** `Spa (A, Aplus)` (Wedhorn Definition
7.23), as a subset of `Spv A`. Definitionally `Spa A (Aplus : Subring A)` — stated once
so pair-level statements need not mention the coercion. -/
def spa (Aplus : RingOfIntegralElements A) : Set (Spv A) := Spa A (Aplus : Subring A)

theorem spa_def (Aplus : RingOfIntegralElements A) :
    Aplus.spa = Spa A (Aplus : Subring A) := rfl

/-- Under the bridge instance, the pair-explicit spectrum is the instance-based one. -/
theorem spa_toPlusSubring (Aplus : RingOfIntegralElements A) :
    (letI := Aplus.toPlusSubring; Spa A A⁺) = Aplus.spa := rfl

end RingOfIntegralElements

end ValuationSpectrum
