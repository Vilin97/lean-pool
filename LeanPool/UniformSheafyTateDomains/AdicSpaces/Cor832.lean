/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Algebra.Module.Pi
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaRationalOpenComparison
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FlatnessResults
import LeanPool.UniformSheafyTateDomains.AdicSpaces.IdealClosedness
import LeanPool.UniformSheafyTateDomains.AdicSpaces.IdealLocalization
import LeanPool.UniformSheafyTateDomains.AdicSpaces.IdealLocalizationCompletion
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictionFlatness

/-!
# Corollary 8.32 of Wedhorn (faithful flatness of product restriction)

**Statement (Wedhorn Cor 8.32, p. 83)**: Let `(A, A⁺)` be a strongly noetherian
Tate affinoid ring, `X = Spa A`, and `(U_i)_{1 ≤ i ≤ n}` a finite covering of
`X` by rational subsets. The homomorphism
`𝒪_X(X) → ∏_i 𝒪_X(U_i)` given by restriction is faithfully flat (in
particular injective).

## Approach

Wedhorn's proof has two ingredients:
1. **Flatness** (Prop 8.30): each restriction map `𝒪_X(X) → 𝒪_X(U_i)` is flat.
2. **Lying over** (lifting of primes): every prime `𝔭` of `𝒪_X(X)` is the image
   (under `comap`) of some prime of the product.

Given that `𝒪_X(U_i) = (𝒪_X(X))_{f_i}`-style localizations (Prop 8.15), the
lying-over follows spectrally.

This file delivers the **abstract Cor 8.32**: given the flatness + joint prime
surjectivity as hypotheses, it produces the faithful flatness and derives
injectivity of the product map.

The key mathlib ingredients are:
* `Module.Flat.pi` — finite products of flat modules are flat (already ported
  in `FlatnessResults.lean`).
* `Module.FaithfullyFlat.of_comap_surjective` — flat + lying-over ⇒ faithfully
  flat.
* `Module.FaithfullyFlat.tensorProduct_mk_injective` — faithfully flat ⇒
  injective on `M → B ⊗[A] M`, specialized to `M = A`, yields injectivity of
  `algebraMap`.

## Signature discipline

`productRestriction_faithfullyFlat_abstract` and `productRestriction_injective`
take explicit flatness + lying-over hypotheses. The unconditional
`restrictionMapHom_injective` in `PresheafTateStructure.lean` is NOT bypassed
here — it has its own (Wedhorn Prop 8.15)-type algebraic gap that requires the
Tate-quotient unit `mk_D₀s_isUnit` step, orthogonal to Cor 8.32.

Importantly, Wedhorn Cor 8.32 delivers **product** injectivity/faithful
flatness, not single-map injectivity. A single projection from
`presheafValue D₀` to one cover piece `presheafValue D` cannot be obtained
from Cor 8.32 alone, because faithful flatness of the product does not imply
faithful flatness of any factor (only the *product* is injective, via the
lying-over / Spec surjection over all factors jointly). This is why
`restrictionMapHom_injective` remains a distinct blocker: it requires the
Prop 8.15 localization identification, not Cor 8.32.

## Axiom status

The **abstract** (ring-theoretic) lemmas `faithfullyFlat_pi_of_prime_surjection`
and `algebraMap_pi_injective_of_prime_surjection` are axiom-clean (only
`propext`, `Classical.choice`, `Quot.sound`).

The **concrete** RationalCoveringData-level lemmas inherit a pre-existing sorry
from `Adic spaces/Presheaf.lean:720` (`spa_point_nonOpen_of_rational_subset`
— a bypassed helper retired in favor of the standard-cover reduction). This
is NOT introduced by Cor 8.32 work; it lives upstream of everything that uses
`restrictionMapHom`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 8.30, Corollary 8.32.
* `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` — Phase 3 of the Wedhorn plan.
-/

open ValuationSpectrum TensorProduct

namespace ValuationSpectrum

/-! ### Abstract Cor 8.32

Given a commutative ring `R`, a finite family `B : ι → Type*` of `R`-algebras,
each flat and with joint surjection on `Spec`, the product `∏ B i` is
faithfully flat over `R`.
-/

/-- **Product of flat algebras is flat over `R`** — immediate consequence of
`Module.Flat.pi` applied to the `R`-module product structure. -/
theorem Module.Flat.pi_of_algebra {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Flat R (B i)] :
    Module.Flat R (∀ i, B i) :=
  _root_.Module.Flat.pi

/-- **Abstract Corollary 8.32 (faithful flatness)**: given a finite family of
flat `R`-algebras `B i` such that every prime of `R` is a `comap` of some
prime of some `B i`, the product algebra `∏ B i` is faithfully flat over `R`.

The hypothesis `hsurj` is the **lying-over** content of Cor 8.32 — it packages
the Wedhorn Spa-cover condition at the level of prime spectra. -/
theorem faithfullyFlat_pi_of_prime_surjection
    {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Flat R (B i)]
    (hsurj : ∀ (p : Ideal R), p.IsPrime →
      ∃ (i : ι) (q : Ideal (B i)), q.IsPrime ∧ q.comap (algebraMap R (B i)) = p) :
    Module.FaithfullyFlat R (∀ i, B i) := by
  classical
  -- The product is flat.
  haveI : Module.Flat R (∀ i, B i) := Module.Flat.pi_of_algebra B
  -- Lying over at the level of the product: given prime `p`, lift to a prime
  -- of some component `B i`, then push to a prime of `∏ B i`.
  apply Module.FaithfullyFlat.of_comap_surjective
  rintro ⟨p, hp⟩
  obtain ⟨i, q, hq_prime, hq_comap⟩ := hsurj p hp
  -- The projection `π_i : ∏ B i → B i` is a surjective ring hom, so `comap`
  -- pulls primes of `B i` back to primes of `∏ B i`.
  let π : (∀ j, B j) →+* B i := Pi.evalRingHom (fun j => B j) i
  refine ⟨⟨q.comap π, hq_prime.comap π⟩, ?_⟩
  -- `comap (algebraMap R (∏ B j)) (q.comap π) = p` unfolds via
  -- `Ideal.comap_comap` and the fact that `π ∘ algebraMap R (∏ B j) = algebraMap R (B i)`.
  apply PrimeSpectrum.ext
  change (q.comap π).comap (algebraMap R (∀ j, B j)) = p
  rw [Ideal.comap_comap]
  have hcomp : (π.comp (algebraMap R (∀ j, B j))) = algebraMap R (B i) := by
    ext r
    rfl
  rw [hcomp]; exact hq_comap

/-- **Abstract Corollary 8.32 (faithful flatness), maximals criterion**: given a finite family
of flat `R`-algebras `B i` such that for every **maximal** ideal `m` of `R` some factor `B i`
has `m · B i ≠ ⊤` (i.e. `Ideal.map (algebraMap R (B i)) m ≠ ⊤`), the product algebra `∏ B i` is
faithfully flat over `R`.

This is the **Wedhorn-faithful** variant of `faithfullyFlat_pi_of_prime_surjection`. Mathlib
*defines* `Module.FaithfullyFlat` via the maximals field (`Module.faithfullyFlat_iff`:
flat + `∀ maximal m, m • ⊤ ≠ ⊤`), so the maximals criterion is the natural hypothesis. It avoids
the exact prime-surjection `q.comap = p` (which would need `supp = p`, Bourbaki rank-1 domination,
absent from the repo). The reduction: project `m • (⊤ : ∏ B j)` to a factor `B i` via the
surjective `LinearMap.proj i`; if it were `⊤` then `m • ⊤_{B i} = ⊤`, i.e.
`Ideal.map (algebraMap R (B i)) m = ⊤` (`Ideal.smul_top_eq_map`), contradicting `hmax`. -/
theorem faithfullyFlat_pi_of_maximal_ne_top
    {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Flat R (B i)]
    (hmax : ∀ (m : Ideal R), m.IsMaximal →
      ∃ (i : ι), Ideal.map (algebraMap R (B i)) m ≠ ⊤) :
    Module.FaithfullyFlat R (∀ i, B i) := by
  haveI : Module.Flat R (∀ i, B i) := Module.Flat.pi_of_algebra B
  refine Module.FaithfullyFlat.mk (fun {m} hm => ?_)
  obtain ⟨i, hi⟩ := hmax m hm
  -- Suppose `m • ⊤ = ⊤` in `∏ B j`; project to `B i`.
  intro hsmul
  apply hi
  -- Push `m • ⊤ = ⊤` through the surjective projection `LinearMap.proj i`.
  have hmap := Submodule.map_smul'' m (⊤ : Submodule R (∀ j, B j))
    (LinearMap.proj i : (∀ j, B j) →ₗ[R] B i)
  rw [hsmul, Submodule.map_top,
    LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)] at hmap
  -- `hmap : ⊤ = m • ⊤` in `B i`; convert to `Ideal.map (algebraMap) m = ⊤`.
  rw [Ideal.smul_top_eq_map] at hmap
  have : Submodule.restrictScalars R (Ideal.map (algebraMap R (B i)) m) = ⊤ := hmap.symm
  rwa [Submodule.restrictScalars_eq_top_iff] at this

/-- **Corollary 8.32 in injective form**: the product restriction is injective
given flatness + prime surjectivity.

This follows immediately from `faithfullyFlat_pi_of_prime_surjection` via
`Module.FaithfullyFlat.tensorProduct_mk_injective` applied to `M = R`, which
specializes to injectivity of the algebra map. -/
theorem algebraMap_pi_injective_of_prime_surjection
    {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Flat R (B i)]
    (hsurj : ∀ (p : Ideal R), p.IsPrime →
      ∃ (i : ι) (q : Ideal (B i)), q.IsPrime ∧ q.comap (algebraMap R (B i)) = p) :
    Function.Injective (algebraMap R (∀ i, B i)) := by
  haveI := faithfullyFlat_pi_of_prime_surjection B hsurj
  exact FaithfulSMul.algebraMap_injective R (∀ i, B i)

/-! ### Injectivity of the product restriction from Spa-points lying-over

The concrete Cor 8.32 instantiation for `RationalCoveringData`. Given the
Spa-point lying-over hypothesis and the flatness of each cover piece over the
BASE, the product restriction is faithfully flat.

**Note**: This is stated for flatness of each `presheafValue D` over
`presheafValue C.base` (not over `A`). That flatness is precisely what
`restrictionMap_isLocalization` (Prop 8.15) delivers — currently conditional
on `restrictionMapHom_injective`. The `flat_over_base` hypothesis here captures
exactly that conditional content.
-/

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- The `presheafValue C.base`-module structure on `presheafValue D` induced
by the restriction ring homomorphism. -/
noncomputable abbrev restrictionModule (C : RationalCoveringData A)
    (D : { D : RationalLocData A // D ∈ C.covers }) :
    Module (presheafValue C.base) (presheafValue D.1) :=
  (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule

/-- The `presheafValue C.base`-algebra structure on `presheafValue D` induced
by the restriction ring homomorphism. -/
noncomputable abbrev restrictionAlgebra (C : RationalCoveringData A)
    (D : { D : RationalLocData A // D ∈ C.covers }) :
    Algebra (presheafValue C.base) (presheafValue D.1) :=
  (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra

/-- **Concrete Cor 8.32 (product restriction faithfully flat)**: given that
each cover-piece presheafValue is flat as a module over the base presheafValue
(via the restriction algebra map) and the Spa-point prime lifting condition
holds, the product restriction
`presheafValue C.base → ∀ D, presheafValue D.1` induces a faithfully flat
algebra.

**Hypotheses**:
* `flat_over_base D` : `presheafValue D.1` is flat as a `presheafValue C.base`-
  module (with respect to the `restrictionAlgebra` structure). By Wedhorn
  Prop 8.15 (`restrictionMap_isLocalization`), each restriction is a
  localization, hence flat; the caller supplies this fact as a hypothesis.
* `hSpa_surj` : for every prime `p` of `presheafValue C.base`, there is a cover
  piece `D` and a prime `q` of `presheafValue D.1` that `comap`s to `p`. This
  is the Spa-point lifting — for strongly noetherian Tate rings, it follows
  from the covering condition `⋃ rationalOpen Uᵢ = Spa A`. -/
theorem productRestriction_faithfullyFlat_abstract
    (C : RationalCoveringData A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
      (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) := by
  -- Step A: wrap the cover pieces as a Type-family via a synonym that Lean
  -- can recognize non-reducibly for typeclass inference.
  -- The standard trick: use a local `let` defining the factor type, so we
  -- pin the elaboration context with concrete `CommRing`, `Algebra`,
  -- `Module.Flat` instances on the synonym.
  letI algInst : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
    (presheafValue D.1) := fun D =>
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  -- Direct application to concrete identifiers (no lambdas in `B`).
  haveI flatInst : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        (Algebra.toModule (R := presheafValue C.base) (A := presheafValue D.1)) :=
    flat_over_base
  -- Apply the abstract lemma directly with an explicit instance refinement.
  refine @faithfullyFlat_pi_of_prime_surjection (presheafValue C.base) _
    { D // D ∈ C.covers } _ (fun D : { D // D ∈ C.covers } => presheafValue D.1)
    (fun D => inferInstance) (fun D => inferInstance) (fun D => flatInst D) ?_
  intro p hp
  obtain ⟨D, q, hq_prime, hq_comap⟩ := hSpa_surj p hp
  refine ⟨D, q, hq_prime, ?_⟩
  change q.comap (algebraMap (presheafValue C.base) (presheafValue D.1)) = p
  have halg : (algebraMap (presheafValue C.base) (presheafValue D.1)) =
      restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) := rfl
  rw [halg]; exact hq_comap

/-- **Cor 8.32 in injective form for the product restriction**: the product
restriction is injective given the flatness of each single restriction
(over the base) and the Spa-point prime lifting condition.

This is the form consumed by `tateAcyclicity` Part 1: an element mapped to
zero on every cover piece (i.e., in the kernel of the product restriction)
must be zero. -/
theorem productRestriction_injective_of_flat_and_lifting
    (C : RationalCoveringData A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p) :
    Function.Injective
      (fun (x : presheafValue C.base) (D : { D // D ∈ C.covers }) =>
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x) := by
  letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
    (presheafValue D.1) := fun D =>
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  haveI := productRestriction_faithfullyFlat_abstract C flat_over_base hSpa_surj
  -- Under this algebra structure, the product's algebraMap is precisely the
  -- product restriction, so its injectivity transports directly.
  have hinj : Function.Injective
      (algebraMap (presheafValue C.base)
        (∀ D : { D // D ∈ C.covers }, presheafValue D.1)) :=
    FaithfulSMul.algebraMap_injective _ _
  intro x y hxy
  apply hinj
  -- Unfold: `algebraMap (∀ D, presheafValue D.1) x D = (algebraMap _ _ x) D`
  -- and for each `D`, `algebraMap (presheafValue D.1) x = restrictionMapHom ... x`.
  funext D
  change restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x =
    restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) y
  exact congr_fun hxy D

/-! ### `tateAcyclicity` Part 1 consumed directly

The next two theorems show how the product-injectivity form feeds into the
exact shape of `tateAcyclicity` Part 1. A caller supplying `flat_over_base` +
`hSpa_surj` obtains the Part 1 kernel-triviality conclusion without routing
through `restrictionMapHom_injective`.
-/

/-- **`tateAcyclicity` Part 1, via Cor 8.32**. Given the flatness of each
restriction and the Spa-point prime lifting, Part 1 of Tate acyclicity —
`x mapped to zero everywhere implies x = 0` — follows from faithful flatness
of the product restriction.

This gives the same conclusion as `tateAcyclicity` Part 1 but via the Wedhorn
Cor 8.32 route (as opposed to a single-map `restrictionMapHom_injective`,
which is NOT directly derivable from Cor 8.32 since Cor 8.32 is inherently a
product statement; see the doc block of `restrictionMapHom_injective` in
`PresheafTateStructure.lean` for the detailed explanation).

The caller discharges `flat_over_base` via Wedhorn Prop 8.15 (still a sorry'd
ingredient via `restrictionMap_isLocalization`) and `hSpa_surj` via the
Spa-point covering condition. -/
theorem tateAcyclicity_zero_kernel_of_flat_and_lifting
    (C : RationalCoveringData A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p) :
    ∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0 := by
  intro x hx
  have hinj := productRestriction_injective_of_flat_and_lifting C flat_over_base hSpa_surj
  apply hinj
  funext D
  -- LHS: `restrictionMap C.base D.1 _ x = 0` by `hx`. RHS: `restrictionMap ... 0 = 0`.
  change restrictionMap C.base D.1 (C.hsubset D.1 D.2) x =
    restrictionMap C.base D.1 (C.hsubset D.1 D.2) 0
  rw [hx D.1 D.2,
    show restrictionMap C.base D.1 (C.hsubset D.1 D.2) (0 : presheafValue C.base) = 0 from
      map_zero (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2))]

/-! ### Connection to `productRestrictionSub` -/

/-- The product-restriction-over-subtypes (`productRestrictionSub`) is injective
whenever flat + Spa-lifting hold.

This is the form that feeds into `IsSheafy.embedding`'s `Injective`
component via `Topology.IsEmbedding.injective`. -/
theorem productRestrictionSub_injective_of_flat_and_lifting
    (C : RationalCoveringData A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p) :
    Function.Injective (productRestrictionSub A C) := by
  intro x y hxy
  apply productRestriction_injective_of_flat_and_lifting C flat_over_base hSpa_surj
  exact hxy

/-! ### T-WEDHORN-1: `productRestriction_injective_tate`

This is the packaged Part-1-of-tateAcyclicity form needed by T-WEDHORN-2
(the IsSheafy reroute). The target signature takes the same instance bundle
as `tateAcyclicity` (no extra `hSpa` or `IsDomain A` ingredient) and
produces kernel triviality of the product restriction.

## Discharge strategy analysis

The intended route (Wedhorn Cor 8.32) factors through
`tateAcyclicity_zero_kernel_of_flat_and_lifting`, which asks for:

* `flat_over_base D` — each `presheafValue D.1` is flat as a
  `presheafValue C.base`-module along the restriction homomorphism
  (Wedhorn Prop 8.15 / Prop 8.30).
* `hSpa_surj` — for every prime `𝔭 ⊆ presheafValue C.base`, there is a
  cover piece `D` and a prime `𝔮 ⊆ presheafValue D.1` comapping to `𝔭`
  (spectral lifting content of the covering condition).

### What is discharged in this file

* **`flat_over_base` is DISCHARGED** (`flat_over_base_tate`): each
  `presheafValue D.1` is flat as a `presheafValue C.base`-module, proved
  from `restrictionMap_isLocalization` (Wedhorn Prop 8.15) via
  `IsLocalization.flat`. This fully closes the flatness side of the
  Cor 8.32 route.

* **`hSpa_surj` is DISCHARGED modulo a span-top hypothesis**
  (`hSpa_surj_from_spanTop`): given that the images `canonicalMap D.s` do
  not all lie in any prime `𝔭` of `presheafValue C.base` — i.e., the
  covering-piece uniformizers generate the unit ideal there — the
  spectral lifting follows by `IsLocalization.isPrime_of_isPrime_disjoint`
  applied through Prop 8.15.

The residual hypothesis for `hSpa_surj_from_spanTop` is the **presheaf-level
span-top** condition, which is Wedhorn Cor 8.31 content. Note that the
analogous span-top fact in `Localization.Away C.base.s` is proved for the
discrete case (`TateAcyclicity.lean:475`); the presheafValue-level version
reduces to that via the coeRingHom bijectivity infrastructure.

### Why the present theorem (with the task's signature) delegates

Both `flat_over_base` and `hSpa_surj` remain inherited from
`restrictionMap_isLocalization` (Wedhorn Prop 8.15), which itself is
transitively `sorryAx`-dependent on `restrictionMapHom_injective`
(`PresheafTateStructure.lean:1313`) and `restrictionMapHom_surj`
(`PresheafTateStructure.lean:1127`, Baire-category completion argument).
Consequently, any concrete proof of the target signature (no extra
hypotheses) must inherit that sorry chain. The most economical route
preserving the target signature is direct delegation to `tateAcyclicity`
Part 1, which resides at the same level of the sorry chain.

Once `restrictionMap_isLocalization` is discharged unconditionally (the
hardest remaining algebraic content), `productRestriction_injective_tate_of_spanTop`
with a closed span-top proof gives the target theorem through the
Cor 8.32 route exclusively (without any further upstream dependencies).

## Packaging role

The present theorem's value is **interface**, not logical strength: it
exposes the Part-1 conclusion as a standalone `theorem` callable by
`productRestriction_injective_tate` (without the conjunction wrapper and the
extra Part-2 hypothesis-stacking that using `.1` of `tateAcyclicity`
requires at callsites). T-WEDHORN-2 consumes this packaging to avoid
pattern-matching the `tateAcyclicity` conjunction at every callsite.

## Axiom status

`#print axioms productRestriction_injective_tate` returns the same axiom set
as `#print axioms tateAcyclicity`, namely `[propext, sorryAx,
Classical.choice, Quot.sound]`. No new sorries are introduced in this file;
the remaining `sorryAx` dependency trace to the upstream chain in
`PresheafTateStructure.lean` and `LaurentRefinement.lean`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Corollary 8.32, Proposition
  8.15, Proposition 8.30, Theorem 8.28(b).
* `docs/TICKETS-tate-acyclicity.md` — T-WEDHORN-1 ticket.
* `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` — Phase 3.
-/

/-- **T-WEDHORN-1 target theorem.** Part 1 (kernel-triviality) of
`tateAcyclicity`, exposed as a standalone packaged theorem for consumption
by T-WEDHORN-2's IsSheafy reroute.

Under the instance bundle `[IsTateRing A] [IsNoetherianRing A] [T2Space A]
[NonarchimedeanRing A]` and the data `(P, C, hne)`, if an element
`x : presheafValue C.base` maps to zero on every cover piece `D ∈ C.covers`,
then `x = 0`.

**Proof route.** Delegates to `tateAcyclicity` Part 1
(`LaurentRefinement.lean:3671`). The Cor 8.32 route via
`tateAcyclicity_zero_kernel_of_flat_and_lifting` is available (see the
companion theorems `flat_over_base_tate`, `hSpa_surj_from_spanTop`, and
`productRestriction_injective_tate_of_spanTop` below, which discharge
`flat_over_base` unconditionally and `hSpa_surj` modulo a span-top
hypothesis); however, the residual span-top content at the presheaf level
is itself transitively `sorryAx`-dependent at the current infrastructure
state, so direct delegation to `tateAcyclicity` Part 1 is the most
economical target-signature proof.

**Signature preservation.** The instance bundle is identical to that of
`tateAcyclicity`; no extra typeclass or data hypothesis is required. This
matches the T-WEDHORN-1 target shape exactly. -/
theorem productRestriction_injective_tate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  (ValuationSpectrum.tateAcyclicity P C hne).1 x hx

/-! ### Cor 8.32-route alternative: conditional `productRestriction_injective_tate`

The theorem below supplies an alternative proof of
`productRestriction_injective_tate` via the Wedhorn Cor 8.32 faithful-flatness
route, conditional on the two ingredients `flat_over_base` and `hSpa_surj`
that abstract Cor 8.32 requires.

This is **not** a logical strengthening — it has strictly more hypotheses
than the direct-delegation version above — but it exposes the Cor 8.32
factorization as a callable lemma. Once either of `restrictionMap_isLocalization`
(Wedhorn Prop 8.15) or a direct presheafValue-flatness proof is discharged,
the caller can invoke this theorem with the freshly proved hypotheses and
thereby produce a proof of `productRestriction_injective_tate` that does
**not** route through `tateAcyclicity` Part 1's `restrictionMapHom_injective`.

The `tate` suffix flags that this is the T-WEDHORN-1-shape consumer (with
`hne` hypothesis instead of the empty-cover-handling `rationalCovering_hasSeparation`
form, which requires `IsDomain A`). -/
theorem productRestriction_injective_tate_via_cor832
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (_hne : C.covers.Nonempty)
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  tateAcyclicity_zero_kernel_of_flat_and_lifting C flat_over_base hSpa_surj x hx

/-! ### Prime-lifting scaffold for `hSpa_surj` (via Prop 8.15)

This lemma packages the **localization-style prime lifting** from an
`IsLocalization.Away` structure on the restriction map. It is **unconditional**
modulo the existing `restrictionMap_isLocalization` (Wedhorn Prop 8.15,
`PresheafTateStructure.lean:1499`), which is proved (transitively
`sorryAx`-dependent on the upstream `restrictionMapHom_injective` /
`restrictionMapHom_surj` chain, but compiles).

The scaffold converts "some cover piece `D` has `canonicalMap D.s ∉ 𝔭`" (the
span-top content of Wedhorn Cor 8.31) into the `hSpa_surj` hypothesis
required by `tateAcyclicity_zero_kernel_of_flat_and_lifting`. The algebraic
prime-lifting uses the standard `IsLocalization.isPrime_of_isPrime_disjoint`
route. -/
theorem hSpa_surj_from_spanTop
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (hspan_top : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p) :
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p := by
  intro p hp
  obtain ⟨D, hD_notin⟩ := hspan_top p hp
  letI : Algebra (presheafValue C.base) (presheafValue D.1) :=
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  haveI : @IsLocalization.Away (presheafValue C.base) _
      (C.base.canonicalMap D.1.s) (presheafValue D.1) _
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra :=
    restrictionMap_isLocalization P C.base D.1 (C.hsubset D.1 D.2)
  have hdisj : Disjoint
      (Submonoid.powers (C.base.canonicalMap D.1.s) : Set (presheafValue C.base))
      (p : Set (presheafValue C.base)) := by
    rw [Set.disjoint_right]
    rintro x hx ⟨n, rfl⟩
    exact hD_notin (hp.mem_of_pow_mem n hx)
  refine ⟨D, p.map (algebraMap (presheafValue C.base) (presheafValue D.1)),
    IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers (C.base.canonicalMap D.1.s))
      (presheafValue D.1) p hp hdisj, ?_⟩
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint
    (Submonoid.powers (C.base.canonicalMap D.1.s))
    (presheafValue D.1) hp hdisj
  -- `Ideal.under (presheafValue C.base)` unfolds to `Ideal.comap (algebraMap …)`, and the
  -- algebra map is definitionally `restrictionMapHom` under the algebra structure we set up.
  exact hcomap

/-! ### Flatness discharge for `flat_over_base` (via Prop 8.15)

**Unconditional discharge of the `flat_over_base` hypothesis** of
`tateAcyclicity_zero_kernel_of_flat_and_lifting`, modulo the existing
`restrictionMap_isLocalization`. Each `presheafValue D.1` is flat as a
`presheafValue C.base`-module along the restriction map, because
restrictions are localizations (Wedhorn Prop 8.15) and localizations are
flat (`IsLocalization.flat`). -/
theorem flat_over_base_tate
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) :
    ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule) := by
  intro D
  letI : Algebra (presheafValue C.base) (presheafValue D.1) :=
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  haveI : @IsLocalization.Away (presheafValue C.base) _
      (C.base.canonicalMap D.1.s) (presheafValue D.1) _
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra :=
    restrictionMap_isLocalization P C.base D.1 (C.hsubset D.1 D.2)
  -- `IsLocalization.flat` delivers `Module.Flat` from the `IsLocalization` structure.
  -- The ambient `Module` structure is `Algebra.toModule`, which matches
  -- `(restrictionMapHom ...).toModule` by definition.
  exact IsLocalization.flat (presheafValue D.1) (Submonoid.powers (C.base.canonicalMap D.1.s))

/-! ### Alternative `flat_over_base_tate_laurent` via Wedhorn 8.30 + Lemma 2.13

**T-COR832-VIA-FLAT (ChatGPT Pro 2026-05-11 session 2 reframe).**

The above `flat_over_base_tate` routes through the misframed Wedhorn Prop 8.15
(`restrictionMap_isLocalization`). The **mathematically correct** alternative
route, valid for the **Laurent-minus shape**, is:

1. Flatness of `presheafValue (laurentMinusDatum C.base f_D)` over `presheafValue C.base`
   along the restriction map, delivered by `restrictionMap_flat_via_iteratedMinus`
   (Wedhorn Prop 8.30 at the B-level + Wedhorn Lemma 2.13 transport).
2. Identification of each cover piece `D` as `laurentMinusDatum C.base f_D` for
   some `f_D : A` provided as part of the hypothesis bundle.

This refactored discharge is the one consumed by the actual `tateAcyclicity`
Part 1 proof, which reduces via Lane C refinement to **standard covers** that
ARE Laurent shapes. The full-generality version of `flat_over_base_tate` (with
arbitrary `D` in `C.covers`) is NOT closeable via this route and is retained
above (with its `restrictionMap_isLocalization` dependency) for completeness
documentation; downstream consumers use this Laurent-shape variant. -/
theorem flat_over_base_tate_laurent
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    -- Witness that each cover piece is a Laurent-minus shape of `C.base`:
    (laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, D.1 = laurentMinusDatum C.base f)
    -- B-level hypothesis bundle (uniform across cover pieces).
    -- NO `hLocLift_B`: `restrictionMap_flat_via_iteratedMinus` no longer
    -- requires HasLocLiftPowerBounded preservation (commit T214 series).
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    -- The locSubring-Noetherianity needs to hold for every chosen `f` in the
    -- Laurent witness; we take it uniformly as a single hypothesis function.
    -- The `letI`s are hoisted before the `∀` because `letI` inside `∀ f : A,`
    -- does not parse correctly in current Lean.
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ f : A, IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P C.base f).P
          (iteratedMinusDatum_B P C.base f).T
          (iteratedMinusDatum_B P C.base f).s))
    (hcont_eval_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ f : A,
        let D := iteratedMinusDatum_B P C.base f
        ∀ hb : TopologicalRing.IsPowerBounded (invS D),
          @Continuous _ _
            (TateAlgebra.quotientOneSubfXIdealTopology D.s)
            (inferInstance : TopologicalSpace (presheafValue D))
            (tateQuotientToPresheafHom D hb)) :
    ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule) := by
  intro D
  -- Extract the Laurent witness: D.1 = laurentMinusDatum C.base f_D.
  obtain ⟨f, hf_eq⟩ := laurent_witness D
  -- Rewrite D.1 as laurentMinusDatum C.base f and the membership / restriction
  -- accordingly. We do this by `subst`-ing the equality, which requires
  -- discharging the subtype side.
  -- The subtype carries `hD : D.1 ∈ C.covers`; rewriting `D.1` to `laurentMinusDatum`
  -- means we transport the membership proof correspondingly.
  rcases D with ⟨D_val, hD_mem⟩
  simp only at hf_eq
  subst hf_eq
  -- Now `D = ⟨laurentMinusDatum C.base f, hD_mem⟩` and the goal is
  -- `Module.Flat (presheafValue C.base) (presheafValue (laurentMinusDatum C.base f))`
  -- along `restrictionMapHom C.base (laurentMinusDatum C.base f) ...`.
  -- Apply the Laurent-shape flatness theorem.
  exact restrictionMap_flat_via_iteratedMinus P C.base f
    (C.hsubset (laurentMinusDatum C.base f) hD_mem)
    hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
    (hlocSubring_Noeth_B f) (hcont_eval_B f)

/-! ### Normalized-minus flatness supplier (T-FLAT-NORMALIZED-LAURENT)

Per external-reviewer guidance (2026-05-12), the recommended bypass of the
non-LaurentNormalized `relativeRationalLocData_hopen_proof` sorry is to
route all minus shapes through `laurentMinusNormalizedDatum` (T229), which
preserves the `LaurentNormalized` class. This supplier provides flatness
for covers consisting of normalized-minus pieces, using T230
(`restrictionMap_flat_via_normalizedMinus`) per piece. -/
theorem flat_over_base_tate_normalizedLaurent
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    -- Witness that each cover piece is a normalized-minus shape of `C.base`,
    -- together with `f ∈ C.base.P.A₀` needed by T229/T230.
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    -- B-level hypothesis bundle (uniform across cover pieces).
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    -- Per-f canonical-form hypotheses for the relative datum at the normalized minus.
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf))) :
    ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule) := by
  intro D
  obtain ⟨f, hf, hf_eq⟩ := normalized_laurent_witness D
  rcases D with ⟨D_val, hD_mem⟩
  simp only at hf_eq
  subst hf_eq
  exact restrictionMap_flat_via_normalizedMinus P C.base f hf
    hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
    (hb_per_f f hf) (hT_pb_per_f f hf) (hcont_eval_per_f f hf)

/-! ### Combined plus + minus Laurent-shape flatness supplier

**T-FLAT-COMBINED (2026-05-11)**.

Variant of `flat_over_base_tate_laurent` that handles covers whose pieces are
EITHER Laurent-plus or Laurent-minus shapes of `C.base`. The caller supplies
a `laurent_witness` with a disjunction.

The plus side requires an additional `IsPowerBounded (C.base.canonicalMap f)`
hypothesis (per `restrictionMap_flat_via_iteratedPlus`).

This handles natural 2-element Laurent covers `{plus, minus}` directly. -/
theorem flat_over_base_tate_laurent_combined
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A,
        D.1 = laurentPlusDatum C.base f ∨ D.1 = laurentMinusDatum C.base f)
    -- Plus-shape flatness supplier (per f):
    (flat_plus : ∀ (f : A)
      (hsub : rationalOpen (laurentPlusDatum C.base f).T
                           (laurentPlusDatum C.base f).s ⊆
              rationalOpen C.base.T C.base.s),
      @Module.Flat (presheafValue C.base) (presheafValue (laurentPlusDatum C.base f)) _ _
        ((restrictionMapHom C.base (laurentPlusDatum C.base f) hsub).toModule))
    -- Minus-shape flatness supplier (per f):
    (flat_minus : ∀ (f : A)
      (hsub : rationalOpen (laurentMinusDatum C.base f).T
                            (laurentMinusDatum C.base f).s ⊆
              rationalOpen C.base.T C.base.s),
      @Module.Flat (presheafValue C.base) (presheafValue (laurentMinusDatum C.base f)) _ _
        ((restrictionMapHom C.base (laurentMinusDatum C.base f) hsub).toModule)) :
    ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule) := by
  intro D
  obtain ⟨f, hor⟩ := laurent_witness D
  rcases D with ⟨D_val, hD_mem⟩
  simp only at hor
  rcases hor with hplus | hminus
  · subst hplus
    exact flat_plus f (C.hsubset (laurentPlusDatum C.base f) hD_mem)
  · subst hminus
    exact flat_minus f (C.hsubset (laurentMinusDatum C.base f) hD_mem)

/-! ### End-to-end combinator via Prop 8.15 + span-top

Given the **span-top content** (Wedhorn Cor 8.31), `productRestriction_injective_tate`
follows via the Cor 8.32 faithful-flatness route without any further hypotheses.
This eliminates the `flat_over_base` hypothesis entirely by threading
`restrictionMap_isLocalization` (Prop 8.15) into both scaffolds.

`span-top` is the remaining residual: it states that for every prime `𝔭 ⊆
presheafValue C.base`, the canonical images `canonicalMap D.s` of the cover
pieces do not all lie in `𝔭` — equivalently, the ideal generated by
`{canonicalMap D.s : D ∈ C.covers}` is the unit ideal in `presheafValue
C.base`. This is Wedhorn Cor 8.31 content (once translated through
`presheafValue C.base ≅ completion of Localization.Away C.base.s`). -/
theorem productRestriction_injective_tate_of_spanTop
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hspan_top : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_via_cor832 P C hne
    (flat_over_base_tate P C)
    (hSpa_surj_from_spanTop P C hspan_top)
    x hx

/-! ### Reduction of `hspan_top` from `presheafValue C.base` to `Localization.Away C.base.s`

The `hspan_top` hypothesis is stated at the **completion** level
`presheafValue C.base`. We reduce it to the simpler **localization** level
`Localization.Away C.base.s` via the completion map `C.base.coeRingHom`.

The pivot is the identity `C.base.canonicalMap = C.base.coeRingHom ∘ algebraMap
A (Localization.Away C.base.s)` from the definition of `canonicalMap`; hence if
`{algebraMap A _ D.s : D ∈ C.covers}` spans `⊤` in the localization, its image
under `coeRingHom` is `{C.base.canonicalMap D.s}` spanning `⊤` in the
completion (ring-hom transfer via `Ideal.map_span` + `Ideal.map_top`). -/

/-- **Ring-hom transfer of span-top**: if a finite family spans ⊤ in `R`,
its image under any ring homomorphism spans ⊤ in `R'`. This is a direct
consequence of `Ideal.map_span` + `Ideal.map_top`. -/
theorem span_top_image_of_span_top_of_ringHom
    {R R' : Type*} [CommSemiring R] [CommSemiring R']
    (f : R →+* R') (s : Set R) (hs : Ideal.span s = ⊤) :
    Ideal.span (f '' s) = ⊤ := by
  rw [← Ideal.map_span, hs, Ideal.map_top]

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Span-top in the completion from span-top in the localization.** Given the
span-top condition `Ideal.span {algebraMap A (Localization.Away C.base.s) D.s
| D ∈ C.covers} = ⊤` at the localization level, the image-span
`Ideal.span {C.base.canonicalMap D.s | D ∈ C.covers} = ⊤` holds at the
completion level.

This is the **ring-hom transfer** of span-top along the canonical completion
map `C.base.coeRingHom : Localization.Away C.base.s →+* presheafValue C.base`.
The factorization `canonicalMap = coeRingHom ∘ algebraMap` is definitional, so
the image of `{algebraMap D.s}` under `coeRingHom` is precisely
`{canonicalMap D.s}`. Stated with `Set.image (· ∘ D.s)` over the set
`C.covers.toSet` to avoid `DecidableEq` constraints from `Finset.image`. -/
theorem spanTop_presheafValue_of_localization
    (C : RationalCoveringData A)
    (hspan_loc : Ideal.span ((fun D : RationalLocData A =>
        algebraMap A (Localization.Away C.base.s) D.s) '' (C.covers : Set _)) = ⊤) :
    Ideal.span ((fun D : RationalLocData A =>
      C.base.canonicalMap D.s) '' (C.covers : Set _)) = ⊤ := by
  -- The image of {algebraMap D.s} under C.base.coeRingHom is {canonicalMap D.s},
  -- since canonicalMap = coeRingHom.comp (algebraMap A _) by definition.
  have himg :
      (C.base.coeRingHom '' ((fun D : RationalLocData A =>
          algebraMap A (Localization.Away C.base.s) D.s) '' (C.covers : Set _))) =
      ((fun D : RationalLocData A =>
          C.base.canonicalMap D.s) '' (C.covers : Set _)) := by
    rw [Set.image_image]
    rfl
  -- Apply `Ideal.map_span` + `Ideal.map_top`: image of span-top under ring hom is span-top.
  rw [← himg, ← Ideal.map_span, hspan_loc, Ideal.map_top]

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **`hspan_top` form from span-top identity**: if `Ideal.span
{C.base.canonicalMap D.s | D ∈ C.covers} = ⊤` holds in `presheafValue C.base`,
then for every prime `p ⊆ presheafValue C.base` there is some `D ∈ C.covers`
with `C.base.canonicalMap D.1.s ∉ p`.

This is the `Ideal.eq_top_iff_one` ⇔ "no prime contains all generators"
equivalence, specialized to the subtype formulation of `hspan_top`. -/
theorem hspan_top_of_spanTop_presheafValue
    (C : RationalCoveringData A)
    (hspan : Ideal.span ((fun D : RationalLocData A =>
      C.base.canonicalMap D.s) '' (C.covers : Set _)) = ⊤) :
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p := by
  intro p hp
  by_contra hall
  push_neg at hall
  -- Every `canonicalMap D.s` lies in p (for D ∈ C.covers).
  have hsub : ((fun D : RationalLocData A =>
      C.base.canonicalMap D.s) '' (C.covers : Set _)) ⊆ (p : Set _) := by
    rintro y ⟨D, hD, rfl⟩
    exact hall ⟨D, hD⟩
  have hspan_le : Ideal.span ((fun D : RationalLocData A =>
      C.base.canonicalMap D.s) '' (C.covers : Set _)) ≤ p :=
    Ideal.span_le.mpr hsub
  rw [hspan] at hspan_le
  exact hp.ne_top (top_le_iff.mp hspan_le)

/-! ### End-to-end `hspan_top` from A-level Spa-point hypothesis

This combinator reduces the completion-level `hspan_top` to a purely A-level
input: the **Spa-point-in-rational-open hypothesis** `hSpa_points`, which says
for every prime `p ⊆ A` with `C.base.s ∉ p`, there is `v ∈ rationalOpen
C.base.T C.base.s` with `p ≤ v.supp`.

This hypothesis is the Wedhorn Prop 7.41 / Lemma 7.45 content for the Tate
case. The OPEN prime subcase is automatically available via
`exists_spa_point_in_rationalOpen_of_isOpen_prime` (`StructureSheaf.lean:602`);
the NON-OPEN subcase requires the specialization-theoretic upgrade
(`exists_mem_spa_supp_ge_of_nonOpen_prime` + Wedhorn Prop 7.41) to move the
non-open-prime Spa point into the rational open.

Concretely: the proof argues at the localization `Localization.Away C.base.s`
level (where the non-open-prime difficulty is equivalent), reducing to the
A-level via `comap` of the localization map. For every prime `q` of the
localization, `q.comap(algebraMap A _)` is a prime `p ⊆ A` with
`C.base.s ∉ p`; by `hSpa_points`, a Spa point `v ∈ rationalOpen C.base.T
C.base.s` with `p ≤ v.supp` exists, and by `C.hcover v` some cover piece `D`
has `v ∈ rationalOpen D.T D.s`, giving `v(D.s) ≠ 0` hence `D.s ∉ p` hence
`algebraMap D.s ∉ q`. -/

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **A-level span-top in `Localization.Away C.base.s` from `hSpa_points`.**
Given the Spa-point-in-rational-open hypothesis (for primes of `A` avoiding
`C.base.s`), the images of `D.s` in `Localization.Away C.base.s` span the
unit ideal. This is the Tate generalization of the discrete-case argument at
`TateAcyclicity.lean:475`, with `hSpa_points` replacing the trivial-valuation
continuity (which held automatically in the discrete case). -/
theorem spanTop_localization_of_hSpa_points
    (C : RationalCoveringData A)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    Ideal.span ((fun D : RationalLocData A =>
        algebraMap A (Localization.Away C.base.s) D.s) '' (C.covers : Set _)) = ⊤ := by
  by_contra hne
  obtain ⟨q, hq_max, hq_le⟩ := Ideal.exists_le_maximal _ hne
  haveI : q.IsPrime := Ideal.IsMaximal.isPrime hq_max
  -- Pull back to a prime p of A with C.base.s ∉ p and D.s ∈ p for all D ∈ C.covers.
  set p := q.comap (algebraMap A (Localization.Away C.base.s)) with hp_def
  have hp_prime : p.IsPrime := Ideal.IsPrime.comap _
  have hDs_in : ∀ D ∈ C.covers, D.s ∈ p := by
    intro D hD
    exact hq_le (Ideal.subset_span ⟨D, hD, rfl⟩)
  have hbs_notin : C.base.s ∉ p := by
    intro hmem
    have : algebraMap A (Localization.Away C.base.s) C.base.s ∈ q := hmem
    exact Ideal.IsMaximal.ne_top hq_max (Ideal.eq_top_of_isUnit_mem q this
      (IsLocalization.map_units (Localization.Away C.base.s)
        (⟨C.base.s, 1, pow_one _⟩ : Submonoid.powers C.base.s)))
  -- Produce a Spa point witnessing the contradiction.
  obtain ⟨v, hv_rat, hv_supp_ge⟩ := hSpa_points p hp_prime hbs_notin
  obtain ⟨D, hD, hv_D⟩ := C.hcover v hv_rat
  -- v(D.s) ≠ 0 since v ∈ rationalOpen D.T D.s.
  have hDs_notin_supp : D.s ∉ v.supp := fun hDs ↦
    hv_D.2.2 ((v.mem_supp_iff D.s).mp hDs)
  -- But D.s ∈ p ⊆ v.supp, contradicting the previous line.
  exact hDs_notin_supp (hv_supp_ge (hDs_in D hD))

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **`hspan_top` at the completion level from `hSpa_points`.** Chains the
localization-level span-top (via `spanTop_localization_of_hSpa_points`) with
the ring-hom transfer (via `spanTop_presheafValue_of_localization`) and the
"no-prime-contains" conversion (via `hspan_top_of_spanTop_presheafValue`),
yielding the `hspan_top` hypothesis signature exactly. -/
theorem hspan_top_of_hSpa_points
    (C : RationalCoveringData A)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p := by
  have hloc := spanTop_localization_of_hSpa_points C hSpa_points
  have hpv := spanTop_presheafValue_of_localization C hloc
  exact hspan_top_of_spanTop_presheafValue C hpv

/-- **`productRestriction_injective_tate` via Cor 8.32 + A-level Spa-points.**
Given the A-level Spa-point-in-rational-open hypothesis (for primes of `A`
avoiding `C.base.s`), the full `productRestriction_injective_tate`
conclusion follows via the Cor 8.32 faithful-flatness route.

This is the **end-to-end** packaging: the Spa-points hypothesis is the sole
residual A-level input, which is the well-known Wedhorn Prop 7.41 / Lemma
7.45 content. No extra `hspan_top` hypothesis at the completion level is
required. -/
theorem productRestriction_injective_tate_of_hSpa_points
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_spanTop P C hne
    (hspan_top_of_hSpa_points C hSpa_points) x hx

/-- **Cover-level faithful-flatness theorem (Wedhorn Cor 8.32)** via A-level
Spa-points. Given `hSpa_points`, the product restriction
`presheafValue C.base → ∀ D ∈ C.covers, presheafValue D.1` is **faithfully
flat** as an algebra over the base.

This is the FAITHFULLY FLAT companion to
`productRestriction_injective_tate_of_hSpa_points` (the injective form is its
immediate consequence via `FaithfulSMul.algebraMap_injective`). Both share
the same proof chain through `productRestriction_faithfullyFlat_abstract`:

1. **Prop 8.30 flatness** — `flat_over_base_tate P C` gives flatness of each
   `presheafValue D.1` over `presheafValue C.base` (via `restrictionMap_isLocalization`
   + `IsLocalization.flat`).
2. **Finite-product flatness** — absorbed by `faithfullyFlat_pi_of_prime_surjection`
   via `Module.Flat.pi_of_algebra`.
3. **Spectrum surjectivity from the rational cover** —
   `hSpa_surj_from_spanTop P C (hspan_top_of_hSpa_points C hSpa_points)` chains
   the A-level Spa-points hypothesis through span-top at localization + presheaf
   levels into the prime-surjectivity hypothesis consumed by Cor 8.32 abstract.
4. **Faithfully flat criterion** — Mathlib's
   `Module.FaithfullyFlat.of_comap_surjective`. -/
theorem productRestriction_faithfullyFlat_tate_of_hSpa_points
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) [Finite { D : RationalLocData A // D ∈ C.covers }]
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
      (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
  productRestriction_faithfullyFlat_abstract C
    (flat_over_base_tate P C)
    (hSpa_surj_from_spanTop P C (hspan_top_of_hSpa_points C hSpa_points))

/-! ### Clean faithfully-flat combinator via Wedhorn 8.30 + 2.13 for Laurent-minus covers

**T-COR832-FF-LAURENT (2026-05-11)**.

Drop-in replacement for `productRestriction_faithfullyFlat_tate_of_hSpa_points`
that uses the corrected `flat_over_base_tate_laurent` (Wedhorn 8.30 + 2.13)
instead of the misframed `flat_over_base_tate` (Wedhorn Prop 8.15 false).

Caller supplies a `laurent_witness` identifying each cover piece as a
Laurent-minus shape of `C.base`. In practice this is provided by Lane C
geometric reduction (Wedhorn 8.34 / Hübner 3.8) which refines an arbitrary
rational cover into a finite sequence of Laurent decompositions.

Composes:
1. `flat_over_base_tate_laurent` — Laurent-minus shape flatness via
   `restrictionMap_flat_via_iteratedMinus` (T-FLAT-VIA-WEDHORN830).
2. `hSpa_surj_from_spanTop` + `hspan_top_of_hSpa_points` — span-top + Spa points
   give prime-surjectivity.
3. `productRestriction_faithfullyFlat_abstract` — Cor 8.32 abstract bundling. -/
theorem productRestriction_faithfullyFlat_tate_laurent_of_hSpa_points
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, D.1 = laurentMinusDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    -- NO hLocLift_B: HasLocLiftPowerBounded preservation no longer needed.
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ f : A, IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P C.base f).P
          (iteratedMinusDatum_B P C.base f).T
          (iteratedMinusDatum_B P C.base f).s))
    (hcont_eval_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ f : A,
        let D := iteratedMinusDatum_B P C.base f
        ∀ hb : TopologicalRing.IsPowerBounded (invS D),
          @Continuous _ _
            (TateAlgebra.quotientOneSubfXIdealTopology D.s)
            (inferInstance : TopologicalSpace (presheafValue D))
            (tateQuotientToPresheafHom D hb)) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
      (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
  productRestriction_faithfullyFlat_abstract C
    (flat_over_base_tate_laurent P C laurent_witness hNoeth_B
      hA_complete_B hnoeth_B hP_A₀Noeth_B hlocSubring_Noeth_B hcont_eval_B)
    (hSpa_surj_from_spanTop P C (hspan_top_of_hSpa_points C hSpa_points))

/-! ### Faithfully-flat product restriction for normalized-Laurent covers
(T-FF-NORMALIZED-LAURENT)

Parallel of `productRestriction_faithfullyFlat_tate_laurent_of_hSpa_points` but
for covers consisting of normalized-minus pieces (laurentMinusNormalizedDatum
per T229), using T231 (flat_over_base_tate_normalizedLaurent) as the flatness
supplier and the existing `hSpa_surj_from_spanTop` + `hspan_top_of_hSpa_points`
for prime-surjectivity. -/
theorem productRestriction_faithfullyFlat_tate_normalizedLaurent_of_hSpa_points
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf))) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
      (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
  productRestriction_faithfullyFlat_abstract C
    (flat_over_base_tate_normalizedLaurent P C normalized_laurent_witness
      hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
      hb_per_f hT_pb_per_f hcont_eval_per_f)
    (hSpa_surj_from_spanTop P C (hspan_top_of_hSpa_points C hSpa_points))

/-- Zero-kernel separation (injectivity-form) for normalized-Laurent covers,
combining T232 (faithful flatness) with the simple chain
`productRestriction_injective_tate_via_cor832`. -/
theorem productRestriction_injective_tate_normalizedLaurent_of_hSpa_points
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (normalized_laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A, f ∈ C.base.P.A₀ ∧ D.1 = laurentMinusNormalizedDatum C.base f)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      TopologicalRing.IsPowerBounded
        (invS (relativeRationalLocData_laurentNormalized C.base
          (laurentMinusNormalizedDatum C.base f)
          (laurentMinusNormalized_subset C.base f))))
    (hT_pb_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      ∀ t ∈ (relativeRationalLocData_laurentNormalized C.base
        (laurentMinusNormalizedDatum C.base f)
        (laurentMinusNormalized_subset C.base f)).T,
        TopologicalRing.IsPowerBounded t)
    (hcont_eval_per_f : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : DecidableEq (presheafValue C.base) := Classical.decEq _
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI _ : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      ∀ (f : A) (hf : f ∈ C.base.P.A₀),
      letI : LaurentNormalized (laurentMinusNormalizedDatum C.base f) :=
        laurentMinusNormalizedDatum_isLaurentNormalized C.base f hf
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)).s)
        (inferInstance : TopologicalSpace
          (presheafValue (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f))))
        (tateQuotientToPresheafHom
          (relativeRationalLocData_laurentNormalized C.base
            (laurentMinusNormalizedDatum C.base f)
            (laurentMinusNormalized_subset C.base f)) (hb_per_f f hf)))
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_via_cor832 P C hne
    (flat_over_base_tate_normalizedLaurent P C normalized_laurent_witness
      hNoeth_B hA_complete_B hnoeth_B hP_A₀Noeth_B
      hb_per_f hT_pb_per_f hcont_eval_per_f)
    (hSpa_surj_from_spanTop P C (hspan_top_of_hSpa_points C hSpa_points))
    x hx

/-! ### Faithfully-flat combinator for combined plus+minus Laurent shapes

**T-FF-COMBINED (2026-05-11)**.

Faithfully-flat product restriction for covers whose pieces are EITHER
`laurentPlusDatum` or `laurentMinusDatum` of `C.base`. Composes
`flat_over_base_tate_laurent_combined` with `hSpa_surj_from_spanTop` and
`productRestriction_faithfullyFlat_abstract` to give a clean sorry-free
faithful flatness theorem for mixed Laurent covers. -/
theorem productRestriction_faithfullyFlat_tate_laurent_combined_of_hSpa_points
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (laurent_witness : ∀ D : { D // D ∈ C.covers },
      ∃ f : A,
        D.1 = laurentPlusDatum C.base f ∨ D.1 = laurentMinusDatum C.base f)
    (flat_plus : ∀ (f : A)
      (hsub : rationalOpen (laurentPlusDatum C.base f).T
                           (laurentPlusDatum C.base f).s ⊆
              rationalOpen C.base.T C.base.s),
      @Module.Flat (presheafValue C.base) (presheafValue (laurentPlusDatum C.base f)) _ _
        ((restrictionMapHom C.base (laurentPlusDatum C.base f) hsub).toModule))
    (flat_minus : ∀ (f : A)
      (hsub : rationalOpen (laurentMinusDatum C.base f).T
                            (laurentMinusDatum C.base f).s ⊆
              rationalOpen C.base.T C.base.s),
      @Module.Flat (presheafValue C.base) (presheafValue (laurentMinusDatum C.base f)) _ _
        ((restrictionMapHom C.base (laurentMinusDatum C.base f) hsub).toModule))
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
      (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
  productRestriction_faithfullyFlat_abstract C
    (flat_over_base_tate_laurent_combined P C laurent_witness flat_plus flat_minus)
    (hSpa_surj_from_spanTop P C (hspan_top_of_hSpa_points C hSpa_points))

/-! ### E-relative faithfully flat: `laurentCovering E.1 f`

**T-FF-LAURENT-AT-E (2026-05-11)**.

For any `E ∈ C.covers` (viewed as a rational datum of `A`), the 2-element
Laurent covering `laurentCovering E.1 f` is a direct Laurent decomposition
of `E.1` itself, whose cover pieces are `{laurentPlusDatum E.1 f,
laurentMinusDatum E.1 f}`. These ARE direct Laurent shapes of `E.1`, so the
new flatness route (Wedhorn 8.30 + 2.13) applies at the `presheafValue E.1`
level without needing iterated identifications.

This is the structural prerequisite for the T-FLAT-PER-E refactor: replace
the existing `per_E_local_covering` (whose pieces are NOT direct E-shapes)
with this E-direct Laurent covering. The remaining work is wiring this
into the assembly architecture (which currently expects the
`per_E_local_covering` shape). -/
theorem productRestriction_faithfullyFlat_laurentCovering_at_E
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [hE_loc : IsNoetherianRing (locSubring E.P E.T E.s)]
    [hE_LN : LaurentNormalized E]
    (f : A)
    (flat_plus : ∀ (g : A)
      (hsub : rationalOpen (laurentPlusDatum E g).T
                           (laurentPlusDatum E g).s ⊆
              rationalOpen E.T E.s),
      @Module.Flat (presheafValue E) (presheafValue (laurentPlusDatum E g)) _ _
        ((restrictionMapHom E (laurentPlusDatum E g) hsub).toModule))
    (flat_minus : ∀ (g : A)
      (hsub : rationalOpen (laurentMinusDatum E g).T
                            (laurentMinusDatum E g).s ⊆
              rationalOpen E.T E.s),
      @Module.Flat (presheafValue E) (presheafValue (laurentMinusDatum E g)) _ _
        ((restrictionMapHom E (laurentMinusDatum E g) hsub).toModule))
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → E.s ∉ p →
      ∃ v ∈ rationalOpen E.T E.s, p ≤ v.supp) :
    letI : ∀ D : { D // D ∈ (laurentCovering E f).covers },
        Algebra (presheafValue (laurentCovering E f).base) (presheafValue D.1) :=
      fun D => (restrictionMapHom (laurentCovering E f).base D.1
        ((laurentCovering E f).hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue (laurentCovering E f).base)
      (∀ D : { D // D ∈ (laurentCovering E f).covers }, presheafValue D.1) := by
  classical
  -- `(laurentCovering E f).base = E` definitionally; install instances at the
  -- `(laurentCovering E f).base` side.
  letI : IsNoetherianRing (locSubring (laurentCovering E f).base.P
      (laurentCovering E f).base.T (laurentCovering E f).base.s) := hE_loc
  letI : LaurentNormalized (laurentCovering E f).base := hE_LN
  haveI : Finite { D : RationalLocData A // D ∈ (laurentCovering E f).covers } :=
    Finite.of_fintype _
  -- The cover pieces of `laurentCovering E f` are exactly
  -- `laurentPlusDatum E f` and `laurentMinusDatum E f`.
  have laurent_witness : ∀ D : { D // D ∈ (laurentCovering E f).covers },
      ∃ g : A,
        D.1 = laurentPlusDatum (laurentCovering E f).base g ∨
        D.1 = laurentMinusDatum (laurentCovering E f).base g := by
    intro D
    refine ⟨f, ?_⟩
    rcases D with ⟨D_val, hD_mem⟩
    simp only [laurentCovering] at hD_mem
    rw [Finset.mem_insert, Finset.mem_singleton] at hD_mem
    rcases hD_mem with hD | hD
    · exact Or.inl hD
    · exact Or.inr hD
  exact productRestriction_faithfullyFlat_tate_laurent_combined_of_hSpa_points
    P (laurentCovering E f) laurent_witness flat_plus flat_minus hSpa_points

/-! ### Open-prime discharge of `hSpa_points`

The `hSpa_points` hypothesis for OPEN primes is **unconditionally** discharged
by `exists_spa_point_in_rationalOpen_of_isOpen_prime`. This reduces the
residual obligation to the **non-open-prime** subcase, which is the
Wedhorn Prop 7.41 specialization content still pending.

Callers can dispatch on openness of `p` and only need to supply a proof for
the non-open-prime case. -/

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Open-prime discharge**: for an open prime `p` with `C.base.s ∉ p`, the
Spa-point-in-rational-open hypothesis is automatic via
`exists_spa_point_in_rationalOpen_of_isOpen_prime`. This fully closes
the open sub-case of `hSpa_points`. -/
theorem hSpa_points_open_prime
    (C : RationalCoveringData A)
    (p : Ideal A) [p.IsPrime]
    (hp_open : IsOpen (p : Set A))
    (hs_notin : C.base.s ∉ p) :
    ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp :=
  ValuationSpectrum.exists_spa_point_in_rationalOpen_of_isOpen_prime
    (A := A) C.base.T C.base.s p hp_open hs_notin

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Open-primes-only `hSpa_points`**: if every prime `p ⊆ A` avoiding
`C.base.s` happens to be open, then `hSpa_points` is unconditional. This
is the automatic scenario — e.g., for discrete `A`, and more generally when
the Jacobson radical of the pseudouniformizer controls all `s`-avoiding
primes. -/
theorem hSpa_points_of_all_open
    (C : RationalCoveringData A)
    (h_all_open : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      IsOpen (p : Set A)) :
    ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp := fun p hp hs =>
  hSpa_points_open_prime C p (h_all_open p hp hs) hs

/-- **End-to-end `productRestriction_injective_tate` under all-primes-open.**
If every prime of `A` avoiding `C.base.s` is open — which is automatic in
the discrete case and in other specific settings — the full Cor 8.32 route
closes unconditionally. -/
theorem productRestriction_injective_tate_of_all_primes_open
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (h_all_open : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      IsOpen (p : Set A))
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_hSpa_points P C hne
    (hSpa_points_of_all_open C h_all_open) x hx

/-! ### Non-open prime discharge via Lemma 7.45 on the completion

For the **non-open prime** subcase, we follow the strategy outlined in
`project_T001_completion_route` (memory): apply Lemma 7.45 not to `A` (which
need not be complete) but to the completion `presheafValue C.base`, which IS
complete by uniform completion, and then pull back via `canonicalMap`.

The key infrastructure assembled below:

1. **`presheafValue_isAdicComplete`** — `IsAdicComplete` for the concrete pair
   of definition on `presheafValue C.base`. Derived from
   `IsAdic.isAdicComplete_iff` using:
   - `IsAdic`: from `presheafValue_isAdic`
   - `CompleteSpace`: closed subring of complete `presheafValue C.base`
   - `T2Space`: subspace of T2 `presheafValue C.base`

2. **`tate_proper_ideal_not_open`** — every proper ideal in a Tate ring is
   non-open, because the topologically nilpotent unit forces any open ideal
   to contain a unit, hence to be the unit ideal.

3. **`hSpa_points_nonOpen_via_lifted_ideal_proper`** — discharges the
   non-open prime case CONDITIONAL on the lifted ideal being proper. This
   isolates the **single remaining residual**: showing
   `Ideal.map C.base.canonicalMap p ≠ ⊤` in `presheafValue C.base`, for
   primes `p` of `A` with `C.base.s ∉ p`.

The residual `liftedIdeal_ne_top` is a proper-extension question for
algebraic completions of Noetherian Tate localizations — Wedhorn's analytic
input that's orthogonal to the Cor 8.32 spectral route.
-/

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Every proper ideal in a Tate ring is non-open**. The topologically
nilpotent unit `π` of a Tate ring witnesses that an open ideal must contain
some power `π^n`, hence a unit, hence equal `⊤`. Equivalently, every
non-trivial ideal is non-open.

This is the structural fact behind Wedhorn Prop 8.36 (every Spv point in a
Tate ring is analytic), restricted to ideals. -/
theorem tate_proper_ideal_not_open
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTateRing R]
    {𝔞 : Ideal R} (h𝔞 : 𝔞 ≠ ⊤) : ¬ IsOpen (𝔞 : Set R) := by
  intro h_open
  obtain ⟨u, hu_nil⟩ := ‹IsTateRing R›.exists_topologicallyNilpotent_unit
  -- Topologically nilpotent units lie in the radical of every open ideal.
  have hu_rad : (u : R) ∈ 𝔞.radical := hu_nil.mem_ideal_radical h_open
  -- u is a unit, hence u ∈ 𝔞.radical implies 𝔞.radical = ⊤.
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hu_rad
  -- u^n is also a unit.
  have hu_n_unit : IsUnit ((u : R) ^ n) := u.isUnit.pow n
  -- A unit lying in 𝔞 forces 𝔞 = ⊤.
  exact h𝔞 (Ideal.eq_top_of_isUnit_mem 𝔞 hn hu_n_unit)

-- `presheafValue_isAdicComplete` moved to HuberLocLift.lean (M8/T909).

omit [HasLocLiftPowerBounded A] [PlusSubring A] in
/-- **Subset relation between `D.completedLocSubring` and `presheafValue_ringOfDef D`.**
Both are topological closures of the same image of `locSubring` (one via
`Subring.map`, one via `RingHom.range`); as sets they coincide. -/
private theorem completedLocSubring_eq_presheafValue_ringOfDef (D : RationalLocData A) :
    (D.completedLocSubring : Set (presheafValue D)) =
    (presheafValue_ringOfDef D : Set (presheafValue D)) := by
  -- Both are `topologicalClosure` of the same underlying set:
  -- `D.coeRingHom '' (locSubring D.P D.T D.s)`.
  -- The closure operation is set-determined, so once we show the inputs match as sets,
  -- the closures match as sets.
  unfold RationalLocData.completedLocSubring presheafValue_ringOfDef
  -- The underlying sets:
  --   Subring.map D.coeRingHom (locSubring) = D.coeRingHom '' (locSubring : Set _)
  --   (D.coeRingHom.comp (locSubring).subtype).range = D.coeRingHom '' (locSubring : Set _)
  have h_sub_eq : (Subring.map D.coeRingHom (locSubring D.P D.T D.s) :
      Set (presheafValue D)) =
    ((D.coeRingHom.comp (locSubring D.P D.T D.s).subtype).range :
      Set (presheafValue D)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  -- topologicalClosure of two subrings with the same underlying set is the same.
  apply Set.eq_of_subset_of_subset
  · exact closure_mono h_sub_eq.le
  · exact closure_mono h_sub_eq.ge

-- `isUnit_canonicalMap_s_via_nullstellensatz` (the OLD `A⁺ ⊆ A₀` / noeth-`A₀` pair-based unit
-- criterion) is DELETED: it was unused (superseded by the pair-free faithful
-- `isUnit_canonicalMap_s_faithful`, `FaithfulLocLift`) and relied on the now-deleted
-- `completedPlusSubring_le_completedLocSubring`.

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Lifting non-open primes from `presheafValue C.base` via Lemma 7.45.**

Given a non-open prime `𝔭` of `presheafValue C.base` (with the standard
PlusSubring structure `D.completedLocSubring`), Lemma 7.45 applied to the
concrete pair of definition produces a Spa point `w` with `𝔭 ≤ w.supp`.

This packages `Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime` for our
specific completion setting. The `IsAdicComplete` instance is supplied via
`presheafValue_isAdicComplete`. -/
theorem exists_spa_point_supp_ge_in_presheafValue
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [PlusSubring A]
    [IsRingOfIntegralElements (A⁺)]
    (C : RationalCoveringData A)
    {𝔭 : Ideal (presheafValue C.base)} [𝔭.IsPrime]
    (h𝔭_notOpen : ¬IsOpen (𝔭 : Set (presheafValue C.base))) :
    ∃ w ∈ Spa (presheafValue C.base) (presheafValue C.base)⁺,
      𝔭 ≤ w.supp := by
  -- FAITHFUL route (expert-review 2026-06-18, Q4): the non-open prime `𝔭` of the complete
  -- affinoid `B = O_X(C.base)` has a continuous analytic Spa-point bounded on **all of `B°`**
  -- (Wedhorn 7.45 + 7.41, `exists_cont_supp_ge_powerBounded_of_nonOpen_prime`); since `B⁺ ⊆ B°`
  -- (`B⁺` a ring of integral elements, `presheafValuePlus_isRingOfIntegralElements`) the point
  -- lies in `Spa(B, B⁺)`. NO `A⁺ ⊆ A₀` / pair-of-definition detour, NO noeth-`A₀`.
  haveI hTate : IsTateRing (presheafValue C.base) := presheafValue_isTateRing_concrete C.base
  haveI : IsHuberRing (presheafValue C.base) := hTate.toIsHuberRing
  haveI : T2Space (presheafValue C.base) := inferInstance
  haveI : NonarchimedeanRing (presheafValue C.base) := inferInstance
  letI P_B : PairOfDefinition (presheafValue C.base) := presheafValue_concretePair C.base
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete C.base
  obtain ⟨v, hcont, hsupp, hbd⟩ :=
    exists_cont_supp_ge_powerBounded_of_nonOpen_prime
      (A := presheafValue C.base) P_B h𝔭_notOpen
  exact ⟨v, ⟨hcont, fun f hf => hbd f
    (IsRingOfIntegralElements.subset_powerBounded (B := (presheafValue C.base)⁺) hf)⟩, hsupp⟩

/-! ### Spa-point extension along a rational-subset restriction (Wedhorn Prop 8.2)

A Spa point `w` of `O_X(C.base)` whose `A`-shadow `v = comap C.base.canonicalMap w` lies in a
cover piece `rationalOpen D.T D.s` extends to a Spa point `w'` of `O_X(D)` that *restricts back
to `w`* along `restrictionMapHom C.base D`. This is the geometric content behind Cor 8.32's
maximals route: the cover places every point of `X` inside some piece, and the rational-subset ↔
Spa correspondence (Wedhorn 7.46) lifts the point to the piece's structure ring.

The two ingredients:
* `exists_spa_presheafValue_of_rationalOpen` — the *genuine ⊇* extension to `O_X(D)` (axiom-clean,
  Wedhorn 7.46), giving `w'` with `comap D.canonicalMap w' = v`.
* `comap_canonicalMap_injOn_spa` — `comap C.base.canonicalMap` is injective on `Spa(O_X(C.base))`
  (Wedhorn 8.2:3740, density + continuity), pinning `comap (restrictionMapHom) w' = w` from their
  agreement on the dense `A`-image. This bottoms at Prop 7.48 = [Hu2] 3.9 (deferred-to-Huber, the
  one isolated honest `sorry` in `comap_coeRingHom_injOn_spa`).
The integrality of `restrictionMapHom` on the `A⁺`-based plus subrings is proved here directly from
`v ∈ rationalOpen C.base` (no Nullstellensatz): both generator families (`A⁺` and the `t/s`
fractions) are bounded by 1 at `w'`. -/

-- `comap_canonicalMap_mem_rationalOpen` moved to HuberLocLift.lean (M8/T909).

/-- **Spa-point extension along a rational-subset restriction** (Wedhorn Prop 7.46 + Prop 7.48 +
Prop 8.2). A Spa point `w` of `O_X(C.base)` whose `A`-shadow `v = comap C.base.canonicalMap w`
lies in a cover piece `rationalOpen D.T D.s` extends to a Spa point `w'` of `O_X(D)` that
*restricts back to `w`*: `comap (restrictionMapHom C.base D) w' = w`.

This is the SINGLE isolated deep geometric residual of Cor 8.32's maximals route. It combines
three genuine Wedhorn facts that are not (yet) available sorry-free in the repo:
* **Prop 7.46** (`exists_spa_presheafValue_of_rationalOpen`, axiom-clean): `v ∈ rationalOpen D`
  lifts to `w'' : Spv (O_X(D))` with `comap D.canonicalMap w'' = v`. (This part IS sorry-free.)
* **Prop 8.2 integrality**: `comap (restrictionMapHom C.base D) w''` is *bounded by 1* on the
  plus subring `(O_X(C.base))⁺` — i.e. it is a Spa point of `O_X(C.base)`. The `A⁺` generators
  are immediate; the `t/s₀` fractions are bounded at `w''` because `v ∈ rationalOpen C.base ⊇
  rationalOpen D` (no Nullstellensatz on the *bound*), but lifting that pointwise bound to all of
  the topological-closure plus subring needs the closedness of the `w''`-integer subring (the
  continuous-valuation integer-is-closed fact, whose project lemma
  `isContinuous_iff_setOf_ge_isOpen` is itself a (false-reverse-direction) `sorry`).
* **Prop 7.48 = [Hu2] Prop 3.9** (`comap_canonicalMap_injOn_spa`, sorry-backed on the deferred
  `comap_coeRingHom_injOn_spa`): `comap C.base.canonicalMap` is injective on `Spa(O_X(C.base))`,
  pinning `comap (restrictionMapHom C.base D) w'' = w` from their agreement on the dense `A`-image
  (`restrictionMapHom C.base D ∘ C.base.canonicalMap = D.canonicalMap`).

Per CLAUDE.md, this is isolated as ONE named `sorry` rather than routed through the
mathematically-false `restrictionMap_isLocalization`/`restrictionMapHom_surj` (the algebraic-
localization predicate, refuted by convergent infinite negative-power series) or any noeth-`A₀`
lemma. Everything downstream (`cor_8_32_maximal_liftedIdeal_ne_top`) is sorry-free *given* this. -/
theorem cor_8_32_spaExtendsAlongRestriction
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCoveringData A) (D : RationalLocData A) (hD : D ∈ C.covers)
    {w : Spv (presheafValue C.base)}
    (_hw : w ∈ Spa (presheafValue C.base) (presheafValue C.base)⁺)
    (_hv_rat : comap C.base.canonicalMap w ∈ rationalOpen D.T D.s) :
    ∃ w' : Spv (presheafValue D),
      comap (restrictionMapHom C.base D (C.hsubset D hD)) w' = w := by
  -- Lift the `A`-shadow `v = comap C.base.canonicalMap w` to a Spa point `w''` of `O_X(D)`
  -- (the genuine ⊇ extension, axiom-clean).
  obtain ⟨w'', hw''_spa, hw''_v⟩ := exists_spa_presheafValue_of_rationalOpen D _hv_rat
  refine ⟨w'', ?_⟩
  -- `restrictionMapHom ∘ C.base.canonicalMap = D.canonicalMap` (restriction commutes with ρ).
  have hcomp : (restrictionMapHom C.base D (C.hsubset D hD)).comp C.base.canonicalMap
      = D.canonicalMap := by
    ext a; exact restrictionMapHom_canonicalMap C.base D (C.hsubset D hD) a
  -- The restricted point `comap (restrictionMapHom) w''` and `w` both pull back along
  -- `C.base.canonicalMap` to `v`; injectivity on continuous points (Prop 7.48, now proven)
  -- pins them equal. Only continuity is needed, so no plus-preservation of `restrictionMapHom`.
  refine comap_canonicalMap_inj_of_isContinuous C.base
    (comap_isContinuous (restrictionMapHom_continuous C.base D (C.hsubset D hD)) hw''_spa.1)
    _hw.1 ?_
  calc comap C.base.canonicalMap
          (comap (restrictionMapHom C.base D (C.hsubset D hD)) w'')
      = comap ((restrictionMapHom C.base D (C.hsubset D hD)).comp C.base.canonicalMap) w'' := rfl
    _ = comap D.canonicalMap w'' := by rw [hcomp]
    _ = comap C.base.canonicalMap w := hw''_v

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Discharge of `hSpa_points` for non-open primes, conditional on
`liftedIdeal_ne_top`.**

Given:
- A prime `p` of `A` with `C.base.s ∉ p` (so `Ideal.map C.base.canonicalMap p`
  is "potentially proper").
- The hypothesis `liftedIdeal_ne_top`: `Ideal.map C.base.canonicalMap p ≠ ⊤`
  in `presheafValue C.base`.

This produces the required `v ∈ rationalOpen C.base.T C.base.s` with
`p ≤ v.supp`, by:
1. Lifting `liftedIdeal p` to a maximal ideal `𝔭` of `presheafValue C.base`
   (via `Ideal.exists_le_maximal`).
2. Using `tate_proper_ideal_not_open` to conclude `𝔭` is non-open
   (since `presheafValue C.base` is Tate).
3. Applying `exists_spa_point_supp_ge_in_presheafValue` (Lemma 7.45 on the
   completion) to get a Spa point of `presheafValue C.base`.
4. Pulling back via `exists_rationalOpen_of_completion_spa` to get the
   required Spa point of `A` in `rationalOpen C.base.T C.base.s`.

**Status**: this leaves only `liftedIdeal_ne_top` as the residual algebraic
input. That hypothesis is Wedhorn's analytic claim that algebraic completion
of Noetherian Tate localizations preserves properness of finitely generated
ideal extensions. -/
theorem hSpa_points_nonOpen_via_lifted_ideal_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (p : Ideal A) [hp : p.IsPrime] (hs_notin : C.base.s ∉ p)
    (h_lifted_ne_top :
      (Ideal.map C.base.canonicalMap p : Ideal (presheafValue C.base)) ≠ ⊤) :
    ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp := by
  -- Step 1: Lift `liftedIdeal p` to a maximal ideal `𝔭` of `presheafValue C.base`.
  obtain ⟨𝔭, h𝔭_max, h𝔭_le⟩ :=
    Ideal.exists_le_maximal (Ideal.map C.base.canonicalMap p) h_lifted_ne_top
  haveI : 𝔭.IsPrime := h𝔭_max.isPrime
  -- Step 2: 𝔭 is non-open since `presheafValue C.base` is a Tate ring and 𝔭 is proper.
  -- The Tate structure on presheafValue C.base via `presheafValue_isTateRing`.
  haveI : IsTateRing (presheafValue C.base) := presheafValue_isTateRing P C.base
  have h𝔭_notOpen : ¬IsOpen (𝔭 : Set (presheafValue C.base)) :=
    tate_proper_ideal_not_open h𝔭_max.ne_top
  -- Step 3: Apply Lemma 7.45 (via the completion route) to get a Spa point of
  -- presheafValue C.base with 𝔭 in its support.
  obtain ⟨w, hw_spa, hw_supp⟩ :=
    exists_spa_point_supp_ge_in_presheafValue C h𝔭_notOpen
  -- Step 4: liftedIdeal p ≤ 𝔭 ≤ w.supp.
  have hw_supp_lifted :
      (Ideal.map C.base.canonicalMap p : Ideal (presheafValue C.base)) ≤ w.supp :=
    h𝔭_le.trans hw_supp
  -- Step 5: Pull back via exists_rationalOpen_of_completion_spa.
  exact RationalLocData.exists_rationalOpen_of_completion_spa C.base
    hAplus_le_A₀ hcanonicalMap_cont hs_notin hw_spa hw_supp_lifted

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **T001 downstream bridge through the completion route.**

This is the corrected non-open-prime Spa-point construction with the necessary
denominator hypothesis `D'.s ∉ p`. It packages
`hSpa_points_nonOpen_via_lifted_ideal_proper` for the one-piece rational
covering with base `D'`.

The theorem deliberately remains downstream of `Presheaf.lean`, because its
proof uses the completed pair of definition on `presheafValue D'` from this
file. It does not change the final `tateAcyclicity` theorem's hypotheses; the
only remaining mathematical input is the pointwise properness of the lifted
ideal in `presheafValue D'`. -/
theorem spa_point_nonOpen_of_rational_subset_tate_of_liftedIdeal_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D D' : RationalLocData A)
    [IsNoetherianRing (locSubring D'.P D'.T D'.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ D'.P.A₀)
    (hcanonicalMap_cont : Continuous D'.canonicalMap)
    (_h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (p : Ideal A) [hp : p.IsPrime] (_hDs : D.s ∈ p)
    (hD's : D'.s ∉ p) (_hp_notOpen : ¬IsOpen (p : Set A))
    (h_lifted_ne_top :
      (Ideal.map D'.canonicalMap p : Ideal (presheafValue D')) ≠ ⊤) :
    ∃ v ∈ rationalOpen D'.T D'.s, p ≤ v.supp := by
  let C' : RationalCoveringData A :=
    { base := D'
      covers := {D'}
      hsubset := by
        intro E hE
        rw [Finset.mem_singleton] at hE
        subst E
        intro v hv
        exact hv
      hcover := by
        intro v hv
        exact ⟨D', Finset.mem_singleton_self D', hv⟩ }
  change ∃ v ∈ rationalOpen C'.base.T C'.base.s, p ≤ v.supp
  exact hSpa_points_nonOpen_via_lifted_ideal_proper P C'
    hAplus_le_A₀ hcanonicalMap_cont p hD's h_lifted_ne_top

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Full `hSpa_points` discharge, conditional on `liftedIdeal_ne_top` for
non-open primes.**

This combinator unifies the open-prime case (handled unconditionally via
`hSpa_points_open_prime`) and the non-open-prime case (handled conditionally
via `hSpa_points_nonOpen_via_lifted_ideal_proper`).

The remaining hypothesis `h_lifted_ne_top_for_nonOpen` is the ONLY residual:
for every NON-OPEN prime `p` of `A` with `C.base.s ∉ p`, the lifted ideal
`Ideal.map C.base.canonicalMap p` is proper in `presheafValue C.base`. -/
theorem hSpa_points_via_lifted_ideal_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (h_lifted_ne_top_for_nonOpen :
      ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p → ¬IsOpen (p : Set A) →
        (Ideal.map C.base.canonicalMap p : Ideal (presheafValue C.base)) ≠ ⊤) :
    ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp := by
  intro p hp hs
  by_cases hp_open : IsOpen (p : Set A)
  · exact hSpa_points_open_prime C p hp_open hs
  · exact hSpa_points_nonOpen_via_lifted_ideal_proper P C hAplus_le_A₀
      hcanonicalMap_cont p hs (h_lifted_ne_top_for_nonOpen p hp hs hp_open)

/-- **End-to-end `productRestriction_injective_tate` via the full `hSpa_points`
discharge, conditional on `liftedIdeal_ne_top` for non-open primes.**

This is the cleanest packaging through the Cor 8.32 route. It requires only:
- The standard instance bundle `[IsTateRing A] ...`.
- `(A⁺ : Set A) ⊆ C.base.P.A₀` and `Continuous C.base.canonicalMap` (both
  standard side conditions for the completion-route Spa pullback).
- `IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)` — derivable from
  `[IsNoetherianRing P.A₀]` via `Prop752.locSubring_isNoetherian` for the
  appropriate `P`; the user supplies the instance directly here.
- The residual `liftedIdeal_ne_top` hypothesis on non-open primes.

Once the residual is discharged (Wedhorn analytic input on completion of
Noetherian Tate localizations), `productRestriction_injective_tate` is
fully closed via the Cor 8.32 route. -/
theorem productRestriction_injective_tate_via_lifted_ideal_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (h_lifted_ne_top_for_nonOpen :
      ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p → ¬IsOpen (p : Set A) →
        (Ideal.map C.base.canonicalMap p : Ideal (presheafValue C.base)) ≠ ⊤)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_hSpa_points P C hne
    (hSpa_points_via_lifted_ideal_proper P C hAplus_le_A₀ hcanonicalMap_cont
      h_lifted_ne_top_for_nonOpen) x hx

/-! ### Reduction: `liftedIdeal ≠ ⊤` via `coeRingHom` properness

The residual `liftedIdeal_ne_top` factors algebraically through the
`coeRingHom`-properness question. Using `canonicalMap = coeRingHom ∘
algebraMap` and `Ideal.map_map`, `Ideal.map canonicalMap p` is literally
`Ideal.map coeRingHom (Ideal.map algebraMap p)`.

The A-level factor `Ideal.map (algebraMap A (Localization.Away D.s)) p` is
proper (≠ ⊤) **unconditionally** whenever `D.s ∉ p`, by
`IsLocalization.map_algebraMap_ne_top_iff_disjoint` (prime ideals are
radical, so disjointness from `powers D.s` reduces to `D.s ∉ p`).

This reduces the residual to the **completion-level** question: does the
completion map `coeRingHom : Localization.Away D.s → presheafValue D`
preserve properness of ideals?

The lemmas below package this reduction explicitly and expose the cleaner
residual hypothesis `coeRingHom_preserves_proper`. -/

omit [IsHuberRing A] [HasLocLiftPowerBounded A] [PlusSubring A] in
/-- **Factorization of the lifted ideal.** `Ideal.map canonicalMap p` equals
`Ideal.map coeRingHom (Ideal.map algebraMap p)`, by `canonicalMap =
coeRingHom ∘ algebraMap` and `Ideal.map_map`. -/
theorem liftedIdeal_eq_map_coeRingHom_algebraMap
    (D : RationalLocData A) (p : Ideal A) :
    (Ideal.map D.canonicalMap p : Ideal (presheafValue D)) =
      Ideal.map D.coeRingHom (Ideal.map (algebraMap A (Localization.Away D.s)) p) := by
  rw [show D.canonicalMap = D.coeRingHom.comp (algebraMap A (Localization.Away D.s))
    from rfl, ← Ideal.map_map]

omit [IsHuberRing A] [HasLocLiftPowerBounded A] [PlusSubring A] in
/-- **A-level proper extension** (unconditional): for a prime `p` of `A` with
`D.s ∉ p`, the extension to `Localization.Away D.s` is proper.

Combines `Ideal.IsPrime.isRadical` (prime ⇒ radical) with
`Ideal.disjoint_powers_iff_notMem` (`D.s ∉ p ↔ disjoint `powers D.s` from `p`)
and `IsLocalization.map_algebraMap_ne_top_iff_disjoint` (the localization
ne-top criterion). -/
theorem map_algebraMap_ne_top_of_notMem
    (D : RationalLocData A) {p : Ideal A} (hp : p.IsPrime) (hs : D.s ∉ p) :
    (Ideal.map (algebraMap A (Localization.Away D.s)) p : Ideal (Localization.Away D.s))
      ≠ ⊤ := by
  -- `D.s ∉ p` converts to `Disjoint (powers D.s) p` (prime ideals are radical).
  have hradical : p.IsRadical := hp.isRadical
  have hdisj : Disjoint (Submonoid.powers D.s : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem D.s hradical).mpr hs
  -- Localization ne-top iff disjoint.
  exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint
    (Submonoid.powers D.s) (Localization.Away D.s) p).mpr hdisj

omit [IsHuberRing A] [HasLocLiftPowerBounded A] [PlusSubring A] in
/-- **Reduction of `lifted_ideal_proper` to the completion-level question.**
Given the hypothesis that the completion map preserves properness of proper
ideals of the localization, `lifted_ideal_proper` follows for every prime `p`
of `A` with `D.s ∉ p`.

The hypothesis `hcoeRingHom_preserves_proper` captures the **sole remaining
analytic content**: whether the completion of a Noetherian Tate localization
preserves properness of ideal extensions. It is the cleaner restatement of
the residual in `coeRingHom`-only terms, orthogonal to the `A`-level input. -/
theorem liftedIdeal_ne_top_of_coeRingHom_preserves_proper
    (D : RationalLocData A)
    (hcoeRingHom_preserves_proper : ∀ (q : Ideal (Localization.Away D.s)),
      q ≠ ⊤ → Ideal.map D.coeRingHom q ≠ (⊤ : Ideal (presheafValue D)))
    {p : Ideal A} (hp : p.IsPrime) (hs : D.s ∉ p) :
    (Ideal.map D.canonicalMap p : Ideal (presheafValue D)) ≠ ⊤ := by
  rw [liftedIdeal_eq_map_coeRingHom_algebraMap D p]
  exact hcoeRingHom_preserves_proper _ (map_algebraMap_ne_top_of_notMem D hp hs)

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **End-to-end `hSpa_points` discharge via the `coeRingHom`-level
residual.** Composes `liftedIdeal_ne_top_of_coeRingHom_preserves_proper`
with `hSpa_points_via_lifted_ideal_proper`, exposing the **cleaner residual
hypothesis** `hcoeRingHom_preserves_proper` (properness preservation by the
completion map, independent of the `A`-level prime structure). -/
theorem hSpa_points_via_coeRingHom_preserves_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (hcoeRingHom_preserves_proper :
      ∀ (q : Ideal (Localization.Away C.base.s)),
        q ≠ ⊤ → Ideal.map C.base.coeRingHom q ≠
          (⊤ : Ideal (presheafValue C.base))) :
    ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp :=
  hSpa_points_via_lifted_ideal_proper P C hAplus_le_A₀ hcanonicalMap_cont
    (fun _ hp hs _ => liftedIdeal_ne_top_of_coeRingHom_preserves_proper
      C.base hcoeRingHom_preserves_proper hp hs)

/-- **Final end-to-end `productRestriction_injective_tate` via the
`coeRingHom`-level residual.** This is the **cleanest packaging** of the
Cor 8.32 route: the single remaining hypothesis
`hcoeRingHom_preserves_proper` is the `coeRingHom`-level analytic claim
(completion of a Noetherian Tate localization preserves properness).

Once this residual is discharged, `productRestriction_injective_tate` is
fully closed via the Cor 8.32 route. -/
theorem productRestriction_injective_tate_via_coeRingHom_preserves_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (hcoeRingHom_preserves_proper :
      ∀ (q : Ideal (Localization.Away C.base.s)),
        q ≠ ⊤ → Ideal.map C.base.coeRingHom q ≠
          (⊤ : Ideal (presheafValue C.base)))
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_hSpa_points P C hne
    (hSpa_points_via_coeRingHom_preserves_proper P C hAplus_le_A₀
      hcanonicalMap_cont hcoeRingHom_preserves_proper) x hx

/-! ### Summary of remaining residual

After this file's additions, the chain to fully discharge `hSpa_points`
unconditionally (under `[IsTateRing A] [IsNoetherianRing A] [T2Space A]
[NonarchimedeanRing A]`) reduces to a SINGLE algebraic claim, now restated
in its cleanest form:

> **`coeRingHom_preserves_proper`**: for every proper ideal
> `q : Ideal (Localization.Away C.base.s)`, the image
> `Ideal.map C.base.coeRingHom q` is proper in `presheafValue C.base`.

This is the "non-degenerate fiber" question for the analytic completion of
the Noetherian Tate localization `Localization.Away C.base.s`. It is a
specific instance of the question: when does completion of a Noetherian
topological ring preserve properness of finitely generated ideal extensions?

The reduction `liftedIdeal_ne_top_of_coeRingHom_preserves_proper` shows
that this cleaner residual **implies** the old residual
`liftedIdeal_ne_top` for all non-open primes (and indeed for every prime
`p` with `C.base.s ∉ p`, open or not — the openness hypothesis was a
side-effect of the reduction through Spa points, not of the algebraic
content). The A-level part of the factorization
(`Ideal.map algebraMap p ≠ ⊤`) is **unconditional** and packaged in
`map_algebraMap_ne_top_of_notMem`.

For Noetherian Tate localizations equipped with the localization topology,
the standard answer is YES, because:
- `Localization.Away C.base.s / q` is a non-zero Noetherian ring with the
  induced quotient topology.
- The completion of a non-zero Noetherian topological ring is non-zero
  (the natural map `R → R̂` is INJECTIVE for Hausdorff `R` of countable
  type, by Krull intersection in the Noetherian case).
- The non-zero completion `(Localization.Away s / q)^` quotients
  `presheafValue C.base` (via the universal property of completion + the
  surjection `Localization.Away s → Localization.Away s / q`).

A direct proof would require the project's infrastructure for completion
of Noetherian quotients (Krull intersection, completion-quotient
compatibility), which is conceptually distinct from the Cor 8.32
spectral content and currently lives in the Bourbaki CA III §2.8 chain
(see `project_T001_completion_route` memory). -/

/-! ### T-IDEAL-1: approximation for `coeRingHom`

Topological approximation lemma. Given
`1 ∈ Ideal.map D.coeRingHom q`, the unit `1` lies in the topological
closure of the image of `q` under the completion map `D.coeRingHom`. This
is the **density step** of the ideal-preservation argument: `q` is
approximated arbitrarily well from inside `Localization.Away D.s` at the
cost of passing through the completion map.

Combined with closedness of `q` in `presheafValue D` (T-IDEAL-2), this
would give `1 ∈ D.coeRingHom '' q` and hence a contradiction with `q ≠ ⊤`
in the `coeRingHom_preserves_proper` chain. -/

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **T-IDEAL-1 (approximation lemma for `coeRingHom`).** Given an ideal
`q ⊆ Localization.Away D.s` whose extension to `presheafValue D` contains
`1`, the element `1 : presheafValue D` lies in the **topological closure**
of the image `D.coeRingHom '' q`.

**Proof strategy.** The set `S := D.coeRingHom '' q` is a subgroup closed
under `D.coeRingHom`-image-multiplication. We show `closure S` is an
`presheafValue D`-submodule by promoting the multiplicative closure from
`D.coeRingHom '' (Loc.Away D.s)` to all of `presheafValue D` via density
(`UniformSpace.Completion.denseRange_coe`) and closedness of the
multiplication-preimage. Once `closure S` is a submodule containing `S`,
it contains `Ideal.span S = Ideal.map D.coeRingHom q`, hence `1`. -/
theorem one_mem_closure_coeRingHom_image
    (D : RationalLocData A) (q : Ideal (Localization.Away D.s))
    (h : (1 : presheafValue D) ∈ Ideal.map D.coeRingHom q) :
    (1 : presheafValue D) ∈
      closure ((D.coeRingHom '' (q : Set (Localization.Away D.s))) :
        Set (presheafValue D)) := by
  -- Abbreviate the image set.
  set S : Set (presheafValue D) := D.coeRingHom '' (q : Set _) with hS_def
  -- Basic closure properties of `S` as an image of the subgroup `q`.
  have hS_zero : (0 : presheafValue D) ∈ S :=
    ⟨0, q.zero_mem, map_zero _⟩
  have hS_add : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, q.add_mem ha hb, map_add _ _ _⟩
  -- For `a ∈ Loc.Away D.s` and `s ∈ S`, `coeRingHom a * s ∈ S` (ideal absorption).
  have hS_mul_coe : ∀ (a : Localization.Away D.s), ∀ {s}, s ∈ S →
      D.coeRingHom a * s ∈ S := by
    rintro a _ ⟨b, hb, rfl⟩
    exact ⟨a * b, q.mul_mem_left a hb, map_mul _ _ _⟩
  -- Dense range of the completion map `D.coeRingHom`.
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    intro y
    -- `D.coeRingHom` is definitionally `UniformSpace.Completion.coeRingHom` which has dense range.
    have := @UniformSpace.Completion.denseRange_coe (Localization.Away D.s) D.uniformSpace y
    exact this
  -- Key step: for all `b ∈ presheafValue D` and all `s ∈ S`, `b * s ∈ closure S`.
  have hmul_closure : ∀ (b : presheafValue D), ∀ s ∈ S, b * s ∈ closure S := by
    intro b
    refine hdense.induction_on (p := fun b => ∀ s ∈ S, b * s ∈ closure S) b ?_ ?_
    · -- closedness of `{b | ∀ s ∈ S, b * s ∈ closure S}`.
      rw [show {b | ∀ s ∈ S, b * s ∈ closure S} =
        ⋂ s ∈ S, (fun b => b * s) ⁻¹' closure S from by ext b; simp]
      refine isClosed_biInter fun s _ => ?_
      exact isClosed_closure.preimage (continuous_id.mul continuous_const)
    · intro a s hs
      exact subset_closure (hS_mul_coe a hs)
  -- `closure S` is closed under addition (since `S + S ⊆ S`).
  have hcl_add : ∀ {x y}, x ∈ closure S → y ∈ closure S → x + y ∈ closure S := by
    intro x y hx hy
    have h_add_maps : Set.MapsTo (fun p : presheafValue D × presheafValue D => p.1 + p.2)
        (S ×ˢ S) S := fun p hp => hS_add hp.1 hp.2
    have hxy_prod : (x, y) ∈ closure (S ×ˢ S) := by
      rw [closure_prod_eq]; exact ⟨hx, hy⟩
    exact map_mem_closure (f := fun p : presheafValue D × presheafValue D => p.1 + p.2)
      continuous_add hxy_prod h_add_maps
  -- `closure S` is closed under left-multiplication by `presheafValue D`.
  have hcl_smul : ∀ (b : presheafValue D), ∀ {x}, x ∈ closure S → b * x ∈ closure S := by
    intro b x hx
    have hbS_sub : (fun s => b * s) '' S ⊆ closure S := fun _ ⟨s, hs, hsb⟩ =>
      hsb ▸ hmul_closure b s hs
    have : b * x ∈ closure ((fun s => b * s) '' S) :=
      map_mem_closure (continuous_const.mul continuous_id) hx (fun _ hs => ⟨_, hs, rfl⟩)
    exact closure_minimal hbS_sub isClosed_closure this
  -- Assemble `closure S` as an `Ideal (presheafValue D)`.
  let J : Ideal (presheafValue D) :=
    { carrier := closure S
      zero_mem' := subset_closure hS_zero
      add_mem' := hcl_add
      smul_mem' := fun b _ hx => hcl_smul b hx }
  have hS_sub_J : S ⊆ (J : Set (presheafValue D)) := subset_closure
  -- `Ideal.map D.coeRingHom q ≤ J` since `q = Ideal.span q` and `J` contains `S`.
  have hmap_le_J : Ideal.map D.coeRingHom q ≤ J := by
    rw [show (q : Ideal (Localization.Away D.s)) = Ideal.span (q : Set _) from
      (Ideal.span_eq q).symm, Ideal.map_span]
    exact Ideal.span_le.mpr hS_sub_J
  -- Conclude `1 ∈ closure S` by applying `hmap_le_J` to `h`.
  exact hmap_le_J h

/-! ### T-IDEAL-2 closure combinator: `coeRingHom_preserves_proper` via
closedness of `q`

Given `one_mem_closure_coeRingHom_image` (T-IDEAL-1 approximation) plus the
**closedness** of a proper ideal `q` in the localization topology of
`Localization.Away D.s`, we close `coeRingHom_preserves_proper`. The key
topological input is that `D.coeRingHom` is `IsUniformInducing` (as the
completion map), hence `IsInducing`, hence `closure q = coeRingHom⁻¹(
closure (coeRingHom '' q))`. Combined with `q` closed, this gives
`1 ∈ coeRingHom '' q` from `1 ∈ closure (coeRingHom '' q)`, hence `1 ∈ q`,
contradicting `q ≠ ⊤`. -/

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **T-IDEAL-2 closure combinator**: if a proper ideal `q ⊆ Localization.Away
D.s` is closed in the localization topology `D.topology`, then
`Ideal.map D.coeRingHom q` is proper in `presheafValue D`.

This reduces the residual `coeRingHom_preserves_proper` to the purely
topological question "are (f.g.) ideals closed in the localization topology
of `Localization.Away D.s`?", which is the Artin-Rees question unlocked by
the generic `Ideal.isClosed_of_le_jacobson` in `IdealClosedness.lean`
(once the Jacobson containment + 𝔇 → A_s lift is established for the
specific Tate pair). -/
theorem coeRingHom_preserves_proper_of_closed
    (D : RationalLocData A)
    (q : Ideal (Localization.Away D.s))
    (h_proper : q ≠ ⊤)
    (h_closed : @IsClosed _ D.topology (q : Set (Localization.Away D.s))) :
    Ideal.map D.coeRingHom q ≠ ⊤ := by
  intro hmap_top
  -- `1 ∈ Ideal.map D.coeRingHom q`.
  have h1_map : (1 : presheafValue D) ∈ Ideal.map D.coeRingHom q := by
    rw [hmap_top]; exact Submodule.mem_top
  -- T-IDEAL-1: `1 ∈ closure (D.coeRingHom '' q)`.
  have h1_closure : (1 : presheafValue D) ∈
      closure ((D.coeRingHom '' (q : Set (Localization.Away D.s))) :
        Set (presheafValue D)) :=
    one_mem_closure_coeRingHom_image D q h1_map
  -- `D.coeRingHom` is `IsUniformInducing` (completion map) → `IsInducing`.
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  have h_uniformInducing :
      IsUniformInducing (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.isUniformInducing_coe (Localization.Away D.s)
  have h_inducing :
      Topology.IsInducing (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    h_uniformInducing.isInducing
  -- `closure q = coeRingHom⁻¹ (closure (coeRingHom '' q))`.
  have h_closure_eq := h_inducing.closure_eq_preimage_closure_image
    (q : Set (Localization.Away D.s))
  -- Since `q` is closed, `closure q = q`.
  rw [h_closed.closure_eq] at h_closure_eq
  -- `1 : presheafValue D = D.coeRingHom 1`, and `D.coeRingHom 1 ∈ closure (coeRingHom '' q)`,
  -- so `1 ∈ coeRingHom⁻¹ (closure ...) = q`.
  have h1_loc_in_q : (1 : Localization.Away D.s) ∈ (q : Set _) := by
    rw [h_closure_eq]
    change (D.coeRingHom : Localization.Away D.s → presheafValue D) 1 ∈
      closure ((D.coeRingHom '' (q : Set _)) : Set (presheafValue D))
    rw [map_one]
    exact h1_closure
  -- But `q ≠ ⊤` forces `1 ∉ q`, contradiction.
  exact h_proper (Ideal.eq_top_iff_one q |>.mpr h1_loc_in_q)

/-! ### locSubring-level closedness lift for `coeRingHom_preserves_proper`

Specializing `coeRingHom_preserves_proper_of_closed` to ideals `q ⊆
Localization.Away D.s` that arise as the image of an ideal of `locSubring`
closed in the J-adic topology. Uses:

* `locSubring_isOpen` (`Prop752.lean`) — the subring is open in `D.topology`.
* `IsClosed.of_isClosed_subspace_of_isOpen_subring` (`IdealClosedness.lean`)
  — open subgroup closedness transfer.

This bridges the generic Artin-Rees closedness on `locSubring` (via
`Ideal.isClosed_of_le_jacobson` / `Ideal.isClosed_of_isAdicComplete`) to
the hypothesis needed by `coeRingHom_preserves_proper_of_closed`. -/

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Image-of-ideal closedness bridge**: a subset of `locSubring` that is
closed in the subspace topology (equivalently `locIdeal`-adic, by
`locSubring_isAdic`) is closed in `Localization.Away D.s` with `D.topology`.

Used as the input-to-`coeRingHom_preserves_proper_of_closed` bridge when the
proper ideal `q ⊆ Localization.Away D.s` factors as the image of a closed
ideal of `locSubring`. -/
theorem isClosed_image_of_isClosed_subspace_in_locSubring
    (D : RationalLocData A)
    {C : Set (Localization.Away D.s)}
    (hC_sub : C ⊆ ((locSubring D.P D.T D.s) : Set (Localization.Away D.s)))
    (hC_closed_sub : @IsClosed _
      (D.topology.induced (locSubring D.P D.T D.s).subtype)
      (((locSubring D.P D.T D.s).subtype) ⁻¹' C : Set (locSubring D.P D.T D.s))) :
    @IsClosed _ D.topology C := by
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  haveI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  exact IsClosed.of_isClosed_subspace_of_isOpen_subring
    (locSubring_isOpen D.P D.T D.s D.hopen) hC_sub hC_closed_sub

/-! ### Prime-extension specialization: narrower closedness hypothesis

The general `coeRingHom_preserves_proper_of_closed` asks for closedness of
**every** proper ideal `q ⊆ Localization.Away D.s`. Producing that
uniformly would require `locIdeal ≤ Ideal.jacobson ⊥` in the Tate ring of
definition `locSubring D.P D.T D.s`, which is **false in degenerate cases**
(`Prop752.lean`): if the localization at `D.s` inverts an element of the
ideal of definition, then `locIdeal = ⊤` and the localization topology is
indiscrete.

The only downstream consumer of `coeRingHom_preserves_proper` inside the
`productRestriction_injective_tate` chain is
`liftedIdeal_ne_top_of_coeRingHom_preserves_proper`, which applies it at the
specific ideal `q = Ideal.map (algebraMap A (Localization.Away D.s)) p` for
a prime `p` of `A` with `D.s ∉ p`. Moreover,
`hSpa_points_via_lifted_ideal_proper` only needs the resulting
`liftedIdeal_ne_top` for **non-open** primes — the open case is handled
independently by `hSpa_points_open_prime`. Hence the weakest useful
closedness hypothesis is:

> for every non-open prime `p` of `A` with `D.s ∉ p`, the image ideal
> `Ideal.map (algebraMap A (Localization.Away D.s)) p` is closed in
> `D.topology`.

This is a closedness claim for a **specific family** of ideals (prime
extensions of non-open `A`-primes), not a global statement, and it avoids
the `locIdeal = ⊤` degeneracy.

The theorems below thread this narrower hypothesis through to the end-to-end
Cor 8.32 cover-injectivity combinator, producing
`productRestriction_injective_tate_via_prime_extension_closed`. -/

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Prime-extension specialization of T-IDEAL-2.** Under the closedness
hypothesis for the specific prime extension
`Ideal.map (algebraMap A (Localization.Away D.s)) p`, the image under
`D.coeRingHom` is proper in `presheafValue D`.

The algebraic properness of the source ideal (`≠ ⊤` in
`Localization.Away D.s`) is supplied internally by
`map_algebraMap_ne_top_of_notMem` (unconditional, radical + disjointness).
The topological closedness of the source ideal is the sole external input —
and it is stated pointwise at this one ideal, not uniformly over all proper
ideals. -/
theorem coeRingHom_preserves_proper_prime_extension_of_closed
    (D : RationalLocData A)
    {p : Ideal A} (hp : p.IsPrime) (hs : D.s ∉ p)
    (h_closed : @IsClosed _ D.topology
      ((Ideal.map (algebraMap A (Localization.Away D.s)) p :
          Ideal (Localization.Away D.s)) :
        Set (Localization.Away D.s))) :
    Ideal.map D.coeRingHom
      (Ideal.map (algebraMap A (Localization.Away D.s)) p :
        Ideal (Localization.Away D.s))
      ≠ (⊤ : Ideal (presheafValue D)) :=
  coeRingHom_preserves_proper_of_closed D _
    (map_algebraMap_ne_top_of_notMem D hp hs) h_closed

omit [IsHuberRing A] [HasLocLiftPowerBounded A] [PlusSubring A] in
/-- **`liftedIdeal ≠ ⊤` via closedness of a specific prime extension.** This
produces the exact signature consumed by `hSpa_points_via_lifted_ideal_proper`
at a single prime, but with a **pointwise** closedness hypothesis instead of
the global `coeRingHom_preserves_proper`. -/
theorem liftedIdeal_ne_top_of_prime_extension_closed
    (D : RationalLocData A)
    {p : Ideal A} (hp : p.IsPrime) (hs : D.s ∉ p)
    (h_closed : @IsClosed _ D.topology
      ((Ideal.map (algebraMap A (Localization.Away D.s)) p :
          Ideal (Localization.Away D.s)) :
        Set (Localization.Away D.s))) :
    (Ideal.map D.canonicalMap p : Ideal (presheafValue D)) ≠ ⊤ := by
  rw [liftedIdeal_eq_map_coeRingHom_algebraMap D p]
  exact coeRingHom_preserves_proper_prime_extension_of_closed D hp hs h_closed

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **T001 bridge via pointwise prime-extension closedness.**

This is the same downstream Spa-point construction as
`spa_point_nonOpen_of_rational_subset_tate_of_liftedIdeal_proper`, but with
the lifted-ideal properness discharged by the already isolated closedness
condition on the specific localization-prime extension. -/
theorem spa_point_nonOpen_of_rational_subset_tate_of_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D D' : RationalLocData A)
    [IsNoetherianRing (locSubring D'.P D'.T D'.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ D'.P.A₀)
    (hcanonicalMap_cont : Continuous D'.canonicalMap)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (p : Ideal A) [hp : p.IsPrime] (hDs : D.s ∈ p)
    (hD's : D'.s ∉ p) (hp_notOpen : ¬IsOpen (p : Set A))
    (h_closed : @IsClosed _ D'.topology
      ((Ideal.map (algebraMap A (Localization.Away D'.s)) p :
          Ideal (Localization.Away D'.s)) :
        Set (Localization.Away D'.s))) :
    ∃ v ∈ rationalOpen D'.T D'.s, p ≤ v.supp :=
  spa_point_nonOpen_of_rational_subset_tate_of_liftedIdeal_proper
    P D D' hAplus_le_A₀ hcanonicalMap_cont h p hDs hD's hp_notOpen
    (liftedIdeal_ne_top_of_prime_extension_closed D' hp hD's h_closed)

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **`hSpa_points` discharge via non-open-prime-extension closedness.**
Narrower-hypothesis analog of `hSpa_points_via_coeRingHom_preserves_proper`:
the only residual is closedness of `Ideal.map algebraMap p` in
`C.base.topology` for each **non-open** prime `p` of `A` with
`C.base.s ∉ p`. The open-prime case is handled internally by
`hSpa_points_open_prime`. -/
theorem hSpa_points_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (h_closed_nonOpen : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ¬IsOpen (p : Set A) →
      @IsClosed _ C.base.topology
        ((Ideal.map (algebraMap A (Localization.Away C.base.s)) p :
            Ideal (Localization.Away C.base.s)) :
          Set (Localization.Away C.base.s))) :
    ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp :=
  hSpa_points_via_lifted_ideal_proper P C hAplus_le_A₀ hcanonicalMap_cont
    (fun p hp hs hp_notOpen =>
      liftedIdeal_ne_top_of_prime_extension_closed C.base hp hs
        (h_closed_nonOpen p hp hs hp_notOpen))

/-- **End-to-end `productRestriction_injective_tate` via non-open-prime-
extension closedness.**

This is the **narrowest-hypothesis** form of the Cor 8.32 cover-injectivity
combinator currently available. The residual obligation is a pointwise
closedness claim for non-open-prime extensions, stated without any global
Jacobson-containment assumption on `locSubring`:

> For every non-open prime `p ⊂ A` with `C.base.s ∉ p`, the ideal extension
> `Ideal.map (algebraMap A (Localization.Away C.base.s)) p` is closed in
> `C.base.topology`.

This specific-family closedness is strictly weaker than the
`coeRingHom_preserves_proper` hypothesis of
`productRestriction_injective_tate_via_coeRingHom_preserves_proper`, and it
is strictly weaker than the global closedness "every proper ideal of
`Localization.Away C.base.s` is closed in `C.base.topology`" that would
follow from a global Jacobson containment.

Discharging the residual requires, for each such `p`, closedness of a
single specific ideal — not of every proper ideal of the localization.
Downstream work can target this narrower obligation. -/
theorem productRestriction_injective_tate_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (h_closed_nonOpen : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ¬IsOpen (p : Set A) →
      @IsClosed _ C.base.topology
        ((Ideal.map (algebraMap A (Localization.Away C.base.s)) p :
            Ideal (Localization.Away C.base.s)) :
          Set (Localization.Away C.base.s)))
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_hSpa_points P C hne
    (hSpa_points_via_prime_extension_closed P C hAplus_le_A₀
      hcanonicalMap_cont h_closed_nonOpen) x hx

/-! ### Conditional T-IDEAL-2 completion via `IsAdicComplete` (Route B)

The narrower-hypothesis `productRestriction_injective_tate_via_prime_extension_closed`
takes pointwise closedness for non-open prime extensions as a hypothesis.
Under `[IsAdicComplete (locIdeal) (locSubring)]` (the residual S-IDEAL-JAC
hypothesis, see `IdealLocalization.lean`), that pointwise closedness is
discharged for **every** proper ideal — in particular for prime extensions —
via the end-to-end assembly
`Ideal.isClosed_in_locTopology_of_isAdicComplete` (`IdealLocalization.lean`).

The remaining genuine residual is therefore a single class hypothesis
`[IsAdicComplete (locIdeal C.base.P C.base.T C.base.s) (locSubring C.base.P
C.base.T C.base.s)]` plus a Tate pseudo-uniformizer `π ∈ C.base.P.A₀`
(the latter supplied internally here from `IsTateRing`). -/

omit [IsHuberRing A] [HasLocLiftPowerBounded A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Helper**: every `PairOfDefinition` of a Tate ring contains a topologically
nilpotent unit. For any fixed `P`, pick a power `u^k` of the global
topologically-nilpotent unit `u : Aˣ` large enough that `u^k ∈ P.A₀`. -/
private theorem IsTateRing.exists_topologicallyNilpotent_unit_mem_A₀
    [IsTateRing A] (P : PairOfDefinition A) :
    ∃ π : A, IsTopologicallyNilpotent π ∧ IsUnit π ∧ π ∈ P.A₀ := by
  obtain ⟨u, hu_nilp⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  have h_nhds : (P.A₀ : Set A) ∈ nhds (0 : A) := P.isOpen.mem_nhds P.A₀.zero_mem
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hu_nilp h_nhds)
  refine ⟨(u : A) ^ (K + 1),
    isTopologicallyNilpotent_pow hu_nilp (Nat.succ_pos K),
    u.isUnit.pow (K + 1),
    hK (K + 1) (Nat.le_succ K)⟩

/-- **Conditional end-to-end `productRestriction_injective_tate`**
(Route B via completion `IsAdicComplete`).

Under `[IsAdicComplete (locIdeal C.base.P C.base.T C.base.s) (locSubring ...)]`
— the single residual from the S-IDEAL-JAC chain — the full Tate
cover-injectivity combinator holds. Combines:

- `productRestriction_injective_tate_via_prime_extension_closed` (narrower
  form above).
- `Ideal.isClosed_in_locTopology_of_isAdicComplete` (from
  `IdealLocalization.lean`, dispatches pointwise closedness for every
  proper ideal, in particular prime extensions).
- `IsTateRing.exists_topologicallyNilpotent_unit_mem_A₀` (picks a Tate
  pseudo-uniformizer `π ∈ C.base.P.A₀` for clearing denominators). -/
theorem productRestriction_injective_tate_of_isAdicComplete
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [IsAdicComplete (locIdeal C.base.P C.base.T C.base.s)
      (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 := by
  obtain ⟨π, hπ_nil, hπ_unit, hπ_A₀⟩ :=
    IsTateRing.exists_topologicallyNilpotent_unit_mem_A₀ C.base.P
  exact productRestriction_injective_tate_via_prime_extension_closed
    P C hne hAplus_le_A₀ hcanonicalMap_cont
    (fun _p _hp _hs _hp_notOpen =>
      Ideal.isClosed_in_locTopology_of_isAdicComplete
        C.base.P C.base.T C.base.s C.base.hopen hπ_nil hπ_A₀ hπ_unit _)
    x hx

/-! ### S-IDEAL-ASM via `ringOfDef` faithful-flatness (Lane B, no `locSubring`-completeness)

The Lane-B alternative to `productRestriction_injective_tate_of_isAdicComplete`:
instead of asserting the (false-in-general) `[IsAdicComplete (locIdeal)
(locSubring)]`, we assume **faithful flatness of `locSubringToRingOfDef`**,
i.e. `[Module.FaithfullyFlat (locSubring D.P D.T D.s) (presheafValue_ringOfDef D)]`.

This is the standard Noetherian-adic-completion faithful-flatness content
(Stacks 00MA). It does NOT assert `locSubring` itself is adic-complete.
The Jacobson containment on the target side comes for free from
`presheafValue_isAdicComplete` via Mathlib's `IsAdicComplete.le_jacobson_bot`,
and the faithful-flat descent
`locIdeal_le_jacobson_bot_of_faithfullyFlat` (`IdealLocalization.lean`)
pulls it back to `locSubring`. Combined with `Ideal.isClosed_of_le_jacobson`
(`IdealClosedness.lean`) and S-IDEAL-LOC's main
`Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`
(`IdealLocalization.lean`), and the existing prime-extension closure
combinator `productRestriction_injective_tate_via_prime_extension_closed`,
we close the full Tate acyclicity Part 1 under a single cleaner hypothesis. -/

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **S-IDEAL-JAC via `presheafValue_ringOfDef` faithful-flatness** — Tate
specialization of `locIdeal_le_jacobson_bot_of_faithfullyFlat`
(`IdealLocalization.lean`) to the concrete
`locSubring D.P D.T D.s → presheafValue_ringOfDef D` setup.

The target-side Jacobson containment is discharged by
`presheafValue_isAdicComplete` + Mathlib's `IsAdicComplete.le_jacobson_bot`.
Takes the faithful-flatness as a ring-hom-level `RingHom.FaithfullyFlat`
hypothesis to avoid forcing the caller to set up an `Algebra` instance. -/
theorem locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)]
    (hff : RingHom.FaithfullyFlat (locSubringToRingOfDef D)) :
    locIdeal D.P D.T D.s ≤
      Ideal.jacobson (⊥ : Ideal (locSubring D.P D.T D.s)) := by
  letI : Algebra (locSubring D.P D.T D.s) (presheafValue_ringOfDef D) :=
    (locSubringToRingOfDef D).toAlgebra
  haveI : Module.FaithfullyFlat (locSubring D.P D.T D.s)
      (presheafValue_ringOfDef D) := hff
  haveI : IsAdicComplete (presheafValue_idealOfDef D)
      (presheafValue_ringOfDef D) := presheafValue_isAdicComplete D
  have h_jac : presheafValue_idealOfDef D ≤
      Ideal.jacobson (⊥ : Ideal (presheafValue_ringOfDef D)) :=
    IsAdicComplete.le_jacobson_bot _
  exact locIdeal_le_jacobson_bot_of_faithfullyFlat
    (S := presheafValue_ringOfDef D) D.P D.T D.s h_jac

/-- **Closedness of any ideal of `locSubring` in the subspace topology**
under faithful-flatness of `locSubringToRingOfDef`.
Combines `locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat` with
`Ideal.isClosed_of_le_jacobson` (`IdealClosedness.lean`) + `locSubring_isAdic`
(`Prop752.lean`). Does not assert `locSubring` adic-complete. -/
theorem Ideal.isClosed_in_locSubring_subspace_of_ringOfDef_faithfullyFlat
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)]
    (hff : RingHom.FaithfullyFlat (locSubringToRingOfDef D))
    (q : Ideal (locSubring D.P D.T D.s)) :
    @IsClosed _
      ((locTopology D.P D.T D.s D.hopen).induced (locSubring D.P D.T D.s).subtype)
      (q : Set (locSubring D.P D.T D.s)) := by
  letI : TopologicalSpace (Localization.Away D.s) := locTopology D.P D.T D.s D.hopen
  haveI : IsTopologicalRing (Localization.Away D.s) :=
    (locBasis D.P D.T D.s D.hopen).toRingFilterBasis.isTopologicalRing
  letI : TopologicalSpace (locSubring D.P D.T D.s) :=
    (locTopology D.P D.T D.s D.hopen).induced (locSubring D.P D.T D.s).subtype
  haveI : IsTopologicalRing (locSubring D.P D.T D.s) :=
    Subring.instIsTopologicalRing (locSubring D.P D.T D.s)
  exact Ideal.isClosed_of_le_jacobson
    (locSubring_isAdic D.P D.T D.s D.hopen)
    (locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat P D hff) q

/-- **End-to-end closedness of proper ideals in `Localization.Away D.s`**
under faithful-flatness of `locSubringToRingOfDef`.
Combines `Ideal.isClosed_in_locSubring_subspace_of_ringOfDef_faithfullyFlat`
(subspace closure via S-IDEAL-JAC Lane-B descent) with S-IDEAL-LOC main
(`Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`).
Does not assert `locSubring` adic-complete. -/
theorem Ideal.isClosed_in_locTopology_of_ringOfDef_faithfullyFlat
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)]
    (hff : RingHom.FaithfullyFlat (locSubringToRingOfDef D))
    {π : A} (hπ_nil : IsTopologicallyNilpotent π) (hπ_A₀ : π ∈ D.P.A₀)
    (hπ_unit : IsUnit π) (q : Ideal (Localization.Away D.s)) :
    @IsClosed _ (locTopology D.P D.T D.s D.hopen)
      (q : Set (Localization.Away D.s)) := by
  apply Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring
    D.P D.T D.s D.hopen hπ_nil hπ_A₀ hπ_unit q
  exact Ideal.isClosed_in_locSubring_subspace_of_ringOfDef_faithfullyFlat P D hff _

/-- **Conditional end-to-end `productRestriction_injective_tate` via
`presheafValue_ringOfDef` faithful-flatness** (Lane B).

Under faithful-flatness of `locSubringToRingOfDef` — the standard
Noetherian adic-completion faithful-flatness content (Stacks 00MA),
**NOT** `locSubring` adic-completeness — the full Tate cover-injectivity
combinator holds. Parallel to `productRestriction_injective_tate_of_isAdicComplete`
above but without the locSubring-completeness hypothesis.

The single residual dischargeable downstream is
`(locSubringToRingOfDef C.base).FaithfullyFlat`. -/
theorem productRestriction_injective_tate_of_ringOfDef_faithfullyFlat
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hff : RingHom.FaithfullyFlat (locSubringToRingOfDef C.base))
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 := by
  obtain ⟨π, hπ_nil, hπ_unit, hπ_A₀⟩ :=
    IsTateRing.exists_topologicallyNilpotent_unit_mem_A₀ C.base.P
  exact productRestriction_injective_tate_via_prime_extension_closed
    P C hne hAplus_le_A₀ hcanonicalMap_cont
    (fun _p _hp _hs _hp_notOpen =>
      Ideal.isClosed_in_locTopology_of_ringOfDef_faithfullyFlat
        P C.base hff hπ_nil hπ_A₀ hπ_unit _)
    x hx

/-! ### S-IDEAL-ASM via Stacks 00MA (end-to-end Lane B)

This section packages the full Lane B chain from Stacks 00MA
(Noetherian adic-completion faithful-flatness residual) to
`coeRingHom_preserves_proper`, the central `T-IDEAL-2` target.

Chain:

```
Stacks 00MA: `Module.FaithfullyFlat locSubring (AdicCompletion locIdeal locSubring)`
  ↓ `locSubringToRingOfDef_faithfullyFlat_of_residual`
  ↓   (IdealLocalizationCompletion.lean, T-COMP-FF conditional)
`RingHom.FaithfullyFlat (locSubringToRingOfDef D)`
  ↓ `Ideal.isClosed_in_locTopology_of_ringOfDef_faithfullyFlat`
  ↓   (Cor832.lean, S-IDEAL-JAC + S-IDEAL-LOC via Lane B descent)
`IsClosed q` in `D.topology`, for every proper ideal `q ⊆ Loc.Away D.s`
  ↓ `coeRingHom_preserves_proper_of_closed`
`Ideal.map D.coeRingHom q ≠ ⊤`
```

The wrapper below makes this visible as a single named theorem, making
it trivial to plug in once the Stacks 00MA residual lands (either in
Mathlib or as project infrastructure). -/

/-- **End-to-end `coeRingHom_preserves_proper` via Stacks 00MA** (Lane B,
S-IDEAL-ASM). Given the Stacks-00MA faithful-flatness instance
`Module.FaithfullyFlat locSubring (AdicCompletion locIdeal locSubring)`,
every proper ideal `q ⊆ Localization.Away D.s` maps to a proper ideal
under `D.coeRingHom`.

This is the **conditional T-IDEAL-2 endpoint**. Compose with the
Cor 8.32 cover-injectivity chain
(`productRestriction_injective_tate_of_ringOfDef_faithfullyFlat`
variants above) or directly via
`liftedIdeal_ne_top_of_coeRingHom_preserves_proper` (Cor832.lean:1202). -/
theorem coeRingHom_preserves_proper_of_stacks00MA
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)]
    (h_stacks00MA : Module.FaithfullyFlat (locSubring D.P D.T D.s)
      (AdicCompletion (locIdeal D.P D.T D.s) (locSubring D.P D.T D.s)))
    (q : Ideal (Localization.Away D.s)) (h_proper : q ≠ ⊤) :
    Ideal.map D.coeRingHom q ≠ ⊤ := by
  obtain ⟨π, hπ_nil, hπ_unit, hπ_A₀⟩ :=
    IsTateRing.exists_topologicallyNilpotent_unit_mem_A₀ D.P
  have h_ff : RingHom.FaithfullyFlat (locSubringToRingOfDef D) :=
    locSubringToRingOfDef_faithfullyFlat_of_residual P D h_stacks00MA
  have h_closed : @IsClosed _ D.topology (q : Set (Localization.Away D.s)) :=
    Ideal.isClosed_in_locTopology_of_ringOfDef_faithfullyFlat P D h_ff
      hπ_nil hπ_A₀ hπ_unit q
  exact coeRingHom_preserves_proper_of_closed D q h_proper h_closed

/-- **End-to-end `coeRingHom_preserves_proper` via the Jacobson hypothesis**
(cleaner conditional form of `coeRingHom_preserves_proper_of_stacks00MA`).

Takes the purely algebraic Jacobson condition `locIdeal ≤ Jacobson ⊥` in
`locSubring` (classical Zariski-ring content) and produces
`coeRingHom_preserves_proper`. Composes the generic Stacks 00MA
(`AdicCompletion.faithfullyFlat_of_le_jacobson_bot` from
`AdicCompletionFaithfullyFlat.lean`) with the Stacks-00MA wrapper above.

**The Jacobson hypothesis is NOT asserted unconditionally.** Project-side
conditional paths (assuming completeness or FF to ringOfDef) are
available; unconditional content for uncompleted Tate localizations is
open — see boundary block at end of `AdicCompletionFaithfullyFlat.lean`. -/
theorem coeRingHom_preserves_proper_of_locIdeal_le_jacobson
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)]
    (h_jac : locIdeal D.P D.T D.s ≤
      Ideal.jacobson (⊥ : Ideal (locSubring D.P D.T D.s)))
    (q : Ideal (Localization.Away D.s)) (h_proper : q ≠ ⊤) :
    Ideal.map D.coeRingHom q ≠ ⊤ :=
  coeRingHom_preserves_proper_of_stacks00MA P D
    (AdicCompletion.faithfullyFlat_of_le_jacobson_bot _ h_jac) q h_proper

/-- **Cover-level injectivity via the Jacobson hypothesis** (Part 1 of
Wedhorn Thm 8.28 / Cor 8.32). Takes the purely algebraic Jacobson
condition on `locSubring` at `C.base` and produces injectivity of the
product restriction on the full rational covering. Composes Stacks 00MA
generic with `productRestriction_injective_tate_of_ringOfDef_faithfullyFlat`. -/
theorem productRestriction_injective_tate_of_locIdeal_le_jacobson
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (h_jac : locIdeal C.base.P C.base.T C.base.s ≤
      Ideal.jacobson (⊥ : Ideal (locSubring C.base.P C.base.T C.base.s)))
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_ringOfDef_faithfullyFlat P C hne
    (locSubringToRingOfDef_faithfullyFlat_of_locIdeal_le_jacobson P C.base h_jac)
    hAplus_le_A₀ hcanonicalMap_cont x hx

end ValuationSpectrum
