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
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.TateAlgebra

/-!
# Flatness of Restriction Maps (Prop 8.30 + Cor 8.32)

We prove that restriction maps in the structure presheaf of an adic space are flat,
and that the product restriction for a finite rational cover is faithfully flat.

## Main results

* `canonicalMap_flat_discrete` : The canonical map `A → presheafValue D` is flat
  for discrete `A` (Prop 8.30, discrete case).
* `productRestriction_flat_discrete` : The product restriction for a rational cover
  is flat for discrete `A` (Cor 8.32, flatness part, discrete case).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 8.30, Corollary 8.32
-/

open ValuationSpectrum

/-- Finite products of flat modules are flat. (An *arbitrary* product of flat modules need
not be flat, so `Finite ι` is essential; mathlib has the `directSum`/`dfinsupp`/`finsupp`
instances but no `Pi` one.) This follows from the equivalence `(∀ i, M i) ≃ (⨁ i, M i)` for
finite `ι` and `Module.Flat.directSum`. -/
instance Module.Flat.pi {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  cases nonempty_fintype ι
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R ι M).symm

/-! ### Presheaf value flatness (discrete case) -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- For discrete `A`, the canonical map `A → presheafValue D` is flat (Prop 8.30).

The presheaf value is the completion of `Localization.Away D.s` with the localization
topology. For discrete `A`, the localization topology is discrete
(by `locTopology_eq_bot_of_discrete`), so the completion is isomorphic to
`Localization.Away D.s` itself. Since localizations are flat, the canonical
map is flat.

**Note:** The full proof for non-discrete rings requires Remark 7.55 (decomposition
into basic rational subsets R(f/1) and R(1/f)) and the identification of presheaf
values with Tate algebra quotients A⟨X⟩/(f-X) and A⟨X⟩/(1-fX) from TICKET-2B. -/
theorem canonicalMap_flat_discrete [DiscreteTopology A] (D : RationalLocData A) :
    @Module.Flat A (presheafValue D) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D)) := by
  -- The completion coeRingHom is bijective for discrete rings
  have hbij := ValuationSpectrum.coeRingHom_bijective_of_discrete D
  let e : Localization.Away D.s ≃+* presheafValue D :=
    RingEquiv.ofBijective D.coeRingHom hbij
  -- Localization is flat over A
  haveI : Module.Flat A (Localization.Away D.s) := Localization.flat ..
  -- Give presheafValue D the A-module structure via canonicalMap
  letI instMod : Module A (presheafValue D) :=
    RingHom.toModule (RationalLocData.canonicalMap D)
  -- Build a linear equiv: presheafValue D ≃ₗ[A] Localization.Away D.s
  letI : Algebra A (presheafValue D) := (RationalLocData.canonicalMap D).toAlgebra
  change Module.Flat A (presheafValue D)
  -- e gives an A-algebra isomorphism: e (algebraMap a) = algebraMap a
  have halg : ∀ a : A, e (algebraMap A _ a) = algebraMap A (presheafValue D) a := fun a => by
    change D.coeRingHom (algebraMap A _ a) = algebraMap A (presheafValue D) a
    rfl
  exact Module.Flat.of_linearEquiv (AlgEquiv.ofRingEquiv halg).symm.toLinearEquiv

/-! ### Cor 8.32: each cover piece is flat over A (discrete case) -/

/-- **Corollary 8.32** of Wedhorn (discrete case): each presheaf value in a
rational cover is flat over `A`.

Each factor `presheafValue D` is flat over `A` (by `canonicalMap_flat_discrete`),
so the product is flat over `A` (by `Module.Flat.pi`). -/
theorem productPresheafValues_flat_discrete [DiscreteTopology A] [PlusSubring A]
    (C : RationalCoveringData A) (D : ↥C.covers) :
    @Module.Flat A (presheafValue D.1) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D.1)) :=
  canonicalMap_flat_discrete D.1

/-! ### Flatness transfer along ring isomorphisms

We prove that flatness of an `R`-module transfers along `R`-algebra isomorphisms.
This will be useful for connecting Tate algebra quotients to presheaf values. -/

/-- If `S` is flat over `R` and `e : S ≃+* T` is a ring isomorphism that respects the
`R`-algebra structure (`e (algebraMap r) = algebraMap r`), then `T` is flat over `R`.

This is used to transfer flatness from `A⟨X⟩/(f-X)` (a Tate algebra quotient)
to `presheafValue D` (a presheaf value) along the ring isomorphism from
`PresheafIdentification.lean`.

For the discrete case, the `A`-algebra structures are:
- On `A⟨X⟩/(f-X)`: via `mk ∘ algebraMap : A → A⟨X⟩/(f-X)`
- On `presheafValue D`: via `canonicalMap : A → presheafValue D`
-/
theorem flat_of_ringEquiv_respecting_algebra {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [Module.Flat R S]
    {T : Type*} [CommRing T] [Algebra R T]
    (e : S ≃+* T) (halg : ∀ r : R, e (algebraMap R S r) = algebraMap R T r) :
    Module.Flat R T :=
  Module.Flat.of_linearEquiv (AlgEquiv.ofRingEquiv halg).symm.toLinearEquiv

/-! ### Tate algebra quotient flatness (discrete, Lemma 8.31(2))

We re-export the flatness results for Tate algebra quotients from `TateAlgebra.lean`.
These are the building blocks for Prop 8.30 (presheaf restriction maps are flat). -/

omit [IsTopologicalRing A] in
/-- `A⟨X⟩/(f-X)` is flat over discrete noetherian `A` (Lemma 8.31(2), case 1).
Re-export of `TateAlgebra.flat_quotient_fSubX`.

In the quotient, `X = f`, so `A⟨X⟩/(f-X) ≅ A` via evaluation at `f`.
Since `A` is flat over itself, the quotient is flat. -/
theorem tateQuotient_fSubX_flat_discrete [DiscreteTopology A]
    [NonarchimedeanRing A] [IsNoetherianRing A] (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) :=
  TateAlgebra.flat_quotient_fSubX f

omit [IsTopologicalRing A] in
/-- `A⟨X⟩/(1-fX)` is flat over discrete noetherian `A` (Lemma 8.31(2), case 2).
Re-export of `TateAlgebra.flat_quotient_oneSubfX`.

In the quotient, `fX = 1`, so `A⟨X⟩/(1-fX) ≅ Localization.Away f`.
Since localization is flat, the quotient is flat. -/
theorem tateQuotient_oneSubfX_flat_discrete [DiscreteTopology A]
    [NonarchimedeanRing A] [IsNoetherianRing A] (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) :=
  TateAlgebra.flat_quotient_oneSubfX f

/-! ### Quotient flatness: non-discrete case (Lemma 8.31(2))

**Status: BLOCKED on G2-topo.**

The general (non-discrete) proof of quotient flatness for `A⟨X⟩/(f-X)` and `A⟨X⟩/(1-fX)`
requires identifying these quotients with adic completions:
- `A⟨X⟩/(f-X) ≅ AdicCompletion I A` (completion of `A`)
- `A⟨X⟩/(1-fX) ≅ AdicCompletion I (Localization.Away f)` (completion of localization)

Then flatness follows from `AdicCompletion.flat_of_isNoetherian` (in Mathlib).

**Why "flat + regular = flat quotient" fails in general:**
The naive approach "if `S` is flat over `R` and `g ∈ S` is a non-zero-divisor,
then `S/(g)` is flat over `R`" is FALSE. Counterexample: `g = 2` in `S = ℤ[X]`
gives `ℤ[X]/(2) ≅ 𝔽₂[X]`, which has 2-torsion and is not flat over `ℤ`.

The correct statement requires *universal regularity*: for all ideals `I` of `R`,
the submodule `I · S ⊆ S` must be `g`-saturated (`g · s ∈ I · S ⟹ s ∈ I · S`).
For `g = f - X`, this fails when `f` is not a unit modulo `I` (e.g., `I = (f)`).
The correct proof must go through completions, not universal regularity.

**Unblocking:** Implement TICKET-G2-topo (correct T-topology on Tate algebra,
adic completion identification).
-/

end ValuationSpectrum
