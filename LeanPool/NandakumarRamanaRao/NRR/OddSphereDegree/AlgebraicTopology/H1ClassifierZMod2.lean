/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.CohomologyCupProduct
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.Ideal.Lattice

/-!
# The Kronecker (evaluation) classifier `Hⁿ(X; F₂) → Hom(Hₙ(X; F₂), F₂)`

This file builds the **honest, general, formalized** evaluation classifier map

```text
Hⁿ(X; F₂) ⟶ Hom_{F₂}(Hₙ(X; F₂), F₂)
```

for the library's constructed singular cohomology `cohomologyZMod2 X n`
(`= Hⁿ(Hom(C_•(X), F₂))`) and the singular homology `homologyZMod2 X n`
(`= Hₙ(C_•(X) ⊗ F₂)`) of the *same* `F₂` chain complex `C_•(X)` underlying the
project's cochain complex.

This is the canonical natural map of the universal-coefficient sequence: it
sends a cohomology class `[φ]` (the class of an `n`-cocycle `φ`) to the functional
`[z] ↦ φ(z)` (evaluate the cocycle on a homology cycle). It is the classifier
map in the always-constructible direction. Concretely it is built by descending,
through the cokernel presentation `Hₙ(C) = coker(∂ : C_{n+1} → Z_n(C))`, the
evaluation `Z_n(C) → F₂`, `c ↦ φ(c)`, which kills boundaries exactly because `φ`
is a cocycle (`δφ = ∂^* φ = 0`); the bundled map descends, through the
cokernel presentation of `Hⁿ(Hom(C, F₂))`, the linear assignment `cocycle ↦ its
Kronecker functional`, which kills coboundaries.

## Main declarations

* `chainCxZMod2 X` / `homologyZMod2 X n` — the `F₂` singular chain complex of `X`
 underlying the library's cochain complex, and its `n`-th homology object.
* `kroneckerFunctional X n φ hφ : Hₙ(X; F₂) ⟶ F₂` — the functional on homology
 defined by a cocycle `φ`.
* `kroneckerFunctional_homologyπ` — its defining factorization through `homologyπ`.
* `kroneckerFunctional_apply` — its value on a homology cycle class:
 `⟨[φ], [c]⟩ = φ(c)`.
* `kroneckerFunctional_add`, `kroneckerFunctional_smul` — `F₂`-linearity in the
 cocycle.
* `kroneckerFunctional_coboundary` — the functional of a coboundary is zero.
* `kroneckerMap X n : Hⁿ(X; F₂) ⟶ Hom_{F₂}(Hₙ(X; F₂), F₂)` — the bundled
 `F₂`-linear classifier map.
* `kroneckerMap_cocycleClass` — `kroneckerMap [φ] = kroneckerFunctional φ`.

## Scope / blocker

The map `kroneckerMap` is the universal-coefficient *evaluation* map. Over the
field `F₂` it is an isomorphism (the universal coefficient theorem degenerates,
`Hom(−, F₂)` being exact); its **injectivity and surjectivity** require that
exactness, which is not available as a packaged instance in pinned Mathlib and is
the precise remaining input toward *inverting* the classifier (and thereby
producing a class `α ∈ H¹(RPⁿ; F₂)` from the monodromy character, together with a
degree-one Hurewicz comparison `π₁(X)ᵃᵇ ≅ H₁(X; ℤ)`).
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace SphereOddDegree

/-- The `F₂` singular chain complex of `X` underlying the library's cochain
complex `cochainCxZMod2 X = Hom(C_•(X), F₂)`. -/
abbrev chainCxZMod2 (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).obj X

/-- The `n`-th singular homology `Hₙ(X; F₂)`, as a `ModuleCat (ZMod 2)`-object. -/
abbrev homologyZMod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (chainCxZMod2 X).homology n

/-- The `F₂`-linear dual `Hom_{F₂}(Hₙ(X; F₂), F₂)` of singular homology, the
codomain of the Kronecker classifier. -/
abbrev homologyDualZMod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2) :=
  ModuleCat.of (ZMod 2) (homologyZMod2 X n →ₗ[ZMod 2] ZMod 2)

/-- Extensionality for maps out of `Hₙ(X; F₂)`: since `homologyπ` is an
epimorphism, two morphisms out of homology agree once they agree after
precomposition with `homologyπ`. -/
theorem homology_hom_ext {X : TopCat.{0}} {n : ℕ} {Z : ModuleCat.{0} (ZMod 2)}
    {f g : homologyZMod2 X n ⟶ Z}
    (h : (chainCxZMod2 X).homologyπ n ≫ f = (chainCxZMod2 X).homologyπ n ≫ g) :
    f = g :=
  (cancel_epi ((chainCxZMod2 X).homologyπ n)).1 h

/-- The cocycle condition rewritten on the chain differential: for a cocycle `φ`,
the composite `∂ ≫ (iCycles ≫ φ) = 0`, so `iCycles ≫ φ` descends along the
cokernel `homologyπ`. -/
theorem toCycles_iCycles_cochain_zero (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    (chainCxZMod2 X).toCycles (n + 1) n ≫ ((chainCxZMod2 X).iCycles n ≫ φ) = 0 := by
  rw [← Category.assoc, HomologicalComplex.toCycles_i]
  exact hφ

/-- The **Kronecker functional** of a cocycle `φ`: the `F₂`-linear functional on
`Hₙ(X; F₂)` obtained by descending the evaluation `Z_n(C) → F₂`, `c ↦ φ(c)`,
through the cokernel presentation `Hₙ(C) = coker(∂ : C_{n+1} → Z_n)`. -/
def kroneckerFunctional (X : TopCat.{0}) (n : ℕ) (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    homologyZMod2 X n ⟶ ModuleCat.of (ZMod 2) (ZMod 2) :=
  ((chainCxZMod2 X).homologyIsCokernel (n + 1) n (by simp [ComplexShape.prev])).desc
    (CokernelCofork.ofπ ((chainCxZMod2 X).iCycles n ≫ φ)
      (toCycles_iCycles_cochain_zero X n φ hφ))

/-- **Defining factorization** of the Kronecker functional: precomposing with
`homologyπ` recovers the evaluation `iCycles ≫ φ`. -/
theorem kroneckerFunctional_homologyπ (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    (chainCxZMod2 X).homologyπ n ≫ kroneckerFunctional X n φ hφ
      = (chainCxZMod2 X).iCycles n ≫ φ :=
  ((chainCxZMod2 X).homologyIsCokernel (n + 1) n (by simp [ComplexShape.prev])).fac
    (CokernelCofork.ofπ ((chainCxZMod2 X).iCycles n ≫ φ)
      (toCycles_iCycles_cochain_zero X n φ hφ)) WalkingParallelPair.one

theorem kroneckerFunctional_apply (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (c : (chainCxZMod2 X).cycles n) :
    (kroneckerFunctional X n φ hφ).hom (((chainCxZMod2 X).homologyπ n).hom c)
      = φ.hom (((chainCxZMod2 X).iCycles n).hom c) := by
  have h := kroneckerFunctional_homologyπ X n φ hφ
  have h2 := congrArg
    (fun (m : (chainCxZMod2 X).cycles n ⟶ ModuleCat.of (ZMod 2) (ZMod 2)) => m.hom c) h
  exact h2

theorem kroneckerFunctional_add (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) (hψ : cochainCoboundary (ZMod 2) X n ψ = 0)
    (hφψ : cochainCoboundary (ZMod 2) X n (φ + ψ) = 0) :
    kroneckerFunctional X n (φ + ψ) hφψ
      = kroneckerFunctional X n φ hφ + kroneckerFunctional X n ψ hψ := by
  apply homology_hom_ext
  have h1 := kroneckerFunctional_homologyπ X n (φ + ψ) hφψ
  have h2 := kroneckerFunctional_homologyπ X n φ hφ
  have h3 := kroneckerFunctional_homologyπ X n ψ hψ
  rw [Preadditive.comp_add, h2, h3, ← Preadditive.comp_add, h1]

theorem kroneckerFunctional_smul (X : TopCat.{0}) (n : ℕ) (s : ZMod 2)
    (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (hsφ : cochainCoboundary (ZMod 2) X n (s • φ) = 0) :
    kroneckerFunctional X n (s • φ) hsφ = s • kroneckerFunctional X n φ hφ := by
  apply homology_hom_ext
  have h1 := kroneckerFunctional_homologyπ X n (s • φ) hsφ
  have h2 := kroneckerFunctional_homologyπ X n φ hφ
  have h_smul : (chainCxZMod2 X).iCycles n ≫ (s • φ) = s • ((chainCxZMod2 X).iCycles n ≫ φ) := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
  have h_smul2 : (chainCxZMod2 X).homologyπ n ≫ (s • kroneckerFunctional X n φ hφ)
      = s • ((chainCxZMod2 X).homologyπ n ≫ kroneckerFunctional X n φ hφ) := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [h1, h_smul, h_smul2, h2]

theorem kroneckerFunctional_zero (X : TopCat.{0}) (n : ℕ)
    (h0 : cochainCoboundary (ZMod 2) X n (0 : singularCochainGroup (ZMod 2) X n) = 0) :
    kroneckerFunctional X n 0 h0 = 0 := by
  apply homology_hom_ext
  rw [kroneckerFunctional_homologyπ, comp_zero, comp_zero]

theorem kroneckerFunctional_coboundary (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup (ZMod 2) X m)
    (hcoc : cochainCoboundary (ZMod 2) X (m + 1) (cochainCoboundary (ZMod 2) X m η) = 0) :
    kroneckerFunctional X (m + 1) (cochainCoboundary (ZMod 2) X m η) hcoc = 0 := by
  apply homology_hom_ext
  rw [kroneckerFunctional_homologyπ, comp_zero]
  change (chainCxZMod2 X).iCycles (m + 1) ≫ ((chainCxZMod2 X).d (m + 1) m ≫ η) = 0
  rw [← Category.assoc, (chainCxZMod2 X).iCycles_d, zero_comp]

theorem kroneckerFunctional_congr (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup (ZMod 2) X n} (h : φ = φ')
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (hφ' : cochainCoboundary (ZMod 2) X n φ' = 0) :
    kroneckerFunctional X n φ hφ = kroneckerFunctional X n φ' hφ' := by
  subst h; rfl

theorem kroneckerFunctional_iCycles_add (X : TopCat.{0}) (n : ℕ)
    (c c' : (cochainCxZMod2 X).cycles n) :
    (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom (c + c'))
        (cochainCoboundary_iCycles X n (c + c'))).hom
      = (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c)
          (cochainCoboundary_iCycles X n c)).hom
        + (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c')
            (cochainCoboundary_iCycles X n c')).hom := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((chainCxZMod2 X).homologyπ n)).1 inferInstance x
  have h_add := kroneckerFunctional_apply X n (((cochainCxZMod2 X).iCycles n).hom (c + c')) (cochainCoboundary_iCycles X n (c + c')) z
  have h_c := kroneckerFunctional_apply X n (((cochainCxZMod2 X).iCycles n).hom c) (cochainCoboundary_iCycles X n c) z
  have h_c' := kroneckerFunctional_apply X n (((cochainCxZMod2 X).iCycles n).hom c') (cochainCoboundary_iCycles X n c') z
  rw [h_add, LinearMap.add_apply, h_c, h_c']
  have hmap : ((cochainCxZMod2 X).iCycles n).hom (c + c')
      = ((cochainCxZMod2 X).iCycles n).hom c + ((cochainCxZMod2 X).iCycles n).hom c' := map_add _ c c'
  rw [hmap]
  rfl

theorem kroneckerFunctional_iCycles_smul (X : TopCat.{0}) (n : ℕ) (s : ZMod 2)
    (c : (cochainCxZMod2 X).cycles n) :
    (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom (s • c))
        (cochainCoboundary_iCycles X n (s • c))).hom
      = s • (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c)
          (cochainCoboundary_iCycles X n c)).hom := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((chainCxZMod2 X).homologyπ n)).1 inferInstance x
  have h_smul := kroneckerFunctional_apply X n (((cochainCxZMod2 X).iCycles n).hom (s • c)) (cochainCoboundary_iCycles X n (s • c)) z
  have h_c := kroneckerFunctional_apply X n (((cochainCxZMod2 X).iCycles n).hom c) (cochainCoboundary_iCycles X n c) z
  rw [h_smul, LinearMap.smul_apply, h_c]
  have hmap : ((cochainCxZMod2 X).iCycles n).hom (s • c)
      = s • ((cochainCxZMod2 X).iCycles n).hom c := map_smul _ s c
  rw [hmap]
  rfl

/-- Evaluate cocycles on homology classes through the Kronecker pairing. -/
def kroneckerCyclesMap (X : TopCat.{0}) (n : ℕ) :
    (cochainCxZMod2 X).cycles n ⟶ homologyDualZMod2 X n :=
  ModuleCat.ofHom
    { toFun := fun c =>
        (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c)
          (cochainCoboundary_iCycles X n c)).hom
      map_add' := kroneckerFunctional_iCycles_add X n
      map_smul' := kroneckerFunctional_iCycles_smul X n }

@[simp] theorem kroneckerCyclesMap_hom_apply (X : TopCat.{0}) (n : ℕ)
    (c : (cochainCxZMod2 X).cycles n) :
    (kroneckerCyclesMap X n).hom c
      = (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c)
          (cochainCoboundary_iCycles X n c)).hom := rfl

theorem kroneckerCyclesMap_toCycles (X : TopCat.{0}) (n : ℕ) :
    (cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ kroneckerCyclesMap X n = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro w
  show (kroneckerCyclesMap X n).hom (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w) = 0
  rw [kroneckerCyclesMap_hom_apply]
  apply LinearMap.ext; intro x
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((chainCxZMod2 X).homologyπ n)).1 inferInstance x
  have h_w := kroneckerFunctional_apply X n (((cochainCxZMod2 X).iCycles n).hom
      (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w)) (cochainCoboundary_iCycles X n _) z
  rw [h_w, LinearMap.zero_apply]
  have heq : ((cochainCxZMod2 X).iCycles n).hom
      (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w)
      = (((cochainCxZMod2 X).d ((ComplexShape.up ℕ).prev n) n).hom w) := by
    rw [← ModuleCat.comp_apply, (cochainCxZMod2 X).toCycles_i]
  rw [heq]
  by_cases h : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev n) n
  · have hcob : (((cochainCxZMod2 X).d ((ComplexShape.up ℕ).prev n) n).hom w)
        = (chainCxZMod2 X).d n ((ComplexShape.up ℕ).prev n) ≫ w := rfl
    rw [hcob]
    have h_comp : ((chainCxZMod2 X).d n ((ComplexShape.up ℕ).prev n) ≫ w).hom (((chainCxZMod2 X).iCycles n).hom z)
        = w.hom ((((chainCxZMod2 X).iCycles n ≫ (chainCxZMod2 X).d n ((ComplexShape.up ℕ).prev n)).hom) z) := by
      change w.hom (((chainCxZMod2 X).d n ((ComplexShape.up ℕ).prev n)).hom (((chainCxZMod2 X).iCycles n).hom z)) = _
      rfl
    have h_zero : (chainCxZMod2 X).iCycles n ≫ (chainCxZMod2 X).d n ((ComplexShape.up ℕ).prev n) = 0 :=
      (chainCxZMod2 X).iCycles_d n ((ComplexShape.up ℕ).prev n)
    rw [h_comp, h_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact map_zero _
  · have hz : ((cochainCxZMod2 X).d ((ComplexShape.up ℕ).prev n) n).hom w = 0 := by
      rw [(cochainCxZMod2 X).shape ((ComplexShape.up ℕ).prev n) n h, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hz]
    rfl

/-- The Kronecker map from cohomology to the linear dual of homology. -/
def kroneckerMap (X : TopCat.{0}) (n : ℕ) :
    cohomologyZMod2 X n ⟶ homologyDualZMod2 X n :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).desc
    (CokernelCofork.ofπ (kroneckerCyclesMap X n) (kroneckerCyclesMap_toCycles X n))

theorem kroneckerMap_homologyπ (X : TopCat.{0}) (n : ℕ) :
    (cochainCxZMod2 X).homologyπ n ≫ kroneckerMap X n = kroneckerCyclesMap X n :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).fac
    (CokernelCofork.ofπ (kroneckerCyclesMap X n) (kroneckerCyclesMap_toCycles X n))
    WalkingParallelPair.one

theorem kroneckerMap_cocycleClass (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    (kroneckerMap X n).hom (cocycleClass X n φ hφ)
      = (kroneckerFunctional X n φ hφ).hom := by
  dsimp [cocycleClass]
  have h := congrArg (fun (f : (cochainCxZMod2 X).cycles n ⟶ homologyDualZMod2 X n) =>
      f.hom ((cochainCxZMod2 X).cyclesMk φ (n + 1) (cochainCx_next n) hφ)) (kroneckerMap_homologyπ X n)
  dsimp at h
  rw [h, kroneckerCyclesMap_hom_apply]
  have h_mk := (cochainCxZMod2 X).i_cyclesMk φ (n + 1) (cochainCx_next n) hφ
  have h_congr : kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom
      ((cochainCxZMod2 X).cyclesMk φ (n + 1) (cochainCx_next n) hφ)) (cochainCoboundary_iCycles X n _)
    = kroneckerFunctional X n φ hφ := by
    apply homology_hom_ext
    have h1 := kroneckerFunctional_homologyπ X n (((cochainCxZMod2 X).iCycles n).hom
      ((cochainCxZMod2 X).cyclesMk φ (n + 1) (cochainCx_next n) hφ)) (cochainCoboundary_iCycles X n _)
    have h2 := kroneckerFunctional_homologyπ X n φ hφ
    have h_c : (chainCxZMod2 X).iCycles n ≫ ((cochainCxZMod2 X).iCycles n).hom ((cochainCxZMod2 X).cyclesMk φ (n + 1) (cochainCx_next n) hφ)
        = (chainCxZMod2 X).iCycles n ≫ φ := by
      have := congrArg (fun (ψ : singularCochainGroup (ZMod 2) X n) => (chainCxZMod2 X).iCycles n ≫ ψ) h_mk
      exact this
    exact h1.trans (h_c.trans h2.symm)
  rw [h_congr]

theorem chainCxZMod2_iCycles_ker (X : TopCat.{0}) (n : ℕ) :
    LinearMap.ker ((chainCxZMod2 X).iCycles n).hom = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact (ModuleCat.mono_iff_injective ((chainCxZMod2 X).iCycles n)).1 inferInstance

theorem moduleInjective_ZMod2 (M : Type) [AddCommGroup M] [Module (ZMod 2) M] :
    Module.Injective (ZMod 2) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Module.Baer.injective
  intro I g
  rcases eq_or_ne I ⊥ with h | h
  · subst h
    refine ⟨0, fun x mem => ?_⟩
    have hx : (⟨x, mem⟩ : ↑(⊥ : Ideal (ZMod 2))) = 0 := by
      apply Subtype.ext; simpa using mem
    rw [hx, map_zero]; rfl
  · have htop : I = ⊤ := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      rw [Ideal.eq_top_iff_one]
      have ha1 : a = 1 := by
        fin_cases a
        · exfalso; exact ha0 rfl
        · rfl
      rwa [ha1] at ha
    subst htop
    refine ⟨{ toFun := fun x => g ⟨x, Submodule.mem_top⟩, map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro a b; rw [← map_add]; rfl
    · intro c a; rw [← map_smul]; rfl
    · intro x mem; rfl

theorem chainCxZMod2_iCycles_split (X : TopCat.{0}) (n : ℕ) :
    ∃ s : (chainCxZMod2 X).X n ⟶ (chainCxZMod2 X).cycles n,
      (chainCxZMod2 X).iCycles n ≫ s = 𝟙 ((chainCxZMod2 X).cycles n) := by
  have : Module.Injective (ZMod 2) ((chainCxZMod2 X).cycles n) :=
    moduleInjective_ZMod2 _
  have : CategoryTheory.Injective ((chainCxZMod2 X).cycles n) :=
    Module.injective_object_of_injective_module (ZMod 2) ((chainCxZMod2 X).cycles n)
  exact ⟨CategoryTheory.Injective.factorThru (𝟙 _) ((chainCxZMod2 X).iCycles n),
    CategoryTheory.Injective.comp_factorThru _ _⟩

theorem kroneckerMap_surjective (X : TopCat.{0}) (n : ℕ) :
    Function.Surjective (kroneckerMap X n).hom := by
  intro g
  obtain ⟨s, hs⟩ := chainCxZMod2_iCycles_split X n
  let g_mor : (chainCxZMod2 X).homology n ⟶ ModuleCat.of (ZMod 2) (ZMod 2) := ModuleCat.ofHom g
  set φ : singularCochainGroup (ZMod 2) X n :=
    s ≫ (chainCxZMod2 X).homologyπ n ≫ g_mor with hφdef
  have h_r_iCycles : (chainCxZMod2 X).iCycles n ≫ φ
      = (chainCxZMod2 X).homologyπ n ≫ g_mor := by
    change ((chainCxZMod2 X).iCycles n ≫ s) ≫ (chainCxZMod2 X).homologyπ n ≫ g_mor = _
    rw [hs, Category.id_comp]
  have h_phi_cocycle : cochainCoboundary (ZMod 2) X n φ = 0 := by
    have hto := (chainCxZMod2 X).toCycles_i (n + 1) n
    have hzero := HomologicalComplex.toCycles_comp_homologyπ (chainCxZMod2 X) (n + 1) n
    have h_to_assoc : (chainCxZMod2 X).d (n + 1) n ≫ φ
        = (chainCxZMod2 X).toCycles (n + 1) n ≫ ((chainCxZMod2 X).iCycles n ≫ φ) := by
      have := congrArg (fun (f : (chainCxZMod2 X).X (n + 1) ⟶ (chainCxZMod2 X).X n) => f ≫ φ) hto
      simp only [Category.assoc] at this
      exact this.symm
    have h_hom_assoc : (chainCxZMod2 X).toCycles (n + 1) n ≫ ((chainCxZMod2 X).homologyπ n ≫ g_mor)
        = ((chainCxZMod2 X).toCycles (n + 1) n ≫ (chainCxZMod2 X).homologyπ n) ≫ g_mor :=
      (Category.assoc _ _ _).symm
    have hzero_comp : ((chainCxZMod2 X).toCycles (n + 1) n ≫ (chainCxZMod2 X).homologyπ n) ≫ g_mor = 0 := by
      have := congrArg (fun (f : (chainCxZMod2 X).X (n + 1) ⟶ (chainCxZMod2 X).homology n) => f ≫ g_mor) hzero
      exact this.trans zero_comp
    change (chainCxZMod2 X).d (n + 1) n ≫ φ = 0
    rw [h_to_assoc, h_r_iCycles, h_hom_assoc, hzero_comp]
  refine ⟨cocycleClass X n φ h_phi_cocycle, ?_⟩
  rw [kroneckerMap_cocycleClass]
  have hkf : kroneckerFunctional X n φ h_phi_cocycle = g_mor := by
    apply homology_hom_ext
    have hfac := kroneckerFunctional_homologyπ X n φ h_phi_cocycle
    exact hfac.trans h_r_iCycles
  have hkf_hom := congrArg (fun (f : homologyZMod2 X n ⟶ ModuleCat.of (ZMod 2) (ZMod 2)) => f.hom) hkf
  dsimp [g_mor] at hkf_hom
  exact hkf_hom

end SphereOddDegree
