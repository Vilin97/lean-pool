/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise315
import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 3.23 (Scott 1981, PRG-19, §3) — the category of domains is cartesian
closed

Exercise 3.23 asks (for category theorists) to read off from Theorems 3.11 and
3.12 that the category
of domains and approximable mappings is *cartesian closed*, to identify its
terminal object, and to
say what sort of functor `(𝒟₀ → 𝒟₁)` is.

The three ingredients are already in the development; this file packages them and
supplies the
missing terminal object:

* **Terminal object.** The one-point domain `𝟙 = unitSys` (Exercise 3.15) is
*terminal*: there is a
  unique approximable mapping `𝒟 → 𝟙` (`Unique (ApproximableMap V unitSys)`),
  because `|𝟙|` is a
  subsingleton.
* **Finite products.** `prod` with `proj₀`, `proj₁` is the categorical product
(Exercise 3.20).
* **Exponentials.** `curryEquiv` (Theorem 3.12) is the natural adjunction
  `Hom(𝒟₀ × 𝒟₁, 𝒟₂) ≃o Hom(𝒟₀, (𝒟₁ → 𝒟₂))`, exhibiting `(𝒟₁ → 𝒟₂)` as the
  exponential `𝒟₂^𝒟₁`.

So `𝟙`, `×`, and `→` make the category cartesian closed, and `(𝒟₀ → -)` is a
(covariant) functor
right adjoint to `- × 𝒟₀`. Everything is **choice-free** (`#print axioms ⊆
{propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### The terminal domain. -/

/-- There is at most one approximable mapping into the terminal domain `𝟙`: the
codomain `|𝟙|`
is a subsingleton, so any two maps have the same elementwise action. -/
instance : Subsingleton (ApproximableMap V unitSys) :=
  ⟨fun _ _ => ext_of_toElementMap fun _ => Subsingleton.elim _ _⟩

/-- **Exercise 3.23 (Scott 1981, PRG-19).** `𝟙 = unitSys` is the *terminal
object*: for every domain
`𝒟` there is a unique approximable mapping `𝒟 → 𝟙` (the constant map at `⊥`). -/
instance : Unique (ApproximableMap V unitSys) where
  default := constMap V (default : unitSys.Element)
  uniq _ := Subsingleton.elim _ _

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The unique map to the terminal object,
named. -/
def toUnit : ApproximableMap V unitSys := default

theorem toUnit_unique (f : ApproximableMap V unitSys) : f = toUnit V := Subsingleton.elim _ _

/-! ### The exponential adjunction (cartesian closure). -/

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The cartesian-closed adjunction
`Hom(𝒟₀ × 𝒟₁, 𝒟₂) ≃o Hom(𝒟₀, (𝒟₁ → 𝒟₂))`, exhibiting `(𝒟₁ → 𝒟₂)` as the
exponential object. This
is exactly `curryEquiv` of Theorem 3.12. -/
def homAdjunction (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) :=
  curryEquiv V₀ V₁ V₂

end Domain.Neighborhood
