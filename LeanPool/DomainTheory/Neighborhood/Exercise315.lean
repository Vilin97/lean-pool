/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Product

/-!
# Exercise 3.15 (Scott 1981, PRG-19, §3) — the usual product isomorphisms

Scott asks for the standard isomorphisms of the product construction. Because
Proposition 3.2 gives
the order-isomorphism `prodEquiv : |𝒟₀ × 𝒟₁| ≃o |𝒟₀| × |𝒟₁|`, every isomorphism
reduces to the
corresponding fact about cartesian products of *ordered sets*: mathlib's
`OrderIso.prodComm` and
`OrderIso.prodAssoc`, together with the two product congruences
`prodCongrOrderIso` /
`prodUniqueOrderIso` we record here.

* **(i)** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀` — `prodCommD`.
* **(ii)** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂` — `prodAssocD`.
* **The product of no factors** is the one-point (terminal) domain `𝟙 = unitSys`;
it is a two-sided
  unit for `×`: `𝒟 × 𝟙 ≅ 𝒟 ≅ 𝟙 × 𝒟` (`prodUnitD`, `unitProdD`).
* **(iii)** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'` — `prodCongrD` /
  `Isomorphic.prod`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-! ### Order-iso helpers for cartesian products. -/

/-- The product of two order isomorphisms, as an order isomorphism. -/
def prodCongrOrderIso {A B C D : Type*} [Preorder A] [Preorder B] [Preorder C] [Preorder D]
    (e₀ : A ≃o B) (e₁ : C ≃o D) : A × C ≃o B × D where
  toFun p := (e₀ p.1, e₁ p.2)
  invFun q := (e₀.symm q.1, e₁.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_rel_iff' := by
    simp_all

/-- For a `Unique` second factor, `A × C ≃o A` (forget the constant component). -/
def prodUniqueOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : A × C ≃o A where
  toFun p := p.1
  invFun a := (a, default)
  left_inv p := by
    have : (default : C) = p.2 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    simp_all

/-- For a `Unique` first factor, `C × A ≃o A` (forget the constant component). -/
def uniqueProdOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : C × A ≃o A where
  toFun p := p.2
  invFun a := (default, a)
  left_inv p := by
    have : (default : C) = p.1 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    simp_all

/-! ### (i) Commutativity. -/

/-- **Exercise 3.15(i) (Scott 1981, PRG-19).** The commutativity order-isomorphism
`|𝒟₀ × 𝒟₁| ≃o |𝒟₁ × 𝒟₀|`, factored through Proposition 3.2 and the cartesian swap. -/
def prodCommD (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (prod V₀ V₁).Element ≃o (prod V₁ V₀).Element :=
  (prodEquiv V₀ V₁).trans (OrderIso.prodComm.trans (prodEquiv V₁ V₀).symm)

/-- **Exercise 3.15(i).** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀`. -/
theorem prod_comm_isomorphic : prod V₀ V₁ ≅ᴰ prod V₁ V₀ := ⟨prodCommD V₀ V₁⟩

/-! ### (ii) Associativity. -/

/-- **Exercise 3.15(ii) (Scott 1981, PRG-19).** The associativity
order-isomorphism
`|𝒟₀ × (𝒟₁ × 𝒟₂)| ≃o |(𝒟₀ × 𝒟₁) × 𝒟₂|`. -/
def prodAssocD (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    (prod V₀ (prod V₁ V₂)).Element ≃o (prod (prod V₀ V₁) V₂).Element :=
  (prodEquiv V₀ (prod V₁ V₂)).trans <|
    (prodCongrOrderIso (OrderIso.refl V₀.Element) (prodEquiv V₁ V₂)).trans <|
      (OrderIso.prodAssoc V₀.Element V₁.Element V₂.Element).symm.trans <|
        (prodCongrOrderIso (prodEquiv V₀ V₁).symm (OrderIso.refl V₂.Element)).trans
          (prodEquiv (prod V₀ V₁) V₂).symm

/-- **Exercise 3.15(ii).** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂`. -/
theorem prod_assoc_isomorphic : prod V₀ (prod V₁ V₂) ≅ᴰ prod (prod V₀ V₁) V₂ :=
  ⟨prodAssocD V₀ V₁ V₂⟩

/-! ### The product of no factors — the terminal (one-point) domain. -/

/-- The **terminal domain** `𝟙`: the neighbourhood system over `Unit` with the
single
neighbourhood `Δ = univ`. Its domain `|𝟙|` has exactly one element (`⊥ = {Δ}`), so
`𝟙` is the
*product of no factors*. -/
def unitSys : NeighborhoodSystem Unit where
  mem X := X = Set.univ
  master := Set.univ
  master_mem := rfl
  inter_mem := by rintro X Y Z rfl rfl _ _; simp
  sub_master := by rintro X rfl; exact subset_rfl

/-- `|𝟙|` is a subsingleton: every element is `⊥`. -/
theorem unitSys_element_eq (x : unitSys.Element) : x = unitSys.bot := by
  apply Element.ext
  intro Y
  constructor
  · intro hY; rw [mem_bot]; exact x.sub hY
  · intro hY; rw [mem_bot] at hY; subst hY; exact x.master_mem

instance : Unique unitSys.Element where
  default := unitSys.bot
  uniq := unitSys_element_eq

/-- **Exercise 3.15 (empty product).** `𝟙` is a right unit: `𝒟 × 𝟙 ≅ 𝒟`. -/
def prodUnitD (V₀ : NeighborhoodSystem α) :
    (prod V₀ unitSys).Element ≃o V₀.Element :=
  (prodEquiv V₀ unitSys).trans (prodUniqueOrderIso _ _)

theorem prod_unit_isomorphic : prod V₀ unitSys ≅ᴰ V₀ := ⟨prodUnitD V₀⟩

/-- **Exercise 3.15 (empty product).** `𝟙` is a left unit: `𝟙 × 𝒟 ≅ 𝒟`. -/
def unitProdD (V₀ : NeighborhoodSystem α) :
    (prod unitSys V₀).Element ≃o V₀.Element :=
  (prodEquiv unitSys V₀).trans (uniqueProdOrderIso _ _)

theorem unit_prod_isomorphic : prod unitSys V₀ ≅ᴰ V₀ := ⟨unitProdD V₀⟩

/-! ### (iii) Functoriality of `≅`. -/

/-- **Exercise 3.15(iii) (Scott 1981, PRG-19).** Two domain isomorphisms induce
one on the products:
`|𝒟₀ × 𝒟₁| ≃o |𝒟₀' × 𝒟₁'|`. -/
def prodCongrD (e₀ : V₀.Element ≃o V₀'.Element) (e₁ : V₁.Element ≃o V₁'.Element) :
    (prod V₀ V₁).Element ≃o (prod V₀' V₁').Element :=
  (prodEquiv V₀ V₁).trans ((prodCongrOrderIso e₀ e₁).trans (prodEquiv V₀' V₁').symm)

/-- **Exercise 3.15(iii).** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'`. -/
theorem Isomorphic.prod (h₀ : V₀ ≅ᴰ V₀') (h₁ : V₁ ≅ᴰ V₁') : prod V₀ V₁ ≅ᴰ prod V₀' V₁' :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨prodCongrD e₀ e₁⟩

end Domain.Neighborhood
