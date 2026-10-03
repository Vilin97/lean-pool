/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom

/-! # Class Field Axiom -/

@[expose] public section
namespace ClassFormation

open CyclicCohomology

/-!
# Abstract reciprocity: the class field axiom

The coefficient group for a finite cyclic extension `L / K` is the actual
fixed module `A_L`, descended to the actual quotient `G_K / G_L`.  Thus the
two numbers below are the orders of the Tate groups occurring in the
original statement the class-field axiom, rather than cardinality data attached to an
auxiliary reciprocity map.
-/

noncomputable
section

open CategoryTheory

/-! `Representation.Rep` places its coefficient ring and acting group in the
same universe.  The shared `IntegralRepGroupType` boundary records the
universe forced by the coefficient ring `ℤ` without scattering raw
universe-zero declarations through the reciprocity API. -/

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The finite cohomology data asserted at one finite cyclic extension.
Finiteness is stored before either natural-valued cardinality is formed. -/
structure ClassFieldAxiomCohomologyData (A : Rep ℤ G)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) : Prop where
  /-- The degree-zero Tate cohomology group is finite. -/
  finiteTateHZero : Finite (tateCohomology (E.fixedRepresentation A) 0)
  /-- The degree-minus-one Tate cohomology group is finite. -/
  finiteTateHMinusOne :
    Finite (tateCohomology (E.fixedRepresentation A) (-1))
  /-- Degree-zero Tate cohomology has cardinality equal to the extension degree. -/
  tateHZero_card :
    Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ)
  /-- Degree-minus-one Tate cohomology is trivial by cardinality. -/
  tateHMinusOne_card :
    Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1

/-- **The class-field axiom.**  For every finite cyclic extension `L / K`
with `K` finite over the distinguished base field,
`#H⁰(G(L/K), A_L) = [L : K]` and `#H⁻¹(G(L/K), A_L) = 1`.

Both the base field and the cyclic extension are bundled, so containment,
finiteness, normality, and the chosen generator cannot become detached from
the subgroups to which they belong. -/
def SatisfiesClassFieldAxiom (A : Rep ℤ G) : Prop :=
  ∀ (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K),
    ClassFieldAxiomCohomologyData A K E

namespace SatisfiesClassFieldAxiom

variable {A : Rep ℤ G}

/-- The degree-zero half of the class-field axiom for a bundled cyclic
extension. -/
theorem tateHZero_card
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ) :=
  (hcf K E).tateHZero_card

/-- The degree-minus-one half of the class-field axiom for a bundled cyclic
extension. -/
theorem tateHMinusOne_card
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1 :=
  (hcf K E).tateHMinusOne_card

/-- The order-one assertion in the class-field axiom gives actual vanishing of
`H⁻¹(G(L/K), A_L)`. -/
theorem tateHMinusOne_isZero
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1)) := by
  let H := tateCohomology (E.fixedRepresentation A) (-1)
  let : Finite H := (hcf K E).finiteTateHMinusOne
  have hcard : Nat.card H = 1 := by
    simpa [H] using hcf.tateHMinusOne_card K E
  let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact ModuleCat.isZero_of_subsingleton H

end SatisfiesClassFieldAxiom

end
end ClassFormation
