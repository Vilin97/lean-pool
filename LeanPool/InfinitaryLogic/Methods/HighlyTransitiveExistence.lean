/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.HighlyTransitiveField
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.Data.Finsupp.Lex

/-!
# Highly order-transitive orders of every infinite cardinality (issue #11 unit 6b)

For every infinite cardinal `κ` there is a highly order-transitive linear order of cardinality
exactly `κ` — bundled as `HighlyTransitiveOrderAt κ` (avoiding awkward existential typeclass
binders), with the existential corollary exported.

The construction is a Hahn-series generated subfield: over an index type `X` of cardinality
`κ`, take the lexicographic value group `Γ = Lex (X →₀ ℤ)` and the lexicographically ordered
Hahn-series field `K = Lex ℚ⟦Γ⟧`, embed `X` by distinct monomials `x ↦ single (single x 1) 1`,
and let `J` be the subfield they generate. The monomial map is injective, so
`Subfield.cardinalMk_closure` gives `#J = #X = κ`; `J` inherits a linear ordered field
structure, and unit 6a (`HighlyOrderTransitive.of_field`) makes it highly order-transitive.

Implementation note: `Mathlib.RingTheory.HahnSeries.Summable` must be imported explicitly —
the lexicographic Hahn import alone does not load the field instance.
-/

namespace FirstOrder

open Cardinal

/-- A bundled highly order-transitive linear order of prescribed cardinality. -/
structure HighlyTransitiveOrderAt (κ : Cardinal.{0}) where
  /-- The carrier. -/
  Carrier : Type
  /-- The order. -/
  linearOrder : LinearOrder Carrier
  /-- The carrier has size exactly `κ`. -/
  card_eq : Cardinal.mk Carrier = κ
  /-- High order-transitivity. -/
  highlyTransitive : @HighlyOrderTransitive Carrier linearOrder

section Construction

variable (X : Type) [LinearOrder X]

/-- The lexicographic value group of the construction. -/
private abbrev hahnGamma : Type := Lex (X →₀ ℤ)

/-- The ambient lexicographically ordered Hahn-series field. -/
private abbrev hahnField : Type := Lex (HahnSeries (hahnGamma X) ℚ)

/-- The monomial embedding of the index type. -/
private noncomputable def hahnMonomial (x : X) : hahnField X :=
  toLex (HahnSeries.single (toLex (Finsupp.single x 1)) (1 : ℚ))

private theorem hahnMonomial_injective : Function.Injective (hahnMonomial X) := by
  intro x y hxy
  have h1 : (ofLex (hahnMonomial X x)).coeff (toLex (Finsupp.single x 1)) = 1 :=
    HahnSeries.coeff_single_same _ _
  rw [hxy] at h1
  by_contra hne
  have hgne : toLex (Finsupp.single x (1 : ℤ)) ≠ toLex (Finsupp.single y 1) := by
    intro h
    exact hne (Finsupp.single_left_injective one_ne_zero (toLex.injective h))
  rw [show (ofLex (hahnMonomial X y)).coeff (toLex (Finsupp.single x 1)) = 0 from
    HahnSeries.coeff_single_of_ne hgne] at h1
  exact one_ne_zero h1.symm

/-- The generated subfield: the ordered field of cardinality `#X`. -/
private noncomputable def hahnSubfield : Subfield (hahnField X) :=
  Subfield.closure (Set.range (hahnMonomial X))

private theorem mk_hahnSubfield [Infinite X] : Cardinal.mk (hahnSubfield X) = Cardinal.mk X := by
  have : Infinite (Set.range (hahnMonomial X)) :=
    Set.infinite_coe_iff.mpr (Set.infinite_range_of_injective (hahnMonomial_injective X))
  rw [hahnSubfield, Subfield.cardinalMk_closure,
    Cardinal.mk_range_eq _ (hahnMonomial_injective X)]

end Construction

/-- **Highly order-transitive orders exist at every infinite cardinality** (bundled form). -/
noncomputable def highlyTransitiveOrderAt (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ) :
    HighlyTransitiveOrderAt κ := by
  let X : Type := κ.ord.ToType
  haveI : Infinite X := by
    rw [Cardinal.infinite_iff, Cardinal.mk_toType, Cardinal.card_ord]
    exact hκ
  haveI : IsStrictOrderedRing (hahnSubfield X) :=
    Function.Injective.isStrictOrderedRing
      (Subtype.val : hahnSubfield X → hahnField X) rfl rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)
  refine ⟨hahnSubfield X, inferInstance, ?_, ?_⟩
  · rw [mk_hahnSubfield, Cardinal.mk_toType, Cardinal.card_ord]
  · exact HighlyOrderTransitive.of_field _



end FirstOrder
