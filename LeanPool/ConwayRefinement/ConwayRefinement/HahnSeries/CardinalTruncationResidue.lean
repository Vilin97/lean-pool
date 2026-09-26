/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation

/-!
# Residues of cardinal-bounded nonpositive Hahn series

The cardinal-bounded nonpositive Hahn series form an algebra over their coefficient field.
Coefficient at exponent zero is an algebra retraction, and imposing that this residue lie in a
coefficient subring recovers the usual cardinal-bounded truncation integer part.

This is the bounded counterpart of
`HahnSeries.Nonpositive.truncationIntegerPartEquivResidueSubring`. It allows equation-local
residue normalization without forgetting the support-cardinality bound.
-/

public noncomputable section

open Cardinal
open scoped HahnSeries

universe u v

namespace HahnSeries

variable {G : Type u} {L : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field L] [Fact (aleph0 < κ)]

/-- Cardinal-bounded Hahn series with nonpositive support. -/
abbrev CardSuppLTNonpositive := cardSuppLTTruncationIntegerPart
  (G := G) (R := L) (κ := κ) (⊤ : Subring L)

/-- Constant series as a ring map into cardinal-bounded nonpositive Hahn series. -/
noncomputable def CardSuppLTNonpositive.C :
    L →+* CardSuppLTNonpositive (G := G) (L := L) (κ := κ) where
  toFun r := ⟨⟨HahnSeries.C r, by
    exact (HahnSeries.cardSupp_single_le (0 : G) r).trans_lt
      (one_lt_aleph0.trans (Fact.out : aleph0 < κ))⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    constructor
    · intro g hg
      have hg0 : g = 0 := HahnSeries.support_single_subset hg
      exact hg0 ▸ le_rfl
    · exact Subring.mem_top _⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one HahnSeries.C
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul HahnSeries.C x y
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_zero HahnSeries.C
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add HahnSeries.C x y

/-- Cardinal-bounded nonpositive Hahn series form an algebra over their coefficient field. -/
noncomputable instance : Algebra L (CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) where
  algebraMap := CardSuppLTNonpositive.C
  smul r x := CardSuppLTNonpositive.C r * x
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

namespace CardSuppLTNonpositive

/-- Coefficient at exponent zero as an algebra retraction on bounded nonpositive series. -/
def constantCoeffAlgHom :
    CardSuppLTNonpositive (G := G) (L := L) (κ := κ) →ₐ[L] L where
  toFun x := (x : L⟦G⟧).coeff 0
  map_one' := by simp
  map_mul' x y := by
    have hx := (mem_cardSuppLTTruncationIntegerPart (Z := (⊤ : Subring L))).mp x.2
    have hy := (mem_cardSuppLTTruncationIntegerPart (Z := (⊤ : Subring L))).mp y.2
    let x' : HahnSeries.Nonpositive G L := ⟨x, hx.1⟩
    let y' : HahnSeries.Nonpositive G L := ⟨y, hy.1⟩
    exact HahnSeries.Nonpositive.coeff_zero_mul x' y'
  map_zero' := by simp
  map_add' x y := by simp
  commutes' r := by
    change (HahnSeries.C r : L⟦G⟧).coeff 0 = r
    simp

@[simp]
theorem constantCoeffAlgHom_apply
    (x : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :
    constantCoeffAlgHom x = (x : L⟦G⟧).coeff 0 :=
  (rfl)

/-- The canonical identity-on-series equivalence between the bounded truncation integer part and
the residue-preimage presentation inside bounded nonpositive Hahn series. -/
def truncationIntegerPartEquivResidueSubring (S : Subring L) :
    cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S ≃+*
      Subring.residueSubring
        (constantCoeffAlgHom (G := G) (L := L) (κ := κ)) S where
  toFun x := ⟨⟨x, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    exact ⟨((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp x.2).1,
      Subring.mem_top _⟩⟩, by
        rw [Subring.mem_residueSubring, constantCoeffAlgHom_apply]
        exact ((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp x.2).2⟩
  invFun x := ⟨x.1.1, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    exact ⟨((mem_cardSuppLTTruncationIntegerPart (Z := (⊤ : Subring L))).mp x.1.2).1,
      x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The residue-subring presentation does not change the underlying Hahn series. -/
@[simp]
theorem coe_truncationIntegerPartEquivResidueSubring (S : Subring L)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
    ((((truncationIntegerPartEquivResidueSubring S x :
        Subring.residueSubring constantCoeffAlgHom S) :
      CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) : L⟦G⟧)) =
      (x : L⟦G⟧) :=
  (rfl)

/-- An exact ambient refinement of bounded nonpositive series can be normalized into the bounded
truncation integer part using primality of the first constant coefficient. -/
theorem exists_refinement_truncationIntegerPart_of_ambient
    (S : Subring L)
    {a b c d : cardSuppLTTruncationIntegerPart
      (G := G) (R := L) (κ := κ) S}
    (haS : IsPrimal (⟨(a : L⟦G⟧).coeff 0,
      ((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp a.2).2⟩ : S))
    (hfrac : Subring.fracSubring S = ⊤) (ha0 : a ≠ 0)
    (habcd : a * b = c * d)
    {e f g h : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)}
    (ha : ((truncationIntegerPartEquivResidueSubring S a :
      Subring.residueSubring constantCoeffAlgHom S) :
        CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) = e * f)
    (hb : ((truncationIntegerPartEquivResidueSubring S b :
      Subring.residueSubring constantCoeffAlgHom S) :
        CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) = g * h)
    (hc : ((truncationIntegerPartEquivResidueSubring S c :
      Subring.residueSubring constantCoeffAlgHom S) :
        CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) = e * g)
    (hd : ((truncationIntegerPartEquivResidueSubring S d :
      Subring.residueSubring constantCoeffAlgHom S) :
        CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) = f * h) :
    ∃ E F H₁ H₂ : cardSuppLTTruncationIntegerPart
        (G := G) (R := L) (κ := κ) S,
      a = E * F ∧ b = H₁ * H₂ ∧ c = E * H₁ ∧ d = F * H₂ := by
  let Φ := truncationIntegerPartEquivResidueSubring
    (G := G) (L := L) (κ := κ) S
  have haS' : IsPrimal
      (⟨constantCoeffAlgHom ((Φ a : Subring.residueSubring constantCoeffAlgHom S) :
          CardSuppLTNonpositive (G := G) (L := L) (κ := κ)), (Φ a).2⟩ : S) := by
    convert haS using 1
    apply Subtype.ext
    rfl
  have ha0' : Φ a ≠ 0 := Φ.injective.ne ha0
  have habcd' : Φ a * Φ b = Φ c * Φ d := by
    simpa only [map_mul] using congrArg Φ habcd
  obtain ⟨E, F, H₁, H₂, ha', hb', hc', hd'⟩ :=
    Subring.exists_refinement_residueSubring_of_ambient haS' hfrac ha0' habcd'
      ha hb hc hd
  exact ⟨Φ.symm E, Φ.symm F, Φ.symm H₁, Φ.symm H₂,
    by simpa using congrArg Φ.symm ha',
    by simpa using congrArg Φ.symm hb',
    by simpa using congrArg Φ.symm hc',
    by simpa using congrArg Φ.symm hd'⟩

end CardSuppLTNonpositive

namespace CardSuppLTTruncationIntegerPart

private theorem isUnit_map_of_isUnit {M N : Type*} [Monoid M] [Monoid N]
    (f : M →* N) {x : M} (hx : IsUnit x) : IsUnit (f x) :=
  hx.map f

private theorem isPrimal_residueSubring_of_isUnit
    {F A : Type*} [Field F] [CommRing A] [Algebra F A] [IsDomain A]
    (π : A →ₐ[F] F) (S : Subring F) [DecompositionMonoid S]
    {x : A} (hx : π x ∈ S) (hx0 : π x ≠ 0) (hunit : IsUnit x) :
    IsPrimal (⟨x, hx⟩ : Subring.residueSubring π S) :=
  Subring.isPrimal_residueSubring_of_isPrimal
    hx hx0 (DecompositionMonoid.primal _) hunit.isPrimal

private theorem isPrimal_equiv_preimage
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {x : A}
    (hx : IsPrimal (e x)) : IsPrimal x :=
  (RingEquiv.isPrimal_iff e x).mp hx

/-- An order-zero element of a cardinal-bounded truncation integer part is primal when its
coefficient subring is pre-Schreier. -/
theorem isPrimal_of_order_eq_zero
    (S : Subring L) [DecompositionMonoid S]
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S)
    (horder : ((toNonpositiveRingHom S x : Nonpositive G L) : HahnSeries G L).order = 0) :
    IsPrimal x := by
  let A := CardSuppLTNonpositive (G := G) (L := L) (κ := κ)
  let π := CardSuppLTNonpositive.constantCoeffAlgHom (G := G) (L := L) (κ := κ)
  let Φ := CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring
    (G := G) (L := L) (κ := κ) S
  by_cases hx : x = 0
  · rw [hx]
    exact isPrimal_zero
  let xN := toNonpositiveRingHom S x
  have hconstant : (xN : HahnSeries G L) = HahnSeries.C ((xN : HahnSeries G L).coeff 0) := by
    ext g
    by_cases hg : g = 0
    · subst g
      simp
    · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg]
      by_contra hcoeff
      have hgNonpos : g ≤ 0 := Nonpositive.support_subset xN
        ((HahnSeries.mem_support _ _).mpr hcoeff)
      have hzeroLe : 0 ≤ g := horder ▸ HahnSeries.order_le_of_coeff_ne_zero hcoeff
      exact hg (le_antisymm hgNonpos hzeroLe)
  have hcoeff : (x : HahnSeries G L).coeff 0 ≠ 0 := by
    intro hzero
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    change (x : HahnSeries G L) = 0
    simpa only [xN, coe_toNonpositiveRingHom, hzero, map_zero] using hconstant
  have hxC : (Φ x : A) = algebraMap L A ((x : HahnSeries G L).coeff 0) := by
    apply Subtype.ext
    apply Subtype.ext
    change (x : HahnSeries G L) = HahnSeries.C ((x : HahnSeries G L).coeff 0)
    simpa only [xN, coe_toNonpositiveRingHom] using hconstant
  have hunit : IsUnit (Φ x : A) := by
    rw [hxC]
    have hcoeffUnit : IsUnit ((x : HahnSeries G L).coeff 0) :=
      isUnit_iff_ne_zero.mpr hcoeff
    exact isUnit_map_of_isUnit (algebraMap L A).toMonoidHom hcoeffUnit
  have hπ : π (Φ x : A) = (x : HahnSeries G L).coeff 0 := rfl
  have hΦ : IsPrimal (Φ x) :=
    isPrimal_residueSubring_of_isUnit π S (Φ x).2 (hπ ▸ hcoeff) hunit
  exact isPrimal_equiv_preimage Φ hΦ

end CardSuppLTTruncationIntegerPart

end HahnSeries
