/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Herbrand.Function
public import Mathlib.GroupTheory.Index
/-!
# Pure group theory for Herbrand towers

This file contains the completion-free finite-group bookkeeping used in
the Herbrand quotient theorem and the quotient and tower filtration theorems.  It packages
the filtrations induced on a subgroup and on its quotient image, proves the
exact cardinality factorization at every level, and records compatibility of
Herbrand functions with transport along group equivalences.

The valued-field inputs of the quotient-depth and upper-numbering identities do not occur here.
Valued-field endpoints combine these structural lemmas with ramification-number
averaging; the inverse-function and upper-numbering statements are proved directly
in the Hilbert-ramification Herbrand theorem module.
-/

@[expose] public section

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction →
    herbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_eq_of_card_lower_eq →
    herbrandFunction_eq_of_card_lower_eq

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_inverseHerbrandFunction →
    herbrandFunction_inverseHerbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_strictMono →
    herbrandFunction_strictMono

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  inverseHerbrandFunction →
    inverseHerbrandFunction


noncomputable section

universe u v

namespace RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G]

/-- The filtration induced on a subgroup by intersection with every ambient
lower group. -/
def subgroupFiltration (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) :
    AntitoneNormalSubgroupFiltration H where
  lower n := (F.lower n).comap H.subtype
  lower_normal n := (F.lower_normal n).comap H.subtype
  antitone := by
    intro m n hmn
    exact Subgroup.comap_mono (F.antitone hmn)

/-- States the theorem `subgroupFiltration_lower`. -/
@[simp] theorem subgroupFiltration_lower
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) (n : ℕ) :
    (subgroupFiltration F H).lower n = (F.lower n).comap H.subtype :=
  rfl

/-- States the theorem `mem_subgroupFiltration_lower_iff`. -/
theorem mem_subgroupFiltration_lower_iff
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G)
    (n : ℕ) (h : H) :
    h ∈ (subgroupFiltration F H).lower n ↔ (h : G) ∈ F.lower n :=
  Iff.rfl

/-- The pointwise image filtration on a quotient by a normal subgroup.  This
is not asserted to be the actual lower filtration of a valued quotient; that
identification is precisely the content supplied by Herbrand's theorem. -/
def quotientImageFiltration (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] :
    AntitoneNormalSubgroupFiltration (G ⧸ H) where
  lower n := (F.lower n).map (QuotientGroup.mk' H)
  lower_normal n := (F.lower_normal n).map
    (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  antitone := by
    intro m n hmn
    exact Subgroup.map_mono (F.antitone hmn)

/-- States the theorem `quotientImageFiltration_lower`. -/
@[simp] theorem quotientImageFiltration_lower
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (n : ℕ) :
    (quotientImageFiltration F H).lower n =
      (F.lower n).map (QuotientGroup.mk' H) :=
  rfl

/-- At each level, the subgroup filtration is the kernel of the quotient map
restricted to the corresponding ambient lower group. -/
def lowerToQuotientImageHom (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] (n : ℕ) :
    F.lower n →* (quotientImageFiltration F H).lower n where
  toFun sigma :=
    ⟨QuotientGroup.mk' H (sigma : G), ⟨sigma, sigma.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' sigma tau := by
    apply Subtype.ext
    change QuotientGroup.mk' H (((sigma * tau : F.lower n) : G)) =
      QuotientGroup.mk' H (sigma : G) * QuotientGroup.mk' H (tau : G)
    rw [show (((sigma * tau : F.lower n) : G)) =
      (sigma : G) * (tau : G) by rfl, map_mul]

/-- States the theorem `lowerToQuotientImageHom_surjective`. -/
theorem lowerToQuotientImageHom_surjective
    (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] (n : ℕ) :
    Function.Surjective (lowerToQuotientImageHom F H n) := by
  rintro ⟨q, hq⟩
  rcases hq with ⟨sigma, hsigma, hsigmaq⟩
  refine ⟨⟨sigma, hsigma⟩, ?_⟩
  apply Subtype.ext
  exact hsigmaq

/-- The kernel of the restricted quotient map is canonically the intersection
filtration on `H`. -/
def lowerToQuotientImageKerEquiv (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] (n : ℕ) :
    (lowerToQuotientImageHom F H n).ker ≃
      (subgroupFiltration F H).lower n where
  toFun sigma := by
    let sigmaLower : F.lower n := sigma
    have hmk : QuotientGroup.mk' H ((sigma : F.lower n) : G) = 1 := by
      exact congrArg Subtype.val sigma.property
    have hsigmaH : ((sigma : F.lower n) : G) ∈ H :=
      (QuotientGroup.eq_one_iff (N := H)
        (x := ((sigma : F.lower n) : G))).1 hmk
    exact ⟨⟨((sigma : F.lower n) : G), hsigmaH⟩, sigmaLower.property⟩
  invFun h := by
    refine ⟨⟨((h : H) : G), h.property⟩, ?_⟩
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := H) (x := ((h : H) : G))).2 h.val.property
  left_inv sigma := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Exact level-cardinality factorization
`|F_n| = |F_n ∩ H| * |image(F_n)|`. -/
theorem card_subgroupFiltration_mul_card_quotientImageFiltration
    (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] (n : ℕ) :
    Nat.card ((subgroupFiltration F H).lower n) *
        Nat.card ((quotientImageFiltration F H).lower n) =
      Nat.card (F.lower n) := by
  let f := lowerToQuotientImageHom F H n
  have hker : Nat.card f.ker =
      Nat.card ((subgroupFiltration F H).lower n) :=
    Nat.card_congr (lowerToQuotientImageKerEquiv F H n)
  have hrange : Nat.card f.range =
      Nat.card ((quotientImageFiltration F H).lower n) := by
    rw [MonoidHom.range_eq_top.mpr
      (lowerToQuotientImageHom_surjective F H n)]
    exact Subgroup.card_top
  rw [← hker, ← hrange, ← Subgroup.index_ker]
  exact Subgroup.card_mul_index f.ker

variable {G' : Type v} [Group G']

/-- Transport a lower ramification filtration across a group equivalence. -/
def transportEquiv (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') :
    AntitoneNormalSubgroupFiltration G' where
  lower n := (F.lower n).comap e.symm.toMonoidHom
  lower_normal n := (F.lower_normal n).comap e.symm.toMonoidHom
  antitone := by
    intro m n hmn
    exact Subgroup.comap_mono (F.antitone hmn)

/-- States the theorem `transportEquiv_lower`. -/
@[simp] theorem transportEquiv_lower
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (n : ℕ) :
    (transportEquiv F e).lower n =
      (F.lower n).comap e.symm.toMonoidHom :=
  rfl

/-- States the theorem `mem_transportEquiv_lower_iff`. -/
theorem mem_transportEquiv_lower_iff
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G')
    (n : ℕ) (sigma : G') :
    sigma ∈ (transportEquiv F e).lower n ↔ e.symm sigma ∈ F.lower n :=
  Iff.rfl

/-- Every integral level is carried to the corresponding transported level. -/
def lowerEquivTransportEquiv
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (n : ℕ) :
    F.lower n ≃ (transportEquiv F e).lower n where
  toFun sigma := ⟨e (sigma : G), by simp⟩
  invFun tau := ⟨e.symm (tau : G'), tau.property⟩
  left_inv sigma := by
    apply Subtype.ext
    simp
  right_inv tau := by
    apply Subtype.ext
    simp

/-- States the theorem `card_lower_transportEquiv`. -/
theorem card_lower_transportEquiv
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (n : ℕ) :
    Nat.card ((transportEquiv F e).lower n) = Nat.card (F.lower n) := by
  exact Nat.card_congr (lowerEquivTransportEquiv F e n).symm

/-- The Herbrand function is invariant under transport across a group
equivalence. -/
theorem herbrandFunction_transportEquiv
    [Finite G] [Finite G']
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (s : ℝ) :
    (herbrandFunction
      (transportEquiv F e)) s =
      (herbrandFunction F) s := by
  apply
    herbrandFunction_eq_of_card_lower_eq (transportEquiv F e) F
  intro n
  exact card_lower_transportEquiv F e n

/-- The inverse Herbrand function is invariant under transport across a
group equivalence. -/
theorem inverseHerbrandFunction_transportEquiv
    [Finite G] [Finite G']
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (t : ℝ) :
    (inverseHerbrandFunction (transportEquiv F e)) t = (inverseHerbrandFunction F) t := by
  apply
    (herbrandFunction_strictMono (transportEquiv F e)).injective
  rw [herbrandFunction_inverseHerbrandFunction (transportEquiv F e)]
  rw [(RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_transportEquiv F)]
  rw [(herbrandFunction_inverseHerbrandFunction F)]

/-- The quotient-image filtration, transported to any isomorphic model of
the quotient group. -/
def quotientImageTransport
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G') : AntitoneNormalSubgroupFiltration G' :=
  transportEquiv (quotientImageFiltration F H) e

/-- States the theorem `quotientImageTransport_lower`. -/
@[simp] theorem quotientImageTransport_lower
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G') (n : ℕ) :
    (quotientImageTransport F H e).lower n =
      ((F.lower n).map (QuotientGroup.mk' H)).comap e.symm.toMonoidHom :=
  rfl

/-- Mapping a subgroup across a group equivalence is inverse to pulling it
back.  This orientation is the one used by the fixed-field quotient map. -/
theorem subgroup_map_equiv_eq_iff_eq_comap
    (e : G ≃* G') (A : Subgroup G) (B : Subgroup G') :
    A.map e.toMonoidHom = B ↔
      A = B.comap e.toMonoidHom := by
  constructor
  · intro h
    rw [← h]
    exact (Subgroup.comap_map_eq_self_of_injective
      (f := e.toMonoidHom) e.injective A).symm
  · intro h
    rw [h]
    exact Subgroup.map_comap_eq_self_of_surjective
      (f := e.toMonoidHom) e.surjective B

/-- States the theorem `transportEquiv_lower_eq_map`. -/
theorem transportEquiv_lower_eq_map
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (n : ℕ) :
    (transportEquiv F e).lower n = (F.lower n).map e.toMonoidHom := by
  ext sigma
  constructor
  · intro hsigma
    exact ⟨e.symm sigma, hsigma, e.apply_symm_apply sigma⟩
  · rintro ⟨tau, htau, rfl⟩
    simpa using htau


/-- States the theorem `transportEquiv_lower_eq_iff`. -/
theorem transportEquiv_lower_eq_iff
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G')
    (n : ℕ) (B : Subgroup G') :
    (transportEquiv F e).lower n = B ↔
      F.lower n = B.comap e.toMonoidHom := by
  rw [transportEquiv_lower_eq_map F e n]
  exact subgroup_map_equiv_eq_iff_eq_comap e (F.lower n) B

/-- Equality with a transported quotient-image level is exactly the usual
map/comap formulation of a lower-quotient theorem. -/
theorem quotientImageTransport_lower_eq_iff
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G') (n : ℕ) (B : Subgroup G') :
    (quotientImageTransport F H e).lower n = B ↔
      (F.lower n).map (QuotientGroup.mk' H) =
        B.comap e.toMonoidHom := by
  exact transportEquiv_lower_eq_iff (quotientImageFiltration F H) e n B


/-- Exact level-cardinality factorization after replacing the abstract
quotient by any isomorphic group model. -/
theorem card_subgroupFiltration_mul_card_quotientImageTransport
    [Finite G] [Finite G'] (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] (e : (G ⧸ H) ≃* G') (n : ℕ) :
    Nat.card ((subgroupFiltration F H).lower n) *
        Nat.card ((quotientImageTransport F H e).lower n) =
      Nat.card (F.lower n) := by
  change Nat.card ((subgroupFiltration F H).lower n) *
      Nat.card ((transportEquiv (quotientImageFiltration F H) e).lower n) = _
  rw [card_lower_transportEquiv (quotientImageFiltration F H) e n]
  exact card_subgroupFiltration_mul_card_quotientImageFiltration F H n

/-- States the theorem `quotientImageTransport_herbrandFunction`. -/
theorem quotientImageTransport_herbrandFunction
    [Finite G] [Finite G']
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G') (s : ℝ) :
    (herbrandFunction
      (quotientImageTransport F H e)) s =
      (herbrandFunction (quotientImageFiltration F H)) s :=
  by
    exact herbrandFunction_transportEquiv (quotientImageFiltration F H) e s

/-- States the theorem `quotientImageTransport_inverseHerbrandFunction`. -/
theorem quotientImageTransport_inverseHerbrandFunction
    [Finite G] [Finite G']
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G') (t : ℝ) :
    (inverseHerbrandFunction (quotientImageTransport F H e)) t =
      (inverseHerbrandFunction (quotientImageFiltration F H)) t :=
  by
    exact inverseHerbrandFunction_transportEquiv (quotientImageFiltration F H) e t

end AntitoneNormalSubgroupFiltration
end RamificationTheory.DiscreteValuationField
