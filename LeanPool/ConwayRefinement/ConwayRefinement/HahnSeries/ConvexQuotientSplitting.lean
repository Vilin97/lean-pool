/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.Module.ConvexQuotientSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEquiv
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Iterate
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Truncation
public import Mathlib.SetTheory.Cardinal.Regular

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CoefficientMap

/-!
# Hahn-series splitting by a convex subspace

An ordered vector space splits additively as the lexicographic product of the quotient by a convex
subspace and that subspace. Reindexing exponents by this splitting and unflattening the
lexicographic product regroups a Hahn series into an outer series on the quotient whose
coefficients are Hahn series on the subspace. Because the splitting is additive, this regrouping
is a ring equivalence.
-/

public noncomputable section

namespace HahnSeries

universe u v w

variable {R : Type v} {K : Type w} {G : Type u} [Semiring R]
variable [Field K] [AddCommGroup G] [Module K G]
variable [LinearOrder G] [IsOrderedAddMonoid G]

noncomputable instance quotientLinearOrder (P : Submodule K G)
    [P.toAddSubgroup.IsConvex] : LinearOrder (G ⧸ P) :=
  ConvexQuotient.instLinearOrder (H := P.toAddSubgroup)

instance quotientIsOrderedAddMonoid (P : Submodule K G) [P.toAddSubgroup.IsConvex] :
    IsOrderedAddMonoid (G ⧸ P) :=
  ConvexQuotient.instIsOrderedAddMonoid (H := P.toAddSubgroup)

local instance submoduleIsOrderedAddMonoid (P : Submodule K G) : IsOrderedAddMonoid P :=
  AddSubgroup.instIsOrderedAddMonoid P.toAddSubgroup

/-- Regroup Hahn series by the cosets of a convex subspace. The quotient exponent is the outer,
dominant coordinate, while exponents in the subspace form the coefficient Hahn series. -/
def convexQuotientSplitRingEquiv (P : Submodule K G) [P.toAddSubgroup.IsConvex] :
    R⟦G⟧ ≃+* (R⟦P⟧)⟦G ⧸ P⟧ :=
  (embDomainRingEquiv (Submodule.quotientLexEquiv P).symm).trans iterateRingEquiv.symm

@[simp]
theorem convexQuotientSplitRingEquiv_coeff (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : R⟦G⟧) (q : G ⧸ P) (p : P) :
    ((convexQuotientSplitRingEquiv P x).coeff q).coeff p =
      x.coeff (Submodule.quotientLexEquiv P (toLex (q, p))) := by
  apply (iterateRingEquiv_coeff (convexQuotientSplitRingEquiv P x) q p).symm.trans
  change (iterateRingEquiv
    (iterateRingEquiv.symm
      (embDomainRingEquiv (Submodule.quotientLexEquiv P).symm x))).coeff
        (toLex (q, p)) = _
  rw [RingEquiv.apply_symm_apply]
  have h := embDomainRingEquiv_coeff (R := R) (Submodule.quotientLexEquiv P).symm x
    (Submodule.quotientLexEquiv P (toLex (q, p)))
  rw [OrderAddMonoidIso.symm_apply_apply] at h
  exact h

open Classical in
/-- Regrouping commutes with restriction to the preimage of a subgroup of the quotient. -/
theorem convexQuotientSplitRingEquiv_filter_comap
    (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (D : AddSubgroup (G ⧸ P)) (x : R⟦G⟧) :
    convexQuotientSplitRingEquiv P
        (HahnSeries.filter (· ∈ D.comap P.mkQ.toAddMonoidHom) x) =
      HahnSeries.filter (· ∈ D) (convexQuotientSplitRingEquiv P x) := by
  ext q p
  rw [convexQuotientSplitRingEquiv_coeff, HahnSeries.coeff_filter,
    HahnSeries.coeff_filter]
  have hmk : Submodule.Quotient.mk
      (Submodule.quotientLexEquiv P (toLex (q, p))) = q := by
    rw [Submodule.quotientLexEquiv_apply, Submodule.mk_quotientProdLinearEquiv]
    rfl
  have hiff : Submodule.quotientLexEquiv P (toLex (q, p)) ∈
      D.comap P.mkQ.toAddMonoidHom ↔ q ∈ D := by
    rw [AddSubgroup.mem_comap]
    change Submodule.Quotient.mk (Submodule.quotientLexEquiv P (toLex (q, p))) ∈ D ↔ _
    rw [hmk]
  split
  · rename_i hmem
    rw [if_pos (hiff.mp hmem), convexQuotientSplitRingEquiv_coeff]
  · rename_i hmem
    rw [if_neg (fun hq ↦ hmem (hiff.mpr hq))]
    rfl

open Classical in
/-- The regrouped outer support lies in a quotient subgroup exactly when the ambient support lies
in its preimage. -/
theorem support_convexQuotientSplitRingEquiv_subset_iff
    (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (D : AddSubgroup (G ⧸ P)) (x : R⟦G⟧) :
    (convexQuotientSplitRingEquiv P x).support ⊆ (D : Set (G ⧸ P)) ↔
      x.support ⊆ (D.comap P.mkQ.toAddMonoidHom : Set G) := by
  constructor
  · intro hs g hg
    let z : (G ⧸ P) ×ₗ P := (Submodule.quotientLexEquiv P).symm g
    let q : G ⧸ P := (ofLex z).1
    let p : P := (ofLex z).2
    have hz : Submodule.quotientLexEquiv P (toLex (q, p)) = g :=
      (Submodule.quotientLexEquiv P).apply_symm_apply g
    have hcoeff : ((convexQuotientSplitRingEquiv P x).coeff q).coeff p ≠ 0 := by
      rw [convexQuotientSplitRingEquiv_coeff, hz]
      exact (HahnSeries.mem_support _ _).mp hg
    have hqsupp : q ∈ (convexQuotientSplitRingEquiv P x).support := by
      rw [HahnSeries.mem_support]
      intro hzero
      exact hcoeff (congrArg (fun y : R⟦P⟧ ↦ y.coeff p) hzero)
    have hqD := hs hqsupp
    change Submodule.Quotient.mk g ∈ D
    have hmk : Submodule.Quotient.mk
        (Submodule.quotientLexEquiv P (toLex (q, p))) = q := by
      rw [Submodule.quotientLexEquiv_apply, Submodule.mk_quotientProdLinearEquiv]
      rfl
    rwa [← hz, hmk]
  · intro hs q hq
    rw [HahnSeries.mem_support] at hq
    obtain ⟨p, hp⟩ : ∃ p : P,
        ((convexQuotientSplitRingEquiv P x).coeff q).coeff p ≠ 0 := by
      by_contra h
      push Not at h
      apply hq
      ext p
      exact h p
    have hxp : Submodule.quotientLexEquiv P (toLex (q, p)) ∈ x.support := by
      rw [HahnSeries.mem_support, ← convexQuotientSplitRingEquiv_coeff]
      exact hp
    have hmem := hs hxp
    change Submodule.Quotient.mk
      (Submodule.quotientLexEquiv P (toLex (q, p))) ∈ D at hmem
    have hmk : Submodule.Quotient.mk
        (Submodule.quotientLexEquiv P (toLex (q, p))) = q := by
      rw [Submodule.quotientLexEquiv_apply, Submodule.mk_quotientProdLinearEquiv]
      rfl
    rwa [hmk] at hmem

open Classical in
/-- The outer support after regrouping along a convex submodule is exactly the quotient image of
the original support. -/
theorem support_convexQuotientSplitRingEquiv
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (x : R⟦G⟧) :
    (convexQuotientSplitRingEquiv P x).support = P.mkQ '' x.support := by
  ext q
  constructor
  · intro hq
    rw [HahnSeries.mem_support] at hq
    obtain ⟨p, hp⟩ : ∃ p : P,
        ((convexQuotientSplitRingEquiv P x).coeff q).coeff p ≠ 0 := by
      by_contra h
      push Not at h
      apply hq
      ext p
      exact h p
    let g := Submodule.quotientLexEquiv P (toLex (q, p))
    refine ⟨g, ?_, ?_⟩
    · rw [HahnSeries.mem_support, ← convexQuotientSplitRingEquiv_coeff]
      exact hp
    · dsimp only [g]
      change Submodule.Quotient.mk
        (Submodule.quotientLexEquiv P (toLex (q, p))) = q
      rw [Submodule.quotientLexEquiv_apply, Submodule.mk_quotientProdLinearEquiv]
      rfl
  · rintro ⟨g, hg, rfl⟩
    let z : (G ⧸ P) ×ₗ P := (Submodule.quotientLexEquiv P).symm g
    let q : G ⧸ P := (ofLex z).1
    let p : P := (ofLex z).2
    have hz : Submodule.quotientLexEquiv P (toLex (q, p)) = g :=
      (Submodule.quotientLexEquiv P).apply_symm_apply g
    have hmk : P.mkQ g = q := by
      rw [← hz]
      change Submodule.Quotient.mk
        (Submodule.quotientLexEquiv P (toLex (q, p))) = q
      rw [Submodule.quotientLexEquiv_apply, Submodule.mk_quotientProdLinearEquiv]
      rfl
    rw [hmk, HahnSeries.mem_support]
    intro hzero
    have hcoeff := congrArg (fun y : R⟦P⟧ ↦ y.coeff p) hzero
    rw [convexQuotientSplitRingEquiv_coeff, hz] at hcoeff
    exact (HahnSeries.mem_support _ _).mp hg hcoeff

/-- Regrouping a nonpositive Hahn series produces no positive quotient exponent. -/
theorem support_convexQuotientSplitRingEquiv_subset_Iic
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (x : R⟦G⟧)
    (hx : x.support ⊆ Set.Iic 0) :
    (convexQuotientSplitRingEquiv P x).support ⊆ Set.Iic 0 := by
  intro q hq
  rw [HahnSeries.mem_support] at hq
  obtain ⟨p, hp⟩ : ∃ p : P, ((convexQuotientSplitRingEquiv P x).coeff q).coeff p ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    ext p
    exact h p
  rw [convexQuotientSplitRingEquiv_coeff] at hp
  have hnonpos : Submodule.quotientLexEquiv P (toLex (q, p)) ≤ 0 :=
    hx ((HahnSeries.mem_support _ _).mpr hp)
  have hlex : toLex (q, p) ≤ 0 := by
    rw [← (Submodule.quotientLexEquiv P).map_zero] at hnonpos
    exact (Submodule.quotientLexEquiv P).map_le_map_iff'.mp hnonpos
  rcases Prod.Lex.le_iff.mp hlex with hqneg | ⟨hqzero, -⟩
  · exact hqneg.le
  · exact hqzero.le

/-- The ordered inclusion of a subspace into its ambient exponent group. -/
def submoduleOrderEmbedding (P : Submodule K G) : P ↪o G where
  toFun := (↑)
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

omit [IsOrderedAddMonoid G] in
@[simp]
theorem submoduleOrderEmbedding_apply (P : Submodule K G) (p : P) :
    submoduleOrderEmbedding P p = (p : G) :=
  (rfl)

/-- The outer-zero coefficient of quotient regrouping is precisely exponent-domain restriction
to the convex subspace. -/
theorem coeff_zero_convexQuotientSplitRingEquiv
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (x : R⟦G⟧) :
    (convexQuotientSplitRingEquiv P x).coeff 0 =
      HahnSeries.restrictDomain (submoduleOrderEmbedding P) x := by
  ext p
  rw [convexQuotientSplitRingEquiv_coeff, HahnSeries.restrictDomain_coeff]
  rw [Submodule.quotientLexEquiv_apply]
  change x.coeff (Submodule.quotientProdLinearEquiv P (0, p)) = x.coeff (p : G)
  rw [Submodule.quotientProdLinearEquiv_zero_left]

/-- A series is nonpositive exactly when quotient regrouping has nonpositive outer support and
its coefficient at outer exponent zero has nonpositive inner support. -/
theorem support_convexQuotientSplitRingEquiv_subset_Iic_iff
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (x : R⟦G⟧) :
    x.support ⊆ Set.Iic 0 ↔
      (convexQuotientSplitRingEquiv P x).support ⊆ Set.Iic 0 ∧
        ((convexQuotientSplitRingEquiv P x).coeff 0).support ⊆ Set.Iic 0 := by
  constructor
  · intro hx
    refine ⟨support_convexQuotientSplitRingEquiv_subset_Iic P x hx, ?_⟩
    intro p hp
    have hpx : (p : G) ∈ x.support := by
      rw [HahnSeries.mem_support] at hp ⊢
      rw [coeff_zero_convexQuotientSplitRingEquiv,
        HahnSeries.restrictDomain_coeff] at hp
      simpa only [submoduleOrderEmbedding_apply] using hp
    exact hx hpx
  · rintro ⟨houter, hinner⟩ g hg
    let z : (G ⧸ P) ×ₗ P := (Submodule.quotientLexEquiv P).symm g
    let q : G ⧸ P := (ofLex z).1
    let p : P := (ofLex z).2
    have hz : Submodule.quotientLexEquiv P z = g :=
      (Submodule.quotientLexEquiv P).apply_symm_apply g
    have hcoeff : ((convexQuotientSplitRingEquiv P x).coeff q).coeff p ≠ 0 := by
      rw [convexQuotientSplitRingEquiv_coeff]
      rw [show toLex (q, p) = z from rfl, hz]
      exact (HahnSeries.mem_support _ _).mp hg
    have hq : q ∈ (convexQuotientSplitRingEquiv P x).support := by
      rw [HahnSeries.mem_support]
      intro hzero
      exact hcoeff (congrArg (fun y : R⟦P⟧ ↦ y.coeff p) hzero)
    have hq0 : q ≤ 0 := houter hq
    change g ≤ 0
    rw [← hz, ← map_zero (Submodule.quotientLexEquiv P)]
    apply (Submodule.quotientLexEquiv P).map_le_map_iff'.mpr
    apply Prod.Lex.le_iff.mpr
    rcases hq0.eq_or_lt with hqzero | hqneg
    · right
      refine ⟨hqzero, ?_⟩
      apply hinner
      rw [HahnSeries.mem_support]
      simpa only [q, hqzero] using hcoeff
    · exact Or.inl hqneg

/-- Suppose the support classes of a nonpositive series lie in the union of a block with no
greatest element and a finite block. After regrouping along the common tail of the first block,
the inner series at outer exponent zero meets only finitely many Archimedean classes. -/
theorem supportArchimedeanClasses_coeff_zero_convexQuotientSplitRingEquiv_finite
    [LinearOrder K] [IsOrderedRing K] [Archimedean K] [PosSMulMono K G]
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) (hT₁ : T₁.Finite)
    (x : R⟦G⟧) (hxclasses : ArchimedeanClass.mk '' x.support ⊆ T₀ ∪ T₁) :
    (ArchimedeanClass.mk ''
      ((convexQuotientSplitRingEquiv
        (FiniteArchimedeanClass.tailSubmodule K
          {c : FiniteArchimedeanClass G | c.1 ∈ T₀})
        x).coeff 0).support).Finite := by
  let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
  let P := FiniteArchimedeanClass.tailSubmodule K T
  let inner := (convexQuotientSplitRingEquiv P x).coeff 0
  let inc : P →+o G :=
    { toFun := fun p ↦ (p : G)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      monotone' := fun _ _ h ↦ h }
  have himage : ArchimedeanClass.orderHom inc ''
      (ArchimedeanClass.mk '' inner.support) ⊆ T₁ := by
    rintro c ⟨d, ⟨p, hp, rfl⟩, rfl⟩
    rw [ArchimedeanClass.orderHom_mk]
    have hpx : (p : G) ∈ x.support := by
      apply (HahnSeries.mem_support _ _).mpr
      have hpne := (HahnSeries.mem_support _ _).mp hp
      dsimp only [inner] at hpne
      rw [coeff_zero_convexQuotientSplitRingEquiv,
        HahnSeries.restrictDomain_coeff] at hpne
      simpa only [submoduleOrderEmbedding_apply] using hpne
    rcases hxclasses ⟨p, hpx, rfl⟩ with hpT₀ | hpT₁
    · obtain ⟨a, haT₀, hpa⟩ := hT₀gt _ hpT₀
      have hpP : (p : G) ∈ P := p.2
      have ha0 : a ≠ ⊤ := fun ha ↦ by
        obtain ⟨b, -, hab⟩ := hT₀gt a haT₀
        exact (not_lt_of_ge le_top) (ha ▸ hab)
      have hpTail : (p : G) ∈ FiniteArchimedeanClass.tailKernel T := by
        rw [← FiniteArchimedeanClass.tailSubmodule_toAddSubgroup K T]
        exact hpP
      have ha_le_p : a ≤ ArchimedeanClass.mk (p : G) :=
        FiniteArchimedeanClass.mem_tailKernel_iff.mp hpTail ⟨⟨a, ha0⟩, haT₀⟩
      exact (not_lt_of_ge ha_le_p) hpa |>.elim
    · exact hpT₁
  change (ArchimedeanClass.mk '' inner.support).Finite
  exact Set.Finite.of_finite_image (hT₁.subset himage)
    (ArchimedeanClass.orderHom_injective Subtype.val_injective).injOn

/-- The support cardinality of every outer coefficient is bounded by that of the original
unregrouped series. -/
theorem cardSupp_coeff_convexQuotientSplitRingEquiv_le
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (x : R⟦G⟧) (q : G ⧸ P) :
    ((convexQuotientSplitRingEquiv P x).coeff q).cardSupp ≤ x.cardSupp := by
  apply (cardSupp_coeff_le_cardSupp_iterateRingEquiv
    (iterateRingEquiv.symm (embDomainRingEquiv (Submodule.quotientLexEquiv P).symm x)) q).trans
  rw [RingEquiv.apply_symm_apply]
  rw [cardSupp_embDomainRingEquiv]

/-- Regrouping preserves a regular support bound on the outer support and on every coefficient. -/
theorem cardSupp_convexQuotientSplitRingEquiv_lt
    {κ : Cardinal.{u}} (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : R⟦G⟧) (hx : x.cardSupp < κ) :
    (convexQuotientSplitRingEquiv P x).cardSupp < κ ∧
      ∀ q, ((convexQuotientSplitRingEquiv P x).coeff q).cardSupp < κ := by
  constructor
  · have h := cardSupp_outer_le_cardSupp_iterateRingEquiv
      (iterateRingEquiv.symm (embDomainRingEquiv (Submodule.quotientLexEquiv P).symm x))
    rw [RingEquiv.apply_symm_apply] at h
    exact h.trans_lt (by rw [cardSupp_embDomainRingEquiv]; exact hx)
  · exact fun q ↦ (cardSupp_coeff_convexQuotientSplitRingEquiv_le P x q).trans_lt hx

/-- If the outer support and every coefficient support satisfy a regular bound, flattening the
regrouped Hahn series satisfies the same bound. -/
theorem cardSupp_convexQuotientSplitRingEquiv_symm_lt_of_isRegular
    {κ : Cardinal.{u}} (hκ : κ.IsRegular) (P : Submodule K G)
    [P.toAddSubgroup.IsConvex] (x : (R⟦P⟧)⟦G ⧸ P⟧)
    (houter : x.cardSupp < κ) (hcoeff : ∀ q, (x.coeff q).cardSupp < κ) :
    ((convexQuotientSplitRingEquiv P).symm x).cardSupp < κ := by
  have heq : (convexQuotientSplitRingEquiv P).symm x =
      embDomainRingEquiv (Submodule.quotientLexEquiv P) (iterateRingEquiv x) := by
    apply (convexQuotientSplitRingEquiv P).injective
    rw [RingEquiv.apply_symm_apply]
    rw [eq_comm]
    change iterateRingEquiv.symm
      (embDomainRingEquiv (Submodule.quotientLexEquiv P).symm
        (embDomainRingEquiv (Submodule.quotientLexEquiv P) (iterateRingEquiv x))) = x
    have hdomain : embDomainRingEquiv (Submodule.quotientLexEquiv P).symm
        (embDomainRingEquiv (Submodule.quotientLexEquiv P) (iterateRingEquiv x)) =
          iterateRingEquiv x := by
      ext p
      have h₁ := embDomainRingEquiv_coeff (R := R)
        (Submodule.quotientLexEquiv P).symm
        (embDomainRingEquiv (Submodule.quotientLexEquiv P) (iterateRingEquiv x))
        (Submodule.quotientLexEquiv P p)
      have h₂ := embDomainRingEquiv_coeff (R := R)
        (Submodule.quotientLexEquiv P) (iterateRingEquiv x) p
      rw [OrderAddMonoidIso.symm_apply_apply] at h₁
      exact h₁.trans h₂
    rw [hdomain, RingEquiv.symm_apply_apply]
  rw [heq]
  rw [cardSupp_embDomainRingEquiv]
  exact cardSupp_iterateRingEquiv_lt_of_isRegular hκ x houter hcoeff

end HahnSeries

namespace HahnSeries

section Bounded

open Cardinal

universe u v w

variable {R : Type v} {K : Type w} {G : Type u} [Field R]
variable [Field K] [AddCommGroup G] [Module K G]
variable [LinearOrder G] [IsOrderedAddMonoid G]

noncomputable local instance boundedQuotientLinearOrder (P : Submodule K G)
    [P.toAddSubgroup.IsConvex] : LinearOrder (G ⧸ P) :=
  ConvexQuotient.instLinearOrder (H := P.toAddSubgroup)

local instance boundedQuotientIsOrderedAddMonoid
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] :
    IsOrderedAddMonoid (G ⧸ P) :=
  ConvexQuotient.instIsOrderedAddMonoid (H := P.toAddSubgroup)

local instance boundedSubmoduleIsOrderedAddMonoid (P : Submodule K G) :
    IsOrderedAddMonoid P :=
  AddSubgroup.instIsOrderedAddMonoid P.toAddSubgroup

variable {κ : Cardinal.{u}} [Fact (aleph0 < κ)] [Fact κ.IsRegular]

/-- Embed a cardinal-bounded iterated Hahn field coefficientwise into the unrestricted iterated
Hahn field. -/
def boundedOuterCoefficientInclusion (P : Submodule K G) [P.toAddSubgroup.IsConvex] :
    CardSuppLTField (G := G ⧸ P)
        (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ) →+*
      (R⟦P⟧)⟦G ⧸ P⟧ :=
  (coefficientMapRingHom
    ((cardSuppLTSubfield P R κ).subtype :
      CardSuppLTField (G := P) (R := R) (κ := κ) →+* R⟦P⟧)).comp
    ((cardSuppLTSubfield (G ⧸ P)
      (CardSuppLTField (G := P) (R := R) (κ := κ)) κ).subtype)

omit [Fact κ.IsRegular] in
@[simp]
theorem boundedOuterCoefficientInclusion_coeff
    (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : CardSuppLTField (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ))
    (q : G ⧸ P) :
    (boundedOuterCoefficientInclusion P x).coeff q = (x.1.coeff q : R⟦P⟧) := by
  change
    (coefficientMapRingHom
      ((cardSuppLTSubfield P R κ).subtype :
        CardSuppLTField (G := P) (R := R) (κ := κ) →+* R⟦P⟧)
      (x : (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧)).coeff q = _
  rw [coefficientMapRingHom_coeff]
  rfl

omit [Fact κ.IsRegular] in
/-- Coefficientwise inclusion of a bounded iterated Hahn field is injective. -/
theorem boundedOuterCoefficientInclusion_injective
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] :
    Function.Injective (boundedOuterCoefficientInclusion
      (R := R) (κ := κ) P) := by
  intro x y hxy
  apply Subtype.ext
  ext q p
  have hcoeff := congrArg (fun z : (R⟦P⟧)⟦G ⧸ P⟧ ↦ (z.coeff q).coeff p) hxy
  simpa using hcoeff

/-- Regroup a bounded Hahn series into a bounded outer Hahn series whose coefficients are bounded
inner Hahn series. -/
def boundedConvexQuotientSplit (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
    CardSuppLTField (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ) := by
  let y := convexQuotientSplitRingEquiv P (x : R⟦G⟧)
  have hy := cardSupp_convexQuotientSplitRingEquiv_lt P (x : R⟦G⟧) x.2
  let f : G ⧸ P → CardSuppLTField (G := P) (R := R) (κ := κ) :=
    fun q ↦ ⟨y.coeff q, hy.2 q⟩
  let z : (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧ :=
    { coeff := f
      isPWO_support' := by
        have hsupport : Function.support f = y.support := by
          ext q
          simp only [Function.mem_support, ne_eq, HahnSeries.mem_support]
          constructor
          · intro hf hyq
            apply hf
            apply Subtype.ext
            exact hyq
          · intro hyq hf
            apply hyq
            exact congrArg Subtype.val hf
        rw [hsupport]
        exact y.isPWO_support }
  exact ⟨z, by
    change z.cardSupp < κ
    have hsupport : z.support = y.support := by
      ext q
      simp only [HahnSeries.mem_support, z]
      constructor
      · intro hf hyq
        apply hf
        apply Subtype.ext
        exact hyq
      · intro hyq hf
        apply hyq
        exact congrArg Subtype.val hf
    rw [HahnSeries.cardSupp_congr hsupport]
    exact hy.1⟩

omit [Fact κ.IsRegular] in
/-- Bounded regrouping agrees with unrestricted regrouping after coefficientwise inclusion. -/
theorem boundedOuterCoefficientInclusion_split
    (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
    boundedOuterCoefficientInclusion P (boundedConvexQuotientSplit P x) =
      convexQuotientSplitRingEquiv P (x : R⟦G⟧) := by
  ext q p
  rw [boundedOuterCoefficientInclusion_coeff]
  rfl

omit [Fact κ.IsRegular] in
/-- Bounded quotient regrouping has the same outer support as unrestricted regrouping. -/
theorem support_boundedConvexQuotientSplit
    (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
    ((boundedConvexQuotientSplit P x :
      CardSuppLTField (G := G ⧸ P)
        (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) :
      (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support =
      (convexQuotientSplitRingEquiv P (x : R⟦G⟧)).support := by
  rw [← support_coefficientMapRingHom
    ((cardSuppLTSubfield P R κ).subtype) Subtype.val_injective]
  exact congrArg HahnSeries.support (boundedOuterCoefficientInclusion_split P x)

/-- Flatten a bounded outer Hahn series with bounded inner coefficients. Regularity of the bound
ensures that the flattened support is still bounded. -/
def boundedConvexQuotientUnsplit (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : CardSuppLTField (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) :
    CardSuppLTField (G := G) (R := R) (κ := κ) :=
  ⟨(convexQuotientSplitRingEquiv P).symm
      (boundedOuterCoefficientInclusion P x), by
    apply cardSupp_convexQuotientSplitRingEquiv_symm_lt_of_isRegular
      (Fact.out : κ.IsRegular) P (boundedOuterCoefficientInclusion P x)
    · have hsupport : (boundedOuterCoefficientInclusion P x).support =
          (x : (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support :=
        support_coefficientMapRingHom _ Subtype.val_injective _
      rw [HahnSeries.cardSupp_congr hsupport]
      exact x.2
    · intro q
      rw [boundedOuterCoefficientInclusion_coeff]
      exact (x.1.coeff q).2⟩

/-- Cardinal-bounded Hahn series split as bounded outer Hahn series with bounded inner Hahn
coefficients along a convex subspace. -/
def boundedConvexQuotientSplitRingEquiv
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] :
    CardSuppLTField (G := G) (R := R) (κ := κ) ≃+*
      CardSuppLTField (G := G ⧸ P)
        (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ) where
  toFun := boundedConvexQuotientSplit P
  invFun := boundedConvexQuotientUnsplit P
  left_inv := by
    intro x
    apply Subtype.ext
    change (convexQuotientSplitRingEquiv P).symm
      (boundedOuterCoefficientInclusion P (boundedConvexQuotientSplit P x)) = _
    rw [boundedOuterCoefficientInclusion_split, RingEquiv.symm_apply_apply]
  right_inv := by
    intro x
    apply boundedOuterCoefficientInclusion_injective P
    rw [boundedOuterCoefficientInclusion_split]
    change convexQuotientSplitRingEquiv P
      ((convexQuotientSplitRingEquiv P).symm
        (boundedOuterCoefficientInclusion P x)) = _
    rw [RingEquiv.apply_symm_apply]
  map_mul' := by
    intro x y
    apply boundedOuterCoefficientInclusion_injective P
    rw [boundedOuterCoefficientInclusion_split, map_mul,
      boundedOuterCoefficientInclusion_split, boundedOuterCoefficientInclusion_split]
    exact map_mul (convexQuotientSplitRingEquiv P) (x : R⟦G⟧) (y : R⟦G⟧)
  map_add' := by
    intro x y
    apply boundedOuterCoefficientInclusion_injective P
    rw [boundedOuterCoefficientInclusion_split, map_add,
      boundedOuterCoefficientInclusion_split, boundedOuterCoefficientInclusion_split]
    exact map_add (convexQuotientSplitRingEquiv P) (x : R⟦G⟧) (y : R⟦G⟧)

/-- The bounded splitting equivalence applies by bounded quotient regrouping. -/
@[simp]
theorem boundedConvexQuotientSplitRingEquiv_apply
    (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
    boundedConvexQuotientSplitRingEquiv P x = boundedConvexQuotientSplit P x :=
  (rfl)

omit [Fact κ.IsRegular] in
/-- The outer-zero coefficient of bounded quotient regrouping is exponent-domain restriction to
the convex subspace. -/
@[simp]
theorem coe_coeff_zero_boundedConvexQuotientSplit
    (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
    (((boundedConvexQuotientSplit P x).1.coeff 0 :
      CardSuppLTField (G := P) (R := R) (κ := κ)) : R⟦P⟧) =
      HahnSeries.restrictDomain (submoduleOrderEmbedding P) (x : R⟦G⟧) := by
  have h := congrArg (fun z : (R⟦P⟧)⟦G ⧸ P⟧ ↦ z.coeff 0)
    (boundedOuterCoefficientInclusion_split P x)
  rw [boundedOuterCoefficientInclusion_coeff,
    coeff_zero_convexQuotientSplitRingEquiv] at h
  exact h

/-- Bounded regrouping preserves membership in the integer part when the allowed outer constant
coefficients are the corresponding bounded inner integer part. -/
theorem mem_cardSuppLTTruncationIntegerPart_boundedConvexQuotientSplitRingEquiv_iff
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
    x ∈ cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z ↔
      boundedConvexQuotientSplitRingEquiv P x ∈
        cardSuppLTTruncationIntegerPart (G := G ⧸ P)
          (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
          (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) := by
  rw [mem_cardSuppLTTruncationIntegerPart, mem_cardSuppLTTruncationIntegerPart]
  change
    (x : R⟦G⟧).support ⊆ Set.Iic 0 ∧ (x : R⟦G⟧).coeff 0 ∈ Z ↔
      ((boundedConvexQuotientSplitRingEquiv P x :
          CardSuppLTField (G := G ⧸ P)
            (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) :
        (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support ⊆
          Set.Iic 0 ∧
      ((boundedConvexQuotientSplitRingEquiv P x :
          CardSuppLTField (G := G ⧸ P)
            (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) :
        (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).coeff 0 ∈
          cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z
  rw [mem_cardSuppLTTruncationIntegerPart, boundedConvexQuotientSplitRingEquiv_apply]
  let y := boundedConvexQuotientSplit P x
  have hcoeff (q : G ⧸ P) : ((y.1.coeff q :
      CardSuppLTField (G := P) (R := R) (κ := κ)) : R⟦P⟧) =
      (convexQuotientSplitRingEquiv P (x : R⟦G⟧)).coeff q := by
    have h := congrArg (fun z : (R⟦P⟧)⟦G ⧸ P⟧ ↦ z.coeff q)
      (boundedOuterCoefficientInclusion_split P x)
    rw [boundedOuterCoefficientInclusion_coeff] at h
    exact h
  have hsupport : (y :
      (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support =
      (convexQuotientSplitRingEquiv P (x : R⟦G⟧)).support := by
    ext q
    rw [HahnSeries.mem_support, HahnSeries.mem_support]
    constructor
    · intro hy hzero
      apply hy
      apply Subtype.ext
      exact (hcoeff q).trans hzero
    · intro hxq hzero
      apply hxq
      rw [← hcoeff q]
      exact congrArg Subtype.val hzero
  change
    (x : R⟦G⟧).support ⊆ Set.Iic 0 ∧ (x : R⟦G⟧).coeff 0 ∈ Z ↔
      ((boundedConvexQuotientSplit P x :
          CardSuppLTField (G := G ⧸ P)
            (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) :
        (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support ⊆
          Set.Iic 0 ∧
        (((boundedConvexQuotientSplit P x :
          CardSuppLTField (G := G ⧸ P)
            (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)).1.coeff 0 :
              CardSuppLTField (G := P) (R := R) (κ := κ)) : R⟦P⟧).support ⊆
            Set.Iic 0 ∧
          (((boundedConvexQuotientSplit P x :
            CardSuppLTField (G := G ⧸ P)
              (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)).1.coeff 0 :
                CardSuppLTField (G := P) (R := R) (κ := κ)) : R⟦P⟧).coeff 0 ∈ Z
  rw [hsupport, hcoeff 0]
  change
    (x : R⟦G⟧).support ⊆ Set.Iic 0 ∧ (x : R⟦G⟧).coeff 0 ∈ Z ↔
      (convexQuotientSplitRingEquiv P (x : R⟦G⟧)).support ⊆ Set.Iic 0 ∧
        (((convexQuotientSplitRingEquiv P (x : R⟦G⟧)).coeff 0).support ⊆
          Set.Iic 0 ∧
        ((convexQuotientSplitRingEquiv P (x : R⟦G⟧)).coeff 0).coeff 0 ∈ Z)
  rw [← and_assoc, ← support_convexQuotientSplitRingEquiv_subset_Iic_iff]
  refine and_congr Iff.rfl ?_
  rw [convexQuotientSplitRingEquiv_coeff]
  simp

/-- Regrouping identifies a bounded Hahn integer part with the outer Hahn integer part whose
allowed constant coefficients are the corresponding bounded inner Hahn integer part. -/
def cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z ≃+*
      cardSuppLTTruncationIntegerPart (G := G ⧸ P)
        (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
        (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) :=
  RingEquiv.restrict (boundedConvexQuotientSplitRingEquiv P) _ _
    (mem_cardSuppLTTruncationIntegerPart_boundedConvexQuotientSplitRingEquiv_iff P Z)

/-- The restricted integer-part equivalence is bounded quotient regrouping on underlying
series. -/
@[simp]
theorem coe_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    (((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x :
      cardSuppLTTruncationIntegerPart (G := G ⧸ P)
        (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
        (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)) :
          CardSuppLTField (G := G ⧸ P)
            (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) :
              (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧) =
      (boundedConvexQuotientSplit P x.1 :
        (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧) :=
  (rfl)

/-- The integer-part splitting equivalence preserves the outer support of unrestricted
regrouping. -/
theorem support_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    ((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x :
      (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support) =
      (convexQuotientSplitRingEquiv P (x : R⟦G⟧)).support := by
  rw [coe_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv]
  exact support_boundedConvexQuotientSplit P x.1

end Bounded

end HahnSeries
