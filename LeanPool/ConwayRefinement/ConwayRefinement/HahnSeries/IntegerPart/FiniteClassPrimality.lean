/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedPrimality
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.CardinalFiniteClassReduction
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.FiniteClassReduction
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.ConvexQuotientSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncationDomainEmbedding
public import Mathlib.Data.Set.Card

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncationResidue
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Primality for finite support-class sets

Under LM24 conditions `(A1)`--`(A3)`, every cardinal-bounded Hahn integer-part series whose
support meets only finitely many Archimedean classes is primal.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries

namespace HahnSeries.Nonpositive

variable {K G R : Type*} {κ : Cardinal}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [Fact (ℵ₀ < κ)]
variable (Z : Subring R)

/-- If order-zero elements and reduced elements with nonzero order are primal, every bounded
integer-part element meeting only finitely many Archimedean classes is primal. -/
theorem isPrimal_of_supportArchimedeanClasses_finite_of_reduced [CharZero R]
    (u : HahnEmbedding.ArchimedeanStrata K G)
    (hzero : ∀ y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y :
        Nonpositive G R) : R⟦G⟧).order = 0 → IsPrimal y)
    (hreduced : ∀ y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y :
        Nonpositive G R) : R⟦G⟧).order ≠ 0 →
      IsReduced (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y) → IsPrimal y)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hfinite : (supportArchimedeanClasses
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)).Finite) : IsPrimal x := by
  let classes := fun y : cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z ↦
    supportArchimedeanClasses (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y)
  have hind : ∀ n : ℕ, ∀ y : cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z,
      (classes y).ncard = n → (classes y).Finite → IsPrimal y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hn hyFinite
        let yN := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y
        by_cases horder : (yN : R⟦G⟧).order = 0
        · exact hzero y horder
        have hyN0 : yN ≠ 0 := by
          intro hyzero
          apply horder
          rw [hyzero, Subring.coe_zero, HahnSeries.order_zero]
        let c := leadingClass yN horder
        have hT : T (K := K) c yN = yN := T_leadingClass yN horder
        by_cases htau : tau (K := K) c yN = 0
        · exact hreduced y horder
            ((isReduced_iff_tau_leadingClass_eq_zero_or_one yN hyN0 horder).mpr
              (Or.inl htau))
        let r := rhoIntegerPart u c Z y hT htau
        let t := tauIntegerPart (K := K) c Z y
        have hfac : r * t = y := rhoIntegerPart_mul_tauIntegerPart u c Z y hT htau
        have hrReduced : IsReduced
            (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z r) := by
          rw [toNonpositive_rhoIntegerPart u c Z y hT htau]
          exact isReduced_rho_leadingClass_of_tau_ne_zero u yN hyN0 horder htau
        have hrPrimal : IsPrimal r := by
          by_cases hrOrder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z r :
            Nonpositive G R) : R⟦G⟧).order = 0
          · exact hzero r hrOrder
          · exact hreduced r hrOrder hrReduced
        have htClasses : classes t =
            supportArchimedeanClasses (tau (K := K) c yN) := by
          apply congrArg supportArchimedeanClasses
          exact toNonpositive_tauIntegerPart c Z y
        have htFinite : (classes t).Finite := by
          rw [htClasses]
          exact hyFinite.subset (supportArchimedeanClasses_tau_subset c yN)
        have htCount : (classes t).ncard < n := by
          rw [htClasses, ← hn]
          exact Set.ncard_lt_ncard
            (supportArchimedeanClasses_tau_ssubset yN hyN0 horder) hyFinite
        have htPrimal : IsPrimal t := ih (classes t).ncard htCount t rfl htFinite
        rw [← hfac]
        exact hrPrimal.mul htPrimal
  exact hind (classes x).ncard x rfl hfinite


/-- The finite-class part of the Hahn integer ring is pre-Schreier under the corresponding
Archimedean hypotheses and the pre-Schreier condition on the coefficient subring. -/
@[blueprint "thm:finite-support-classes-primality"
  (phase := "Finitely many Archimedean classes")
  (title := "Primality for finitely many Archimedean support classes")
  (statement := /--
    Let $K$ be an Archimedean ordered division ring, $G$ an ordered $K$-vector
    space, $R$ a field of characteristic zero, $\kappa>\aleph_0$ a regular
    cardinal, and $Z\subseteq R$ a pre-Schreier subring.  At every nonzero
    Archimedean class $\sigma$, choose an additive complement $H_\sigma$ to
    $G_{\prec\sigma}$ in $G_{\preceq\sigma}$ that is order additively
    isomorphic to $\mathbb R$.  Assume that $G_{\prec\sigma}$ either has
    cofinality at least $\kappa$, or is zero and every element of $R$ is a
    fraction of elements of $Z$.  Every element of
    $Z+R((G^{<0}))_\kappa$ whose support meets only finitely many Archimedean
    classes is primal.
  -/)
  (proof := /--
    Induct on the number of Archimedean classes met by the support.  At the
    leading class, split the series into its reduced factor and its strict
    lower-class factor.  The reduced factor is primal by
    \ref{cor:reduced-hahn-integer-part-primal}; the other factor meets strictly
    fewer classes and is primal by induction.  A product of primal elements is
    primal.
  -/)]
theorem isPrimal_of_supportArchimedeanClasses_finite [CharZero R]
    [Fact κ.IsRegular] [DecompositionMonoid Z]
    (u : HahnEmbedding.ArchimedeanStrata K G)
    (hA1 : ∀ c : FiniteArchimedeanClass G, Nonempty (u.stratum c ≃+o ℝ))
    (hA2 : ∀ c : FiniteArchimedeanClass G,
      LM24.AssumptionA2AtFiniteClass (K := K) κ Z c)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hfinite : (supportArchimedeanClasses
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)).Finite) : IsPrimal x := by
  apply isPrimal_of_supportArchimedeanClasses_finite_of_reduced Z u
  · exact CardSuppLTTruncationIntegerPart.isPrimal_of_order_eq_zero Z
  · intro y hyOrder hyReduced
    have hy0 : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y ≠ 0 := by
      intro hyzero
      apply hyOrder
      rw [hyzero, Subring.coe_zero, HahnSeries.order_zero]
    let c := leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z y) hyOrder
    exact isPrimal_of_isReduced_of_leadingClass_orderIso_real
      u Z y hy0 hyOrder hyReduced (hA2 c)
      (Classical.choice (hA1 c))
  · exact hfinite

end HahnSeries.Nonpositive

namespace HahnSeries.CardSuppLTTruncationIntegerPart

open Cardinal

variable {G R : Type*} {κ : Cardinal}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field R] [Fact (ℵ₀ < κ)]

/-- Viewing a bounded Hahn integer-part series as nonpositive does not change the
Archimedean classes met by its support. -/
theorem supportArchimedeanClasses_toNonpositiveRingHom
    (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    HahnSeries.Nonpositive.supportArchimedeanClasses (toNonpositiveRingHom Z x) =
      ArchimedeanClass.mk '' (x : HahnSeries G R).support := by
  ext c
  rw [HahnSeries.Nonpositive.mem_supportArchimedeanClasses]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, by simpa only [coe_toNonpositiveRingHom] using hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, by simpa only [coe_toNonpositiveRingHom] using hg, rfl⟩

/-- Finite-class primality in an ambient exponent group descends to every convex exponent
subgroup. -/
private theorem isPrimal_addSubgroup_of_ambient_finiteClasses
    (Z : Subring R)
    (hfinite : ∀ x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (x : HahnSeries G R).support).Finite → IsPrimal x)
    (P : AddSubgroup G) (hP : (P : Set G).OrdConnected)
    (a : cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)
    (ha : (ArchimedeanClass.mk '' (a : HahnSeries P R).support).Finite) : IsPrimal a := by
  let inc : P →+ G := P.subtype
  have hinci : Function.Injective inc := Subtype.val_injective
  have hinco : ∀ x y : P, inc x ≤ inc y ↔ x ≤ y := fun _ _ ↦ Iff.rfl
  let A := mapDomain inc hinci hinco Z a
  have hAfinite : (ArchimedeanClass.mk '' (A : HahnSeries G R).support).Finite := by
    have hsupport : (A : HahnSeries G R).support = inc '' (a : HahnSeries P R).support := by
      rw [coe_mapDomain]
      exact HahnSeries.support_embDomain _ _
    rw [hsupport]
    let e : P →+o G :=
      { toFun := inc
        map_zero' := map_zero inc
        map_add' := map_add inc
        monotone' := fun _ _ h ↦ h }
    let ac : ArchimedeanClass P → ArchimedeanClass G := ArchimedeanClass.orderHom e
    have heq : ArchimedeanClass.mk '' (inc '' (a : HahnSeries P R).support) =
        ac '' (ArchimedeanClass.mk '' (a : HahnSeries P R).support) := by
      ext c
      constructor
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨ArchimedeanClass.mk p, ⟨p, hp, rfl⟩,
          ArchimedeanClass.orderHom_mk e p⟩
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨inc p, ⟨p, hp, rfl⟩, (ArchimedeanClass.orderHom_mk e p).symm⟩
    rw [heq]
    exact ha.image ac
  apply isPrimal_of_isPrimal_mapDomain inc hinci hinco Z
  · have hrange : Set.range inc = (P : Set G) := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        exact p.2
      · exact fun hx ↦ ⟨⟨x, hx⟩, rfl⟩
    rw [hrange]
    exact hP
  exact hfinite A hAfinite

/-- The common-tail coefficient of a series is primal when its remaining support classes form
a finite block and finite-class primality is known in the ambient exponent group. -/
theorem isPrimal_restrictDomain_tailSubmodule_of_ambient_finiteClasses
    [Module ℚ G] [PosSMulMono ℚ G]
    (Z : Subring R)
    (hfinite : ∀ y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (y : HahnSeries G R).support).Finite → IsPrimal y)
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) (hT₁ : T₁.Finite)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support ⊆ T₀ ∪ T₁) :
    let P := FiniteArchimedeanClass.tailSubmodule ℚ
      {c : FiniteArchimedeanClass G | c.1 ∈ T₀}
    IsPrimal (restrictDomain P.toAddSubgroup.subtype Subtype.val_injective
      (fun _ _ ↦ Iff.rfl) Z x) := by
  let P := FiniteArchimedeanClass.tailSubmodule ℚ
    {c : FiniteArchimedeanClass G | c.1 ∈ T₀}
  apply isPrimal_addSubgroup_of_ambient_finiteClasses Z hfinite P.toAddSubgroup
    (inferInstance : P.toAddSubgroup.IsConvex).ordConnected
  have hfinite' :=
    HahnSeries.supportArchimedeanClasses_coeff_zero_convexQuotientSplitRingEquiv_finite
      (K := ℚ) T₀ T₁ hT₀gt hT₁ (x : HahnSeries G R) hxclasses
  rw [HahnSeries.coeff_zero_convexQuotientSplitRingEquiv] at hfinite'
  have hre : ((restrictDomain P.toAddSubgroup.subtype Subtype.val_injective
      (fun _ _ ↦ Iff.rfl) Z x :
      cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) : HahnSeries P R) =
      HahnSeries.restrictDomain (HahnSeries.submoduleOrderEmbedding P)
        (x : HahnSeries G R) := by
    ext p
    rw [coe_restrictDomain, HahnSeries.restrictDomain_coeff,
      HahnSeries.restrictDomain_coeff]
    congr 1
    exact HahnSeries.submoduleOrderEmbedding_apply P p |>.symm
  rw [hre]
  exact hfinite'

/-- The constant coefficient after regrouping along the common tail is primal when finite-class
primality holds in the ambient exponent group. -/
theorem isPrimal_coeff_zero_convexQuotientSplitRingEquiv_of_ambient_finiteClasses
    [Module ℚ G] [PosSMulMono ℚ G] [Fact κ.IsRegular]
    (Z : Subring R)
    (hfinite : ∀ y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (y : HahnSeries G R).support).Finite → IsPrimal y)
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) (hT₁ : T₁.Finite)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support ⊆ T₀ ∪ T₁) :
    let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
    let P := FiniteArchimedeanClass.tailSubmodule ℚ T
    let S := cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z
    let E := cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z
    IsPrimal (⟨(E x : (CardSuppLTField (G := P) (R := R) (κ := κ))⟦
      G ⧸ P⟧).coeff 0,
      ((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp (E x).2).2⟩ : S) := by
  dsimp only
  rw [CardSuppLTTruncationIntegerPart.coeff_zero_convexQuotientSplitRingEquiv]
  exact isPrimal_restrictDomain_tailSubmodule_of_ambient_finiteClasses
    Z hfinite T₀ T₁ hT₀gt hT₁ x hxclasses

end HahnSeries.CardSuppLTTruncationIntegerPart
