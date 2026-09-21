/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Scalar
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.TruncationIntegerPartPrimal
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeRepresentatives
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Representatives in the associated graded ring of the Cantor–Bendixson degree

A nonpositive Hahn series represents a homogeneous class in the associated graded ring of the
Cantor–Bendixson degree
when it lies in the weight filtration and its class is that element. Evaluating a weighted
homogeneous polynomial at lifts of homogeneous classes is again such a lift: the evaluation lies
in the filtration of the weighted degree, and its class is the evaluation at the classes in the
associated graded ring.

Consequently, whenever every homogeneous class of degree below `α` is a homogeneous polynomial in
prescribed classes, every series of degree below `α` agrees, up to a series bounded strictly
below zero, with the evaluation at the lifts of a polynomial all of whose monomials have weight
below `α`. The construction removes leading homogeneous classes along a strictly decreasing
sequence of degrees, so no countability, cofinality, or support-order hypothesis enters.
-/

public noncomputable section

open Set MvPolynomial
open scoped NatOrdinal DirectSum

universe u v w

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

/-- A nonpositive series representing a homogeneous class of specified degree. -/
abbrev Represents (b : Nonpositive G K) (m : NatOrdinal.{u}) (e : (ν).AssociatedGraded) : Prop :=
  (ν).Represents b m e

theorem represents_iff {b : Nonpositive G K} {m : NatOrdinal.{u}}
    {e : (ν).AssociatedGraded} :
    Represents b m e ↔
      ∃ h : ν b ≤ m, (ν).homogeneousMk m ⟨b, ((ν).mem_filtrationLE_iff m b).mpr h⟩ = e :=
  MaxAddDegree.represents_iff

theorem Represents.degree_le {b : Nonpositive G K} {m : NatOrdinal.{u}}
    {e : (ν).AssociatedGraded} (h : Represents b m e) : ν b ≤ m :=
  MaxAddDegree.Represents.degree_le h

/-- The zero series lifts the zero class in every degree. -/
theorem represents_zero (m : NatOrdinal.{u}) :
    Represents (0 : Nonpositive G K) m 0 :=
  (ν).represents_zero m

/-- The identity series lifts the identity class in degree zero. -/
theorem represents_one : Represents (1 : Nonpositive G K) 0 1 :=
  (ν).represents_one

/-- A constant series lifts the corresponding scalar class in degree zero. -/
theorem represents_algebraMap (k : K) :
    Represents (algebraMap K (Nonpositive G K) k) 0 (algebraMap K (ν).AssociatedGraded k) := by
  refine ⟨by rw [algebraMap_apply]; exact degree_C_le k, ?_⟩
  rw [cantorBendixson_algebraMap_apply, cantorBendixsonLayerScalarHom_apply,
    (ν).homogeneousMk_apply]
  exact congrArg (DirectSum.of (ν).Component 0)
    (congrArg ((ν).componentMk 0) (Subtype.ext (algebraMap_apply k)))

/-- Lifts add: the sum of two lifts in a common degree lifts the sum of the classes. -/
theorem Represents.add {a b : Nonpositive G K} {m : NatOrdinal.{u}}
    {e f : (ν).AssociatedGraded} (ha : Represents a m e) (hb : Represents b m f) :
    Represents (a + b) m (e + f) :=
  MaxAddDegree.Represents.add ha hb

/-- Lifts multiply: the product of two lifts, at the sum of the degrees, lifts the product of
the classes. -/
theorem Represents.mul {a b : Nonpositive G K} {m n p : NatOrdinal.{u}}
    {e f : (ν).AssociatedGraded} (hp : p = m + n)
    (ha : Represents a m e) (hb : Represents b n f) :
    Represents (a * b) p (e * f) :=
  MaxAddDegree.Represents.mul hp ha hb

/-- Powers of a lift, at multiples of the degree, lift the powers of the class. -/
theorem Represents.pow {b : Nonpositive G K} {m : NatOrdinal.{u}} {e : (ν).AssociatedGraded}
    (hb : Represents b m e) (n : ℕ) : Represents (b ^ n) (n • m) (e ^ n) :=
  MaxAddDegree.Represents.pow hb n

/-- A finite product of lifts, at the sum of the degrees, lifts the product of the classes. -/
theorem represents_prod {ι' : Type w} {s : Finset ι'} {a : ι' → Nonpositive G K}
    {m : ι' → NatOrdinal.{u}} {e : ι' → (ν).AssociatedGraded}
    (h : ∀ i ∈ s, Represents (a i) (m i) (e i)) :
    Represents (∏ i ∈ s, a i) (∑ i ∈ s, m i) (∏ i ∈ s, e i) :=
  (ν).represents_prod h

/-- A finite sum of lifts in a common degree lifts the sum of the classes. -/
theorem represents_sum {ι' : Type w} {s : Finset ι'} {a : ι' → Nonpositive G K}
    {m : NatOrdinal.{u}} {e : ι' → (ν).AssociatedGraded}
    (h : ∀ i ∈ s, Represents (a i) m (e i)) :
    Represents (∑ i ∈ s, a i) m (∑ i ∈ s, e i) :=
  (ν).represents_sum h

/-- Two lifts of one class in a common degree differ by a series of strictly smaller degree. -/
theorem Represents.degree_sub_lt {a b : Nonpositive G K} {m : NatOrdinal.{u}}
    {e : (ν).AssociatedGraded} (ha : Represents a m e) (hb : Represents b m e) :
    ν (a - b) < m :=
  MaxAddDegree.Represents.degree_sub_lt ha hb

/-- A series of degree strictly below `m` lifts the zero class in degree `m`. -/
theorem represents_of_degree_lt {b : Nonpositive G K} {m : NatOrdinal.{u}}
    (h : ν b < (m : WithBot NatOrdinal)) : Represents b m 0 :=
  (ν).represents_zero_of_degree_lt h

/-- A series lifts at most one class in each degree. -/
theorem Represents.unique {b : Nonpositive G K} {m : NatOrdinal.{u}}
    {e f : (ν).AssociatedGraded} (he : Represents b m e) (hf : Represents b m f) : e = f :=
  MaxAddDegree.Represents.unique he hf

/-- A lift of a nonzero class has degree exactly the class degree. -/
theorem Represents.degree_eq {b : Nonpositive G K} {m : NatOrdinal.{u}}
    {e : (ν).AssociatedGraded} (h : Represents b m e) (he : e ≠ 0) :
    ν b = (m : WithBot NatOrdinal) :=
  MaxAddDegree.Represents.degree_eq h he

variable {ι : Type w} {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}

/-- Evaluating a weighted homogeneous polynomial at lifts of homogeneous classes lifts the
evaluation at the classes: it lies in the filtration of the weighted degree, and its class is
the evaluation in the associated graded ring. -/
theorem represents_aeval (x : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (x i))
    {F : MvPolynomial ι K} {β : NatOrdinal.{u}} (hF : IsWeightedHomogeneous wt F β) :
    Represents (aeval V F) β (aeval x F) :=
  (ν).represents_aeval represents_algebraMap hV hF

/-- The evaluation of a polynomial all of whose monomials have weight strictly below `α` has
degree strictly below `α`. -/
theorem degree_aeval_lt_of_forall_weight_lt (x : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (x i))
    {F : MvPolynomial ι K} {α : NatOrdinal.{u}}
    (hF : ∀ d ∈ F.support, (Finsupp.weight wt) d < α) :
    ν (aeval V F) < (α : WithBot NatOrdinal) :=
  (ν).degree_aeval_lt_of_forall_weight_lt represents_algebraMap hV hF

/-- Evaluation of a polynomial with weights at most `β` lifts the evaluation of its top weighted
homogeneous component. -/
theorem represents_aeval_weightedHomogeneousComponent (x : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (x i))
    {F : MvPolynomial ι K} {β : NatOrdinal.{u}}
    (hw : ∀ d ∈ F.support, (Finsupp.weight wt) d ≤ β) :
    Represents (aeval V F) β (aeval x (weightedHomogeneousComponent wt β F)) :=
  (ν).represents_aeval_weightedHomogeneousComponent represents_algebraMap hV hw

/-- Evaluation at the lifts has degree exactly `β` whenever the evaluation of the top weighted
homogeneous component does not vanish in the associated graded ring. -/
theorem degree_aeval_eq_of_aeval_weightedHomogeneousComponent_ne_zero
    (x : ι → (ν).AssociatedGraded) (hV : ∀ i, Represents (V i) (wt i) (x i))
    {F : MvPolynomial ι K} {β : NatOrdinal.{u}}
    (hw : ∀ d ∈ F.support, (Finsupp.weight wt) d ≤ β)
    (hne : aeval x (weightedHomogeneousComponent wt β F) ≠ 0) :
    ν (aeval V F) = (β : WithBot NatOrdinal) :=
  (represents_aeval_weightedHomogeneousComponent x hV hw).degree_eq hne

/-- Under injectivity of the graded evaluation below `α`, a polynomial with weights below `α`
whose evaluation at the lifts is bounded strictly below zero is the zero polynomial. This is the
uniqueness of the polynomial of a series modulo bounded series. -/
theorem eq_zero_of_forall_weight_lt_of_degree_aeval_eq_bot
    (x : ι → (ν).AssociatedGraded) (hV : ∀ i, Represents (V i) (wt i) (x i))
    {α : NatOrdinal.{u}}
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval x F = 0 → F = 0)
    {F : MvPolynomial ι K} (hw : ∀ d ∈ F.support, (Finsupp.weight wt) d < α)
    (hbot : ν (aeval V F) = ⊥) : F = 0 := by
  classical
  suffices H : ∀ β : NatOrdinal.{u}, ∀ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) →
      (∀ d ∈ F.support, (Finsupp.weight wt) d ≤ β) →
      ν (aeval V F) = ⊥ → F = 0 from
    H (F.support.sup (Finsupp.weight wt)) F hw (fun _ hd ↦ Finset.le_sup hd) hbot
  intro β
  induction β using WellFoundedLT.induction with
  | _ β ih =>
    intro F hw hβ hbot
    have hcomp0 : weightedHomogeneousComponent wt β F = 0 := by
      by_cases hzero : weightedHomogeneousComponent wt β F = 0
      · exact hzero
      · obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hzero
        rw [coeff_weightedHomogeneousComponent] at hd
        by_cases hdw : (Finsupp.weight wt) d = β
        · rw [if_pos hdw] at hd
          have hβα : β < α := hdw ▸ hw d (MvPolynomial.mem_support_iff.mpr hd)
          have hrep := represents_aeval_weightedHomogeneousComponent x hV hβ
          have hrep0 : Represents (aeval V F) β 0 :=
            represents_of_degree_lt (by rw [hbot]; exact WithBot.bot_lt_coe β)
          exact absurd (hinj β _ hβα
            (weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := β) (φ := F))
            (hrep.unique hrep0)) hzero
        · rw [if_neg hdw] at hd
          exact absurd rfl hd
    have hlt : ∀ d ∈ F.support, (Finsupp.weight wt) d < β := by
      intro d hd
      refine lt_of_le_of_ne (hβ d hd) fun he ↦ ?_
      have := congrArg (MvPolynomial.coeff d) hcomp0
      rw [coeff_weightedHomogeneousComponent, if_pos he, MvPolynomial.coeff_zero] at this
      exact MvPolynomial.mem_support_iff.mp hd this
    rcases eq_or_ne β 0 with rfl | hβ0
    · rw [MvPolynomial.eq_zero_iff]
      intro d
      by_contra hd
      exact absurd (hlt d (MvPolynomial.mem_support_iff.mpr hd))
        (not_lt_of_ge (zero_le (a := (Finsupp.weight wt) d)))
    · have hsuplt : F.support.sup (Finsupp.weight wt) < β :=
        Finset.sup_lt_iff (pos_of_ne_zero hβ0) |>.mpr hlt
      exact ih _ hsuplt F hw (fun _ hd ↦ Finset.le_sup hd) hbot

/-- Under injectivity of the graded evaluation below `α`, every monomial weight of a polynomial
is bounded by the degree of its evaluation at the lifts. -/
theorem forall_weight_le_degree_aeval_of_injective
    (x : ι → (ν).AssociatedGraded) (hV : ∀ i, Represents (V i) (wt i) (x i))
    {α : NatOrdinal.{u}}
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval x F = 0 → F = 0)
    {F : MvPolynomial ι K} (hw : ∀ d ∈ F.support, (Finsupp.weight wt) d < α) :
    ∀ d ∈ F.support, (((Finsupp.weight wt) d : NatOrdinal) : WithBot NatOrdinal) ≤
      ν (aeval V F) := by
  classical
  suffices H : ∀ β : NatOrdinal.{u}, ∀ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) →
      (∀ d ∈ F.support, (Finsupp.weight wt) d ≤ β) →
      ∀ d ∈ F.support, (((Finsupp.weight wt) d : NatOrdinal) : WithBot NatOrdinal) ≤
        ν (aeval V F) from
    H (F.support.sup (Finsupp.weight wt)) F hw (fun _ hd ↦ Finset.le_sup hd)
  intro β
  induction β using WellFoundedLT.induction with
  | _ β ih =>
    intro F hw hβ d hd
    by_cases hzero : weightedHomogeneousComponent wt β F = 0
    · have hlt : ∀ e ∈ F.support, (Finsupp.weight wt) e < β := by
        intro e he
        refine lt_of_le_of_ne (hβ e he) fun heq ↦ ?_
        have hcz := congrArg (MvPolynomial.coeff e) hzero
        rw [coeff_weightedHomogeneousComponent, if_pos heq, MvPolynomial.coeff_zero] at hcz
        exact MvPolynomial.mem_support_iff.mp he hcz
      rcases eq_or_ne β 0 with rfl | hβ0
      · exact absurd (hlt d hd) (not_lt_of_ge (zero_le (a := (Finsupp.weight wt) d)))
      · exact ih (F.support.sup (Finsupp.weight wt))
          (Finset.sup_lt_iff (pos_of_ne_zero hβ0) |>.mpr hlt) F hw
          (fun _ he ↦ Finset.le_sup he) d hd
    · obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.mp hzero
      rw [coeff_weightedHomogeneousComponent] at he
      by_cases hew : (Finsupp.weight wt) e = β
      · have hβα : β < α := hew ▸ hw e (MvPolynomial.mem_support_iff.mpr (by
          rwa [if_pos hew] at he))
        have haev : aeval x (weightedHomogeneousComponent wt β F) ≠ 0 := fun h ↦
          hzero (hinj β _ hβα
            (weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := β) (φ := F)) h)
        rw [(represents_aeval_weightedHomogeneousComponent x hV hβ).degree_eq haev]
        exact WithBot.coe_le_coe.mpr (hβ d hd)
      · rw [if_neg hew] at he
        exact absurd rfl he

open Classical in
/-- The polynomial of a series modulo bounded series, at arbitrary cofinality. If every
homogeneous class of degree below `α` is a homogeneous polynomial in prescribed classes, then
every series of degree below `α` agrees, up to a series bounded strictly below zero, with the
evaluation at the lifts of a polynomial all of whose monomials have weight below `α`. -/
theorem exists_forall_weight_lt_and_degree_sub_aeval_eq_bot
    (x : ι → (ν).AssociatedGraded) (hV : ∀ i, Represents (V i) (wt i) (x i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval x F = y)
    (u : Nonpositive G K) (hu : ν u < (α : WithBot NatOrdinal)) :
    ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (((Finsupp.weight wt) d : NatOrdinal) : WithBot NatOrdinal) ≤ ν u) ∧
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (u - aeval V F) = ⊥ := by
  classical
  suffices H : ∀ b : WithBot NatOrdinal.{u}, b < (α : WithBot NatOrdinal) →
      ∀ u : Nonpositive G K, ν u = b →
        ∃ F : MvPolynomial ι K,
          (∀ d ∈ F.support, (((Finsupp.weight wt) d : NatOrdinal) : WithBot NatOrdinal) ≤ ν u) ∧
          (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
          ν (u - aeval V F) = ⊥ from H (ν u) hu u rfl
  intro b
  induction b using WellFoundedLT.induction with
  | _ b ih =>
    intro hbα u hb
    cases b with
    | bot =>
        refine ⟨0, by simp, by simp, ?_⟩
        rw [map_zero, sub_zero, hb]
    | coe β =>
        have hβα : β < α := WithBot.coe_lt_coe.mp hbα
        have hle : ν u ≤ β := hb.le
        obtain ⟨Fβ, hFβhom, hFβval⟩ := hgen β hβα (DirectSum.of (ν).Component β
            ((ν).componentMk β ⟨u, ((ν).mem_filtrationLE_iff β u).mpr hle⟩))
          (DirectSum.of_mem_rangeLof K (ν).Component β _)
        have hrepu : Represents u β (DirectSum.of (ν).Component β
            ((ν).componentMk β ⟨u, ((ν).mem_filtrationLE_iff β u).mpr hle⟩)) :=
          ⟨hle, (ν).homogeneousMk_apply β _⟩
        have hrepF : Represents (aeval V Fβ) β (DirectSum.of (ν).Component β
            ((ν).componentMk β ⟨u, ((ν).mem_filtrationLE_iff β u).mpr hle⟩)) := by
          rw [← hFβval]
          exact represents_aeval x hV hFβhom
        have hdrop : ν (u - aeval V Fβ) < (β : WithBot NatOrdinal) :=
          hrepu.degree_sub_lt hrepF
        obtain ⟨F', hF'd, hF'w, hF'⟩ := ih (ν (u - aeval V Fβ)) hdrop (hdrop.trans hbα)
          (u - aeval V Fβ) rfl
        refine ⟨Fβ + F', ?_, ?_, ?_⟩
        · intro d hd
          rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
          · rw [hFβhom (MvPolynomial.mem_support_iff.mp hd), hb]
          · exact (hF'd d hd).trans (hdrop.le.trans hb.ge)
        · intro d hd
          rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
          · rw [hFβhom (MvPolynomial.mem_support_iff.mp hd)]
            exact hβα
          · exact hF'w d hd
        · rw [map_add, show u - (aeval V Fβ + aeval V F') =
            u - aeval V Fβ - aeval V F' by ring]
          exact hF'

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CharZero K] in
/-- Translated weak truncation is linear over the coefficient field. -/
theorem translatedTruncLE_smul (γ : G) (k : K) (b : Nonpositive G K) :
    translatedTruncLE γ (k • b) = k • translatedTruncLE γ b := by
  apply Subtype.ext
  rw [coe_translatedTruncLE, coe_smul, coe_smul, coe_translatedTruncLE]
  ext g
  rw [HahnSeries.coeff_smul, coeff_translate, coeff_translate, HahnSeries.coeff_truncLE,
    HahnSeries.coeff_truncLE, HahnSeries.coeff_smul]
  by_cases h : g - -γ ≤ γ
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, smul_zero]

/-- A lift of the zero class has degree strictly below the class degree. -/
theorem Represents.degree_lt_of_eq_zero {b : Nonpositive G K} {m : NatOrdinal.{u}}
    (h : Represents b m 0) : ν b < (m : WithBot NatOrdinal) :=
  MaxAddDegree.Represents.degree_lt_of_eq_zero h

/-- A degree strictly below a nonzero bound admits a natural-ordinal witness. -/
theorem exists_le_of_degree_lt {b : Nonpositive G K} {m : NatOrdinal.{u}}
    (h : ν b < (m : WithBot NatOrdinal)) (hm : m ≠ 0) :
    ∃ m₀ : NatOrdinal.{u}, m₀ < m ∧ ν b ≤ (m₀ : WithBot NatOrdinal) := by
  by_cases hbot : ν b = ⊥
  · exact ⟨0, pos_iff_ne_zero.mpr hm, by rw [hbot]; exact bot_le⟩
  · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
    rw [← hd] at h ⊢
    exact ⟨d, WithBot.coe_lt_coe.mp h, le_rfl⟩

/-- **Lifting a series congruence back to a polynomial identity.** Under injectivity of the graded
evaluation below `α`, two weighted homogeneous polynomials of a common degree below `α` whose
evaluations at the lifts differ by a series of strictly smaller degree are equal. This is how a
relation established among series is returned to the polynomial ring. -/
theorem eq_of_degree_sub_aeval_lt {ι : Type w} {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}
    (xg : ι → (ν).AssociatedGraded) (hV : ∀ i, Represents (V i) (wt i) (xg i))
    {α : NatOrdinal.{u}}
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    {A B : MvPolynomial ι K} {m : NatOrdinal.{u}} (hm : m < α)
    (hA : IsWeightedHomogeneous wt A m) (hB : IsWeightedHomogeneous wt B m)
    (h : ν (aeval V A - aeval V B) < (m : WithBot NatOrdinal)) :
    A = B := by
  have hAB : IsWeightedHomogeneous wt (A - B) m := by
    rw [← MvPolynomial.mem_weightedHomogeneousSubmodule] at hA hB ⊢
    exact Submodule.sub_mem _ hA hB
  have hcoe : aeval V (A - B) = aeval V A - aeval V B := map_sub _ _ _
  have hzero : Represents (aeval V (A - B)) m 0 := by
    rw [hcoe]
    exact represents_of_degree_lt h
  have hrep : Represents (aeval V (A - B)) m (aeval xg (A - B)) := represents_aeval xg hV hAB
  have hclass : aeval xg (A - B) = 0 := hrep.unique hzero
  have := hinj m (A - B) hm hAB hclass
  exact sub_eq_zero.mp this

/-- The class a series lifts lies in the corresponding homogeneous component. -/
theorem Represents.mem_rangeLof {b : Nonpositive G K} {m : NatOrdinal.{u}}
    {e : (ν).AssociatedGraded} (h : Represents b m e) :
    e ∈ DirectSum.rangeLof K (ν).Component m := by
  obtain ⟨hd, he⟩ := h
  rw [← he, (ν).homogeneousMk_apply]
  exact DirectSum.of_mem_rangeLof K (ν).Component m _

end HahnSeries.Nonpositive
