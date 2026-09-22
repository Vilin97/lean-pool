/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.OrdinalGenerators
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeRepresentatives
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalGraded
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.SuccessorLeibniz
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAt
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.TruncationIntegerPartPrimal
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Lifts of a minimal system of homogeneous generators of `P̂` and the polynomial of a series
modulo `J`

Fix a minimal system of homogeneous generators `𝓑` of `P̂` (Lean `x : ι → P̂`, the generator `x i`
of degree `wt i`; `OrdinalGraded.IsMinimalSystem`) and lifts: series `lift i ∈ J_{ω^(wt i + 1)}`
representing `x i`, i.e. with class `x i` in `P_{wt i}`. Evaluation at the lifts is graded modulo
`J_{ω^β}`: a polynomial `F` homogeneous of degree `β` evaluates to a series `F(b_𝓑) ∈ J_{ω^(β+1)}`
representing `F(𝓑)`.

Read modulo Berarducci's ideal `J` [Ber00, Def. 5.1], this gives the *polynomial of a series
modulo `J`*. Without any hypothesis, every series of ordinal value below `ω^α` is congruent
modulo `J` to a value `F(b_𝓑)` with every monomial of `F` of degree below `α`, by well-founded
induction on the ordinal value. If moreover evaluation `K[X] → P̂` is injective in every degree
below `α`, the polynomial is unique, and `v_J(F(b_𝓑)) = ω^(deg F)` for `F ≠ 0`. The function
`pol` records the polynomial of a series modulo `J`.
-/

universe v w

open scoped NatOrdinal DirectSum
open Berarducci MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

local notation "ν" => (ordinalValueDegreeValuation K)

/-! ### Series representing homogeneous elements of `P̂` -/

/-- A series representing a homogeneous element of `P̂` in a specified degree. -/
abbrev Represents (u : Series K) (β : NatOrdinal) (e : PrincipalSubring K) : Prop :=
  (ν).Represents u β e

theorem represents_iff {u : Series K} {β : NatOrdinal} {e : PrincipalSubring K} :
    Represents u β e ↔ ∃ h : ordinalValue u < ω^ (β + 1),
      DirectSum.of (PrincipalComponent K) β (principalComponentMk β u h) = e := by
  change (ν).Represents u β e ↔ _
  rw [MaxAddDegree.represents_iff]
  constructor
  · rintro ⟨hdegree, hclass⟩
    have hvalue : ordinalValue u < ω^ (β + 1) :=
      (mem_ordinalValueDegreeValuation_filtrationLE_iff u β).mp
        ((ν).mem_filtrationLE_iff β u |>.mpr hdegree)
    refine ⟨hvalue, ?_⟩
    simpa only [MaxAddDegree.homogeneousMk_apply, principalComponentMk_eq_componentMk] using hclass
  · rintro ⟨hvalue, hclass⟩
    have hdegree : ν u ≤ β :=
      ((ν).mem_filtrationLE_iff β u).mp
        ((mem_ordinalValueDegreeValuation_filtrationLE_iff u β).mpr hvalue)
    refine ⟨hdegree, ?_⟩
    simpa only [MaxAddDegree.homogeneousMk_apply, principalComponentMk_eq_componentMk] using hclass

theorem Represents.ordinalValue_lt {u : Series K} {β : NatOrdinal} {e : PrincipalSubring K}
    (h : Represents u β e) : ordinalValue u < ω^ (β + 1) :=
  (ordinalValueDegree_le_coe_iff u β).mp (by
    simpa only [ordinalValueDegreeValuation_apply] using h.degree_le)

theorem Represents.of_principalComponentMk {u : Series K} {β : NatOrdinal} {e : PrincipalSubring K}
    (h : Represents u β e) :
    DirectSum.of (PrincipalComponent K) β (principalComponentMk β u h.ordinalValue_lt) = e :=
  (represents_iff.mp h).2

theorem represents_zero (β : NatOrdinal) : Represents (0 : Series K) β 0 :=
  (ν).represents_zero β

theorem represents_C (k : K) :
    Represents ((HahnSeries.Nonpositive.C : K →+* Series K) k) 0
      (algebraMap K (PrincipalSubring K) k) :=
  represents_iff.mpr ⟨ordinalValue_C_lt_wpow_one k, by
    rw [principalSubring_algebraMap_apply, principalComponentScalarHom_apply]⟩

theorem represents_one : Represents (1 : Series K) 0 1 := by
  have := represents_C (K := K) 1
  rwa [map_one, map_one] at this

theorem Represents.add {u u' : Series K} {β : NatOrdinal} {e e' : PrincipalSubring K}
    (h : Represents u β e) (h' : Represents u' β e') : Represents (u + u') β (e + e') :=
  MaxAddDegree.Represents.add h h'

theorem Represents.mul {u u' : Series K} {β β' : NatOrdinal} {e e' : PrincipalSubring K}
    (h : Represents u β e) (h' : Represents u' β' e') :
    Represents (u * u') (β + β') (e * e') :=
  MaxAddDegree.Represents.mul rfl h h'

theorem Represents.pow {u : Series K} {β : NatOrdinal} {e : PrincipalSubring K}
    (h : Represents u β e) (n : ℕ) : Represents (u ^ n) (n • β) (e ^ n) :=
  MaxAddDegree.Represents.pow h n

theorem represents_prod {ι : Type w} (s : Finset ι) (f : ι → Series K) (g : ι → NatOrdinal)
    (e : ι → PrincipalSubring K) (h : ∀ i ∈ s, Represents (f i) (g i) (e i)) :
    Represents (∏ i ∈ s, f i) (∑ i ∈ s, g i) (∏ i ∈ s, e i) :=
  (ν).represents_prod h

/-- The ordinal value of a series representing a nonzero element of `P̂` in degree `β` is
exactly `ω^β`. -/
theorem Represents.ordinalValue_eq {u : Series K} {β : NatOrdinal} {e : PrincipalSubring K}
    (h : Represents u β e) (he : e ≠ 0) : ordinalValue u = ω^ β := by
  apply (ordinalValueDegree_eq_coe_iff u β).mp
  simpa only [ordinalValueDegreeValuation_apply] using
    MaxAddDegree.Represents.degree_eq h he

/-- A series representing `0` in degree `β` has ordinal value below `ω^β`. -/
theorem Represents.ordinalValue_lt_of_eq_zero {u : Series K} {β : NatOrdinal}
    (h : Represents u β 0) : ordinalValue u < ω^ β := by
  apply (ordinalValueDegree_lt_coe_iff u β).mp
  simpa only [ordinalValueDegreeValuation_apply] using
    MaxAddDegree.Represents.degree_lt_of_eq_zero h

/-! ### Lifts of a minimal system of homogeneous generators -/

variable {ι : Type w} (wt : ι → NatOrdinal) (x : ι → PrincipalSubring K)

/-- Representatives of a family of homogeneous elements of `P̂`, in their specified degrees. -/
abbrev Lifts := MaxAddDegree.LiftFamily (ordinalValueDegreeValuation K) wt x

variable {wt x}

/-- Lifts exist for every family of homogeneous elements. -/
theorem exists_lifts (hmem : ∀ i, x i ∈ Berarducci.principalGrading K (wt i)) :
    Nonempty (Lifts wt x) := by
  have h : ∀ i, ∃ u : Series K, Represents u (wt i) (x i) := fun i ↦ by
    obtain ⟨a, ha⟩ := (DirectSum.mem_rangeLof_iff K _ _ _).mp (hmem i)
    obtain ⟨u, hu, rfl⟩ := exists_principalComponentMk (wt i) a
    exact ⟨u, represents_iff.mpr ⟨hu, by rw [← ha, DirectSum.lof_eq_of]⟩⟩
  choose u hu using h
  exact ⟨⟨u, hu⟩⟩

namespace Lifts

variable (σ : Lifts wt x)

/-- Evaluation at the lifts is graded: `F(b_𝓑) ∈ J_{ω^(β+1)}` represents `F(𝓑)` in degree `β` for
`F` homogeneous of degree `β`. -/
@[blueprint "lem:homogeneous-evaluation-represents"
  (phase := "Translated truncations")
  (title := "Initial form of a weighted-homogeneous evaluation")
  (statement := /--
    Let $K$ be a field. For each $i\in I$, let
    $x_i\in\mathrm P_{\alpha_i}\subseteq\widehat{\mathrm P}$ and choose
    $b_i\in K((\mathbb R^{\le0}))$ representing $x_i$, so that
    \[
      v_J(b_i)<\omega^{\alpha_i+1},\qquad
      b_i+J_{\omega^{\alpha_i}}=x_i.
    \]
    If $F\in K[X_i:i\in I]$ is weighted-homogeneous of degree $\beta$ for the
    weights $\alpha_i$, then
    \[
      v_J(F(b_i))<\omega^{\beta+1},\qquad
      F(b_i)+J_{\omega^\beta}=F(x_i)\in\mathrm P_\beta.
    \]
  -/)
  (proof := /--
  Constants represent their images in degree $0$, and representatives are
  preserved by addition, multiplication, and powers. Hence every monomial in
  $F(b_i)$ represents the corresponding monomial in $F(x_i)$ in its weighted
  degree. Since every monomial of $F$ has weighted degree $\beta$, summing gives
  the two asserted properties in degree $\beta$.
  -/)]
theorem aeval_represents {F : MvPolynomial ι K} {β : NatOrdinal}
    (hF : IsWeightedHomogeneous wt F β) : Represents (aeval σ.lift F) β (aeval x F) :=
  (ν).represents_aeval represents_C σ.represents hF

/-- `v_J(F(b_𝓑)) < ω^(β+1)` for `F` homogeneous of degree `β`. -/
theorem ordinalValue_aeval_lt_of_isWeightedHomogeneous {F : MvPolynomial ι K} {β : NatOrdinal}
    (hF : IsWeightedHomogeneous wt F β) : ordinalValue (aeval σ.lift F) < ω^ (β + 1) :=
  (σ.aeval_represents hF).ordinalValue_lt

/-- `v_J(F(b_𝓑)) = ω^β` for `F` homogeneous of degree `β` with `F(𝓑) ≠ 0`. -/
theorem ordinalValue_aeval_eq_of_aeval_ne_zero {F : MvPolynomial ι K} {β : NatOrdinal}
    (hF : IsWeightedHomogeneous wt F β) (h : aeval x F ≠ 0) :
    ordinalValue (aeval σ.lift F) = ω^ β :=
  (σ.aeval_represents hF).ordinalValue_eq h

/-- `v_J(F(b_𝓑)) < ω^β` for `F` homogeneous of degree `β` with `F(𝓑) = 0`. -/
theorem ordinalValue_aeval_lt_of_aeval_eq_zero {F : MvPolynomial ι K} {β : NatOrdinal}
    (hF : IsWeightedHomogeneous wt F β) (h : aeval x F = 0) :
    ordinalValue (aeval σ.lift F) < ω^ β :=
  (h ▸ σ.aeval_represents hF).ordinalValue_lt_of_eq_zero

end Lifts

/-! ### Polynomials of degree below `α` -/

variable (wt) in
/-- Every monomial of `F` has degree below `α`. -/
def DegreeLT (F : MvPolynomial ι K) (α : NatOrdinal) : Prop :=
  ∀ d ∈ F.support, Finsupp.weight wt d < α

theorem degreeLT_iff {F : MvPolynomial ι K} {α : NatOrdinal} :
    DegreeLT wt F α ↔ ∀ d ∈ F.support, Finsupp.weight wt d < α :=
  Iff.rfl

theorem degreeLT_zero (α : NatOrdinal) : DegreeLT wt (0 : MvPolynomial ι K) α := fun d hd ↦ by
  simp at hd

theorem DegreeLT.add {F G : MvPolynomial ι K} {α : NatOrdinal} (hF : DegreeLT wt F α)
    (hG : DegreeLT wt G α) : DegreeLT wt (F + G) α := fun d hd ↦ by
  classical
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hF d h
  · exact hG d h

theorem DegreeLT.neg {F : MvPolynomial ι K} {α : NatOrdinal} (hF : DegreeLT wt F α) :
    DegreeLT wt (-F) α := fun d hd ↦ hF d (by rwa [MvPolynomial.support_neg] at hd)

theorem DegreeLT.sub {F G : MvPolynomial ι K} {α : NatOrdinal} (hF : DegreeLT wt F α)
    (hG : DegreeLT wt G α) : DegreeLT wt (F - G) α := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

theorem DegreeLT.mono {F : MvPolynomial ι K} {α α' : NatOrdinal} (hF : DegreeLT wt F α)
    (h : α ≤ α') : DegreeLT wt F α' := fun d hd ↦ (hF d hd).trans_le h

theorem _root_.MvPolynomial.IsWeightedHomogeneous.degreeLT {F : MvPolynomial ι K}
    {β α : NatOrdinal} (hF : IsWeightedHomogeneous wt F β) (h : β < α) : DegreeLT wt F α :=
  fun _ hd ↦ (hF (mem_support_iff.mp hd)).symm ▸ h

/-- The homogeneous components of `F` of degree at least `α` vanish when `F` has degree below `α`.
-/
theorem DegreeLT.weightedHomogeneousComponent_eq_zero {F : MvPolynomial ι K} {α β : NatOrdinal}
    (hF : DegreeLT wt F α) (h : α ≤ β) : weightedHomogeneousComponent wt β F = 0 :=
  weightedHomogeneousComponent_eq_zero' β F fun d hd (hw : Finsupp.weight wt d = β) ↦
    (hF d hd).not_ge (hw.symm ▸ h)

/-- The component of `F` in degree `β` has degree below `α` whenever `F` does. -/
theorem DegreeLT.weightedHomogeneousComponent {F : MvPolynomial ι K} {α : NatOrdinal}
    (hF : DegreeLT wt F α) (β : NatOrdinal) :
    DegreeLT wt (weightedHomogeneousComponent wt β F) α := by
  classical
  intro d hd
  rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with hw
  · exact hF d (mem_support_iff.mpr hd)
  · exact absurd rfl hd

/-- A nonzero polynomial of degree below `α` has total degree below `α`. -/
theorem DegreeLT.weightedTotalDegree_lt {F : MvPolynomial ι K} {α : NatOrdinal}
    (hF : DegreeLT wt F α) (hF0 : F ≠ 0) : weightedTotalDegree wt F < α := by
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr hF0)
    (Finsupp.weight wt)
  rw [weightedTotalDegree, hsup]
  exact hF d hd

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
theorem weightedHomogeneousComponent_weightedTotalDegree_ne_zero {F : MvPolynomial ι K}
    (hF0 : F ≠ 0) : weightedHomogeneousComponent wt (weightedTotalDegree wt F) F ≠ 0 := by
  classical
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr hF0)
    (Finsupp.weight wt)
  intro h
  have := congrArg (fun p : MvPolynomial ι K ↦ p.coeff d) h
  rw [coeff_weightedHomogeneousComponent, ite_eq_left (by rw [weightedTotalDegree, hsup]),
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  exact mem_support_iff.mp hd this

/-- Removing the top homogeneous component leaves a polynomial of degree below the top degree. -/
theorem degreeLT_sub_weightedHomogeneousComponent_weightedTotalDegree (F : MvPolynomial ι K) :
    DegreeLT wt (F - weightedHomogeneousComponent wt (weightedTotalDegree wt F) F)
      (weightedTotalDegree wt F) := by
  classical
  intro d hd
  rw [mem_support_iff, coeff_sub, coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with hw
  · exact absurd (sub_self _) hd
  · exact lt_of_le_of_ne (le_weightedTotalDegree wt (mem_support_iff.mpr fun h ↦ hd
      (by rw [h, sub_zero]))) hw

/-- A polynomial of degree below `α` is the sum of its homogeneous components of degree below `α`,
over the finite set of degrees occurring. -/
theorem sum_weightedHomogeneousComponent_eq (F : MvPolynomial ι K) :
    ∑ β ∈ (weightedHomogeneousComponent_finsupp (w := wt) F).toFinset,
      weightedHomogeneousComponent wt β F = F := by
  rw [← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp F), sum_weightedHomogeneousComponent]

/-! ### Ordinal value of a finite sum -/

/-- The ordinal value of a finite sum of series of ordinal value below `c > 0` is below `c`. -/
theorem ordinalValue_sum_lt {ι' : Type*} (s : Finset ι') (f : ι' → Series K) {c : NatOrdinal}
    (hc : 0 < c) (h : ∀ i ∈ s, ordinalValue (f i) < c) : ordinalValue (∑ i ∈ s, f i) < c := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ordinalValue_zero]; exact hc
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (ordinalValue_add_le_max _ _).trans_lt (max_lt (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

/-- The ordinal value of `a + b` is that of `a` when `v_J(b) < v_J(a)`. -/
theorem ordinalValue_add_eq_of_lt {a b : Series K} (h : ordinalValue b < ordinalValue a) :
    ordinalValue (a + b) = ordinalValue a := by
  refine le_antisymm ((ordinalValue_add_le_max a b).trans (max_le le_rfl h.le)) ?_
  have h1 : a = a + b + -b := by abel
  calc ordinalValue a = ordinalValue (a + b + -b) := by rw [← h1]
    _ ≤ max (ordinalValue (a + b)) (ordinalValue (-b)) := ordinalValue_add_le_max _ _
    _ ≤ ordinalValue (a + b) := by
      rw [ordinalValue_neg]
      refine max_le le_rfl ?_
      by_contra hlt
      rw [not_le] at hlt
      have h2 : ordinalValue (a + b) ≤ max (ordinalValue a) (ordinalValue b) :=
        ordinalValue_add_le_max a b
      rw [max_eq_left h.le] at h2
      have h3 : ordinalValue a ≤ max (ordinalValue (a + b)) (ordinalValue b) := by
        calc ordinalValue a = ordinalValue (a + b + -b) := by rw [← h1]
          _ ≤ max (ordinalValue (a + b)) (ordinalValue (-b)) := ordinalValue_add_le_max _ _
          _ = _ := by rw [ordinalValue_neg]
      rw [max_eq_right hlt.le] at h3
      exact h.not_ge h3

namespace Lifts

variable (σ : Lifts wt x)

/-- `v_J(F(b_𝓑)) < ω^α` when every monomial of `F` has degree below `α`. -/
theorem ordinalValue_aeval_lt_of_degreeLT {F : MvPolynomial ι K} {α : NatOrdinal}
    (hF : DegreeLT wt F α) : ordinalValue (aeval σ.lift F) < ω^ α :=
  (ordinalValueDegree_lt_coe_iff _ _).mp (by
    simpa only [ordinalValueDegreeValuation_apply] using
      (ν).degree_aeval_lt_of_forall_weight_lt represents_C σ.represents hF)

/-! ### Every series of ordinal value below `ω^α` is congruent modulo `J` to a value `F(b_𝓑)` -/

variable (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
include hx

/-- Every series of ordinal value below `ω^α` is congruent modulo `J` to a value `F(b_𝓑)` with
every monomial of `F` of degree below `α`. -/
@[blueprint "prop:polynomial-representative-exists"
  (phase := "Translated truncations")
  (title := "Existence of polynomial representatives modulo $J$")
  (statement := /--
    Let $K$ be a field, let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of
    $\widehat{\mathrm P}=\bigoplus_{\beta<\omega_1}\mathrm P_\beta$, with
    $x_i\in\mathrm P_{w_i}$, and choose representatives $b_i$ satisfying
    \[
      v_J(b_i)<\omega^{w_i+1},\qquad
      b_i+J_{\omega^{w_i}}=x_i.
    \]
    If $\alpha<\omega_1$ and
    $u\in K((\mathbb R^{\le0}))$ satisfies $v_J(u)<\omega^\alpha$, then there
    is a polynomial $F\in K[X_i:i\in I]$ such that every monomial of $F$ has
    weighted degree less than $\alpha$ and
    \[
      u\equiv F(b_i)\pmod J.
    \]
  -/)
  (proof := /--
  Use well-founded induction on $v_J(u)$. The case $u\in J$ is represented by
  $0$. Otherwise $v_J(u)=\omega^\beta$ for some $\beta<\alpha$. Since the
  chosen $b_i$ are available by
  \ref{fact:principal-series-representatives}, and since the $x_i$ generate
  $\widehat{\mathrm P}$, \ref{lem:generate} gives a weighted-homogeneous polynomial $F_0$ of
  degree $\beta$ whose value $F_0(x_i)$ is the class of $u$ in $\mathrm P_\beta$.
  By \ref{lem:homogeneous-evaluation-represents}, $F_0(b_i)$ represents the
  same class, so
  \[
    v_J\bigl(u-F_0(b_i)\bigr)<v_J(u).
  \]
  Apply the induction hypothesis to this difference, obtaining $F_1$, and take
  $F=F_0+F_1$.
  -/)]
theorem exists_degreeLT_toGerm_aeval_eq (α : NatOrdinal) :
    ∀ u : Series K, ordinalValue u < ω^ α →
      ∃ F : MvPolynomial ι K, DegreeLT wt F α ∧ toGerm (aeval σ.lift F) = toGerm u := by
  suffices h : ∀ o : NatOrdinal, ∀ u : Series K, ordinalValue u = o → ordinalValue u < ω^ α →
      ∃ F : MvPolynomial ι K, DegreeLT wt F α ∧ toGerm (aeval σ.lift F) = toGerm u from
    fun u hu ↦ h _ u rfl hu
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
  intro u huo hu
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal u with h0 | hprin
  · -- `u ∈ J`
    refine ⟨0, degreeLT_zero α, ?_⟩
    rw [map_zero, map_zero, eq_comm, toGerm_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact ordinalValue_eq_zero_iff.mp h0
  · obtain ⟨γ, hγ⟩ := Ordinal.isAdditivelyPrincipal_iff.mp hprin
    set β : NatOrdinal := NatOrdinal.of γ with hβdef
    have hval : ordinalValue u = ω^ β := by
      rw [hβdef, NatOrdinal.wpow_def, NatOrdinal.val_of, ← hγ, NatOrdinal.of_val]
    have hβα : β < α := by rwa [hval, NatOrdinal.wpow_lt_wpow] at hu
    have hu1 : ordinalValue u < ω^ (β + 1) := by
      rw [hval, NatOrdinal.wpow_lt_wpow]; exact Order.lt_add_one_iff.mpr le_rfl
    -- the class of `u` in `P_β` is the evaluation of a homogeneous polynomial
    obtain ⟨G, hG, hGu⟩ := hx.exists_aeval_eq
      (Berarducci.principalGrading_gradeZeroScalars K) β
      (DirectSum.of (PrincipalComponent K) β (principalComponentMk β u hu1))
      (Berarducci.of_mem_principalGrading β _)
    have hrep := σ.aeval_represents hG
    rw [hGu] at hrep
    obtain ⟨hGlt, hGmk⟩ := represents_iff.mp hrep
    have hmk : principalComponentMk β (aeval σ.lift G) hGlt = principalComponentMk β u hu1 :=
      DirectSum.of_injective β hGmk
    rw [principalComponentMk_eq_iff] at hmk
    -- the difference `u - G(b_𝓑)` has smaller ordinal value
    have hrem : ordinalValue (u - aeval σ.lift G) < o := by
      rw [← huo, hval]
      have := hmk
      rwa [← ordinalValue_neg, neg_sub] at this
    obtain ⟨F', hF', hF'u⟩ := ih _ hrem (u - aeval σ.lift G) rfl
      (hrem.trans (huo ▸ hu))
    refine ⟨G + F', (hG.degreeLT hβα).add hF', ?_⟩
    rw [map_add, map_add, hF'u, map_sub, add_sub_cancel]

end Lifts

/-! ### Uniqueness of the polynomial when evaluation is injective below `α` -/

namespace Lifts

variable (σ : Lifts wt x)

/-- When evaluation is injective in degree `β`, `v_J(F(b_𝓑)) = ω^β` for every nonzero `F`
homogeneous of degree `β`. -/
theorem ordinalValue_aeval_eq_of_injectiveAt {β : NatOrdinal} (hβ : InjectiveAt K wt x β)
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F β) (hF0 : F ≠ 0) :
    ordinalValue (aeval σ.lift F) = ω^ β :=
  σ.ordinalValue_aeval_eq_of_aeval_ne_zero hF fun h ↦ hF0 ((injectiveAt_iff β).mp hβ F hF h)

/-- When evaluation is injective in the top degree of `F ≠ 0`, `v_J(F(b_𝓑)) = ω^(deg F)`. -/
@[blueprint "prop:polynomial-evaluation-ordinal-value"
  (phase := "Translated truncations")
  (title := "Ordinal value of a polynomial evaluation")
  (statement := /--
    Let $K$ be a field. For each $i\in I$, let
    $x_i\in\mathrm P_{w_i}\subseteq\widehat{\mathrm P}$ and choose a
    representative $b_i\in K((\mathbb R^{\le0}))$. Let
    $F\in K[X_i:i\in I]$ be nonzero, and let $\deg_w(F)$ be the largest weighted
    degree of a monomial of $F$. If evaluation at $(x_i)$ is injective on the
    weighted-homogeneous polynomials of degree $\deg_w(F)$, then
    \[
      v_J(F(b_i))=\omega^{\deg_w(F)}.
    \]
  -/)
  (proof := /--
  Let $F_d$ be the weighted-homogeneous component of $F$ of top degree
  $d=\deg_w(F)$. It is nonzero, and injectivity in degree $d$ gives
  $F_d(x_i)\ne0$. By \ref{lem:homogeneous-evaluation-represents},
  $F_d(b_i)$ represents this nonzero class in $\mathrm P_d$, so
  $v_J(F_d(b_i))=\omega^d$. Every monomial of $F-F_d$ has weighted degree less
  than $d$, whence $v_J((F-F_d)(b_i))<\omega^d$. Since
  $F(b_i)=F_d(b_i)+(F-F_d)(b_i)$, the strict inequality and the ultrametric
  property give $v_J(F(b_i))=\omega^d$.
  -/)]
theorem ordinalValue_aeval_eq_wpow_weightedTotalDegree {F : MvPolynomial ι K}
    (hβ : InjectiveAt K wt x (weightedTotalDegree wt F)) (hF0 : F ≠ 0) :
    ordinalValue (aeval σ.lift F) = ω^ (weightedTotalDegree wt F) := by
  set β := weightedTotalDegree wt F
  set T := weightedHomogeneousComponent wt β F
  have hT : ordinalValue (aeval σ.lift T) = ω^ β :=
    σ.ordinalValue_aeval_eq_of_injectiveAt hβ
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := β) (φ := F))
      (weightedHomogeneousComponent_weightedTotalDegree_ne_zero hF0)
  have hR : ordinalValue (aeval σ.lift (F - T)) < ω^ β :=
    σ.ordinalValue_aeval_lt_of_degreeLT
      (degreeLT_sub_weightedHomogeneousComponent_weightedTotalDegree F)
  have hsplit : aeval σ.lift F = aeval σ.lift T + aeval σ.lift (F - T) := by
    rw [← map_add, add_sub_cancel]
  rw [hsplit, ordinalValue_add_eq_of_lt (hT ▸ hR), hT]

/-- When evaluation is injective in every degree below `α`, a polynomial of degree below `α`
whose value at the lifts lies in `J` is zero. -/
theorem eq_zero_of_degreeLT_of_toGerm_aeval_eq_zero {α : NatOrdinal}
    (hinj : ∀ β < α, InjectiveAt K wt x β) {F : MvPolynomial ι K} (hF : DegreeLT wt F α)
    (h : toGerm (aeval σ.lift F) = 0) : F = 0 := by
  by_contra hF0
  have hval := σ.ordinalValue_aeval_eq_wpow_weightedTotalDegree
    (hinj _ (hF.weightedTotalDegree_lt hF0)) hF0
  rw [toGerm_apply, Ideal.Quotient.eq_zero_iff_mem, ← ordinalValue_eq_zero_iff, hval] at h
  exact NatOrdinal.wpow_ne_zero _ h

/-- Uniqueness of the polynomial: two polynomials of degree below `α` whose values at the lifts
are congruent modulo `J` agree, when evaluation is injective in every degree below `α`. -/
theorem eq_of_degreeLT_of_toGerm_aeval_eq {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β)
    {F G : MvPolynomial ι K} (hF : DegreeLT wt F α) (hG : DegreeLT wt G α)
    (h : toGerm (aeval σ.lift F) = toGerm (aeval σ.lift G)) : F = G := by
  rw [← sub_eq_zero]
  exact σ.eq_zero_of_degreeLT_of_toGerm_aeval_eq_zero hinj (hF.sub hG)
    (by rw [map_sub, map_sub, h, sub_self])

end Lifts

/-! ### The polynomial of a series modulo `J` -/

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)

/-- The polynomial `pol(u)` of a series `u` of ordinal value below `ω^α` modulo `J`: a polynomial
`F` with every monomial of degree below `α` and `F(b_𝓑) ≡ u (mod J)`, chosen by
`exists_degreeLT_toGerm_aeval_eq`; `0` when `v_J(u) ≥ ω^α`. -/
def pol (α : NatOrdinal) (u : Series K) : MvPolynomial ι K := by
  classical
  exact if hu : ordinalValue u < ω^ α then
    Classical.choose (σ.exists_degreeLT_toGerm_aeval_eq hx α u hu) else 0

theorem pol_degreeLT (α : NatOrdinal) (u : Series K) : DegreeLT wt (σ.pol hx α u) α := by
  classical
  unfold pol
  split_ifs with hu
  · exact (Classical.choose_spec (σ.exists_degreeLT_toGerm_aeval_eq hx α u hu)).1
  · exact degreeLT_zero α

theorem toGerm_aeval_pol {α : NatOrdinal} {u : Series K} (hu : ordinalValue u < ω^ α) :
    toGerm (aeval σ.lift (σ.pol hx α u)) = toGerm u := by
  classical
  unfold pol
  rw [dite_eq_left hu]
  exact (Classical.choose_spec (σ.exists_degreeLT_toGerm_aeval_eq hx α u hu)).2

/-- When evaluation is injective below `α`, the polynomial of `u` modulo `J` is the unique
polynomial of degree below `α` whose value at the lifts is congruent to `u` modulo `J`. -/
theorem pol_eq_of_toGerm_aeval_eq {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β)
    {u : Series K} (hu : ordinalValue u < ω^ α) {F : MvPolynomial ι K} (hF : DegreeLT wt F α)
    (h : toGerm (aeval σ.lift F) = toGerm u) : σ.pol hx α u = F :=
  σ.eq_of_degreeLT_of_toGerm_aeval_eq hinj (σ.pol_degreeLT hx α u) hF
    (by rw [σ.toGerm_aeval_pol hx hu, h])

/-- The polynomial of a value `F(b_𝓑)`, `F` of degree below `α`, is `F`. -/
theorem pol_aeval {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β)
    {F : MvPolynomial ι K} (hF : DegreeLT wt F α) :
    σ.pol hx α (aeval σ.lift F) = F :=
  σ.pol_eq_of_toGerm_aeval_eq hx hinj (σ.ordinalValue_aeval_lt_of_degreeLT hF) hF rfl

/-- `pol` is additive. -/
theorem pol_add {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β) {u u' : Series K}
    (hu : ordinalValue u < ω^ α) (hu' : ordinalValue u' < ω^ α) :
    σ.pol hx α (u + u') = σ.pol hx α u + σ.pol hx α u' :=
  σ.pol_eq_of_toGerm_aeval_eq hx hinj
    ((ordinalValue_add_le_max u u').trans_lt (max_lt hu hu'))
    ((σ.pol_degreeLT hx α u).add (σ.pol_degreeLT hx α u'))
    (by rw [map_add, map_add, σ.toGerm_aeval_pol hx hu, σ.toGerm_aeval_pol hx hu', map_add])

/-- The polynomial of a series in `J` is zero. -/
theorem pol_eq_zero_of_mem {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β)
    {u : Series K} (hu : u ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    σ.pol hx α u = 0 :=
  σ.pol_eq_of_toGerm_aeval_eq hx hinj
    (by rw [ordinalValue_eq_zero_iff.mpr hu]; exact NatOrdinal.wpow_pos α) (degreeLT_zero α)
    (by rw [map_zero, map_zero, toGerm_apply, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact hu)

/-- `v_J(u) = ω^(deg pol(u))` for `u ∉ J` of ordinal value below `ω^α`, when evaluation is
injective below `α`. -/
@[blueprint "prop:ordinal-value-of-polynomial-representative"
  (phase := "Translated truncations")
  (title := "Ordinal value of a polynomial representative")
  (statement := /--
    Let $K$ be a field, let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$ with
    $x_i\in\mathrm P_{w_i}$, and choose representatives $b_i$. Fix
    $\alpha<\omega_1$ and assume that evaluation at $(x_i)$ is injective on
    weighted-homogeneous polynomials of every degree less than $\alpha$.

    For $u\in K((\mathbb R^{\le0}))$ with $v_J(u)<\omega^\alpha$, let $P_u$ be
    the unique polynomial whose monomials have weight less than $\alpha$ and
    which satisfies $P_u(b_i)\equiv u\pmod J$. If $u\notin J$, then
    \[
      v_J(u)=\omega^{\deg_w(P_u)},
    \]
    where $\deg_w(P_u)$ is the largest weighted degree of a monomial of $P_u$.
  -/)
  (proof := /--
  Existence and congruence of $P_u$ come from
  \ref{prop:polynomial-representative-exists}. The polynomial is nonzero,
  since otherwise its congruence would put $u$ in $J$. Its largest weighted
  degree is less than $\alpha$, so the injectivity hypothesis applies there.
  By \ref{prop:polynomial-evaluation-ordinal-value},
  \[
    v_J(P_u(b_i))=\omega^{\deg_w(P_u)}.
  \]
  Congruence modulo $J$ preserves every nonzero ordinal value, giving the
  asserted equality for $u$.
  -/)]
theorem ordinalValue_eq_wpow_weightedTotalDegree_pol {α : NatOrdinal}
    (hinj : ∀ β < α, InjectiveAt K wt x β) {u : Series K} (hu : ordinalValue u < ω^ α)
    (hu0 : u ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    ordinalValue u = ω^ (weightedTotalDegree wt (σ.pol hx α u)) := by
  have hp0 : σ.pol hx α u ≠ 0 := by
    intro h
    have := σ.toGerm_aeval_pol hx hu
    rw [h, map_zero, map_zero, toGerm_apply, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hu0 this
  rw [← ordinalValue_eq_of_sub_mem_negativeMonomialIdeal
    (toGerm_eq_toGerm_iff.mp (σ.toGerm_aeval_pol hx hu))]
  exact σ.ordinalValue_aeval_eq_wpow_weightedTotalDegree
    (hinj _ ((σ.pol_degreeLT hx α u).weightedTotalDegree_lt hp0)) hp0

end Lifts

end Berarducci
