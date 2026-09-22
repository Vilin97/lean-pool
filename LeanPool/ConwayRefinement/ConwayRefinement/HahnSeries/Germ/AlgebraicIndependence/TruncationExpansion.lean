/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TruncationPolynomial
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.TermDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.ComponentsSpan

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# The translated-truncation Leibniz expansion in representing polynomials

The finite closed-support convolution formula expands a proper translated truncation of a
monomial in series representatives satisfying the assigned degree and proper-truncation bounds.
Its two boundary terms
give the usual first-order Leibniz sum; every interior term contains at least two proper
truncations. This file records the resulting polynomial identity and tracks the weight of every
remainder monomial by `TermDegree`.
-/

universe u v w

open scoped NatOrdinal Topology

open MvPolynomial HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

variable {ι : Type w} {wt : ι → NatOrdinal.{u}}
  {xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded}

namespace LiftFamily

variable (σ : LiftFamily wt xg)
variable (hx : OrdinalGraded.IsMinimalSystem
  (DirectSum.rangeLof K (cantorBendixsonDegreeValuation (G := G) (R := K)).Component) wt xg)

/-- Every monomial of a polynomial has weight strictly below the given ordinal. -/
def DegreeLT (wt : ι → NatOrdinal.{u}) (P : MvPolynomial ι K) (α : NatOrdinal.{u}) : Prop :=
  ∀ d ∈ P.support, Finsupp.weight wt d < α

omit [CharZero K] in
theorem degreeLT_iff {P : MvPolynomial ι K} {α : NatOrdinal.{u}} :
    DegreeLT wt P α ↔ ∀ d ∈ P.support, Finsupp.weight wt d < α :=
  Iff.rfl

variable (wt) in
/-- A polynomial remainder for a monomial: every monomial has the degree of an expansion term
with at least two truncated factors. -/
def IsRemainder (d : ι →₀ ℕ) (E : MvPolynomial ι K) : Prop :=
  ∀ d' ∈ E.support, ∃ k, 2 ≤ k ∧ TermDegree wt d k (Finsupp.weight wt d')

omit [CharZero K] in
theorem isRemainder_zero (d : ι →₀ ℕ) :
    IsRemainder wt d (0 : MvPolynomial ι K) := by
  intro d' hd'
  rw [MvPolynomial.support_zero] at hd'
  exact absurd hd' (Finset.notMem_empty d')

omit [CharZero K] in
theorem IsRemainder.add {d : ι →₀ ℕ} {E E' : MvPolynomial ι K}
    (hE : IsRemainder wt d E) (hE' : IsRemainder wt d E') :
    IsRemainder wt d (E + E') := by
  classical
  intro d' hd'
  rcases Finset.mem_union.mp (support_add hd') with h | h
  · exact hE d' h
  · exact hE' d' h

omit [CharZero K] in
theorem IsRemainder.sum {κ : Type*} {d : ι →₀ ℕ} (s : Finset κ)
    (E : κ → MvPolynomial ι K) (hE : ∀ j ∈ s, IsRemainder wt d (E j)) :
    IsRemainder wt d (∑ j ∈ s, E j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact isRemainder_zero d
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hE a (Finset.mem_insert_self a s)).add
        (ih fun j hj ↦ hE j (Finset.mem_insert_of_mem hj))

/-- Multiplication by an untruncated variable preserves the number of truncated factors. -/
theorem IsRemainder.mul_X {d : ι →₀ ℕ} {E : MvPolynomial ι K}
    (hE : IsRemainder wt d E) (i : ι) :
    IsRemainder wt (d + Finsupp.single i 1) (E * X i) := by
  classical
  intro d' hd'
  obtain ⟨d₁, hd₁, d₂, hd₂, hw⟩ := exists_add_eq_weight_of_mem_support_mul (wt := wt) hd'
  obtain ⟨k, hk, hT⟩ := hE d₁ hd₁
  rw [X, support_monomial, ite_eq_right one_ne_zero, Finset.mem_singleton] at hd₂
  subst d₂
  rw [Finsupp.weight_single, one_smul] at hw
  exact ⟨k, hk, hw ▸ TermDegree.untrunc i hT⟩

omit [CharZero K] in
/-- Multiplying an expansion with a truncated factor by another proper truncation produces a
remainder with at least two truncated factors. -/
theorem isRemainder_mul_of_degreeLT {d : ι →₀ ℕ} {P Q : MvPolynomial ι K}
    (hP : ∀ d' ∈ P.support, ∃ k, 1 ≤ k ∧ TermDegree wt d k (Finsupp.weight wt d'))
    {i : ι} (hQ : DegreeLT wt Q (wt i)) :
    IsRemainder wt (d + Finsupp.single i 1) (P * Q) := by
  classical
  intro d' hd'
  obtain ⟨d₁, hd₁, d₂, hd₂, hw⟩ := exists_add_eq_weight_of_mem_support_mul (wt := wt) hd'
  obtain ⟨k, hk, hT⟩ := hP d₁ hd₁
  exact ⟨k + 1, by omega,
    hw ▸ TermDegree.trunc i ((degreeLT_iff).mp hQ d₂ hd₂) hT⟩

omit [CharZero K] in
/-- The first-order expansion terms of a monomial have exactly one designated truncated factor. -/
theorem forall_termDegree_sum_mul_pderiv_monomial (d : ι →₀ ℕ)
    (T : ι → MvPolynomial ι K) (hT : ∀ j ∈ d.support, DegreeLT wt (T j) (wt j)) :
    ∀ d' ∈ (∑ j ∈ d.support, T j * pderiv j (monomial d (1 : K))).support,
      ∃ k, 1 ≤ k ∧ TermDegree wt d k (Finsupp.weight wt d') := by
  classical
  intro d' hd'
  obtain ⟨j, hj, hd'j⟩ := Finset.mem_biUnion.mp (support_sum hd')
  obtain ⟨d₁, hd₁, d₂, hd₂, hw⟩ := exists_add_eq_weight_of_mem_support_mul (wt := wt) hd'j
  rw [pderiv_monomial, support_monomial] at hd₂
  split_ifs at hd₂ with hzero
  · exact absurd hd₂ (Finset.notMem_empty d₂)
  · rw [Finset.mem_singleton] at hd₂
    subst d₂
    have hdj : d - Finsupp.single j 1 + Finsupp.single j 1 = d :=
      Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hj)
    refine ⟨1, le_rfl, ?_⟩
    have hterm := TermDegree.trunc_left j ((degreeLT_iff).mp (hT j hj) d₁ hd₁)
      (termDegree_weight wt (d - Finsupp.single j 1))
    rw [add_comm (Finsupp.single j 1), hdj] at hterm
    rwa [← hw]

omit [CharZero K] in
/-- Splitting one variable from a monomial. -/
theorem monomial_add_single_one (d : ι →₀ ℕ) (i : ι) :
    monomial (d + Finsupp.single i 1) (1 : K) = monomial d 1 * X i := by
  rw [X, MvPolynomial.monomial_mul_monomial, mul_one]

omit [CharZero K] in
/-- The first-order Leibniz sum after splitting one variable from a monomial. -/
theorem sum_mul_pderiv_monomial_add_single (d : ι →₀ ℕ) (i : ι)
    (T : ι → MvPolynomial ι K) :
    ∑ j ∈ (d + Finsupp.single i 1).support,
        T j * pderiv j (monomial (d + Finsupp.single i 1) 1) =
      (∑ j ∈ d.support, T j * pderiv j (monomial d (1 : K))) * X i +
        T i * monomial d 1 := by
  classical
  have hmem : i ∈ (d + Finsupp.single i 1).support := by
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  have hsub : d.support ⊆ (d + Finsupp.single i 1).support := fun j hj ↦ by
    rw [Finsupp.mem_support_iff] at hj ⊢
    rw [Finsupp.add_apply]
    omega
  simp only [monomial_add_single_one, pderiv_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul, ← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun j _ ↦ by ring
    · intro j _ hj
      rw [pderiv_monomial, Finsupp.notMem_support_iff.mp hj, Nat.cast_zero, mul_zero,
        monomial_zero, zero_mul, mul_zero]
  · rw [Finset.sum_eq_single i]
    · rw [pderiv_X_self, mul_one]
    · intro j _ hji
      rw [pderiv_X_of_ne (Ne.symm hji), mul_zero, mul_zero]
    · intro h
      exact absurd hmem h

omit [CharZero K] in
/-- Split a finite sum at two distinct members. -/
private theorem sum_eq_add_add_sum_erase {κ : Type*} [DecidableEq κ]
    {S : Finset κ} {a b : κ} (ha : a ∈ S) (hb : b ∈ S) (hne : b ≠ a)
    (f : κ → MvPolynomial ι K) :
    ∑ q ∈ S, f q = f a + f b + ∑ q ∈ (S.erase a).erase b, f q := by
  rw [add_assoc, Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, hb⟩),
    Finset.add_sum_erase _ _ ha]

include hx in
/-- The translated-truncation Leibniz expansion for a monomial. At every negative cutoff, the
representing polynomial of a translated truncation is its first-order Leibniz sum plus a
remainder whose monomials contain at least two truncated factors. -/
theorem exists_pol_translatedTruncLE_aeval_monomial
    (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (d : ι →₀ ℕ) (hd : Finsupp.weight wt d ≤ α)
    (hvars : ∀ i ∈ d.support, wt i < α) {γ : G} (hγ : γ < 0) :
    ∃ E : MvPolynomial ι K, IsRemainder wt d E ∧
      σ.pol hx α (translatedTruncLE γ (aeval σ.lift (monomial d (1 : K)))) =
        ∑ j ∈ d.support, σ.pol hx α (translatedTruncLE γ (σ.lift j)) *
          pderiv j (monomial d 1) + E := by
  classical
  suffices h : ∀ n : ℕ, ∀ d : ι →₀ ℕ, Finsupp.degree d = n →
      Finsupp.weight wt d ≤ α → (∀ i ∈ d.support, wt i < α) →
      ∀ {γ : G}, γ < 0 →
        ∃ E : MvPolynomial ι K, IsRemainder wt d E ∧
          σ.pol hx α (translatedTruncLE γ (aeval σ.lift (monomial d (1 : K)))) =
            ∑ j ∈ d.support, σ.pol hx α (translatedTruncLE γ (σ.lift j)) *
              pderiv j (monomial d 1) + E by
    exact h _ d rfl hd hvars hγ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro d hdn hd hvars γ hγ
    rcases eq_or_ne d 0 with rfl | hd0
    · refine ⟨0, isRemainder_zero 0, ?_⟩
      have htr : translatedTruncLE γ (1 : Nonpositive G K) = 0 :=
        FreeOfVariable.translatedTruncLE_one hγ
      have hone : aeval σ.lift (monomial (0 : ι →₀ ℕ) (1 : K)) =
          (1 : Nonpositive G K) := by simp
      rw [hone, htr, σ.pol_eq_zero_of_degree_eq_bot hx (by rw [(ν).map_zero]),
        Finsupp.support_zero, Finset.sum_empty, add_zero]
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
      set d' := d - Finsupp.single i 1 with hd'def
      have hdd' : d' + Finsupp.single i 1 = d :=
        Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)
      have hwd : Finsupp.weight wt d' + wt i = Finsupp.weight wt d := by
        rw [← hdd', map_add, Finsupp.weight_single, one_smul]
      have hdeg : Finsupp.degree d' < n := by
        rw [← hdn, ← hdd', map_add, Finsupp.degree_single]
        omega
      have hwi : wt i < α := hvars i hi
      have hwd'α : Finsupp.weight wt d' < α := by
        have hlt : Finsupp.weight wt d' < Finsupp.weight wt d' + wt i :=
          lt_add_of_pos_right _ (pos_iff_ne_zero.mpr (hx.ne_zero i))
        exact hlt.trans_le (hwd ▸ hd)
      have hsub : d'.support ⊆ d.support := by
        rw [hd'def]
        exact Finsupp.support_tsub
      have ih' : ∀ {y : G}, y < 0 →
          ∃ E : MvPolynomial ι K, IsRemainder wt d' E ∧
            σ.pol hx α (translatedTruncLE y (aeval σ.lift (monomial d' (1 : K)))) =
              ∑ j ∈ d'.support, σ.pol hx α (translatedTruncLE y (σ.lift j)) *
                pderiv j (monomial d' 1) + E :=
        ih _ hdeg d' rfl hwd'α.le (fun j hj ↦ hvars j (hsub hj))
      set a : Nonpositive G K := aeval σ.lift (monomial d' (1 : K)) with hadef
      have ha : HasLowerTruncationDegree a (Finsupp.weight wt d') := by
        rw [hadef]
        exact σ.hasLowerTruncationDegree_aeval hσ
          (isWeightedHomogeneous_monomial wt d' 1 rfl)
      have hb : HasLowerTruncationDegree (σ.lift i) (wt i) :=
        (hasLowerTruncationDegrees_iff σ).mp hσ i
      have hconv := σ.pol_translatedTruncLE_mul_boundary hx hinj ha hb hwd'α hwi
        (hwd ▸ hd) hγ
      set S := insert (0, γ) (insert (γ, 0)
        ((a : HahnSeries G K).closedSupportAddFiber (σ.lift i : HahnSeries G K) γ)) with hS
      set f : G × G → MvPolynomial ι K := fun q ↦
        σ.pol hx α (translatedTruncLE q.1 a) *
          σ.pol hx α (translatedTruncLE q.2 (σ.lift i)) with hf
      have h0S : (0, γ) ∈ S := Finset.mem_insert_self _ _
      have hγS : (γ, 0) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hne : (γ, 0) ≠ (0, γ) := fun h ↦ hγ.ne (congrArg Prod.fst h)
      have hsplit : ∑ q ∈ S, f q = f (0, γ) + f (γ, 0) +
          ∑ q ∈ (S.erase (0, γ)).erase (γ, 0), f q :=
        sum_eq_add_add_sum_erase h0S hγS hne f
      have hf0 : f (0, γ) = monomial d' 1 *
          σ.pol hx α (translatedTruncLE γ (σ.lift i)) := by
        change σ.pol hx α (translatedTruncLE 0 a) *
          σ.pol hx α (translatedTruncLE γ (σ.lift i)) = _
        rw [translatedTruncLE_zero, hadef,
          σ.pol_aeval hx hinj (fun e he ↦ by
            rw [support_monomial, ite_eq_right one_ne_zero, Finset.mem_singleton] at he
            rwa [he])]
      have hfγ : f (γ, 0) =
          σ.pol hx α (translatedTruncLE γ a) * X i := by
        change σ.pol hx α (translatedTruncLE γ a) *
          σ.pol hx α (translatedTruncLE 0 (σ.lift i)) = _
        rw [translatedTruncLE_zero, σ.pol_lift hx hinj hwi]
      have hinterior : ∀ q ∈ (S.erase (0, γ)).erase (γ, 0),
          q.1 < 0 ∧ q.2 < 0 := by
        intro q hq
        have hqneγ : q ≠ (γ, 0) := (Finset.mem_erase.mp hq).1
        have hqne0 : q ≠ (0, γ) :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
        have hqmemS : q ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).2
        have hqmem : q ∈ (a : HahnSeries G K).closedSupportAddFiber
            (σ.lift i : HahnSeries G K) γ := by
          rw [hS] at hqmemS
          rcases Finset.mem_insert.mp hqmemS with hqeq | hqmemS
          · exact (hqne0 hqeq).elim
          rcases Finset.mem_insert.mp hqmemS with hqeq | hqmemS
          · exact (hqneγ hqeq).elim
          · exact hqmemS
        obtain ⟨hq1mem, hq2mem, hsum⟩ :=
          ((a : HahnSeries G K).mem_closedSupportAddFiber
            (σ.lift i : HahnSeries G K) γ q).mp hqmem
        have hq1le : q.1 ≤ 0 := closure_minimal a.property isClosed_Iic
          ((mem_closedSupport _ _).mp hq1mem)
        have hq2le : q.2 ≤ 0 := closure_minimal (σ.lift i).property isClosed_Iic
          ((mem_closedSupport _ _).mp hq2mem)
        have hq1ne : q.1 ≠ 0 := fun hq10 ↦ hqne0 (Prod.ext hq10 (by
          simpa [hq10] using hsum))
        have hq2ne : q.2 ≠ 0 := fun hq20 ↦ hqneγ (Prod.ext (by
          simpa [hq20] using hsum) hq20)
        exact ⟨lt_of_le_of_ne hq1le hq1ne, lt_of_le_of_ne hq2le hq2ne⟩
      choose Eq hEqrem hEq using fun q (hq : q ∈ (S.erase (0, γ)).erase (γ, 0)) ↦
        ih' (hinterior q hq).1
      set R : MvPolynomial ι K := ∑ q ∈ (S.erase (0, γ)).erase (γ, 0),
        f q with hRdef
      have hR : IsRemainder wt d R := by
        rw [← hdd', hRdef]
        refine IsRemainder.sum _ _ fun q hq ↦ ?_
        change IsRemainder wt (d' + Finsupp.single i 1)
          (σ.pol hx α (translatedTruncLE q.1 a) *
            σ.pol hx α (translatedTruncLE q.2 (σ.lift i)))
        rw [hEq q hq]
        have hleft : IsRemainder (K := K) wt (d' + Finsupp.single i 1)
            ((∑ j ∈ d'.support, σ.pol hx α (translatedTruncLE q.1 (σ.lift j)) *
              pderiv j (monomial d' 1)) *
                σ.pol hx α (translatedTruncLE q.2 (σ.lift i))) := by
          exact isRemainder_mul_of_degreeLT (wt := wt)
            (forall_termDegree_sum_mul_pderiv_monomial (wt := wt) d' _ fun j hj ↦
              fun e he ↦ σ.pol_weight_lt_of_degree_lt hx (hvars j (hsub hj)).le
                (((hasLowerTruncationDegrees_iff σ).mp hσ j).degree_translatedTruncLE_lt
                  (hinterior q hq).1) e he)
            (fun e he ↦ σ.pol_weight_lt_of_degree_lt hx hwi.le
              (hb.degree_translatedTruncLE_lt (hinterior q hq).2) e he)
        have hright : IsRemainder (K := K) wt (d' + Finsupp.single i 1)
            (Eq q hq * σ.pol hx α (translatedTruncLE q.2 (σ.lift i))) := by
          exact isRemainder_mul_of_degreeLT (wt := wt)
            (fun e he ↦ by
              obtain ⟨k, hk, hterm⟩ := hEqrem q hq e he
              exact ⟨k, by omega, hterm⟩)
            (fun e he ↦ σ.pol_weight_lt_of_degree_lt hx hwi.le
              (hb.degree_translatedTruncLE_lt (hinterior q hq).2) e he)
        rw [add_mul]
        exact hleft.add hright
      obtain ⟨E', hE', hEq'⟩ := ih' hγ
      refine ⟨E' * X i + R, (hdd' ▸ hE'.mul_X i).add hR, ?_⟩
      have hprod : a * σ.lift i = aeval σ.lift (monomial d (1 : K)) := by
        rw [hadef, ← hdd', monomial_add_single_one, map_mul, aeval_X]
      rw [← hprod, hconv, hsplit, hf0, hfγ, hEq', ← hdd',
        sum_mul_pderiv_monomial_add_single, hRdef]
      ring

include hx in
/-- The translated-truncation Leibniz expansion for a polynomial. At every negative cutoff, the
representing polynomial of a translated truncation is its first-order Leibniz sum plus a
remainder coming from at least two truncated factors of a monomial of the original polynomial. -/
theorem exists_pol_translatedTruncLE_aeval
    (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (H : MvPolynomial ι K) (hH : ∀ d ∈ H.support, Finsupp.weight wt d ≤ α)
    (hvars : ∀ i ∈ H.vars, wt i < α) {γ : G} (hγ : γ < 0) :
    ∃ E : MvPolynomial ι K,
      (∀ d' ∈ E.support, ∃ d ∈ H.support, ∃ k, 2 ≤ k ∧
        TermDegree wt d k (Finsupp.weight wt d')) ∧
      σ.pol hx α (translatedTruncLE γ (aeval σ.lift H)) =
        ∑ j ∈ H.vars, σ.pol hx α (translatedTruncLE γ (σ.lift j)) * pderiv j H + E := by
  classical
  have hmono : ∀ d ∈ H.support,
      ∃ E : MvPolynomial ι K, IsRemainder wt d E ∧
        σ.pol hx α (translatedTruncLE γ (aeval σ.lift (monomial d (1 : K)))) =
          ∑ j ∈ d.support, σ.pol hx α (translatedTruncLE γ (σ.lift j)) *
            pderiv j (monomial d 1) + E := fun d hd ↦
    σ.exists_pol_translatedTruncLE_aeval_monomial hx hσ hinj d (hH d hd)
      (fun i hi ↦ hvars i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)) hγ
  choose E hE hEq using hmono
  have hmonomialBounds : ∀ d ∈ H.support,
      HasLowerTruncationDegree (aeval σ.lift (monomial d (1 : K))) (Finsupp.weight wt d) :=
    fun d _ ↦ σ.hasLowerTruncationDegree_aeval hσ (isWeightedHomogeneous_monomial wt d 1 rfl)
  have hdegree : ∀ d ∈ H.support,
      ν (translatedTruncLE γ (aeval σ.lift (monomial d (1 : K)))) <
        (α : WithBot NatOrdinal) := fun d hd ↦
    (hmonomialBounds d hd).degree_translatedTruncLE_lt hγ |>.trans_le
      (WithBot.coe_le_coe.mpr (hH d hd))
  refine ⟨∑ d ∈ H.support.attach, MvPolynomial.C (H.coeff d.1) * E d.1 d.2,
    ?_, ?_⟩
  · intro d' hd'
    obtain ⟨d, _, hd'd⟩ := Finset.mem_biUnion.mp (support_sum hd')
    have hd'E : d' ∈ (E d.1 d.2).support := by
      rw [C_mul'] at hd'd
      exact support_smul hd'd
    obtain ⟨k, hk, hterm⟩ := hE d.1 d.2 d' hd'E
    exact ⟨d.1, d.2, k, hk, hterm⟩
  have hmonomial : ∀ d, monomial d (H.coeff d) =
      MvPolynomial.C (H.coeff d) * monomial d (1 : K) := fun d ↦ by
    rw [C_mul_monomial, mul_one]
  have hleft : σ.pol hx α (translatedTruncLE γ (aeval σ.lift H)) =
      ∑ d ∈ H.support.attach,
        MvPolynomial.C (H.coeff d.1) *
          σ.pol hx α (translatedTruncLE γ (aeval σ.lift (monomial d.1 (1 : K)))) := by
    conv_lhs => rw [H.as_sum]
    rw [map_sum, map_sum, ← Finset.sum_attach H.support]
    have hterm : ∀ d ∈ H.support.attach,
        translatedTruncLE γ (aeval σ.lift
          (monomial d.1 (H.coeff d.1))) =
          H.coeff d.1 • translatedTruncLE γ
            (aeval σ.lift (monomial d.1 (1 : K))) := by
      intro d _
      rw [hmonomial, map_mul, aeval_C, ← Algebra.smul_def, translatedTruncLE_smul]
    rw [Finset.sum_congr rfl hterm,
      σ.pol_sum hx hinj _ _ (fun d hd ↦ by
        exact (degree_smul_le _ _).trans_lt (hdegree d.1 d.2))]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [σ.pol_smul hx hinj _ (hdegree d.1 d.2), C_mul']
  rw [hleft]
  have hsub : ∀ d ∈ H.support, d.support ⊆ H.vars := fun d hd j hj ↦
    (mem_vars_iff_mem_support j).mpr ⟨d, hd, hj⟩
  have hsupp : ∀ d : ι →₀ ℕ, ∀ j, j ∉ d.support →
      pderiv j (monomial d (1 : K)) = 0 := fun d j hj ↦ by
    rw [pderiv_monomial, Finsupp.notMem_support_iff.mp hj, Nat.cast_zero, mul_zero,
      monomial_zero]
  have hpd : ∀ j, pderiv j H =
      ∑ d ∈ H.support.attach, MvPolynomial.C (H.coeff d.1) *
        pderiv j (monomial d.1 1) := fun j ↦ by
    conv_lhs => rw [H.as_sum, map_sum, ← Finset.sum_attach H.support]
    exact Finset.sum_congr rfl fun d _ ↦ by rw [hmonomial, pderiv_C_mul]
  rw [Finset.sum_congr rfl (fun d _ ↦ congrArg
      (MvPolynomial.C (H.coeff d.1) * ·) (hEq d.1 d.2))]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [hpd, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have heq : ∑ j ∈ d.1.support,
      σ.pol hx α (translatedTruncLE γ (σ.lift j)) * pderiv j (monomial d.1 1) =
      ∑ j ∈ H.vars,
        σ.pol hx α (translatedTruncLE γ (σ.lift j)) * pderiv j (monomial d.1 1) :=
    Finset.sum_subset (hsub d.1 d.2) fun j _ hj ↦ by
      rw [hsupp d.1 j hj, mul_zero]
  rw [← Finset.mul_sum]
  conv_lhs => rw [heq]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by
    exact mul_left_comm
      (MvPolynomial.C (H.coeff d.1))
      (σ.pol hx α (translatedTruncLE γ (σ.lift j))) _

include hx in
/-- The differentiated translated-truncation Leibniz expansion. Differentiating the expansion of `F`
and comparing it with the expansion of `∂F/∂X_v` expresses the latter using the partials of `F`
and two `TermDegree`-controlled remainders. -/
theorem exists_pol_translatedTruncLE_aeval_pderiv
    (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (F : MvPolynomial ι K) (hF : ∀ d ∈ F.support, Finsupp.weight wt d ≤ α)
    (hvars : ∀ i ∈ F.vars, wt i < α) (v : ι) {γ : G} (hγ : γ < 0) :
    ∃ E E' : MvPolynomial ι K,
      (∀ d' ∈ E.support, ∃ d ∈ F.support, ∃ k, 2 ≤ k ∧
        TermDegree wt d k (Finsupp.weight wt d')) ∧
      (∀ d' ∈ E'.support, ∃ d ∈ (pderiv v F).support, ∃ k, 2 ≤ k ∧
        TermDegree wt d k (Finsupp.weight wt d')) ∧
      σ.pol hx α (translatedTruncLE γ (aeval σ.lift (pderiv v F))) =
        pderiv v (σ.pol hx α (translatedTruncLE γ (aeval σ.lift F))) -
          ∑ j ∈ F.vars,
            pderiv v (σ.pol hx α (translatedTruncLE γ (σ.lift j))) * pderiv j F -
          pderiv v E + E' := by
  classical
  have hΘ : ∀ d ∈ (pderiv v F).support, Finsupp.weight wt d ≤ α := fun d' hd' ↦ by
    obtain ⟨d, hd, hw⟩ := exists_add_eq_weight_of_mem_support_pderiv wt hd'
    exact (NatOrdinal.le_add_right.trans hw.le).trans (hF d hd)
  have hvarsΘ : ∀ i ∈ (pderiv v F).vars, wt i < α :=
    fun i hi ↦ hvars i (vars_pderiv_subset v F hi)
  obtain ⟨E, hE, hexpF⟩ :=
    σ.exists_pol_translatedTruncLE_aeval hx hσ hinj F hF hvars hγ
  obtain ⟨E', hE', hexpΘ⟩ :=
    σ.exists_pol_translatedTruncLE_aeval hx hσ hinj (pderiv v F) hΘ hvarsΘ hγ
  refine ⟨E, E', hE, hE', ?_⟩
  set T : ι → MvPolynomial ι K := fun j ↦
    σ.pol hx α (translatedTruncLE γ (σ.lift j)) with hTdef
  have hdF : pderiv v (σ.pol hx α (translatedTruncLE γ (aeval σ.lift F))) =
      ∑ j ∈ F.vars, pderiv v (T j) * pderiv j F +
        ∑ j ∈ F.vars, T j * pderiv j (pderiv v F) + pderiv v E := by
    rw [hexpF, map_add, map_sum, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [pderiv_mul, pderiv_pderiv_comm]
  have hexpΘ' : σ.pol hx α (translatedTruncLE γ (aeval σ.lift (pderiv v F))) =
      ∑ j ∈ F.vars, T j * pderiv j (pderiv v F) + E' := by
    rw [hexpΘ]
    congr 1
    exact Finset.sum_subset (vars_pderiv_subset v F) fun j _ hj ↦ by
      rw [pderiv_eq_zero_of_notMem_vars hj, mul_zero]
  rw [hexpΘ', hdF]
  ring

omit [CharZero K] in
/-- A monomial of a partial derivative regains a monomial of the original polynomial after
restoring the differentiated variable. -/
theorem add_single_mem_support_of_mem_support_pderiv {i : ι}
    {P : MvPolynomial ι K} {d' : ι →₀ ℕ} (hd' : d' ∈ (pderiv i P).support) :
    d' + Finsupp.single i 1 ∈ P.support := by
  obtain ⟨d, hd, hdi, rfl⟩ := exists_mem_support_of_mem_support_pderiv hd'
  rwa [tsub_add_cancel_of_le
    (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hdi))]

omit [CharZero K] in
/-- A polynomial whose monomials have degree below `g ≤ wt v` has zero derivative at `v`. -/
theorem pderiv_eq_zero_of_degreeLT_le {P : MvPolynomial ι K} {g : NatOrdinal.{u}}
    (hP : DegreeLT wt P g) {v : ι} (hg : g ≤ wt v) : pderiv v P = 0 := by
  by_contra h
  obtain ⟨d', hd'⟩ := support_nonempty.mpr h
  have hmem := add_single_mem_support_of_mem_support_pderiv hd'
  have hlt := hP _ hmem
  rw [map_add, Finsupp.weight_single, one_smul] at hlt
  have hle : wt v ≤ Finsupp.weight wt d' + wt v := by
    rw [add_comm]
    exact NatOrdinal.le_add_right
  exact absurd (hg.trans hle) (not_le.mpr hlt)

include hx in
/-- **Local ideal membership for a truncated partial derivative.** If the represented
translated truncation of `F` and all two-truncation remainder terms lie below `α''`, then above
any `τ` with `α'' ≤ τ + wt v'`, the truncated partial derivative lies in the ideal generated by
partials at variables of strictly larger weight. -/
@[blueprint "lem:local-jacobian-ideal-membership"
  (phase := "Algebraic independence in graded rings")
  (title := "Local Jacobian ideal membership for translated partial derivatives")
  (statement := /--
    Let $F$ be weighted homogeneous of degree $\alpha$, evaluated at series
    $b_i$ representing a minimal homogeneous generating system of weights
    $w_i$. Assume
    \[
      \deg(b_i)\le w_i,
      \qquad \deg(b_i^{\vert y})<w_i\quad\text{for every }y<0.
    \]
    Assume evaluation is injective below $\alpha$, every variable of $F$ has
    weight below $\alpha$, and at a negative cutoff $\gamma$ the translated
    truncation of $F(b)$ has degree less than $\alpha'$. Suppose also that every term in
    the translated-truncation expansion containing at least two proper
    truncations has degree less than $\alpha''$, where
    $\alpha'\le\alpha''$ and $\alpha'\le\alpha$.

    If $\alpha''\le\tau\oplus w_{B'}$, then the terms of weighted degree at
    least $\tau$ in a polynomial representing
    $(\partial_{B'}F)(b)^{\vert\gamma}$ belong to the ideal generated by
    $\partial_BF$ for the variables satisfying $w_{B'}<w_B$.
  -/)
  (proof := /--
    By \ref{thm:cantor-bendixson-value-multiplicative}, the
    Cantor--Bendixson degree defines the associated graded ring and its
    homogeneous components.  By \ref{lem:generate}, translated truncations
    have homogeneous polynomial
    representatives. Differentiate the translated-truncation Leibniz
    expansion. The derivative of the represented value of $F$, and both
    remainders containing at least two proper truncations, have no terms of
    degree at least $\tau$. By \ref{lem:partial-derivative-vanishes}, every
    term indexed by
    $w_B\le w_{B'}$ vanishes. The remaining first-order terms are multiples of
    $\partial_BF$ with $w_{B'}<w_B$.
  -/)]
theorem componentsGE_pol_translatedTruncLE_aeval_pderiv_mem
    (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F α)
    (hvars : ∀ i ∈ F.vars, wt i < α) {α' α'' : NatOrdinal.{u}}
    (hα' : α' ≤ α'') (hα'α : α' ≤ α)
    {γ : G} (hγ : γ < 0)
    (hG : ν (translatedTruncLE γ (aeval σ.lift F)) < (α' : WithBot NatOrdinal))
    (hwin : ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k →
      TermDegree wt d k ρ → ρ < α'')
    (v' : ι) {τ : NatOrdinal.{u}} (hτ : α'' ≤ τ + wt v') :
    componentsGE wt τ
        (σ.pol hx α (translatedTruncLE γ (aeval σ.lift (pderiv v' F)))) ∈
      Ideal.span (Set.range fun j : {j : ι // j ∈ F.vars ∧ wt v' < wt j} ↦
        pderiv j.1 F) := by
  classical
  have hFdeg : ∀ d ∈ F.support, Finsupp.weight wt d ≤ α :=
    fun d hd ↦ (hF (mem_support_iff.mp hd)).le
  obtain ⟨E, E', hE, hE', heq⟩ :=
    σ.exists_pol_translatedTruncLE_aeval_pderiv hx hσ hinj F hFdeg hvars v' hγ
  rw [heq, componentsGE_add, componentsGE_sub, componentsGE_sub]
  have hlow : ∀ d' : ι →₀ ℕ, Finsupp.weight wt d' + wt v' < α'' →
      Finsupp.weight wt d' < τ := fun d' h ↦
    lt_of_add_lt_add_right (h.trans_le hτ)
  have h1 : componentsGE wt τ
      (pderiv v' (σ.pol hx α (translatedTruncLE γ (aeval σ.lift F)))) = 0 := by
    refine componentsGE_eq_zero_of_forall_lt wt fun d' hd' ↦ ?_
    obtain ⟨d, hd, hw⟩ := exists_add_eq_weight_of_mem_support_pderiv wt hd'
    refine hlow d' ?_
    rw [hw]
    exact (σ.pol_weight_lt_of_degree_lt hx hα'α hG d hd).trans_le hα'
  have h2 : componentsGE wt τ (pderiv v' E) = 0 := by
    refine componentsGE_eq_zero_of_forall_lt wt fun d' hd' ↦ ?_
    obtain ⟨d, hd, hw⟩ := exists_add_eq_weight_of_mem_support_pderiv wt hd'
    obtain ⟨d₀, hd₀, k, hk, hterm⟩ := hE d hd
    refine hlow d' ?_
    rw [hw]
    exact hwin d₀ hd₀ k _ hk hterm
  have h3 : componentsGE wt τ E' = 0 := by
    refine componentsGE_eq_zero_of_forall_lt wt fun d' hd' ↦ ?_
    obtain ⟨d, hd, k, hk, hterm⟩ := hE' d' hd'
    exact hlow d' (hwin _ (add_single_mem_support_of_mem_support_pderiv hd)
      k _ hk (hterm.untrunc v'))
  rw [h1, h2, h3, zero_sub, sub_zero, add_zero]
  refine neg_mem ?_
  rw [← Finset.sum_filter_add_sum_filter_not F.vars fun j ↦ wt v' < wt j,
    componentsGE_add]
  have hzero : ∑ j ∈ F.vars.filter (fun j ↦ ¬wt v' < wt j),
      pderiv v' (σ.pol hx α (translatedTruncLE γ (σ.lift j))) * pderiv j F = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hj' := (Finset.mem_filter.mp hj).2
    rw [not_lt] at hj'
    have hdeg : DegreeLT wt (σ.pol hx α (translatedTruncLE γ (σ.lift j))) (wt j) :=
      fun d hd ↦ σ.pol_weight_lt_of_degree_lt hx (hvars j (Finset.mem_filter.mp hj).1).le
        (((hasLowerTruncationDegrees_iff σ).mp hσ j).degree_translatedTruncLE_lt hγ) d hd
    rw [pderiv_eq_zero_of_degreeLT_le hdeg hj', zero_mul]
  rw [hzero, componentsGE_zero, add_zero]
  have hgen : ∀ j : {j : ι // j ∈ F.vars ∧ wt v' < wt j},
      ∃ c, IsWeightedHomogeneous wt (pderiv j.1 F) c := by
    intro j
    by_cases h : ∃ β, β + wt j.1 = α
    · obtain ⟨β, hβ⟩ := h
      exact ⟨β, isWeightedHomogeneous_pderiv wt hF j.1 hβ⟩
    · exact ⟨0, by
        rw [pderiv_eq_zero_of_isWeightedHomogeneous wt hF j.1 h]
        exact isWeightedHomogeneous_zero _ _ _⟩
  choose c hc using hgen
  have : Finite {j : ι // j ∈ F.vars ∧ wt v' < wt j} :=
    (F.vars.finite_toSet.subset fun j (hj : j ∈ F.vars ∧ wt v' < wt j) ↦ hj.1).to_subtype
  refine componentsGE_mem_span wt hc ?_ τ
  refine Ideal.sum_mem _ fun j hj ↦ ?_
  have hj' := Finset.mem_filter.mp hj
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, hj'.1, hj'.2⟩, rfl⟩)

end LiftFamily

end HahnSeries.Nonpositive

end
