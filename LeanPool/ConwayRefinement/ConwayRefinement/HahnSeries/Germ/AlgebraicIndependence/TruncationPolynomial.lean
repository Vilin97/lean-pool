/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LiftFamily
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.OrdinalExpansion
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Polynomial representatives modulo series bounded strictly below zero

Fix homogeneous generators of the associated graded ring of the Cantor–Bendixson degree and series
representing them.
Every series of degree below `α` agrees, modulo a series bounded away from zero, with evaluation
of a polynomial whose monomial weights are below `α`. We choose such a polynomial. Injectivity of
graded evaluation below `α` makes this choice unique, so it can be used as the polynomial of a
translated truncation without choosing a cofinal sequence of cutoffs.
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

include hx in
/-- A series of degree below `α` has a polynomial representative modulo series bounded away from
zero, with every monomial weight bounded by the degree of the series. -/
theorem exists_polynomial {α : NatOrdinal.{u}} (u : Nonpositive G K)
    (hu : ν u < (α : WithBot NatOrdinal)) :
    ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (((Finsupp.weight wt) d : NatOrdinal) : WithBot NatOrdinal) ≤ ν u) ∧
      (∀ d ∈ F.support, Finsupp.weight wt d < α) ∧
      ν (u - aeval σ.lift F) = ⊥ :=
  exists_forall_weight_lt_and_degree_sub_aeval_eq_bot xg σ.represents α
    (fun β _ y hy ↦ OrdinalGraded.IsMinimalSystem.exists_aeval_eq hx
      cantorBendixson_gradeZeroScalars β y hy) u hu

/-- The polynomial representing `u` modulo series bounded away from zero, among polynomials with
monomial weights below `α`; it is zero when `u` does not have degree below `α`. -/
def pol (α : NatOrdinal.{u}) (u : Nonpositive G K) : MvPolynomial ι K := by
  by_cases hu : ν u < (α : WithBot NatOrdinal)
  · exact Classical.choose (σ.exists_polynomial hx u hu)
  · exact 0

include hx in
/-- Every monomial of the chosen polynomial has weight below its cutoff. -/
theorem pol_weight_lt (α : NatOrdinal.{u}) (u : Nonpositive G K) :
    ∀ d ∈ (σ.pol hx α u).support, Finsupp.weight wt d < α := by
  classical
  unfold pol
  split_ifs with hu
  · exact (Classical.choose_spec (σ.exists_polynomial hx u hu)).2.1
  · simp

include hx in
/-- Every monomial weight is bounded by the degree of the represented series. -/
theorem pol_weight_le_degree {α : NatOrdinal.{u}} {u : Nonpositive G K}
    (hu : ν u < (α : WithBot NatOrdinal)) :
    ∀ d ∈ (σ.pol hx α u).support,
      (((Finsupp.weight wt) d : NatOrdinal) : WithBot NatOrdinal) ≤ ν u := by
  classical
  unfold pol
  rw [dif_pos hu]
  exact (Classical.choose_spec (σ.exists_polynomial hx u hu)).1

include hx in
/-- The chosen polynomial evaluates to the original series modulo series bounded away from zero. -/
theorem degree_sub_aeval_pol_eq_bot {α : NatOrdinal.{u}} {u : Nonpositive G K}
    (hu : ν u < (α : WithBot NatOrdinal)) :
    ν (u - aeval σ.lift (σ.pol hx α u)) = ⊥ := by
  classical
  unfold pol
  rw [dif_pos hu]
  exact (Classical.choose_spec (σ.exists_polynomial hx u hu)).2.2

include hx in
/-- Below `α`, graded injectivity makes the polynomial representative unique. -/
theorem pol_eq_of_degree_sub_aeval_eq_bot {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {u : Nonpositive G K} (hu : ν u < (α : WithBot NatOrdinal))
    {F : MvPolynomial ι K} (hF : ∀ d ∈ F.support, Finsupp.weight wt d < α)
    (h : ν (u - aeval σ.lift F) = ⊥) : σ.pol hx α u = F := by
  classical
  rw [← sub_eq_zero]
  have hinj' : ∀ β < α, ∀ P : MvPolynomial ι K,
      IsWeightedHomogeneous wt P β → aeval xg P = 0 → P = 0 := by
    intro β hβα
    rw [← OrdinalGraded.injectiveAt_iff]
    exact hinj β hβα
  apply eq_zero_of_forall_weight_lt_of_degree_aeval_eq_bot xg σ.represents
    (fun β P hβα hP hP0 ↦ hinj' β hβα P hP hP0) (fun d hd ↦ by
      have hdne : MvPolynomial.coeff d (σ.pol hx α u - F) ≠ 0 := mem_support_iff.mp hd
      rw [MvPolynomial.coeff_sub ι] at hdne
      by_cases hdpol : d ∈ (σ.pol hx α u).support
      · exact σ.pol_weight_lt hx α u d hdpol
      · have hdpol0 := notMem_support_iff.mp hdpol
        rw [hdpol0, zero_sub, neg_ne_zero] at hdne
        exact hF d (mem_support_iff.mpr hdne))
  rw [map_sub]
  have hpol := σ.degree_sub_aeval_pol_eq_bot hx hu
  have hsplit : aeval σ.lift (σ.pol hx α u) - aeval σ.lift F =
      -(u - aeval σ.lift (σ.pol hx α u)) + (u - aeval σ.lift F) := by ring
  rw [hsplit]
  refine le_bot_iff.mp (((ν).map_add_le_max _ _).trans ?_)
  rw [(ν).map_neg, hpol, h, max_self]

include hx in
/-- The polynomial of a series of degree below `α' ≤ α` has every monomial weight below `α'`. -/
theorem pol_weight_lt_of_degree_lt {α α' : NatOrdinal.{u}} (hα' : α' ≤ α)
    {u : Nonpositive G K} (hu : ν u < (α' : WithBot NatOrdinal)) :
    ∀ d ∈ (σ.pol hx α u).support, Finsupp.weight wt d < α' := by
  intro d hd
  exact WithBot.coe_lt_coe.mp ((σ.pol_weight_le_degree hx
    (hu.trans_le (WithBot.coe_le_coe.mpr hα'))) d hd |>.trans_lt hu)

include hx in
/-- Evaluation of a polynomial of weights below `α` is recovered by `pol`. -/
theorem pol_aeval {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {F : MvPolynomial ι K} (hF : ∀ d ∈ F.support, Finsupp.weight wt d < α) :
    σ.pol hx α (aeval σ.lift F) = F := by
  apply σ.pol_eq_of_degree_sub_aeval_eq_bot hx hinj
    (σ.degree_aeval_lt hF) hF
  rw [sub_self, (ν).map_zero]

include hx in
/-- `pol` is additive on series below the cutoff. -/
theorem pol_add {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {u v : Nonpositive G K} (hu : ν u < (α : WithBot NatOrdinal))
    (hv : ν v < (α : WithBot NatOrdinal)) :
    σ.pol hx α (u + v) = σ.pol hx α u + σ.pol hx α v := by
  have huv : ν (u + v) < (α : WithBot NatOrdinal) :=
    ((ν).map_add_le_max u v).trans_lt (max_lt hu hv)
  apply σ.pol_eq_of_degree_sub_aeval_eq_bot hx hinj huv (fun d hd ↦ by
    have hdne : MvPolynomial.coeff d (σ.pol hx α u + σ.pol hx α v) ≠ 0 :=
      mem_support_iff.mp hd
    rw [MvPolynomial.coeff_add] at hdne
    by_cases hdu : d ∈ (σ.pol hx α u).support
    · exact σ.pol_weight_lt hx α u d hdu
    · have hdu0 := notMem_support_iff.mp hdu
      rw [hdu0, zero_add] at hdne
      exact σ.pol_weight_lt hx α v d (mem_support_iff.mpr hdne))
  have hu' := σ.degree_sub_aeval_pol_eq_bot hx hu
  have hv' := σ.degree_sub_aeval_pol_eq_bot hx hv
  rw [map_add]
  have hsplit : u + v - (aeval σ.lift (σ.pol hx α u) +
      aeval σ.lift (σ.pol hx α v)) =
      (u - aeval σ.lift (σ.pol hx α u)) +
        (v - aeval σ.lift (σ.pol hx α v)) := by ring
  rw [hsplit]
  refine le_bot_iff.mp (((ν).map_add_le_max _ _).trans ?_)
  rw [hu', hv', max_self]

include hx in
/-- `pol` commutes with finite sums of series below the cutoff. -/
theorem pol_sum {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {κ : Type*} (s : Finset κ) (f : κ → Nonpositive G K)
    (h : ∀ i ∈ s, ν (f i) < (α : WithBot NatOrdinal)) :
    σ.pol hx α (∑ i ∈ s, f i) = ∑ i ∈ s, σ.pol hx α (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact σ.pol_aeval hx hinj (F := 0) (by simp)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        σ.pol_add hx hinj (h a (Finset.mem_insert_self a s))
          ((ν).map_sum_lt_of_forall_lt s f (WithBot.bot_lt_coe α)
            fun i hi ↦ h i (Finset.mem_insert_of_mem hi)),
        ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]

include hx in
/-- `pol` commutes with scalar multiplication on series below the cutoff. -/
theorem pol_smul {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (k : K) {u : Nonpositive G K} (hu : ν u < (α : WithBot NatOrdinal)) :
    σ.pol hx α (k • u) = k • σ.pol hx α u := by
  have hku : ν (k • u) < (α : WithBot NatOrdinal) :=
    (degree_smul_le k u).trans_lt hu
  apply σ.pol_eq_of_degree_sub_aeval_eq_bot hx hinj hku
  · intro d hd
    have hdne : MvPolynomial.coeff d (k • σ.pol hx α u) ≠ 0 :=
      mem_support_iff.mp hd
    rw [MvPolynomial.coeff_smul] at hdne
    exact σ.pol_weight_lt hx α u d
      (mem_support_iff.mpr fun hzero ↦ hdne (by rw [hzero, smul_zero]))
  · rw [map_smul]
    have herror := σ.degree_sub_aeval_pol_eq_bot hx hu
    have heq : k • u - k • aeval σ.lift (σ.pol hx α u) =
        k • (u - aeval σ.lift (σ.pol hx α u)) := by module
    rw [heq]
    exact le_bot_iff.mp ((degree_smul_le k _).trans_eq herror)

omit [CharZero K] in
open Classical in
/-- If a polynomial has all monomial weights below `bound`, then a nonzero coefficient of
`X B₀ ^ k` has weight, after restoring that power, below `bound`. -/
theorem weightedTotalDegree_xCoeff_add_nsmul_lt
    {Q : MvPolynomial ι K} {bound : NatOrdinal.{u}}
    (hQ : ∀ d ∈ Q.support, Finsupp.weight wt d < bound)
    (B₀ : ι) (k : ℕ) (h : xCoeff B₀ k Q ≠ 0) :
    weightedTotalDegree wt (xCoeff B₀ k Q) + k • wt B₀ < bound := by
  classical
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr h)
    (Finsupp.weight wt)
  have hmem : d + Finsupp.single B₀ k ∈ (xCoeff B₀ k Q * X B₀ ^ k).support := by
    rw [mem_support_iff, X_pow_eq_monomial, coeff_mul_monomial', if_pos le_add_self,
      add_tsub_cancel_right, mul_one]
    exact mem_support_iff.mp hd
  have hlt := hQ _ (support_xCoeff_mul_X_pow_subset B₀ k Q hmem)
  rw [map_add, Finsupp.weight_single] at hlt
  rwa [weightedTotalDegree, hsup]

include hx in
/-- The chosen polynomial of a series of non-bottom degree is nonzero. -/
theorem pol_ne_zero_of_degree_eq {α ρ : NatOrdinal.{u}} {u : Nonpositive G K}
    (hu : ν u = (ρ : WithBot NatOrdinal)) (hρα : ρ < α) : σ.pol hx α u ≠ 0 := by
  intro hzero
  have hsub := σ.degree_sub_aeval_pol_eq_bot hx (hu.trans_lt (WithBot.coe_lt_coe.mpr hρα))
  rw [hzero, map_zero, sub_zero, hu] at hsub
  exact WithBot.coe_ne_bot hsub

include hx in
/-- A series of bottom degree has zero representing polynomial. -/
theorem pol_eq_zero_of_degree_eq_bot {α : NatOrdinal.{u}} {u : Nonpositive G K}
    (hu : ν u = ⊥) : σ.pol hx α u = 0 := by
  classical
  unfold pol
  rw [dif_pos (by rw [hu]; exact WithBot.bot_lt_coe α)]
  have hspec := Classical.choose_spec (σ.exists_polynomial hx u
    (by rw [hu]; exact WithBot.bot_lt_coe α))
  apply MvPolynomial.eq_zero_iff.mpr
  intro d
  by_contra hd
  have hdmem := mem_support_iff.mpr hd
  exact WithBot.not_coe_le_bot _ ((hspec.1 d hdmem).trans_eq hu)

include hx in
/-- At exact non-bottom degree `ρ`, the chosen polynomial has weighted total degree `ρ`. -/
theorem weightedTotalDegree_pol_eq_of_degree_eq {α ρ : NatOrdinal.{u}}
    {u : Nonpositive G K} (hu : ν u = (ρ : WithBot NatOrdinal)) (hρα : ρ < α) :
    weightedTotalDegree wt (σ.pol hx α u) = ρ := by
  have hne := σ.pol_ne_zero_of_degree_eq hx hu hρα
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr hne)
    (Finsupp.weight wt)
  have hle : weightedTotalDegree wt (σ.pol hx α u) ≤ ρ := by
    rw [weightedTotalDegree, hsup]
    exact WithBot.coe_le_coe.mp (σ.pol_weight_le_degree hx
      (hu.trans_lt (WithBot.coe_lt_coe.mpr hρα)) d hd |>.trans_eq hu)
  refine le_antisymm hle ?_
  by_contra hnot
  have hlt : weightedTotalDegree wt (σ.pol hx α u) < ρ := lt_of_not_ge hnot
  have heval : ν (aeval σ.lift (σ.pol hx α u)) < (ρ : WithBot NatOrdinal) :=
    σ.degree_aeval_lt (fun d' hd' ↦ by
      exact (le_weightedTotalDegree wt hd').trans_lt hlt)
  have hsub := σ.degree_sub_aeval_pol_eq_bot hx
    (hu.trans_lt (WithBot.coe_lt_coe.mpr hρα))
  have hdegree := degree_eq_of_degree_sub_eq_bot hsub
  rw [hu] at hdegree
  exact heval.ne (hdegree.symm)

include hx in
/-- A fixed upper bound on the chosen polynomials of proper truncations contradicts exact degree
and the approach theorem for Cantor–Bendixson ranks whenever the shifted degree exceeds it. -/
theorem false_of_forall_weightedTotalDegree_pol_add_lt {α lam sigma bound : NatOrdinal.{u}}
    {u : Nonpositive G K} (hu : ν u = (lam : WithBot NatOrdinal)) (hlam : lam ≠ 0)
    (hσ : sigma = 0 ∨ NatOrdinal.leastTerm lam ≤ NatOrdinal.leastTerm sigma)
    (hbound : bound < lam + sigma) {l : G} (hl : l < 0)
    (hwin : ∀ γ : G, l < γ → γ < 0 → σ.pol hx α (translatedTruncLE γ u) ≠ 0 →
      weightedTotalDegree wt (σ.pol hx α (translatedTruncLE γ u)) + sigma < bound)
    (hlamα : lam < α) : False := by
  obtain ⟨ρ, hρlam, hρbound⟩ :=
    NatOrdinal.exists_lt_le_add_of_lastCantorTerm_le hlam hσ hbound
  obtain ⟨γ, hlγ, hγ0, hγeq⟩ := exists_lt_and_degree_translatedTruncLE_eq
    u lam ρ hu hρlam hl
  have hρα : ρ < α := hρlam.trans hlamα
  have hp0 := σ.pol_ne_zero_of_degree_eq hx hγeq hρα
  have hdeg := σ.weightedTotalDegree_pol_eq_of_degree_eq hx hγeq hρα
  exact absurd (hwin γ hlγ hγ0 hp0) (not_lt.mpr (hdeg ▸ hρbound))

include hx in
/-- Multiplication of represented polynomials computes the polynomial of a product when the
product polynomial still has all weights below the cutoff. -/
theorem pol_mul {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {u v : Nonpositive G K} (hu : ν u < (α : WithBot NatOrdinal))
    (hv : ν v < (α : WithBot NatOrdinal))
    (hprod : ∀ d ∈ (σ.pol hx α u * σ.pol hx α v).support, Finsupp.weight wt d < α) :
    ν (u * v) < (α : WithBot NatOrdinal) ∧
      σ.pol hx α (u * v) = σ.pol hx α u * σ.pol hx α v := by
  have hcongr := degree_sub_eq_bot_mul
    (σ.degree_sub_aeval_pol_eq_bot hx hu) (σ.degree_sub_aeval_pol_eq_bot hx hv)
  rw [← map_mul] at hcongr
  have heval : ν (aeval σ.lift (σ.pol hx α u * σ.pol hx α v)) <
      (α : WithBot NatOrdinal) := σ.degree_aeval_lt hprod
  have hdegree : ν (u * v) = ν (aeval σ.lift (σ.pol hx α u * σ.pol hx α v)) :=
    degree_eq_of_degree_sub_eq_bot hcongr
  refine ⟨hdegree ▸ heval, ?_⟩
  exact σ.pol_eq_of_degree_sub_aeval_eq_bot hx hinj (hdegree ▸ heval) hprod hcongr

include hx in
/-- The finite Cantor–Bendixson convolution formula in the representing polynomial ring. -/
theorem pol_translatedTruncLE_mul {α m n : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {a b : Nonpositive G K} (ha : Nonpositive.HasLowerTruncationDegree a m)
    (hb : Nonpositive.HasLowerTruncationDegree b n)
    (hm : m < α) (hn : n < α) (hmn : m + n ≤ α) {γ : G} (hγ : γ < 0) :
    σ.pol hx α (translatedTruncLE γ (a * b)) =
      ∑ q ∈ (a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) γ,
        σ.pol hx α (translatedTruncLE q.1 a) * σ.pol hx α (translatedTruncLE q.2 b) := by
  classical
  set S := (a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) γ with hS
  have hq : ∀ q ∈ S, q.1 ≤ 0 ∧ q.2 ≤ 0 ∧ (q.1 < 0 ∨ q.2 < 0) := by
    intro q hq
    obtain ⟨hq1, hq2, hsum⟩ := ((a : HahnSeries G K).mem_closedSupportAddFiber
      (b : HahnSeries G K) γ q).mp hq
    have hq1le : q.1 ≤ 0 := closure_minimal a.property isClosed_Iic
      ((mem_closedSupport _ _).mp hq1)
    have hq2le : q.2 ≤ 0 := closure_minimal b.property isClosed_Iic
      ((mem_closedSupport _ _).mp hq2)
    refine ⟨hq1le, hq2le, ?_⟩
    rcases lt_or_eq_of_le hq1le with hq1neg | hq1zero
    · exact Or.inl hq1neg
    · right
      have : q.2 = γ := by rw [← hsum, hq1zero, zero_add]
      exact this ▸ hγ
  have hterm : ∀ q ∈ S, ∀ d ∈
      (σ.pol hx α (translatedTruncLE q.1 a) *
        σ.pol hx α (translatedTruncLE q.2 b)).support,
      Finsupp.weight wt d < α := by
    intro q hqS d hd
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp
      (MvPolynomial.support_mul _ _ hd)
    rw [map_add]
    obtain ⟨hq1le, hq2le, hproper⟩ := hq q hqS
    rcases hproper with hq1neg | hq2neg
    · have h1 := σ.pol_weight_lt_of_degree_lt hx hm.le
        (ha.degree_translatedTruncLE_lt hq1neg) d₁ hd₁
      have h2 := σ.pol_weight_le_degree hx
        ((ha.degree_translatedTruncLE_lt hq1neg).trans
          (WithBot.coe_lt_coe.mpr hm)) d₁ hd₁
      have h2' := σ.pol_weight_le_degree hx
        ((hb.degree_translatedTruncLE_le hq2le).trans_lt
          (WithBot.coe_lt_coe.mpr hn)) d₂ hd₂
      have h2n : Finsupp.weight wt d₂ ≤ n :=
        WithBot.coe_le_coe.mp (h2'.trans (hb.degree_translatedTruncLE_le hq2le))
      exact (add_lt_add_of_lt_of_le h1 h2n).trans_le hmn
    · have h1m : Finsupp.weight wt d₁ ≤ m := WithBot.coe_le_coe.mp
        ((σ.pol_weight_le_degree hx
          ((ha.degree_translatedTruncLE_le hq1le).trans_lt
            (WithBot.coe_lt_coe.mpr hm)) d₁ hd₁).trans
          (ha.degree_translatedTruncLE_le hq1le))
      have h2 := σ.pol_weight_lt_of_degree_lt hx hn.le
        (hb.degree_translatedTruncLE_lt hq2neg) d₂ hd₂
      exact (add_lt_add_of_le_of_lt h1m h2).trans_le hmn
  have hsumw : ∀ d ∈ (∑ q ∈ S,
      σ.pol hx α (translatedTruncLE q.1 a) *
        σ.pol hx α (translatedTruncLE q.2 b)).support,
      Finsupp.weight wt d < α := by
    intro d hd
    obtain ⟨q, hqS, hdq⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    exact hterm q hqS d hdq
  have hdeg : ν (translatedTruncLE γ (a * b)) < (α : WithBot NatOrdinal) :=
    ((ha.mul rfl hb).degree_translatedTruncLE_lt hγ).trans_le
      (WithBot.coe_le_coe.mpr hmn)
  have haall : ∀ q : G, ν (translatedTruncLE q a) < (α : WithBot NatOrdinal) := by
    intro q
    rcases le_total q 0 with hq | hq
    · exact (ha.degree_translatedTruncLE_le hq).trans_lt (WithBot.coe_lt_coe.mpr hm)
    · by_cases hq0 : q = 0
      · subst q
        rw [translatedTruncLE_zero]
        exact ha.degree_le.trans_lt (WithBot.coe_lt_coe.mpr hm)
      rw [degree_translatedTruncLE_of_pos (lt_of_le_of_ne hq (Ne.symm hq0))]
      exact WithBot.bot_lt_coe α
  have hball : ∀ q : G, ν (translatedTruncLE q b) < (α : WithBot NatOrdinal) := by
    intro q
    rcases le_total q 0 with hq | hq
    · exact (hb.degree_translatedTruncLE_le hq).trans_lt (WithBot.coe_lt_coe.mpr hn)
    · by_cases hq0 : q = 0
      · subst q
        rw [translatedTruncLE_zero]
        exact hb.degree_le.trans_lt (WithBot.coe_lt_coe.mpr hn)
      rw [degree_translatedTruncLE_of_pos (lt_of_le_of_ne hq (Ne.symm hq0))]
      exact WithBot.bot_lt_coe α
  apply σ.pol_eq_of_degree_sub_aeval_eq_bot hx hinj hdeg hsumw
  simpa only [hS, map_sum, map_mul] using
    degree_translatedTruncLE_mul_sub_aeval_sum_eq_bot a b γ
      (fun q ↦ σ.pol hx α (translatedTruncLE q a))
      (fun q ↦ σ.pol hx α (translatedTruncLE q b))
      (fun q ↦ σ.degree_sub_aeval_pol_eq_bot hx (haall q))
      (fun q ↦ σ.degree_sub_aeval_pol_eq_bot hx (hball q))

include hx in
/-- The convolution identity remains true after adjoining the two boundary pairs `(0, γ)` and
`(γ, 0)`: a missing boundary point contributes a bottom-degree truncation and hence zero. -/
theorem pol_translatedTruncLE_mul_boundary {α m n : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {a b : Nonpositive G K} (ha : Nonpositive.HasLowerTruncationDegree a m)
    (hb : Nonpositive.HasLowerTruncationDegree b n)
    (hm : m < α) (hn : n < α) (hmn : m + n ≤ α) {γ : G} (hγ : γ < 0) :
    σ.pol hx α (translatedTruncLE γ (a * b)) =
      ∑ q ∈ insert (0, γ) (insert (γ, 0)
        ((a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) γ)),
        σ.pol hx α (translatedTruncLE q.1 a) * σ.pol hx α (translatedTruncLE q.2 b) := by
  rw [σ.pol_translatedTruncLE_mul hx hinj ha hb hm hn hmn hγ]
  classical
  refine Finset.sum_subset (by
    intro q hq
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq)) ?_
  intro q hq hqnot
  rcases Finset.mem_insert.mp hq with hq | hq
  · subst q
    have hnot : ¬(0 ∈ (a : HahnSeries G K).closedSupport ∧
        γ ∈ (b : HahnSeries G K).closedSupport) := by
      intro h
      exact hqnot ((a : HahnSeries G K).mem_closedSupportAddFiber
        (b : HahnSeries G K) γ (0, γ) |>.mpr ⟨h.1, h.2, zero_add γ⟩)
    by_cases h0a : 0 ∈ (a : HahnSeries G K).closedSupport
    · have hγb : γ ∉ (b : HahnSeries G K).closedSupport := fun h ↦ hnot ⟨h0a, h⟩
      have hbot : ν (translatedTruncLE γ b) = ⊥ := by
        rw [degree_translatedTruncLE_eq, if_neg hγb]
      rw [σ.pol_eq_zero_of_degree_eq_bot hx hbot, mul_zero]
    · have hbot : ν a = ⊥ := by
        rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
          cantorBendixsonValue_of_notMem (a : HahnSeries G K)
            (by simpa only [mem_closedSupport] using h0a), NatOrdinal.of_zero,
          NatOrdinal.cantorDegree_zero]
      rw [translatedTruncLE_zero, σ.pol_eq_zero_of_degree_eq_bot hx hbot, zero_mul]
  · rcases Finset.mem_insert.mp hq with hq | hq
    · subst q
      have hnot : ¬(γ ∈ (a : HahnSeries G K).closedSupport ∧
        0 ∈ (b : HahnSeries G K).closedSupport) := by
        intro h
        exact hqnot ((a : HahnSeries G K).mem_closedSupportAddFiber
          (b : HahnSeries G K) γ (γ, 0) |>.mpr ⟨h.1, h.2, add_zero γ⟩)
      by_cases hγa : γ ∈ (a : HahnSeries G K).closedSupport
      · have h0b : 0 ∉ (b : HahnSeries G K).closedSupport := fun h ↦ hnot ⟨hγa, h⟩
        have hbot : ν b = ⊥ := by
          rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
            cantorBendixsonValue_of_notMem (b : HahnSeries G K)
              (by simpa only [mem_closedSupport] using h0b), NatOrdinal.of_zero,
            NatOrdinal.cantorDegree_zero]
        rw [translatedTruncLE_zero, σ.pol_eq_zero_of_degree_eq_bot hx hbot, mul_zero]
      · have hbot : ν (translatedTruncLE γ a) = ⊥ := by
          rw [degree_translatedTruncLE_eq, if_neg hγa]
        rw [σ.pol_eq_zero_of_degree_eq_bot hx hbot, zero_mul]
    · exact absurd hq hqnot

include hx in
/-- The polynomial representing an untruncated lifted generator is its variable. -/
theorem pol_lift {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {i : ι} (hi : wt i < α) : σ.pol hx α (σ.lift i) = X i := by
  rw [← (aeval_X (R := K) σ.lift i)]
  apply σ.pol_aeval hx hinj
  intro d hd
  rw [support_X, Finset.mem_singleton] at hd
  rwa [hd, Finsupp.weight_single, one_smul]

include hx in
/-- The polynomial representing a power of a lifted generator is the corresponding variable
power, while its weight stays below the cutoff. -/
theorem pol_lift_pow {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {i : ι} (e : ℕ) (he : e • wt i < α) :
    σ.pol hx α (σ.lift i ^ e) = X i ^ e := by
  classical
  have hpow : σ.lift i ^ e = aeval σ.lift (X i ^ e : MvPolynomial ι K) := by
    rw [map_pow, aeval_X]
  rw [hpow]
  apply σ.pol_aeval hx hinj
  intro d hd
  rw [X_pow_eq_monomial, support_monomial, if_neg one_ne_zero,
    Finset.mem_singleton] at hd
  rw [hd, Finsupp.weight_single]
  exact he

include hx in
/-- A proper truncation of a lifted generator does not involve any variable of at least its
weight. -/
theorem pol_translatedTruncLE_lift_mem_supported {α : NatOrdinal.{u}}
    (hσ : HasLowerTruncationDegrees σ) {i B₀ : ι} (hi : wt i < α) (hle : wt i ≤ wt B₀)
    {γ : G} (hγ : γ < 0) :
    σ.pol hx α (translatedTruncLE γ (σ.lift i)) ∈ supported K {B₀}ᶜ := by
  apply mem_supported_of_forall_weight_lt B₀ wt
  intro d hd
  exact (σ.pol_weight_lt_of_degree_lt hx hi.le
    (((hasLowerTruncationDegrees_iff σ).mp hσ i).degree_translatedTruncLE_lt hγ) d hd).trans_le hle

variable (α : NatOrdinal.{u}) (B₀ : ι) in
/-- A series satisfying the degree and proper-truncation bounds whose polynomial, and the
polynomial of every proper truncation, omit `X_{B₀}`. -/
structure FreeOfVariable (u : Nonpositive G K) (m : NatOrdinal.{u}) : Prop where
  lowerTruncationDegree : Nonpositive.HasLowerTruncationDegree u m
  degree_lt : m < α
  pol_mem : σ.pol hx α u ∈ supported K {B₀}ᶜ
  trunc_mem : ∀ {γ : G}, γ < 0 →
    σ.pol hx α (translatedTruncLE γ u) ∈ supported K {B₀}ᶜ

namespace FreeOfVariable

variable {σ hx}

/-- The polynomial at any nonpositive cutoff omits the distinguished variable. -/
theorem pol_trunc_mem_nonpos {α : NatOrdinal.{u}} {B₀ : ι} {u : Nonpositive G K}
    {m : NatOrdinal.{u}} (hu : FreeOfVariable σ hx α B₀ u m) {γ : G} (hγ : γ ≤ 0) :
    σ.pol hx α (translatedTruncLE γ u) ∈ supported K {B₀}ᶜ := by
  rcases eq_or_lt_of_le hγ with rfl | hγ
  · rw [translatedTruncLE_zero]
    exact hu.pol_mem
  · exact hu.trunc_mem hγ

/-- A lifted generator distinct from `B₀` and of no greater weight is free of `B₀`. -/
theorem lift (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}} {B₀ i : ι}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (hi : i ≠ B₀) (hile : wt i ≤ wt B₀) (hB₀ : wt B₀ < α) :
    FreeOfVariable σ hx α B₀ (σ.lift i) (wt i) where
  lowerTruncationDegree := (hasLowerTruncationDegrees_iff σ).mp hσ i
  degree_lt := hile.trans_lt hB₀
  pol_mem := by
    rw [σ.pol_lift hx hinj (hile.trans_lt hB₀)]
    exact X_mem_supported.mpr hi
  trunc_mem := fun hγ ↦
    σ.pol_translatedTruncLE_lift_mem_supported hx hσ (hile.trans_lt hB₀) hile hγ

/-- Sums of series free of `B₀` at a common degree remain free. -/
theorem add {α : NatOrdinal.{u}} {B₀ : ι} {a b : Nonpositive G K} {m : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (ha : FreeOfVariable σ hx α B₀ a m) (hb : FreeOfVariable σ hx α B₀ b m) :
    FreeOfVariable σ hx α B₀ (a + b) m where
  lowerTruncationDegree := ha.lowerTruncationDegree.add hb.lowerTruncationDegree
  degree_lt := ha.degree_lt
  pol_mem := by
    rw [σ.pol_add hx hinj
      (ha.lowerTruncationDegree.degree_le.trans_lt (WithBot.coe_lt_coe.mpr ha.degree_lt))
      (hb.lowerTruncationDegree.degree_le.trans_lt (WithBot.coe_lt_coe.mpr hb.degree_lt))]
    exact Subalgebra.add_mem _ ha.pol_mem hb.pol_mem
  trunc_mem := by
    intro γ hγ
    rw [map_add, σ.pol_add hx hinj
      (ha.lowerTruncationDegree.degree_translatedTruncLE_lt hγ |>.trans
        (WithBot.coe_lt_coe.mpr ha.degree_lt))
      (hb.lowerTruncationDegree.degree_translatedTruncLE_lt hγ |>.trans
        (WithBot.coe_lt_coe.mpr hb.degree_lt))]
    exact Subalgebra.add_mem _ (ha.trunc_mem hγ) (hb.trunc_mem hγ)

/-- Scalar multiples of a series free of `B₀` remain free. -/
theorem smul {α : NatOrdinal.{u}} {B₀ : ι} (k : K) {a : Nonpositive G K}
    {m : NatOrdinal.{u}} (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (ha : FreeOfVariable σ hx α B₀ a m) : FreeOfVariable σ hx α B₀ (k • a) m where
  lowerTruncationDegree := by
    rw [Nonpositive.hasLowerTruncationDegree_iff]
    constructor
    · exact (degree_smul_le k a).trans ha.lowerTruncationDegree.degree_le
    · intro γ hγ
      rw [translatedTruncLE_smul]
      exact (degree_smul_le k _).trans_lt
        (ha.lowerTruncationDegree.degree_translatedTruncLE_lt hγ)
  degree_lt := ha.degree_lt
  pol_mem := by
    rw [σ.pol_smul hx hinj k
      (ha.lowerTruncationDegree.degree_le.trans_lt (WithBot.coe_lt_coe.mpr ha.degree_lt))]
    exact Subalgebra.smul_mem _ ha.pol_mem k
  trunc_mem := by
    intro γ hγ
    rw [translatedTruncLE_smul, σ.pol_smul hx hinj k
      (ha.lowerTruncationDegree.degree_translatedTruncLE_lt hγ |>.trans
        (WithBot.coe_lt_coe.mpr ha.degree_lt))]
    exact Subalgebra.smul_mem _ (ha.trunc_mem hγ) k

/-- The zero series is free at every degree below `α`. -/
theorem zero {α : NatOrdinal.{u}} {B₀ : ι} {m : NatOrdinal.{u}} (hm : m < α) :
    FreeOfVariable σ hx α B₀ (0 : Nonpositive G K) m where
  lowerTruncationDegree := hasLowerTruncationDegree_zero m
  degree_lt := hm
  pol_mem := by
    rw [σ.pol_eq_zero_of_degree_eq_bot hx (by rw [(ν).map_zero])]
    exact Subalgebra.zero_mem _
  trunc_mem := by
    intro γ _
    rw [map_zero, σ.pol_eq_zero_of_degree_eq_bot hx (by rw [(ν).map_zero])]
    exact Subalgebra.zero_mem _

open Classical in
/-- The identity series is free of every variable when `0 < α`. -/
theorem one {α : NatOrdinal.{u}} {B₀ : ι} (hα : 0 < α)
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) :
    FreeOfVariable σ hx α B₀ (1 : Nonpositive G K) 0 where
  lowerTruncationDegree := hasLowerTruncationDegree_one
  degree_lt := hα
  pol_mem := by
    have hone : σ.pol hx α (1 : Nonpositive G K) = 1 := by
      rw [← map_one (MvPolynomial.aeval (R := K) σ.lift)]
      exact σ.pol_aeval hx hinj (F := 1) (by
        intro d hd
        have hdne : MvPolynomial.coeff d (1 : MvPolynomial ι K) ≠ 0 :=
          mem_support_iff.mp hd
        rw [MvPolynomial.coeff_one] at hdne
        split_ifs at hdne with hd0
        · subst d
          simpa only [map_zero] using hα
        · exact absurd rfl hdne)
    rw [hone]
    exact Subalgebra.one_mem _
  trunc_mem := by
    intro γ hγ
    have hzero : translatedTruncLE γ (1 : Nonpositive G K) = 0 := by
      apply Subtype.ext
      ext g
      rw [coe_translatedTruncLE, HahnSeries.coeff_translate, HahnSeries.coeff_truncLE,
        show ((1 : Nonpositive G K) : HahnSeries G K) = HahnSeries.C 1 by rfl,
        HahnSeries.C_apply, HahnSeries.coeff_single]
      split_ifs with hle heq
      · exact absurd (heq ▸ hle) (not_le.mpr hγ)
      · rfl
      · rfl
    rw [hzero, σ.pol_eq_zero_of_degree_eq_bot hx (by rw [(ν).map_zero])]
    exact Subalgebra.zero_mem _

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CharZero K] in
/-- A proper translated truncation of the identity series is zero. -/
theorem translatedTruncLE_one {γ : G} (hγ : γ < 0) :
    translatedTruncLE γ (1 : Nonpositive G K) = 0 := by
  apply Subtype.ext
  ext g
  rw [coe_translatedTruncLE, HahnSeries.coeff_translate, HahnSeries.coeff_truncLE,
    show ((1 : Nonpositive G K) : HahnSeries G K) = HahnSeries.C 1 by rfl,
    HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs with hle heq
  · exact absurd (heq ▸ hle) (not_le.mpr hγ)
  · rfl
  · rfl

/-- A finite sum of series free of `B₀` at a common degree remains free. -/
theorem sum {α : NatOrdinal.{u}} {B₀ : ι} {κ : Type*} {m : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (hm : m < α) (s : Finset κ) (f : κ → Nonpositive G K)
    (h : ∀ i ∈ s, FreeOfVariable σ hx α B₀ (f i) m) :
    FreeOfVariable σ hx α B₀ (∑ i ∈ s, f i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (σ := σ) (hx := hx) (B₀ := B₀) hm
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add hinj
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Products of series free of `B₀` remain free when their degree sum stays below `α`. -/
theorem mul {α : NatOrdinal.{u}} {B₀ : ι} {a b : Nonpositive G K} {m n : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (ha : FreeOfVariable σ hx α B₀ a m) (hb : FreeOfVariable σ hx α B₀ b n)
    (hmn : m + n < α) : FreeOfVariable σ hx α B₀ (a * b) (m + n) where
  lowerTruncationDegree := ha.lowerTruncationDegree.mul rfl hb.lowerTruncationDegree
  degree_lt := hmn
  pol_mem := by
    classical
    have hprod : ∀ d ∈ (σ.pol hx α a * σ.pol hx α b).support,
        Finsupp.weight wt d < α := by
      intro d hd
      obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp
        (MvPolynomial.support_mul _ _ hd)
      rw [map_add]
      have h1m : Finsupp.weight wt d₁ ≤ m := WithBot.coe_le_coe.mp
        ((σ.pol_weight_le_degree hx
          (ha.lowerTruncationDegree.degree_le.trans_lt
            (WithBot.coe_lt_coe.mpr ha.degree_lt)) d₁ hd₁).trans
          ha.lowerTruncationDegree.degree_le)
      have h2n : Finsupp.weight wt d₂ ≤ n := WithBot.coe_le_coe.mp
        ((σ.pol_weight_le_degree hx
          (hb.lowerTruncationDegree.degree_le.trans_lt
            (WithBot.coe_lt_coe.mpr hb.degree_lt)) d₂ hd₂).trans
          hb.lowerTruncationDegree.degree_le)
      exact (add_le_add h1m h2n).trans_lt hmn
    have haα : ν a < (α : WithBot NatOrdinal) :=
      ha.lowerTruncationDegree.degree_le.trans_lt (WithBot.coe_lt_coe.mpr ha.degree_lt)
    have hbα : ν b < (α : WithBot NatOrdinal) :=
      hb.lowerTruncationDegree.degree_le.trans_lt (WithBot.coe_lt_coe.mpr hb.degree_lt)
    rw [(σ.pol_mul hx hinj haα hbα hprod).2]
    exact Subalgebra.mul_mem _ ha.pol_mem hb.pol_mem
  trunc_mem := by
    intro γ hγ
    rw [σ.pol_translatedTruncLE_mul hx hinj ha.lowerTruncationDegree hb.lowerTruncationDegree
      ha.degree_lt hb.degree_lt hmn.le hγ]
    refine Subalgebra.sum_mem _ fun q hq ↦ Subalgebra.mul_mem _ ?_ ?_
    · exact ha.pol_trunc_mem_nonpos (closure_minimal a.property isClosed_Iic
        ((mem_closedSupport _ _).mp (((a : HahnSeries G K).mem_closedSupportAddFiber
          (b : HahnSeries G K) γ q).mp hq).1))
    · exact hb.pol_trunc_mem_nonpos (closure_minimal b.property isClosed_Iic
        ((mem_closedSupport _ _).mp (((a : HahnSeries G K).mem_closedSupportAddFiber
          (b : HahnSeries G K) γ q).mp hq).2.1))

/-- Powers of a free series remain free when their weighted degree stays below `α`. -/
theorem pow {α : NatOrdinal.{u}} {B₀ : ι} {a : Nonpositive G K} {m : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (ha : FreeOfVariable σ hx α B₀ a m) (n : ℕ) (hn : n • m < α) :
    FreeOfVariable σ hx α B₀ (a ^ n) (n • m) := by
  induction n with
  | zero =>
      classical
      rw [pow_zero, zero_smul]
      refine ⟨hasLowerTruncationDegree_one, hn, ?_, ?_⟩
      · have hone : σ.pol hx α (1 : Nonpositive G K) = 1 := by
          rw [← map_one (aeval (R := K) σ.lift)]
          exact σ.pol_aeval hx hinj (F := 1) (by
            intro d hd
            have hdne : MvPolynomial.coeff d (1 : MvPolynomial ι K) ≠ 0 :=
              mem_support_iff.mp hd
            rw [MvPolynomial.coeff_one] at hdne
            split_ifs at hdne with hd0
            · subst d
              simpa only [map_zero, zero_smul] using hn
            · exact absurd rfl hdne)
        rw [hone]
        exact Subalgebra.one_mem _
      · intro γ hγ
        have hzero : translatedTruncLE γ (1 : Nonpositive G K) = 0 := by
          apply Subtype.ext
          ext g
          rw [coe_translatedTruncLE, HahnSeries.coeff_translate, HahnSeries.coeff_truncLE,
            show ((1 : Nonpositive G K) : HahnSeries G K) = HahnSeries.C 1 by rfl,
            HahnSeries.C_apply, HahnSeries.coeff_single]
          split_ifs with hle heq
          · exact absurd (heq ▸ hle) (not_le.mpr hγ)
          · rfl
          · rfl
        rw [hzero, σ.pol_eq_zero_of_degree_eq_bot hx (by rw [(ν).map_zero])]
        exact Subalgebra.zero_mem _
  | succ n ih =>
      rw [pow_succ]
      have hsucc : (n + 1) • m = n • m + m := by
        rw [add_nsmul, one_nsmul]
      rw [hsucc] at hn ⊢
      have hn' : n • m < α := by
        exact NatOrdinal.le_add_right.trans_lt hn
      apply (ih hn').mul hinj ha
      exact hn

/-- A finite product of free series is free when the sum of their degrees stays below `α`. -/
theorem prod {α : NatOrdinal.{u}} {B₀ : ι} {κ : Type*} (hα : 0 < α)
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (s : Finset κ) (f : κ → Nonpositive G K) (m : κ → NatOrdinal.{u})
    (h : ∀ i ∈ s, FreeOfVariable σ hx α B₀ (f i) (m i))
    (hsum : ∑ i ∈ s, m i < α) :
    FreeOfVariable σ hx α B₀ (∏ i ∈ s, f i) (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact (hasLowerTruncationDegree_one |> fun hp ↦
        ⟨hp, hα, by
          have hone : σ.pol hx α (1 : Nonpositive G K) = 1 := by
            rw [← map_one (aeval (R := K) σ.lift)]
            exact σ.pol_aeval hx hinj (F := 1) (by
              intro d hd
              have hdne : MvPolynomial.coeff d (1 : MvPolynomial ι K) ≠ 0 :=
                mem_support_iff.mp hd
              rw [MvPolynomial.coeff_one] at hdne
              split_ifs at hdne with hd0
              · subst d
                simpa only [map_zero] using hα
              · exact absurd rfl hdne)
          rw [hone]
          exact Subalgebra.one_mem _, fun {γ} hγ ↦ by
            have hzero : translatedTruncLE γ (1 : Nonpositive G K) = 0 := by
              apply Subtype.ext
              ext g
              rw [coe_translatedTruncLE, HahnSeries.coeff_translate,
                HahnSeries.coeff_truncLE,
                show ((1 : Nonpositive G K) : HahnSeries G K) = HahnSeries.C 1 by rfl,
                HahnSeries.C_apply, HahnSeries.coeff_single]
              split_ifs with hle heq
              · exact absurd (heq ▸ hle) (not_le.mpr hγ)
              · rfl
              · rfl
            rw [hzero, σ.pol_eq_zero_of_degree_eq_bot hx (by rw [(ν).map_zero])]
            exact Subalgebra.zero_mem _⟩)
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hs : ∑ i ∈ s, m i < α := by
        rw [Finset.sum_insert ha] at hsum
        exact NatOrdinal.le_add_left.trans_lt hsum
      rw [Finset.sum_insert ha] at hsum
      exact (h a (Finset.mem_insert_self a s)).mul hinj
        (ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)) hs) hsum

/-- Evaluating a monomial not involving `B₀`, in variables of weight at most `wt B₀`, gives a
series free of `B₀`. -/
theorem aeval_monomial (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}} {B₀ : ι}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (hB₀ : wt B₀ < α) (d : ι →₀ ℕ) (hd : d B₀ = 0)
    (hle : ∀ i ∈ d.support, wt i ≤ wt B₀) (hdegree : Finsupp.weight wt d < α) :
    FreeOfVariable σ hx α B₀
      (aeval σ.lift (monomial d (1 : K))) (Finsupp.weight wt d) := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]
  rw [Finsupp.weight_apply, Finsupp.sum] at hdegree ⊢
  apply prod (zero_le.trans_lt hdegree) hinj d.support (fun i ↦ σ.lift i ^ d i)
    (fun i ↦ d i • wt i)
  · intro i hi
    have hiB₀ : i ≠ B₀ := fun h ↦ (Finsupp.mem_support_iff.mp hi) (h ▸ hd)
    have hiterm : d i • wt i < α := (Finset.single_le_sum
      (f := fun i ↦ d i • wt i) (fun _ _ ↦ zero_le) hi).trans_lt hdegree
    exact (lift hσ hinj hiB₀ (hle i hi) hB₀).pow hinj (d i) hiterm
  · exact hdegree

/-- Evaluating a homogeneous polynomial which omits `B₀` and uses no heavier variable gives a
series free of `B₀`. -/
theorem aeval (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}} {B₀ : ι}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    (hB₀ : wt B₀ < α) {F : MvPolynomial ι K} {m : NatOrdinal.{u}}
    (hF : IsWeightedHomogeneous wt F m) (hm : m < α)
    (hmem : F ∈ supported K {B₀}ᶜ) (hle : ∀ i ∈ F.vars, wt i ≤ wt B₀) :
    FreeOfVariable σ hx α B₀ (aeval σ.lift F) m := by
  classical
  conv => rw [F.as_sum]
  rw [map_sum]
  apply sum hinj hm F.support
  intro d hd
  have hdw : Finsupp.weight wt d = m := hF (mem_support_iff.mp hd)
  have hd0 : d B₀ = 0 := by
    by_contra h0
    have hv : B₀ ∈ F.vars :=
      (mem_vars_iff_mem_support B₀).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr h0⟩
    exact (mem_supported.mp hmem) hv rfl
  have hwt : ∀ i ∈ d.support, wt i ≤ wt B₀ := fun i hi ↦
    hle i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)
  have hmono : (monomial d (MvPolynomial.coeff d F) : MvPolynomial ι K) =
      MvPolynomial.C (MvPolynomial.coeff d F) * monomial d 1 := by
    rw [C_mul_monomial, mul_one]
  rw [hmono, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [← hdw]
  exact (aeval_monomial (σ := σ) (hx := hx) hσ hinj hB₀ d hd0 hwt
    (hdw ▸ hm)).smul (MvPolynomial.coeff d F) hinj

/-- Multiplying a free series by a power of the distinguished lift is represented by the
corresponding variable power. -/
theorem pol_lift_pow_mul (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}} {B₀ : ι}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {u : Nonpositive G K} {m : NatOrdinal.{u}} (hu : FreeOfVariable σ hx α B₀ u m)
    (e : ℕ) (he : e • wt B₀ + m < α) :
    σ.pol hx α (σ.lift B₀ ^ e * u) = X B₀ ^ e * σ.pol hx α u := by
  classical
  have hpow : Nonpositive.HasLowerTruncationDegree (σ.lift B₀ ^ e) (e • wt B₀) :=
    ((hasLowerTruncationDegrees_iff σ).mp hσ B₀).pow e
  have hpowα : ν (σ.lift B₀ ^ e) < (α : WithBot NatOrdinal) :=
    hpow.degree_le.trans_lt (WithBot.coe_lt_coe.mpr (NatOrdinal.le_add_right.trans_lt he))
  have huα : ν u < (α : WithBot NatOrdinal) :=
    hu.lowerTruncationDegree.degree_le.trans_lt (WithBot.coe_lt_coe.mpr hu.degree_lt)
  have hprod : ∀ d ∈ (σ.pol hx α (σ.lift B₀ ^ e) * σ.pol hx α u).support,
      Finsupp.weight wt d < α := by
    intro d hd
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp
      (MvPolynomial.support_mul _ _ hd)
    rw [map_add]
    have h1 : Finsupp.weight wt d₁ ≤ e • wt B₀ := WithBot.coe_le_coe.mp
      ((σ.pol_weight_le_degree hx hpowα d₁ hd₁).trans hpow.degree_le)
    have h2 : Finsupp.weight wt d₂ ≤ m := WithBot.coe_le_coe.mp
      ((σ.pol_weight_le_degree hx huα d₂ hd₂).trans hu.lowerTruncationDegree.degree_le)
    exact (add_le_add h1 h2).trans_lt he
  rw [(σ.pol_mul hx hinj hpowα huα hprod).2,
    σ.pol_lift_pow hx hinj e (NatOrdinal.le_add_right.trans_lt he)]

omit [CharZero K] in
/-- Split a finite sum at two distinct members. -/
private theorem sum_eq_add_add_sum_erase {κ : Type*} [DecidableEq κ]
    {S : Finset κ} {a b : κ} (ha : a ∈ S) (hb : b ∈ S) (hne : b ≠ a)
    (f : κ → MvPolynomial ι K) :
    ∑ q ∈ S, f q = f a + f b + ∑ q ∈ (S.erase a).erase b, f q := by
  rw [add_assoc, Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, hb⟩),
    Finset.add_sum_erase _ _ ha]

open Classical in
/-- For `u` free of `B₀`, the polynomial of a proper truncation of `lift B₀ ^ e * u` has no
coefficient above `e`, and its coefficient at `e` is the polynomial of the same truncation of
`u`. -/
theorem xCoeff_pol_translatedTruncLE_lift_pow_mul
    (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {B₀ : ι} {u : Nonpositive G K} {m : NatOrdinal.{u}}
    (hB₀ : wt B₀ < α) (hu : FreeOfVariable σ hx α B₀ u m) (e : ℕ)
    (he : e • wt B₀ + m ≤ α) {γ : G} (hγ : γ < 0) :
    (∀ k, e < k →
      xCoeff B₀ k (σ.pol hx α (translatedTruncLE γ (σ.lift B₀ ^ e * u))) = 0) ∧
    xCoeff B₀ e (σ.pol hx α (translatedTruncLE γ (σ.lift B₀ ^ e * u))) =
      σ.pol hx α (translatedTruncLE γ u) := by
  classical
  induction e generalizing γ with
  | zero =>
      rw [pow_zero, one_mul]
      exact ⟨fun k hk ↦ by
        rw [xCoeff_of_mem_supported B₀ (hu.trunc_mem hγ) k, if_neg (Nat.ne_of_gt hk)],
        by rw [xCoeff_of_mem_supported B₀ (hu.trunc_mem hγ) 0, if_pos rfl]⟩
  | succ e ih =>
      have hg0 : wt B₀ ≠ 0 := hx.ne_zero B₀
      have hstep : e • wt B₀ + m < (e + 1) • wt B₀ + m := by
        rw [succ_nsmul, add_right_comm]
        exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hg0)
      have he' : e • wt B₀ + m < α := hstep.trans_le he
      have ih' := ih he'.le hγ
      have hright : Nonpositive.HasLowerTruncationDegree
          (σ.lift B₀ ^ e * u) (e • wt B₀ + m) :=
        (((hasLowerTruncationDegrees_iff σ).mp hσ B₀).pow e).mul rfl
          hu.lowerTruncationDegree
      have hconv := σ.pol_translatedTruncLE_mul_boundary hx hinj
        ((hasLowerTruncationDegrees_iff σ).mp hσ B₀) hright hB₀ he' (by
          rw [← add_assoc, add_comm (wt B₀), ← succ_nsmul]
          exact he) hγ
      set S := insert (0, γ) (insert (γ, 0)
        ((σ.lift B₀ : HahnSeries G K).closedSupportAddFiber
          ((σ.lift B₀ ^ e * u : Nonpositive G K) : HahnSeries G K) γ)) with hS
      set f : G × G → MvPolynomial ι K := fun q ↦
        σ.pol hx α (translatedTruncLE q.1 (σ.lift B₀)) *
          σ.pol hx α (translatedTruncLE q.2 (σ.lift B₀ ^ e * u)) with hf
      have h0S : (0, γ) ∈ S := Finset.mem_insert_self _ _
      have hγS : (γ, 0) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hne : (γ, 0) ≠ (0, γ) := fun h ↦ hγ.ne (congrArg Prod.fst h)
      have hsplit : ∑ q ∈ S, f q = f (0, γ) + f (γ, 0) +
          ∑ q ∈ (S.erase (0, γ)).erase (γ, 0), f q :=
        sum_eq_add_add_sum_erase h0S hγS hne f
      have hpowmul := hu.pol_lift_pow_mul hσ hinj e he'
      have hf0 : f (0, γ) = X B₀ * σ.pol hx α
          (translatedTruncLE γ (σ.lift B₀ ^ e * u)) := by
        rw [hf]
        change σ.pol hx α (translatedTruncLE 0 (σ.lift B₀)) *
          σ.pol hx α (translatedTruncLE γ (σ.lift B₀ ^ e * u)) = _
        rw [translatedTruncLE_zero, σ.pol_lift hx hinj hB₀]
      have hfγ : f (γ, 0) = σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) *
          (X B₀ ^ e * σ.pol hx α u) := by
        rw [hf]
        change σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) *
          σ.pol hx α (translatedTruncLE 0 (σ.lift B₀ ^ e * u)) = _
        rw [translatedTruncLE_zero, hpowmul]
      have hinterior : ∀ q ∈ (S.erase (0, γ)).erase (γ, 0),
          q.1 < 0 ∧ q.2 < 0 ∧
            σ.pol hx α (translatedTruncLE q.1 (σ.lift B₀)) ∈ supported K {B₀}ᶜ := by
        intro q hq
        have hqneγ : q ≠ (γ, 0) := (Finset.mem_erase.mp hq).1
        have hqne0 : q ≠ (0, γ) := (Finset.mem_erase.mp
          (Finset.mem_erase.mp hq).2).1
        have hqmemS : q ∈ S := (Finset.mem_erase.mp
          (Finset.mem_erase.mp hq).2).2
        have hqmem : q ∈ (σ.lift B₀ : HahnSeries G K).closedSupportAddFiber
            ((σ.lift B₀ ^ e * u : Nonpositive G K) : HahnSeries G K) γ := by
          rw [hS] at hqmemS
          rcases Finset.mem_insert.mp hqmemS with hqeq | hqmemS
          · exact (hqne0 hqeq).elim
          rcases Finset.mem_insert.mp hqmemS with hqeq | hqmemS
          · exact (hqneγ hqeq).elim
          · exact hqmemS
        obtain ⟨hq1mem, hq2mem, hsum⟩ :=
          ((σ.lift B₀ : HahnSeries G K).mem_closedSupportAddFiber
            ((σ.lift B₀ ^ e * u : Nonpositive G K) : HahnSeries G K) γ q).mp hqmem
        have hq1le : q.1 ≤ 0 := closure_minimal (σ.lift B₀).property isClosed_Iic
          ((mem_closedSupport _ _).mp hq1mem)
        have hq2le : q.2 ≤ 0 := closure_minimal (σ.lift B₀ ^ e * u).property isClosed_Iic
          ((mem_closedSupport _ _).mp hq2mem)
        have hq1ne : q.1 ≠ 0 := fun hq10 ↦ hqne0 (Prod.ext hq10 (by
          simpa [hq10] using hsum))
        have hq2ne : q.2 ≠ 0 := fun hq20 ↦ hqneγ (Prod.ext (by
          simpa [hq20] using hsum) hq20)
        have hq1neg : q.1 < 0 := lt_of_le_of_ne hq1le hq1ne
        have hq2neg : q.2 < 0 := lt_of_le_of_ne hq2le hq2ne
        exact ⟨hq1neg, hq2neg,
          σ.pol_translatedTruncLE_lift_mem_supported hx hσ hB₀ le_rfl hq1neg⟩
      have hfhigh : ∀ q ∈ (S.erase (0, γ)).erase (γ, 0), ∀ k, e < k →
          xCoeff B₀ k (f q) = 0 := by
        intro q hq k hk
        have hiq := ih he'.le (hinterior q hq).2.1
        rw [hf, xCoeff_mul_of_mem_supported B₀ (hinterior q hq).2.2 k,
          hiq.1 k hk, mul_zero]
      have hexp : σ.lift B₀ ^ (e + 1) * u =
          σ.lift B₀ * (σ.lift B₀ ^ e * u) := by ring
      rw [hexp, hconv, hsplit, hf0, hfγ]
      refine ⟨fun k hk ↦ ?_, ?_⟩
      · rw [map_add, map_add, map_sum,
          Finset.sum_eq_zero fun q hq ↦ hfhigh q hq k (by omega)]
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [xCoeff_succ_X_mul, ih'.1 k' (by omega), ← mul_assoc,
          show σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) * X B₀ ^ e *
              σ.pol hx α u =
            (σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) * σ.pol hx α u) *
              X B₀ ^ e by ring,
          xCoeff_mul_X_pow B₀ (Subalgebra.mul_mem _
            (σ.pol_translatedTruncLE_lift_mem_supported hx hσ hB₀ le_rfl hγ)
            hu.pol_mem) (k' + 1) e, if_neg (by omega), add_zero, add_zero]
      · rw [map_add, map_add, map_sum,
          Finset.sum_eq_zero fun q hq ↦ hfhigh q hq (e + 1) (Nat.lt_succ_self e),
          xCoeff_succ_X_mul, ih'.2, ← mul_assoc,
          show σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) * X B₀ ^ e *
              σ.pol hx α u =
            (σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) * σ.pol hx α u) *
              X B₀ ^ e by ring,
          xCoeff_mul_X_pow B₀ (Subalgebra.mul_mem _
            (σ.pol_translatedTruncLE_lift_mem_supported hx hσ hB₀ le_rfl hγ)
            hu.pol_mem) (e + 1) e, if_neg (Nat.succ_ne_self e), add_zero, add_zero]

/-- A proper truncation of the evaluation of a top-degree homogeneous polynomial which omits
`B₀` and uses no heavier variable still has a representing polynomial which omits `B₀`. -/
theorem pol_translatedTruncLE_aeval_mem_supported
    (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {B₀ : ι} (hB₀ : wt B₀ < α) {F : MvPolynomial ι K}
    (hF : IsWeightedHomogeneous wt F α) (hmem : F ∈ supported K {B₀}ᶜ)
    (hle : ∀ i ∈ F.vars, wt i ≤ wt B₀) {γ : G} (hγ : γ < 0) :
    σ.pol hx α (translatedTruncLE γ (MvPolynomial.aeval σ.lift F)) ∈
      supported K {B₀}ᶜ := by
  classical
  have hα0 : α ≠ 0 := ne_of_gt ((zero_le : (0 : NatOrdinal) ≤ wt B₀).trans_lt hB₀)
  have hterm : ∀ d ∈ F.support,
      σ.pol hx α (translatedTruncLE γ
        (MvPolynomial.aeval σ.lift (monomial d (MvPolynomial.coeff d F)))) ∈
          supported K {B₀}ᶜ := by
    intro d hd
    have hdw : Finsupp.weight wt d = α := hF (mem_support_iff.mp hd)
    have hd0 : d B₀ = 0 := by
      by_contra h0
      exact (mem_supported.mp hmem) ((mem_vars_iff_mem_support B₀).mpr
        ⟨d, hd, Finsupp.mem_support_iff.mpr h0⟩) rfl
    have hdne : d ≠ 0 := by
      rintro rfl
      rw [map_zero] at hdw
      exact hα0 hdw.symm
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hdne
    have hi0 : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hiB₀ : i ≠ B₀ := fun h ↦ hi0 (h ▸ hd0)
    have hiwt : wt i ≤ wt B₀ :=
      hle i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)
    set d' := d - Finsupp.single i 1 with hd'
    have hdd' : d = Finsupp.single i 1 + d' := by
      rw [hd', add_comm, tsub_add_cancel_of_le]
      intro j
      rw [Finsupp.single_apply]
      split_ifs with hji
      · subst j
        exact Nat.pos_of_ne_zero hi0
      · exact Nat.zero_le _
    have hweight : wt i + Finsupp.weight wt d' = α := by
      rw [← hdw, hdd', map_add, Finsupp.weight_single, one_smul]
    have hiα : wt i < α := hiwt.trans_lt hB₀
    have hd'α : Finsupp.weight wt d' < α := by
      rw [← hweight]
      exact lt_add_of_pos_left _ (pos_iff_ne_zero.mpr (hx.ne_zero i))
    have hd'0 : d' B₀ = 0 := by
      rw [hd', Finsupp.tsub_apply, hd0, zero_tsub]
    have hd'wt : ∀ j ∈ d'.support, wt j ≤ wt B₀ := fun j hj ↦
      hle j ((mem_vars_iff_mem_support j).mpr ⟨d, hd, Finsupp.support_tsub hj⟩)
    have hfreei := FreeOfVariable.lift (σ := σ) (hx := hx) hσ hinj hiB₀ hiwt hB₀
    have hfreed := FreeOfVariable.aeval_monomial (σ := σ) (hx := hx) hσ hinj hB₀
      d' hd'0 hd'wt hd'α
    have hsplit : MvPolynomial.aeval σ.lift (monomial d (1 : K)) =
        σ.lift i * MvPolynomial.aeval σ.lift (monomial d' (1 : K)) := by
      rw [hdd', add_comm, monomial_add_single, pow_one, map_mul, aeval_X, mul_comm]
    have hconv := σ.pol_translatedTruncLE_mul hx hinj hfreei.lowerTruncationDegree
      hfreed.lowerTruncationDegree
      hiα hd'α hweight.le hγ
    have hone : σ.pol hx α (translatedTruncLE γ
        (MvPolynomial.aeval σ.lift (monomial d (1 : K)))) ∈ supported K {B₀}ᶜ := by
      rw [hsplit, hconv]
      refine Subalgebra.sum_mem _ fun q hq ↦ Subalgebra.mul_mem _ ?_ ?_
      · exact hfreei.pol_trunc_mem_nonpos (closure_minimal (σ.lift i).property isClosed_Iic
          ((mem_closedSupport _ _).mp (((σ.lift i : HahnSeries G K).mem_closedSupportAddFiber
            ((MvPolynomial.aeval σ.lift (monomial d' (1 : K)) : Nonpositive G K) :
              HahnSeries G K) γ q).mp
              hq).1))
      · exact hfreed.pol_trunc_mem_nonpos
          (closure_minimal (MvPolynomial.aeval σ.lift (monomial d' (1 : K))).property
            isClosed_Iic
            ((mem_closedSupport _ _).mp (((σ.lift i : HahnSeries G K).mem_closedSupportAddFiber
              ((MvPolynomial.aeval σ.lift (monomial d' (1 : K)) : Nonpositive G K) :
                HahnSeries G K) γ q).mp
                hq).2.1))
    have hmono : (monomial d (MvPolynomial.coeff d F) : MvPolynomial ι K) =
        MvPolynomial.C (MvPolynomial.coeff d F) * monomial d (1 : K) := by
      rw [C_mul_monomial, mul_one]
    rw [hmono, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      translatedTruncLE_smul, σ.pol_smul hx hinj]
    · exact Subalgebra.smul_mem _ hone _
    · exact (σ.hasLowerTruncationDegree_aeval hσ
        (isWeightedHomogeneous_monomial wt d (1 : K) hdw)).degree_translatedTruncLE_lt hγ
  have hexp : MvPolynomial.aeval σ.lift F = ∑ d ∈ F.support,
      MvPolynomial.aeval σ.lift (monomial d (MvPolynomial.coeff d F)) := by
    conv_lhs => rw [F.as_sum]
    rw [map_sum]
  rw [hexp, map_sum, σ.pol_sum hx hinj _ _ (fun d hd ↦ by
    have hp := σ.hasLowerTruncationDegree_aeval hσ (isWeightedHomogeneous_monomial wt d
      (MvPolynomial.coeff d F) (hF (mem_support_iff.mp hd)))
    exact hp.degree_translatedTruncLE_lt hγ)]
  exact Subalgebra.sum_mem _ fun d hd ↦ hterm d hd

open Classical in
/-- The coefficient one below the top in a proper truncation of `lift B₀ ^ (e + 1)` is
`(e + 1)` times the polynomial of the truncated lift. -/
theorem xCoeff_pol_translatedTruncLE_lift_pow
    (hσ : HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {B₀ : ι} (hB₀ : wt B₀ < α) (e : ℕ)
    (he : (e + 1) • wt B₀ ≤ α) {γ : G} (hγ : γ < 0) :
    xCoeff B₀ e (σ.pol hx α (translatedTruncLE γ (σ.lift B₀ ^ (e + 1)))) =
      (e + 1 : ℕ) • σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) := by
  classical
  induction e generalizing γ with
  | zero =>
      rw [zero_add, pow_one, xCoeff_of_mem_supported B₀
        (σ.pol_translatedTruncLE_lift_mem_supported hx hσ hB₀ le_rfl hγ) 0,
        if_pos rfl, one_smul]
  | succ e ih =>
      have hg0 : wt B₀ ≠ 0 := hx.ne_zero B₀
      have hstep : (e + 1) • wt B₀ < (e + 1 + 1) • wt B₀ := by
        rw [succ_nsmul]
        exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hg0)
      have he' : (e + 1) • wt B₀ < α := hstep.trans_le he
      have hα0 : 0 < α := (zero_le : (0 : NatOrdinal) ≤ wt B₀).trans_lt hB₀
      have hone := FreeOfVariable.one (σ := σ) (hx := hx) hα0 hinj (B₀ := B₀)
      have hright : Nonpositive.HasLowerTruncationDegree
          (σ.lift B₀ ^ (e + 1)) ((e + 1) • wt B₀) :=
        ((hasLowerTruncationDegrees_iff σ).mp hσ B₀).pow (e + 1)
      have hconv := σ.pol_translatedTruncLE_mul_boundary hx hinj
        ((hasLowerTruncationDegrees_iff σ).mp hσ B₀) hright hB₀ he' (by
          rw [add_comm, ← succ_nsmul]
          exact he) hγ
      set S := insert (0, γ) (insert (γ, 0)
        ((σ.lift B₀ : HahnSeries G K).closedSupportAddFiber
          ((σ.lift B₀ ^ (e + 1) : Nonpositive G K) : HahnSeries G K) γ)) with hS
      set f : G × G → MvPolynomial ι K := fun q ↦
        σ.pol hx α (translatedTruncLE q.1 (σ.lift B₀)) *
          σ.pol hx α (translatedTruncLE q.2 (σ.lift B₀ ^ (e + 1))) with hf
      have h0S : (0, γ) ∈ S := Finset.mem_insert_self _ _
      have hγS : (γ, 0) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hne : (γ, 0) ≠ (0, γ) := fun h ↦ hγ.ne (congrArg Prod.fst h)
      have hsplit : ∑ q ∈ S, f q = f (0, γ) + f (γ, 0) +
          ∑ q ∈ (S.erase (0, γ)).erase (γ, 0), f q :=
        sum_eq_add_add_sum_erase h0S hγS hne f
      have hf0 : f (0, γ) = X B₀ *
          σ.pol hx α (translatedTruncLE γ (σ.lift B₀ ^ (e + 1))) := by
        rw [hf]
        change σ.pol hx α (translatedTruncLE 0 (σ.lift B₀)) * _ = _
        rw [translatedTruncLE_zero, σ.pol_lift hx hinj hB₀]
      have hfγ : f (γ, 0) = σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) *
          X B₀ ^ (e + 1) := by
        rw [hf]
        change σ.pol hx α (translatedTruncLE γ (σ.lift B₀)) *
          σ.pol hx α (translatedTruncLE 0 (σ.lift B₀ ^ (e + 1))) = _
        rw [translatedTruncLE_zero, σ.pol_lift_pow hx hinj (e + 1) he']
      have hinterior : ∀ q ∈ (S.erase (0, γ)).erase (γ, 0),
          q.1 < 0 ∧ q.2 < 0 ∧
            σ.pol hx α (translatedTruncLE q.1 (σ.lift B₀)) ∈ supported K {B₀}ᶜ := by
        intro q hq
        have hqneγ : q ≠ (γ, 0) := (Finset.mem_erase.mp hq).1
        have hqne0 : q ≠ (0, γ) := (Finset.mem_erase.mp
          (Finset.mem_erase.mp hq).2).1
        have hqmemS : q ∈ S := (Finset.mem_erase.mp
          (Finset.mem_erase.mp hq).2).2
        have hqmem : q ∈ (σ.lift B₀ : HahnSeries G K).closedSupportAddFiber
            ((σ.lift B₀ ^ (e + 1) : Nonpositive G K) : HahnSeries G K) γ := by
          rw [hS] at hqmemS
          rcases Finset.mem_insert.mp hqmemS with hqeq | hqmemS
          · exact (hqne0 hqeq).elim
          rcases Finset.mem_insert.mp hqmemS with hqeq | hqmemS
          · exact (hqneγ hqeq).elim
          · exact hqmemS
        obtain ⟨hq1mem, hq2mem, hsum⟩ :=
          ((σ.lift B₀ : HahnSeries G K).mem_closedSupportAddFiber
            ((σ.lift B₀ ^ (e + 1) : Nonpositive G K) : HahnSeries G K) γ q).mp hqmem
        have hq1le : q.1 ≤ 0 := closure_minimal (σ.lift B₀).property isClosed_Iic
          ((mem_closedSupport _ _).mp hq1mem)
        have hq2le : q.2 ≤ 0 := closure_minimal (σ.lift B₀ ^ (e + 1)).property isClosed_Iic
          ((mem_closedSupport _ _).mp hq2mem)
        have hq1ne : q.1 ≠ 0 := fun hq10 ↦ hqne0 (Prod.ext hq10 (by
          simpa [hq10] using hsum))
        have hq2ne : q.2 ≠ 0 := fun hq20 ↦ hqneγ (Prod.ext (by
          simpa [hq20] using hsum) hq20)
        have hq1neg : q.1 < 0 := lt_of_le_of_ne hq1le hq1ne
        have hq2neg : q.2 < 0 := lt_of_le_of_ne hq2le hq2ne
        exact ⟨hq1neg, hq2neg,
          σ.pol_translatedTruncLE_lift_mem_supported hx hσ hB₀ le_rfl hq1neg⟩
      have hfzero : ∀ q ∈ (S.erase (0, γ)).erase (γ, 0),
          xCoeff B₀ (e + 1) (f q) = 0 := by
        intro q hq
        have htopq := FreeOfVariable.xCoeff_pol_translatedTruncLE_lift_pow_mul
          (σ := σ) (hx := hx) hσ hinj hB₀ hone (e + 1) (by simpa using he'.le)
          (hinterior q hq).2.1
        rw [mul_one] at htopq
        have hpone : σ.pol hx α (translatedTruncLE q.2 (1 : Nonpositive G K)) = 0 := by
          rw [FreeOfVariable.translatedTruncLE_one (hinterior q hq).2.1,
            σ.pol_eq_zero_of_degree_eq_bot hx (by rw [(ν).map_zero])]
        rw [hf, xCoeff_mul_of_mem_supported B₀ (hinterior q hq).2.2 (e + 1),
          htopq.2, hpone, mul_zero]
      have hexp : σ.lift B₀ ^ (e + 1 + 1) =
          σ.lift B₀ * σ.lift B₀ ^ (e + 1) := by ring
      rw [hexp, hconv, hsplit, hf0, hfγ, map_add, map_add, map_sum,
        Finset.sum_eq_zero hfzero, add_zero, xCoeff_succ_X_mul, ih he'.le hγ,
        xCoeff_mul_X_pow B₀
          (σ.pol_translatedTruncLE_lift_mem_supported hx hσ hB₀ le_rfl hγ)
          (e + 1) (e + 1), if_pos rfl]
      exact (succ_nsmul _ (e + 1)).symm

end FreeOfVariable

end LiftFamily

end HahnSeries.Nonpositive

end
