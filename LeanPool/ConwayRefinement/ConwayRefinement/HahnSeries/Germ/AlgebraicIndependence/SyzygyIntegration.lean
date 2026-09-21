/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermSyzygy
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.DerivationSet
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LiftFamily
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.CantorBendixsonRankLevels
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.FinitePWOUnion

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Successor syzygy integration for the Cantor–Bendixson derivation

The abstract successor induction asks for a pointwise representative of the derivative of a
finite homogeneous tuple, supported on one set on which arbitrary homogeneous functions can be
integrated. For the Cantor–Bendixson derivation the set is the finite union, above a common negative
cutoff, of the exact-rank levels of representatives of the tuple entries.

That union is discrete and partially well ordered. Near zero its closure adds no points, so the
integration theorem for discrete cutoff sets realizes arbitrary homogeneous values on it. Tuple
coordinates with no positive forced degree have zero derivative and need no level.
-/

universe u v w

open scoped NatOrdinal Topology

open Filter Set HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

/-- Successor syzygy integration for the Cantor–Bendixson derivation. -/
@[blueprint "lem:simultaneous-cantor-bendixson-derivative-representatives"
  (phase := "Algebraic independence in graded rings")
  (title := "Simultaneous Cantor--Bendixson derivatives of homogeneous tuples")
  (statement := /--
    Let $B$ be finite, let $\lambda_b$ be ordinal weights, and let $(u_b)$ be
    homogeneous of total degree $d$, where the constant Cantor coefficient of
    $d$ is positive.  There are a set $S\subseteq G$ and functions
    $D_b:G\to\operatorname{gr}_\nu$ such that:
    \begin{enumerate}
    \item the derivative of $u_b$ agrees near $0$ with $D_b$;
    \item for every $\gamma$, $(D_b(\gamma))_b$ is homogeneous of total
      degree $d'$, where $d'+1=d$;
    \item every $D_b$ vanishes outside $S$;
    \item for every homogeneous function $a:G\to\operatorname{gr}_\nu$ of
      degree $\rho$, some homogeneous class of degree $\rho+1$ has derivative
      equal near $0$ to $a$ on $S$ and to zero outside $S$.
    \end{enumerate}
  -/)
  (proof := /--
    Choose a series representative for each active coordinate of the tuple.
    Its derivative is supported near $0$ on one exact-rank set.  By
    \ref{lem:discrete-finite-union-cantor-bendixson-rank-sets}, after one
    common negative cutoff the union $S$ of these finitely many sets is
    discrete.  The pointwise derivative tuple has predecessor degree $d'$ and
    vanishes outside $S$; the operator used here is a derivation by
    \ref{lem:cantor-bendixson-derivation-leibniz}.  The union is partially
    well ordered and agrees near $0$ with its closure, so
    \ref{lem:prescribed-cantor-bendixson-derivative-discrete-set} realizes
    every homogeneous prescription on $S$ in degree one higher.
  -/)]
theorem hasSyzygyIntegration {B : Type w} [Finite B] (lam : B → NatOrdinal.{u}) :
    OrdinalGraded.HasSyzygyIntegration
      (DirectSum.rangeLof K (ν).Component) cantorBendixsonDerivation lam (T := G) := by
  classical
  rw [OrdinalGraded.hasSyzygyIntegration_iff]
  intro d hd u hu
  let active : Set B := {b | ∃ β, β + lam b = d ∧ 0 < β.constantCoeff}
  have hdegree : ∀ b : ↥active, ∃ β, β + lam b = d ∧ 0 < β.constantCoeff :=
    fun b ↦ b.property
  choose β hβ hβpos using hdegree
  have hlift : ∀ b : ↥active, ∃ p : Nonpositive G K, Represents p (β b) (u b) :=
    fun b ↦ exists_represents (hu.mem (hβ b))
  choose p hp using hlift
  let ρ : ↥active → NatOrdinal.{u} := fun b ↦ (β b).removeNat 1
  have hρsucc : ∀ b, ρ b + 1 = β b := fun b ↦ by
    simpa only [ρ, Nat.cast_one] using NatOrdinal.removeNat_add_natCast (hβpos b)
  obtain ⟨η, hη0, hdisc⟩ := exists_isDiscrete_iUnion_rankLevelSet p ρ (fun b ↦ by
    rw [hρsucc]
    exact hp b |>.degree_le)
  let S : Set G := ⋃ b : ↥active, rankLevelSet (p b) (ρ b) ∩ Ioo η 0
  let D : B → G → (ν).AssociatedGraded := fun b γ ↦
    if hb : b ∈ active then
      if γ ∈ S then DirectSum.of (ν).Component (ρ ⟨b, hb⟩)
        (cantorBendixsonDerivAt (ρ ⟨b, hb⟩) (p ⟨b, hb⟩) γ) else 0
    else 0
  refine ⟨S, D, ?_, ?_, ?_, ?_⟩
  · intro b
    by_cases hb : b ∈ active
    · let b' : ↥active := ⟨b, hb⟩
      obtain ⟨hpdeg, hpu⟩ := represents_iff.mp (hp b')
      rw [← hpu, cantorBendixsonDerivation_apply,
        cantorBendixsonGradedDerivation_homogeneousMk_succ (ρ b') (hρsucc b').symm]
      rw [Filter.Germ.coe_eq]
      have hIoo : ∀ᶠ γ in nhdsWithin (0 : G) (Iio 0), γ ∈ Ioo η 0 :=
        eventually_nhdsLT_iff_exists.mpr ⟨η, hη0, fun γ hγη hγ0 ↦ ⟨hγη, hγ0⟩⟩
      filter_upwards [hIoo,
        eventually_degree_translatedTruncLE_le (p b') (ρ b') (by
          rw [hρsucc]
          exact hpdeg)] with γ hγI hγdeg
      simp only [D, dif_pos hb]
      by_cases hne : cantorBendixsonDerivAt (ρ b') (p b') γ ≠ 0
      · rw [if_pos]
        refine mem_iUnion_of_mem b' ⟨?_, hγI⟩
        rw [mem_rankLevelSet_iff, ← cantorBendixsonRank_eq]
        exact (cantorBendixsonDerivAt_ne_zero_iff _ _ _ hγdeg).mp hne
      · have hz : cantorBendixsonDerivAt (ρ b') (p b') γ = 0 := not_ne_iff.mp hne
        rw [hz, map_zero]
        split <;> rfl
    · have hDzero : D b = 0 := by
        funext γ
        simp only [D, dif_neg hb, Pi.zero_apply]
      rw [hDzero, Filter.Germ.coe_zero]
      by_cases hex : ∃ β, β + lam b = d
      · obtain ⟨β', hβ'⟩ := hex
        have hβ'zero : β'.constantCoeff = 0 := by
          by_contra hn
          exact hb ⟨β', hβ', pos_iff_ne_zero.mpr hn⟩
        rw [cantorBendixsonDerivation_apply]
        exact cantorBendixsonGradedDerivation_eq_zero_of_constantCoeff_eq_zero
          hβ'zero (hu.mem hβ')
      · rw [hu.eq_zero hex, map_zero]
  · intro γ
    rw [OrdinalGraded.isHomogeneousTuple_iff]
    intro b
    refine ⟨fun κ hκ ↦ ?_, fun hn ↦ ?_⟩
    · by_cases hb : b ∈ active
      · let b' : ↥active := ⟨b, hb⟩
        have hρ : ρ b' = κ := by
          apply add_right_cancel (b := lam b)
          have hleft : ρ b' + lam b = d.removeNat 1 := by
            rw [← NatOrdinal.removeNat_add_right (β b') (lam b) (hβpos b'), hβ]
          exact hleft.trans hκ.symm
        simp only [D, dif_pos hb]
        split
        · rw [← hρ]
          exact DirectSum.of_mem_rangeLof K (ν).Component (ρ b') _
        · exact zero_mem _
      · simp only [D, dif_neg hb]
        exact zero_mem _
    · by_cases hb : b ∈ active
      · exact (hn ⟨ρ ⟨b, hb⟩, by
          rw [← NatOrdinal.removeNat_add_right (β ⟨b, hb⟩) (lam b) (hβpos ⟨b, hb⟩), hβ]⟩).elim
      · simp only [D, dif_neg hb]
  · intro b γ hγ
    simp only [D]
    split <;> rfl
  · intro τ a ha
    have hSneg : S ⊆ Iic (0 : G) := by
      rintro γ hγ
      obtain ⟨b, hb⟩ := mem_iUnion.mp hγ
      exact hb.2.2.le
    have hSpwo : (Set.univ : Set ↥S).IsPWO := by
      have hunion : S.IsPWO := Set.IsPWO.iUnion_of_finite
        (fun b : ↥active ↦ rankLevelSet (p b) (ρ b) ∩ Ioo η 0) (fun b ↦
          (p b : HahnSeries G K).closedSupport_isPWO.mono fun γ hγ ↦
            ((mem_rankLevelSet_iff (p := p b) (α := ρ b)).mp hγ.1).1)
      rw [Set.isPWO_iff_exists_monotone_subseq]
      intro f _
      obtain ⟨g, hg⟩ := hunion.exists_monotone_subseq fun n ↦ (f n).2
      exact ⟨g, fun i j hij ↦ Subtype.coe_le_coe.mp (hg hij)⟩
    have hnear : ∀ᶠ γ in nhdsWithin (0 : G) (Iio 0), γ ∈ closure S → γ ∈ S := by
      change ∀ᶠ γ in nhdsWithin (0 : G) (Iio 0),
        γ ∈ closure (⋃ b : ↥active, rankLevelSet (p b) (ρ b) ∩ Ioo η 0) →
          γ ∈ ⋃ b : ↥active, rankLevelSet (p b) (ρ b) ∩ Ioo η 0
      rw [closure_iUnion_of_finite]
      have hall : ∀ᶠ γ in nhdsWithin (0 : G) (Iio 0), ∀ b : ↥active,
          γ ∈ closure (rankLevelSet (p b) (ρ b) ∩ Ioo η 0) →
            γ ∈ rankLevelSet (p b) (ρ b) ∩ Ioo η 0 := by
        rw [Filter.eventually_all]
        intro b
        have hIoo : ∀ᶠ γ in nhdsWithin (0 : G) (Iio 0), γ ∈ Ioo η 0 :=
          eventually_nhdsLT_iff_exists.mpr
            ⟨η, hη0, fun γ hγη hγ0 ↦ ⟨hγη, hγ0⟩⟩
        filter_upwards [eventually_mem_rankLevelSet_of_mem_closure (p b) (ρ b) (by
            rw [hρsucc]
            exact hp b |>.degree_le),
          hIoo] with γ hrank hγIoo hclose
        exact ⟨hrank (closure_mono inter_subset_left hclose), hγIoo⟩
      filter_upwards [hall] with γ hγ hclose
      obtain ⟨b, hb⟩ := mem_iUnion.mp hclose
      exact mem_iUnion_of_mem b (hγ b hb)
    obtain ⟨s, hs, hderiv⟩ := exists_derivation_eq_of_isDiscrete τ S hSneg hSpwo
      (by simpa only [S] using hdisc) hnear a ha
    refine ⟨s, hs, fun γ ↦ if γ ∈ S then a γ else 0, ?_, ?_, ?_⟩
    · rw [cantorBendixsonDerivation_apply]
      exact hderiv
    · intro γ hγ
      simp only [if_pos hγ]
    · intro γ hγ
      simp only [if_neg hγ]

end HahnSeries.Nonpositive

end
