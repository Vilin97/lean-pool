/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Lifts
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LowerTruncationDegree
public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TranslatedTruncationInterpolation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.CofactorInduction

/-!
# A family of series lifting a family of homogeneous classes

The limit step of the polynomiality induction works with series representatives of the generators
rather than with the generators themselves, so that truncations and their degrees are available.
This module bundles such a choice: a series for each generator, lifting it in its own degree.

Lifts exist for any family of homogeneous classes, because every class of degree at most `m` is the
class of a series in the weight filtration at `m`. Evaluating a weighted homogeneous polynomial at
the lifts again lifts the evaluation at the generators, which is what makes the bundle useful.
-/

universe u v w

open scoped NatOrdinal

open MvPolynomial

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

/-- Every homogeneous class is the class of a series in the corresponding weight filtration. -/
theorem exists_represents {m : NatOrdinal.{u}} {e : (ν).AssociatedGraded}
    (he : e ∈ DirectSum.rangeLof K (ν).Component m) :
    ∃ b : Nonpositive G K, Represents b m e := by
  obtain ⟨a, ha⟩ := (DirectSum.mem_rangeLof_iff K (ν).Component m e).mp he
  rw [DirectSum.lof_eq_of] at ha
  induction a using MaxAddDegree.componentInductionOn with
  | H p =>
    refine ⟨(p : Nonpositive G K), represents_iff.mpr
      ⟨((ν).mem_filtrationLE_iff m _).mp p.2, ?_⟩⟩
    rw [← ha, MaxAddDegree.homogeneousMk_apply]

/-- A series bounded strictly below zero has bottom degree. -/
theorem degree_eq_bot_of_support_subset_Iic {b : Nonpositive G K} {c : G} (hc : c < 0)
    (hb : (b : HahnSeries G K).support ⊆ Set.Iic c) : ν b = ⊥ := by
  have hclosed : (0 : G) ∉ closure (b : HahnSeries G K).support := by
    intro h0
    exact absurd (isClosed_Iic.closure_subset_iff.mpr hb h0) (not_le.mpr hc)
  rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
    cantorBendixsonValue_of_notMem _ hclosed, NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]

open Classical in
/-- **Every homogeneous class has a representative with the required truncation bounds.**
Cutting a representative below a negative bound leaves the class unchanged, because the discarded
part is bounded strictly below zero and so has bottom degree. Choose the bound past which every
proper translated truncation already drops. Above it, the chosen drop applies; at or below it, the
truncation is empty. -/
theorem exists_representative_hasLowerTruncationDegree
    {m : NatOrdinal.{u}} {e : (ν).AssociatedGraded}
    (he : e ∈ DirectSum.rangeLof K (ν).Component m) :
    ∃ b : Nonpositive G K, Represents b m e ∧ HasLowerTruncationDegree b m := by
  obtain ⟨a, ha⟩ := (DirectSum.mem_rangeLof_iff K (ν).Component m e).mp he
  rw [DirectSum.lof_eq_of] at ha
  obtain ⟨d, hd⟩ : ∃ d : G, d < 0 := exists_lt (0 : G)
  obtain ⟨w, c, hw, -, hc0, hwa, hdrop⟩ := exists_representative_with_lower_truncation_degree m a hd
  -- the part of `w` strictly above the cutoff
  obtain ⟨b, hbdef⟩ : ∃ b : Nonpositive G K,
      (b : HahnSeries G K) = truncGT c (w : HahnSeries G K) :=
    ⟨⟨truncGT c (w : HahnSeries G K), fun g hg ↦ w.property (support_truncGT_subset c _ hg)⟩, rfl⟩
  -- what was cut off is bounded strictly below zero
  have hcut : ∀ γ : G, c < γ → γ ≤ 0 →
      ν (translatedTruncLE γ (w - b)) = ⊥ := by
    intro γ hcγ hγ
    refine degree_eq_bot_of_support_subset_Iic (c := c - γ) (by
      simpa using sub_neg.mpr hcγ) ?_
    intro g hg
    have hg' : g + γ ∈ ((w : HahnSeries G K) - (b : HahnSeries G K)).support := by
      have hcoe : ((translatedTruncLE γ (w - b) : Nonpositive G K) : HahnSeries G K) =
          translate (-γ) (truncLE γ ((w : HahnSeries G K) - (b : HahnSeries G K))) :=
        coe_translatedTruncLE γ (w - b)
      rw [hcoe, mem_support, HahnSeries.coeff_translate, HahnSeries.coeff_truncLE] at hg
      split_ifs at hg with hle
      · exact (mem_support _ _).mpr (by simpa using hg)
      · exact absurd rfl hg
    have hcoeff : ((w : HahnSeries G K) - (b : HahnSeries G K)).coeff (g + γ) ≠ 0 :=
      (mem_support _ _).mp hg'
    rw [HahnSeries.coeff_sub, hbdef, HahnSeries.coeff_truncGT] at hcoeff
    have hle : g + γ ≤ c := by
      by_contra hn
      rw [ite_eq_left (not_le.mp hn), sub_self] at hcoeff
      exact hcoeff rfl
    simpa using sub_le_sub_right hle γ
  have hsub : ν ((w : Nonpositive G K) - b) = ⊥ := by
    have h := hcut 0 hc0 le_rfl
    rwa [translatedTruncLE_zero] at h
  have hbw : ν b ≤ m := by
    have heq := degree_eq_of_degree_sub_eq_bot hsub
    rwa [heq] at hw
  refine ⟨b, represents_iff.mpr ⟨hbw, ?_⟩, hasLowerTruncationDegree_iff.mpr ⟨hbw, fun y hy ↦ ?_⟩⟩
  · rw [← ha, ← hwa]
    refine (MaxAddDegree.homogeneousMk_apply _ _ _).trans ?_
    congr 1
    refine ((ν).componentMk_eq_componentMk_iff m _ _).mpr ?_
    rw [show ((b : Nonpositive G K) : Nonpositive G K) - (w : Nonpositive G K) =
      -((w : Nonpositive G K) - b) by ring, (ν).map_neg, hsub]
    exact bot_lt_iff_ne_bot.mpr (by simp)
  · by_cases hyc : c < y
    · have hdiff := hcut y hyc hy.le
      have heq := degree_eq_of_degree_sub_eq_bot (a := translatedTruncLE y (w : Nonpositive G K))
        (b := translatedTruncLE y b) (by rw [← map_sub]; exact hdiff)
      rw [← heq]
      exact hdrop y hyc hy
    · have hzero : translatedTruncLE y b = 0 := by
        apply Subtype.ext
        ext g
        have hcoe : ((translatedTruncLE y b : Nonpositive G K) : HahnSeries G K) =
            translate (-y) (truncLE y (b : HahnSeries G K)) := coe_translatedTruncLE y b
        rw [hcoe, HahnSeries.coeff_translate, HahnSeries.coeff_truncLE, hbdef,
          HahnSeries.coeff_truncGT]
        split_ifs with h1 h2
        · exact absurd h2 (not_lt.mpr (le_trans (by simpa using h1) (not_lt.mp hyc)))
        · rfl
        · rfl
      rw [hzero, (ν).map_zero]
      exact bot_lt_iff_ne_bot.mpr (by simp)

variable {ι : Type w}

/-- Series representing a family of homogeneous classes, each in its own degree. -/
abbrev LiftFamily (wt : ι → NatOrdinal.{u})
    (x : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded) :=
  MaxAddDegree.LiftFamily (cantorBendixsonDegreeValuation (G := G) (R := K)) wt x

variable {wt : ι → NatOrdinal.{u}}
  {x : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded}

/-- Lifts exist for every family of homogeneous classes. -/
theorem nonempty_liftFamily (hmem : ∀ i, x i ∈ DirectSum.rangeLof K (ν).Component (wt i)) :
    Nonempty (LiftFamily wt x) := by
  choose b hb using fun i ↦ exists_represents (hmem i)
  exact ⟨⟨b, hb⟩⟩

namespace LiftFamily

variable (σ : LiftFamily wt x)

/-- Evaluating a weighted homogeneous polynomial at the lifts lifts the evaluation at the
classes. -/
theorem represents_aeval {F : MvPolynomial ι K} {β : NatOrdinal.{u}}
    (hF : IsWeightedHomogeneous wt F β) :
    Represents (aeval σ.lift F) β (aeval x F) :=
  Nonpositive.represents_aeval x σ.represents hF

/-- A relation evaluates at the lifts to a series of degree strictly below its own. -/
theorem degree_aeval_lt_of_aeval_eq_zero {F : MvPolynomial ι K} {β : NatOrdinal.{u}}
    (hF : IsWeightedHomogeneous wt F β) (h : aeval x F = 0) :
    ν (aeval σ.lift F) < (β : WithBot NatOrdinal.{u}) :=
  Represents.degree_lt_of_eq_zero (h ▸ σ.represents_aeval hF)

/-- Every representative satisfies the degree and proper-truncation bounds assigned to its
class. -/
def HasLowerTruncationDegrees (σ : LiftFamily wt x) : Prop :=
  ∀ i, Nonpositive.HasLowerTruncationDegree (σ.lift i) (wt i)

theorem hasLowerTruncationDegrees_iff (σ : LiftFamily wt x) :
    HasLowerTruncationDegrees σ ↔ ∀ i, Nonpositive.HasLowerTruncationDegree (σ.lift i) (wt i) :=
  Iff.rfl

/-- Evaluating a weighted homogeneous polynomial preserves the assigned lower-truncation
degree. -/
theorem hasLowerTruncationDegree_aeval (hσ : HasLowerTruncationDegrees σ)
    {F : MvPolynomial ι K} {β : NatOrdinal.{u}} (hF : IsWeightedHomogeneous wt F β) :
    Nonpositive.HasLowerTruncationDegree (aeval σ.lift F) β :=
  Nonpositive.hasLowerTruncationDegree_aeval ((hasLowerTruncationDegrees_iff σ).mp hσ) hF

/-- A polynomial all of whose monomials have weight below `α` evaluates at the lifts to a series of
degree below `α`. -/
theorem degree_aeval_lt {F : MvPolynomial ι K} {α : NatOrdinal.{u}}
    (hF : ∀ d ∈ F.support, Finsupp.weight wt d < α) :
    ν (aeval σ.lift F) < (α : WithBot NatOrdinal.{u}) :=
  Nonpositive.degree_aeval_lt_of_forall_weight_lt x σ.represents hF

end LiftFamily

/-- Every family of homogeneous classes has representatives of the assigned lower-truncation
degrees. -/
theorem exists_liftFamily_hasLowerTruncationDegrees
    (hmem : ∀ i, x i ∈ DirectSum.rangeLof K (ν).Component (wt i)) :
    ∃ σ : LiftFamily wt x, LiftFamily.HasLowerTruncationDegrees σ := by
  choose b hb hbounds using fun i ↦ exists_representative_hasLowerTruncationDegree (hmem i)
  exact ⟨⟨b, hb⟩, hbounds⟩

end HahnSeries.Nonpositive

end
