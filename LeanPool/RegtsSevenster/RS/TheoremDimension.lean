/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.TheoremTotal
public import LeanPool.RegtsSevenster.RS.TheoremConverse

/-!
# Minimum colour dimension and connection-rank growth

The total dimension of the reconstructed standard model is minimal
among all mixed models of the parameter. Its value is the limit of
the even roots of the actual connection ranks. The assembly is
conditional on Deligne's theorem, discharged in `RS/Summit.lean`.
-/

@[expose] public section

namespace RS

open CategoryTheory

/-- A representing model bounds the minimum total colour dimension. -/
theorem minimumColourDimension_le_of_represents
    {f : ClosedFragment → ℂ} {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (hrep : h.Represents f) : minimumColourDimension f ≤ k + 2 * ℓ :=
  Nat.sInf_le (show IsMixedPartitionFunctionTotalBounded f (k + 2 * ℓ)
    from ⟨⟨k, ℓ, h, le_rfl, hrep⟩⟩)

/-- Every parameter admitting a mixed model admits one at the least
total colour bound. -/
theorem minimumColourDimension_attained {f : ClosedFragment → ℂ}
    (hf : IsMixedPartitionFunction f) :
    IsMixedPartitionFunctionTotalBounded f (minimumColourDimension f) := by
  apply Nat.sInf_mem (s := {d | IsMixedPartitionFunctionTotalBounded f d})
  obtain ⟨k, ℓ, h, hrep⟩ := hf
  exact ⟨k + 2 * ℓ, ⟨⟨k, ℓ, h, le_rfl, hrep⟩⟩⟩

/-- A model at the least colour bound has exactly that total
dimension, rather than merely a dimension bounded by it. -/
theorem TotalBoundedMixedModel.dimension_eq_minimum
    {f : ClosedFragment → ℂ}
    (M : TotalBoundedMixedModel f (minimumColourDimension f)) :
    M.k + 2 * M.ℓ = minimumColourDimension f :=
  le_antisymm M.dimension_le
    (minimumColourDimension_le_of_represents M.functional M.partition_eq)

/-- A represented parameter satisfies the rank bound with the
representing model's exact total dimension. -/
theorem MixedFunctional.Represents.edgeRankBounded
    {f : ClosedFragment → ℂ} {k ℓ : ℕ} {h : MixedFunctional k ℓ}
    (hrep : h.Represents f) : EdgeRankBounded f (k + 2 * ℓ) := by
  rw [show f = fun W => mixedPartition h W from funext hrep]
  exact mixedPartition_edgeRankBounded h

/-- The standard model's dimension is the intrinsic minimum as
soon as its graph evaluations agree with the parameter. -/
theorem stdModel_dimension_eq_minimum {R k ℓ : ℕ}
    (f : EdgeRankParameter R) (P : DelignePackage (SkeinObj f))
    (e : stdSuperPair k ℓ ≅ strandImage f P)
    (h : MixedFunctional k ℓ) (hrep : h.Represents f.val) :
    k + 2 * ℓ = minimumColourDimension f.val := by
  obtain ⟨M⟩ := minimumColourDimension_attained
    (show IsMixedPartitionFunction f.val from ⟨k, ℓ, h, hrep⟩)
  have hsmall : k + 2 * ℓ ≤ M.k + 2 * M.ℓ :=
    stdModel_total_dimension_le_of_rank_bound f P e
      (show M.functional.Represents f.val from M.partition_eq).edgeRankBounded
  exact le_antisymm (hsmall.trans M.dimension_le)
    (minimumColourDimension_le_of_represents h hrep)

/-- The even roots of the connection ranks tend to the total
dimension of the reconstructed standard model. -/
theorem stdModel_connectionRank_growth {R k ℓ : ℕ}
    (f : EdgeRankParameter R) (P : DelignePackage (SkeinObj f))
    (e : stdSuperPair k ℓ ≅ strandImage f P)
    (h : MixedFunctional k ℓ) (hrep : h.Represents f.val) :
    Filter.Tendsto
      (fun n => (connectionRank f.val (2 * n) : ℝ) ^
        ((2 * n : ℕ) : ℝ)⁻¹)
      Filter.atTop (nhds ((k + 2 * ℓ : ℕ) : ℝ)) :=
  tendsto_even_root_of_polynomial_bounds _ (k + 2 * ℓ)
    (2 * (k + 2 * ℓ) ^ 2) (stdModel_pow_le_connectionRank f P e)
    (fun n => connectionRank_le_pow hrep.edgeRankBounded (2 * n))

/-- Exponentially bounded connection rank admits a model attaining
the minimum total colour dimension, conditional on Deligne alone. -/
theorem regts_sevenster_minimum_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) {R : ℕ}
    (f : EdgeRankParameter R) :
    IsMixedPartitionFunctionTotalBounded f.val
      (minimumColourDimension f.val) :=
  minimumColourDimension_attained
    (regts_sevenster_deligne_only hDeligne R f)

/-- The even connection-rank growth rate exists and equals the
minimum total colour dimension, conditional on Deligne alone. -/
theorem regts_sevenster_rank_growth_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) {R : ℕ}
    (f : EdgeRankParameter R) :
    Filter.Tendsto
      (fun n => (connectionRank f.val (2 * n) : ℝ) ^
        ((2 * n : ℕ) : ℝ)⁻¹)
      Filter.atTop (nhds (minimumColourDimension f.val : ℝ)) := by
  obtain ⟨P⟩ := skein_delignePackage f hDeligne
  obtain ⟨k, ℓ, e, e', he'e, hee', hform, hcopair⟩ :=
    skein_std_model f P
  let eModel : stdSuperPair k ℓ ≅ strandImage f P :=
    ⟨e, e', he'e, hee'⟩
  have hrep : (hRS f P e').Represents f.val := fun W =>
    parameter_eq_mixedPartition f P e e' W hee' he'e hform hcopair
  have hdim := stdModel_dimension_eq_minimum f P eModel _ hrep
  simpa only [hdim] using
    stdModel_connectionRank_growth f P eModel _ hrep

end RS
