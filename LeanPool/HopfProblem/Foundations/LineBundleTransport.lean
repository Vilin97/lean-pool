/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Uniformization.HolomorphicCousin
import all LeanPool.HopfProblem.Foundations.Core1

/-!
# Hopf problem: foundations · line bundle transport

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem
    LineBundleTransport.exists_smooth_cutoff_near_closed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K U : Set E} (hK : IsClosed K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
        tsupport χ ⊆ U ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn χ (fun _ => 1) W := by
  classical
  let O : Bool → Set E := fun b => if b then Kᶜ else U
  have hOo (b : Bool) : IsOpen (O b) := by
    cases b
    · exact hU
    · exact hK.isOpen_compl
  have hOc : Set.univ ⊆ ⋃ b, O b := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.true, fun hk => hx (hKU hk)⟩
  obtain ⟨W, hWo, hKW, hWU, ρ, hρ, hρone, -, -⟩ :=
    HolomorphicCousin.exists_smoothPartitionOfUnity_eq_one_near_closed (modelWithCornersSelf ℝ E)
      O hOo hOc Bool.false hK hKU
  exact ⟨ρ Bool.false, (ρ Bool.false).contMDiff.contDiff, hρ Bool.false, W, hWo, hKW, hWU, hρone⟩

private theorem LineBundleTransport.exists_smooth_extension_near_closed {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K U : Set E} {f : E → F} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn G f W := by
  obtain ⟨χ, hχ, hχU, W, hWo, hKW, hWU, hχone⟩ := exists_smooth_cutoff_near_closed hK hU hKU
  let G : E → F := fun x => χ x • f x
  have hG : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ G := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxU : x ∈ U := hχU (tsupport_smul_subset_left χ f hx)
    exact hχ.contMDiff.contMDiffAt.smul ((hf.contDiffAt (hU.mem_nhds hxU)).contMDiffAt)
  refine ⟨G, hG.contDiff, W, hWo, hKW, hWU, ?_⟩
  intro x hx
  change χ x • f x = f x
  rw [hχone hx, one_smul]

public
theorem LineBundleTransport.exists_interval_cutoff (a b : ℝ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ Set.EqOn χ (fun _ => 1) (Set.uIcc a b) := by
  obtain ⟨R, -, hR⟩ :=
    (isCompact_uIcc : IsCompact (Set.uIcc a b)).isBounded.subset_ball_lt (0 : ℝ) 0
  obtain ⟨χ, hχ, hχU, W, -, hKW, -, hχone⟩ :=
    exists_smooth_cutoff_near_closed (isCompact_uIcc : IsCompact (Set.uIcc a b)).isClosed
      Metric.isOpen_ball hR
  refine ⟨χ, hχ, ?_, hχone.mono hKW⟩
  exact
    (ProperSpace.isCompact_closedBall (0 : ℝ) R).of_isClosed_subset (isClosed_tsupport χ)
      (hχU.trans Metric.ball_subset_closedBall)

end Mathoverflow1973

end
