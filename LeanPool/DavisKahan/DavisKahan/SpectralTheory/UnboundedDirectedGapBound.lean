/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Reducing
public import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbation
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.SelfAdjointCompletion

/-!
# The unbounded `sin Θ` estimate at the operator norm

The directed `sin Θ` theorem for an unbounded self-adjoint partial map and a
bounded perturbation, read at the **operator norm**.  That reading is possible
only because the operator norm is the first Ky Fan norm and therefore a member
of the source norm class.

It is a generic foundation, not a source façade: the moving-band Lipschitz
estimate for Theorem 8.2's homotopy consumes it, and so does the static branch
bound.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester

noncomputable section

universe v

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete.  `local instance` does not propagate through imports, so it is
reinstalled here. -/
local instance instCompleteSpaceCoeBranchBound
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- **The `sin Θ` estimate at the operator norm, unbounded ambient scope,
directed form.**

`δ · directedGap P Q ≤ ‖H‖` from the separation between the unperturbed block on
`P` and the perturbed block on `Qᗮ`.

The trial datum is the inclusion of `P`; the residual it produces is `H`
restricted to `P`, whose norm is at most `‖H‖`, and that is where the printed
perturbation norm enters. -/
theorem directedGap_le_of_reducingGap_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    δ * P.directedProjectionGap Q ≤ ‖Hop‖ := by
  classical
  have hB : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop
  have hA0 : IsSelfAdjoint (TauCeti.LinearPMap.reducingRestriction A P hPred) :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A P hPred hA.dense_domain hA
  have hX : DavisKahan.IsometricEmbedding (P.subtypeL : P →L[ℂ] Hc) := fun _ => rfl
  have hXdom : ∀ x : (TauCeti.LinearPMap.reducingRestriction A P hPred).domain,
      (P.subtypeL (x : P) : Hc) ∈ (TauCeti.LinearPMap.addBounded A Hop).domain := by
    intro x
    exact x.2
  have hReq : ∀ x : (TauCeti.LinearPMap.reducingRestriction A P hPred).domain,
      (TauCeti.LinearPMap.addBounded A Hop) ⟨P.subtypeL (x : P), hXdom x⟩ -
          P.subtypeL ((TauCeti.LinearPMap.reducingRestriction A P hPred) x) =
        (Hop ∘L (P.subtypeL : P →L[ℂ] Hc)) (x : P) := by
    intro x
    have hxA : ((x : P) : Hc) ∈ A.domain := x.2
    change (A (⟨((x : P) : Hc), hxA⟩ : A.domain) : Hc) + Hop ((x : P) : Hc)
        - (A (⟨((x : P) : Hc), hxA⟩ : A.domain) : Hc) = Hop ((x : P) : Hc)
    abel
  have key := DavisKahan.ExactSinTheta.sinTheta_unbounded_complex_reducingSubspace
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) 1 one_pos)
    (TauCeti.LinearPMap.addBounded A Hop) hB.dense_domain hB.isClosed hB Q hQred
    (TauCeti.LinearPMap.reducingRestriction A P hPred)
    hA0.dense_domain hA0.isClosed hA0
    (P.subtypeL : P →L[ℂ] Hc) (Hop ∘L (P.subtypeL : P →L[ℂ] Hc)) hX hXdom hReq hδ hgap
    (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) 1 one_pos _)
  obtain ⟨-, hle⟩ := key
  rw [KyFanDominantIdealFamily.kyFan_gauge, KyFanDominantIdealFamily.kyFan_gauge,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one] at hle
  have hblock : (ContinuousLinearMap.id ℂ Hc -
      Q.subtypeL ∘L ContinuousLinearMap.adjoint Q.subtypeL) = Qᗮ.starProjection := by
    rw [Submodule.adjoint_subtypeL]
    exact (Submodule.starProjection_orthogonal Q).symm
  rw [hblock] at hle
  have hgapeq : ‖Qᗮ.starProjection ∘L (P.subtypeL : P →L[ℂ] Hc)‖ =
      P.directedProjectionGap Q :=
    TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection Qᗮ.starProjection P
  rw [hgapeq] at hle
  refine hle.trans ?_
  calc ‖Hop ∘L (P.subtypeL : P →L[ℂ] Hc)‖ ≤ ‖Hop‖ * ‖(P.subtypeL : P →L[ℂ] Hc)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Hop‖ := by
        have : ‖(P.subtypeL : P →L[ℂ] Hc)‖ ≤ 1 := by
          refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
          simp
        nlinarith [norm_nonneg Hop, norm_nonneg (P.subtypeL : P →L[ℂ] Hc)]

end

end Section8
end DavisKahan1970
end TauCeti
