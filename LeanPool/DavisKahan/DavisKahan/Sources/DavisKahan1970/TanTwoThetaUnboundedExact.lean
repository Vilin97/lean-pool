/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedGramMiddle
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-! # Tan Two Theta Unbounded Exact -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Exact source-facing unbounded `tan 2Theta` theorem

The Davis--Kahan Section 2 headline theorem is stated to persist when the
unperturbed self-adjoint operator is unbounded and the residual is bounded.
The lower-level development already supplies all analytic ingredients:

* the canonical spectral cutoffs `spectralCutoffSeq` and their strong
  convergence on the source spectral subspace;
* unconditional pole exclusion from the printed gap data;
* the sharp residual estimate at every Ky Fan prefix; and
* Fan dominance for every paper unitarily invariant norm.

This module performs only the source-facing assembly.  No cutoff net, pole
exclusion, angle smallness, finite rank, or extremality premise is exposed to
the caller.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open Filter
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u

variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]

/-- The canonical one-sided spectral cutoffs, after compression to the source
spectral subspace, converge strongly to the identity of that subspace. -/
theorem stronglyTendsto_cutoffCorner_spectralCutoffSeq
    {A : G →ₗ.[ℂ] G} (hA : IsSelfAdjoint A) (c : ℝ) :
    StronglyTendsto
      (fun n : ℕ => cutoffCorner (TauCeti.spectralCutoffSeq hA c n))
      atTop
      (ContinuousLinearMap.id ℂ
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)) := by
  intro y
  apply tendsto_subtype_rng.mpr
  have h := TauCeti.tendsto_spectralCutoff hA c y.property
  simpa only [Function.comp_apply, ContinuousLinearMap.id_apply, coe_cutoffCorner_apply] using h

/-- **Paper-exact unbounded directed residual `tan 2Theta` theorem, complex
Hilbert-space form.**

The caller supplies exactly the source data used in the unbounded extension:
`A` is self-adjoint (possibly unbounded), `U = 1_{(-infty,c]}(A)`, the bounded
residual `B` is off-diagonal relative to `U`, `Z` is the reducing reflection,
and the two form bounds are separated by `a < b`.  Membership of the residual
corner in the chosen paper unitarily invariant ideal is the only norm-domain
premise.

The conclusion includes pole exclusion/invertibility, membership of the genuine
directed `tan 2Theta` corner, and the sharp source inequality

`(b-a) * N(tan 2Theta_0) <= 2 * N(R)`.

In particular, the spectral cutoff family and its convergence are derived
internally rather than appearing in the theorem statement. -/
theorem tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G} {a b c : ℝ}
    (hA : IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : G), hZdom x⟩ + B (Z (x : G)) = Z (A x) + Z (B (x : G)))
    (hUa : ∀ x : A.domain,
      (x : G) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : G) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b)
    (hRmem : N.Mem (blockCompression
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)) :
    IsUnit
        ((TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z *
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z) ∧
      N.Mem (reflectionTangentCorner
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ∧
      (b - a) * N.gauge (reflectionTangentCorner
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ≤
        2 * N.gauge (blockCompression
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B) := by
  let U : Submodule ℂ G :=
    TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic
  have hred : TauCeti.LinearPMap.ReducesSubspace A U :=
    TauCeti.LinearPMap.reducesSubspace_specRange hA (Set.Iic c) measurableSet_Iic
  have hgU : ∀ y ∈ U,
      ‖U.offDiagonalPart Z y‖ ≤
        TauCeti.crossBlockBound (b - a) ‖B‖ * ‖y‖ := by
    intro y hy
    exact TauCeti.norm_offDiagonalPart_apply_le_specRange hA hB hZsa hZ2 hZdom
      hZcomm hUa hUb hab hy
  have hg0 : 0 ≤ TauCeti.crossBlockBound (b - a) ‖B‖ :=
    TauCeti.crossBlockBound_nonneg (norm_nonneg B)
  have hg1 : TauCeti.crossBlockBound (b - a) ‖B‖ < 1 :=
    crossBlockBound_lt_one (sub_pos.mpr hab) (norm_nonneg B)
  have hSle : ‖U.offDiagonalPart Z‖ ≤ TauCeti.crossBlockBound (b - a) ‖B‖ :=
    norm_offDiagonalPart_le hZsa hg0 hgU
  have hS1 : ‖U.offDiagonalPart Z‖ < 1 := lt_of_le_of_lt hSle hg1
  have hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z) :=
    isUnit_diagonalPart_sq_of_forall_mem hZsa hZ2 hg0 hg1 hgU
  have hstrong : StronglyTendsto
      (fun n : ℕ => cutoffCorner (TauCeti.spectralCutoffSeq hA c n))
      atTop (ContinuousLinearMap.id ℂ U) := by
    simpa [U] using stronglyTendsto_cutoffCorner_spectralCutoffSeq hA c
  have hkyFan : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
        2 * kyFanApproximationGauge k (reflectionResidualCorner U B) := by
    intro k
    exact gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan hred hB hZsa hZ2
      hZdom hZcomm hUa hUb hab hS1
      (σ := fun n : ℕ => |c| + n) (fun n : ℕ => by positivity)
      (fun n : ℕ => TauCeti.spectralCutoffSeq hA c n) hstrong k
  have hhalf : 0 < (b - a) / 2 := by linarith
  have hscaled : ∀ k : ℕ,
      ((b - a) / 2) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
        kyFanApproximationGauge k (reflectionResidualCorner U B) := by
    intro k
    have h := hkyFan k
    linarith
  have hRmem' : N.Mem (reflectionResidualCorner U B) := by
    simpa [U] using hRmem
  have hUI := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hRmem' hscaled
  change IsUnit (U.diagonalPart Z * U.diagonalPart Z) ∧
      N.Mem (reflectionTangentCorner U Z) ∧
      (b - a) * N.gauge (reflectionTangentCorner U Z) ≤
        2 * N.gauge (reflectionResidualCorner U B)
  refine ⟨hCC, hUI.1, ?_⟩
  nlinarith [hUI.2]

end

end DavisKahan1970
end TauCeti
