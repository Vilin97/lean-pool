/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaDirectedRCLike

/-!
# Double-angle residual bounds on a common dense domain

This module supplies the source-facing common-domain form of the Section 2
`sin 2Θ` theorem. It is imported by the Section 2 inventory and selected by the
result census as the canonical whole-result witness.

The existing combined endpoint requires the whole trial space to lie in the
operator domain and a bounded trial operator. Here `A` and `T` are self-adjoint
partial maps on the same domain, `P` reduces `A`, and `Q` reduces `T`. The bounded
residual is the extension of `(T - A)` restricted to `P` on that domain. Neither
`A|P` nor `T - A` is required to be bounded. This is the operator-theoretic setup
of Davis--Kahan (1970), Sections 1, 2 and the unbounded appendix.

The new analytic step is the common-domain reflection identity. Its proof uses
only symmetry, domain preservation inherited from reduction of `A`, and density.
The double-angle estimate then reuses the existing reflection and Ky Fan engines.

The ambient clause keeps its bounded perturbation assumption *inside that
clause*. It does not inherit a residual hypothesis or a bounded trial block.
The norm boundary includes the source-cited, where-defined Fan comparison law;
this file does not claim to derive that law from bare unitary invariance.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester
open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
variable {A T : E →ₗ.[K] E}
variable {P : Submodule K E} [P.HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- Domain preservation is inherited from the unperturbed reducing subspace.
It is required only for vectors already in the operator domain, not for all of `P`. -/
theorem commonDomain_projection_mem
    (hdom : T.domain = A.domain)
    (hP : TauCeti.LinearPMap.ReducesSubspace A P) (x : T.domain) :
    P.starProjection (x : E) ∈ T.domain := by
  obtain ⟨y, hy⟩ := x
  have hy' : y ∈ A.domain := hdom ▸ hy
  change P.starProjection y ∈ T.domain
  rw [hdom]
  exact hP.projection_mem_domain (⟨y, hy'⟩)

omit [CompleteSpace E] in
/-- Reflection preserves the common domain even when its trial restriction is unbounded. -/
theorem commonDomain_reflection_mem
    (hdom : T.domain = A.domain)
    (hP : TauCeti.LinearPMap.ReducesSubspace A P) (x : T.domain) :
    P.reflectionOperator (x : E) ∈ T.domain := by
  rw [Submodule.reflectionOperator_apply]
  exact T.domain.sub_mem
    (T.domain.smul_mem _ (commonDomain_projection_mem hdom hP x)) x.property

/-- The bounded off-diagonal residual implements reflection on the entire common domain.

The occurrence of `0` below is just a convenient parameter for the existing
bounded-block constructor: `trialOffDiagonalBlock_eq` shows that this block is
`P.orthogonal.starProjection` composed with `R` and the adjoint inclusion.
It is NOT an assumption that the unbounded trial operator is zero or bounded. -/
theorem commonDomain_trialReflection_intertwines
    (_hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    (hP : TauCeti.LinearPMap.ReducesSubspace A P)
    (R : P →L[K] E)
    (hres : ∀ p : P, ∀ hp : (p : E) ∈ T.domain,
      T (⟨(p : E), hp⟩) =
        A (⟨(p : E), by rw [← hdom]; exact hp⟩) + R p)
    (x : T.domain) :
    (TauCeti.LinearPMap.addBounded T ((-2 : K) • trialOffDiagonalPart P 0 R))
      (⟨P.reflectionOperator (x : E), commonDomain_reflection_mem hdom hP x⟩) =
        P.reflectionOperator (T x) := by
  let C : E →L[K] E := trialOffDiagonalBlock P 0 R
  have hproj (y : T.domain) : P.starProjection (y : E) ∈ T.domain :=
    commonDomain_projection_mem hdom hP y
  have hperp (y : T.domain) : P.orthogonal.starProjection (y : E) ∈ T.domain := by
    rw [Submodule.starProjection_orthogonal_apply]
    exact T.domain.sub_mem y.property (hproj y)
  have hpp (y : E) : P.starProjection (P.starProjection y) = P.starProjection y :=
    Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem y)
  have hpzero (y : E) : P.orthogonal.starProjection (P.starProjection y) = 0 := by
    rw [Submodule.starProjection_orthogonal_apply, hpp, sub_self]
  have hRoff (p : P) (hp : (p : E) ∈ T.domain) :
      P.orthogonal.starProjection (T (⟨(p : E), hp⟩)) =
        P.orthogonal.starProjection (R p) := by
    rw [hres p hp, map_add]
    have hin : A (⟨(p : E), by rw [← hdom]; exact hp⟩) ∈ P :=
      hP.invariant _ p.property
    have hz : P.orthogonal.starProjection
        (A (⟨(p : E), by rw [← hdom]; exact hp⟩)) = 0 := by
      rw [Submodule.starProjection_orthogonal_apply,
        Submodule.starProjection_eq_self_iff.mpr hin, sub_self]
    rw [hz, zero_add]
  have hC (y : T.domain) :
      C (y : E) = P.orthogonal.starProjection
        (T (⟨P.starProjection (y : E), hproj y⟩)) := by
    have hp : ((P.subtypeL.adjoint (y : E) : P) : E) ∈ T.domain := by
      rw [coe_subtypeL_adjoint_apply]
      exact hproj y
    have heq := hRoff (P.subtypeL.adjoint (y : E)) hp
    have hsub : (⟨((P.subtypeL.adjoint (y : E) : P) : E), hp⟩ : T.domain) =
        (⟨P.starProjection (y : E), hproj y⟩ : T.domain) := by
      apply Subtype.ext
      exact coe_subtypeL_adjoint_apply (y : E)
    rw [hsub] at heq
    simpa only [C, trialOffDiagonalBlock_eq, ContinuousLinearMap.comp_apply] using heq.symm
  have hsym := TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint hT
  have hCstar (y : T.domain) :
      C.adjoint (y : E) = P.starProjection
        (T (⟨P.orthogonal.starProjection (y : E), hperp y⟩)) := by
    apply ext_inner_left K
    intro z
    have hcore : ∀ w ∈ (T.domain : Set E),
        ⟪w, C.adjoint (y : E)⟫_K =
          ⟪w, P.starProjection
            (T (⟨P.orthogonal.starProjection (y : E), hperp y⟩))⟫_K := by
      intro w hw
      let wd : T.domain := ⟨w, hw⟩
      calc
        ⟪w, C.adjoint (y : E)⟫_K = ⟪C w, (y : E)⟫_K :=
          ContinuousLinearMap.adjoint_inner_right C w (y : E)
        _ = ⟪P.orthogonal.starProjection
            (T (⟨P.starProjection w, hproj wd⟩)), (y : E)⟫_K := by
          rw [hC wd]
        _ = ⟪T (⟨P.starProjection w, hproj wd⟩),
            P.orthogonal.starProjection (y : E)⟫_K := by
          simpa only [(isSelfAdjoint_starProjection P.orthogonal).adjoint_eq] using
            (ContinuousLinearMap.adjoint_inner_right P.orthogonal.starProjection
              (T (⟨P.starProjection w, hproj wd⟩)) (y : E)).symm
        _ = ⟪P.starProjection w,
            T (⟨P.orthogonal.starProjection (y : E), hperp y⟩)⟫_K :=
          hsym (⟨P.starProjection w, hproj wd⟩)
            (⟨P.orthogonal.starProjection (y : E), hperp y⟩)
        _ = ⟪w, P.starProjection
            (T (⟨P.orthogonal.starProjection (y : E), hperp y⟩))⟫_K := by
          simpa only [(isSelfAdjoint_starProjection P).adjoint_eq] using
            (ContinuousLinearMap.adjoint_inner_right P.starProjection w
              (T (⟨P.orthogonal.starProjection (y : E), hperp y⟩))).symm
    exact congrFun (Continuous.ext_on hT.dense_domain
      (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const) hcore) z
  have hsum :
      (⟨P.starProjection (x : E), hproj x⟩ : T.domain) +
        (⟨P.orthogonal.starProjection (x : E), hperp x⟩ : T.domain) = x := by
    apply Subtype.ext
    change P.starProjection (x : E) + P.orthogonal.starProjection (x : E) = (x : E)
    rw [Submodule.starProjection_orthogonal_apply]
    abel
  have hTx : T x = T (⟨P.starProjection (x : E), hproj x⟩) +
      T (⟨P.orthogonal.starProjection (x : E), hperp x⟩) := by
    have h := T.map_add (⟨P.starProjection (x : E), hproj x⟩ : T.domain)
      (⟨P.orthogonal.starProjection (x : E), hperp x⟩)
    rw [hsum] at h
    exact h
  have hcomm : C (x : E) - C.adjoint (x : E) =
      T (⟨P.starProjection (x : E), hproj x⟩) - P.starProjection (T x) := by
    rw [hC x, hCstar x, Submodule.starProjection_orthogonal_apply, hTx, map_add]
    abel
  have hPrefl : P.starProjection (P.reflectionOperator (x : E)) =
      P.starProjection (x : E) := by
    rw [Submodule.reflectionOperator_apply, map_sub, map_smul, hpp]
    module
  have hQrefl : P.orthogonal.starProjection (P.reflectionOperator (x : E)) =
      -P.orthogonal.starProjection (x : E) := by
    rw [Submodule.reflectionOperator_apply, map_sub, map_smul, hpzero]
    module
  have hXrefl : C (P.reflectionOperator (x : E)) = C (x : E) := by
    change P.orthogonal.starProjection
        (trialCompression P 0 R (P.starProjection (P.reflectionOperator (x : E)))) = _
    rw [hPrefl]
    rfl
  have hXadjrefl : C.adjoint (P.reflectionOperator (x : E)) = -C.adjoint (x : E) := by
    simp only [C, trialOffDiagonalBlock_adjoint, ContinuousLinearMap.comp_apply,
      hQrefl, map_neg]
  have hdefect : trialOffDiagonalPart P 0 R (P.reflectionOperator (x : E)) =
      T (⟨P.starProjection (x : E), hproj x⟩) - P.starProjection (T x) := by
    change C (P.reflectionOperator (x : E)) + C.adjoint (P.reflectionOperator (x : E)) = _
    rw [hXrefl, hXadjrefl, ← sub_eq_add_neg, hcomm]
  have hsplit :
      (⟨P.reflectionOperator (x : E), commonDomain_reflection_mem hdom hP x⟩ : T.domain) =
        (2 : K) • (⟨P.starProjection (x : E), hproj x⟩ : T.domain) - x := by
    apply Subtype.ext
    simp [Submodule.reflectionOperator_apply]
  change T (⟨P.reflectionOperator (x : E), commonDomain_reflection_mem hdom hP x⟩) +
      ((-2 : K) • trialOffDiagonalPart P 0 R) (P.reflectionOperator (x : E)) = _
  rw [hsplit, LinearPMap.map_sub, LinearPMap.map_smul, smul_apply, hdefect,
    Submodule.reflectionOperator_apply]
  module

/-- The common-domain directed estimate, first in the existing block representation. -/
theorem sinTwoTheta_commonDomain_block_kyFan
    (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    (hP : TauCeti.LinearPMap.ReducesSubspace A P)
    {Q : Submodule K E} [Q.HasOrthogonalProjection]
    (hQ : TauCeti.LinearPMap.ReducesSubspace T Q)
    (R : P →L[K] E)
    (hres : ∀ p : P, ∀ hp : (p : E) ∈ T.domain,
      T (⟨(p : E), hp⟩) =
        A (⟨(p : E), by rw [← hdom]; exact hp⟩) + R p)
    {gap : Real} (hgapPos : 0 < gap)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction T Q hQ)
      (TauCeti.LinearPMap.reducingRestriction T Q.orthogonal hQ.orthogonal) gap) :
    ∀ k : Nat,
      gap * kyFanApproximationGauge k (sinTwoThetaIdealBlock Q P) ≤
        2 * kyFanApproximationGauge k R := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hSsa : IsSelfAdjoint (trialOffDiagonalPart P 0 R) :=
    isSelfAdjoint_trialOffDiagonalPart
  have hDsa' : IsSelfAdjoint ((-2 : K) • trialOffDiagonalPart P 0 R) := by
    rw [IsSelfAdjoint, star_smul, hSsa.star_eq]
    norm_num
  have hDsa : ((-2 : K) • trialOffDiagonalPart P 0 R).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hDsa'
  have hraw := sinTwoTheta_reflectionResidual_block_gauge_reducing_rclike
    hT hQ (KyFanDominantIdealFamily.kyFan (𝕜 := K) k hk)
    ((-2 : K) • trialOffDiagonalPart P 0 R) hDsa P hgapPos hgap
    (commonDomain_reflection_mem hdom hP)
    (commonDomain_trialReflection_intertwines hA hT hdom hP R hres)
    (KyFanDominantIdealFamily.kyFan_mem (𝕜 := K) k hk _)
  rw [KyFanDominantIdealFamily.kyFan_gauge,
    KyFanDominantIdealFamily.kyFan_gauge] at hraw
  have hflip : kyFanApproximationGauge k
        (Q.starProjection ∘L
          ((-2 : K) • trialOffDiagonalPart P 0 R) ∘L
          (Qᗮ.map (P.reflection.toLinearEquiv : E →ₗ[K] E)).starProjection) =
      kyFanApproximationGauge k
        ((Qᗮ.map (P.reflection.toLinearEquiv : E →ₗ[K] E)).starProjection ∘L
          ((-2 : K) • trialOffDiagonalPart P 0 R) ∘L Q.starProjection) := by
    rw [← kyFanApproximationGauge_adjoint]
    congr 1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hDsa']
    rfl
  have hdouble := kyFan_reflectionDefectBlock_le_two_mul hSsa Q P k
  rw [reflectionDefect_trialOffDiagonalPart, trialOffDiagonalPart_upper] at hdouble
  have hblockR : kyFanApproximationGauge k (trialOffDiagonalBlock P 0 R) ≤
      kyFanApproximationGauge k R := by
    rw [trialOffDiagonalBlock_eq]
    refine (kyFanApproximationGauge_comp_le k Pᗮ.starProjection R
      P.subtypeL.adjoint).trans ?_
    have hQ : ‖(Pᗮ.starProjection : E →L[K] E)‖ ≤ 1 :=
      Submodule.starProjection_norm_le _
    have hI : ‖(P.subtypeL.adjoint : E →L[K] P)‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry (fun _ => rfl)
    have hnn : 0 ≤ kyFanApproximationGauge k R := kyFanApproximationGauge_nonneg k R
    calc
      ‖(Pᗮ.starProjection : E →L[K] E)‖ * kyFanApproximationGauge k R *
            ‖(P.subtypeL.adjoint : E →L[K] P)‖
          ≤ 1 * kyFanApproximationGauge k R * 1 := by gcongr
      _ = kyFanApproximationGauge k R := by ring
  calc
    gap * kyFanApproximationGauge k (sinTwoThetaIdealBlock Q P)
        ≤ kyFanApproximationGauge k
          (Q.starProjection ∘L
            ((-2 : K) • trialOffDiagonalPart P 0 R) ∘L
            (Qᗮ.map (P.reflection.toLinearEquiv : E →ₗ[K] E)).starProjection) := hraw.2
    _ = kyFanApproximationGauge k
          ((Qᗮ.map (P.reflection.toLinearEquiv : E →ₗ[K] E)).starProjection ∘L
            ((-2 : K) • trialOffDiagonalPart P 0 R) ∘L Q.starProjection) := hflip
    _ ≤ 2 * kyFanApproximationGauge k (trialOffDiagonalBlock P 0 R) := hdouble
    _ ≤ 2 * kyFanApproximationGauge k R := by gcongr

/-- Source-oriented common-domain directed residual bound. Both displayed norms are finite.
There is no bounded trial operator and no global bounded perturbation in the hypotheses. -/
theorem sinTwoTheta_directed_commonDomain_whereDefinedUIN_rclike
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} K)
    (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    (hP : TauCeti.LinearPMap.ReducesSubspace A P)
    {Q : Submodule K E} [Q.HasOrthogonalProjection]
    (hQ : TauCeti.LinearPMap.ReducesSubspace T Q)
    (R : P →L[K] E)
    (hres : ∀ p : P, ∀ hp : (p : E) ∈ T.domain,
      T (⟨(p : E), hp⟩) =
        A (⟨(p : E), by rw [← hdom]; exact hp⟩) + R p)
    {gap : Real} (hgapPos : 0 < gap)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction T Q hQ)
      (TauCeti.LinearPMap.reducingRestriction T Q.orthogonal hQ.orthogonal) gap) :
    N.Mem (Angle.directedSinTwoAngleOperator P Q) → N.Mem R ->
      gap * N.gaugeReal (Angle.directedSinTwoAngleOperator P Q) ≤ 2 * N.gaugeReal R := by
  intro hAngle hR
  have hhalf : N.ScaledGaugeLEWhereDefined (gap / 2)
      (Angle.directedSinTwoAngleOperator P Q) R := by
    apply N.scaledGaugeLEWhereDefined_of_all_mul_kyFan_le
      (div_pos hgapPos (by norm_num : (0 : Real) < 2))
    intro k
    by_cases hk0 : k = 0
    · subst k
      simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge_zero_index]
    · have hk : 0 < k := Nat.pos_of_ne_zero hk0
      have hblock := sinTwoTheta_commonDomain_block_kyFan
        hA hT hdom hP hQ R hres hgapPos hgap k
      have hsame : kyFanApproximationGauge k (Angle.directedSinTwoAngleOperator P Q) =
          kyFanApproximationGauge k (sinTwoThetaIdealBlock Q P) := by
        have h := Angle.gauge_directedSinTwoAngleOperator_trialSide Q P
          (kyFanNormingFunction k hk)
        simpa only [kyFanNormingFunction_gauge] using h
      rw [← hsame] at hblock
      nlinarith
  have hle := hhalf hAngle hR
  nlinarith

/-- Both double-angle clauses, with clause-local boundedness assumptions.

Here `T` is the source's `A + H`. The directed clause only asks for its bounded
residual on the common domain. The ambient clause asks separately for a bounded
self-adjoint perturbation. A residual is not required to use the ambient clause.
-/
theorem sinTwoTheta_commonDomain_whereDefinedUIN_rclike
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} K)
    {A T : E →ₗ.[K] E} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule K E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hP : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQ : TauCeti.LinearPMap.ReducesSubspace T Q)
    {gap : Real} (hgapPos : 0 < gap)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction T Q hQ)
      (TauCeti.LinearPMap.reducingRestriction T Q.orthogonal hQ.orthogonal) gap) :
    (∀ R : P →L[K] E,
      (∀ p : P, ∀ hp : (p : E) ∈ T.domain,
        T (⟨(p : E), hp⟩) = A (⟨(p : E), by rw [← hdom]; exact hp⟩) + R p) ->
      N.Mem (Angle.directedSinTwoAngleOperator P Q) → N.Mem R ->
        gap * N.gaugeReal (Angle.directedSinTwoAngleOperator P Q) ≤ 2 * N.gaugeReal R) ∧
    (∀ Hop : E →L[K] E, Hop.IsSymmetric ->
      T = TauCeti.LinearPMap.addBounded A Hop ->
      N.Mem (Angle.sinTwoAngleOperator P Q) → N.Mem Hop ->
        gap * N.gaugeReal (Angle.sinTwoAngleOperator P Q) ≤ 2 * N.gaugeReal Hop) := by
  constructor
  · intro R hres
    exact sinTwoTheta_directed_commonDomain_whereDefinedUIN_rclike
      N hA hT hdom hP hQ R hres hgapPos hgap
  · intro Hop hHop hEq hAngle hHopMem
    subst T
    exact sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
      N hA Hop hHop hP hQ hgapPos hgap hAngle hHopMem

end
end DavisKahan1970
end TauCeti
