/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SharpIdeal
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.QuarterAcuteFormGap
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.CanonicalTangentBridge
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.TanTheta
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalReverseGap
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport

/-! # Selected Branch Symmetric Norming -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Full bounded paper-facing `tan 2Theta` theorem

This module now has two deliberately distinct results.

* `tanTwoTheta_uiNorm_finite_alternate` retains the independently compiled
  finite-dimensional Riccati/approximation-number derivation.  The main
  Davis--Kahan tree already proves the finite Section 7 theorem, so this result
  is explicitly a duplicate regression proof rather than the completion target.
* `tanTwoTheta_selectedBranch_symmetricNorming` states the unrestricted bounded target used
  by this package: no finite-dimensional or finite-carrier hypothesis, the
  quarter-acute branch derived from the original form-gap/off-diagonal data,
  and the sharp source-ideal estimate for the canonical ambient
  `directedTanTwoAngleOperatorC`.

The unrestricted proof is split into two genuine bridges:

1. `InfiniteQuarterAcute` proves the dimension-free branch by a
   reflection-product Lyapunov identity and a strict accretivity/spectrum
   argument, replacing the finite proof's norm-attaining eigenvector.
2. `CanonicalTangentBridge` identifies the complete approximation-number
   sequence of the canonical ambient tangent with the graph-coordinate tangent.

The post-branch Riccati/Ky-Fan/Fan-dominance estimate is then supplied by the
already proved `sharp_symmetricNormingFunction` stack.

*Moved, not restated.*  Promoted out of the non-default `FinishTanTwoTheta`
completion lane so the unrestricted bounded theorem is covered by the
default build.  Only the namespace changed
(`TauCeti.DavisKahan.FinishTanTwoTheta` to `TauCeti.DavisKahan`).
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan
open ExactSinTheta

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

-- `CanonicalTangentBridge` already declares
-- `completeSpaceOfHasOrthogonalProjection` in this namespace; `local instance` only
-- scopes the *attribute*, not the name, so re-enable the attribute here rather than
-- redeclaring it.  It is needed at *statement* time -- `N.Mem
-- (tanTwoThetaGraphCoordinateOperator …)` mentions operators on `↥U` -- where the
-- `letI`s inside the proofs below cannot help.
attribute [local instance] completeSpaceOfHasOrthogonalProjection

/-- The source-permitted graph-coordinate representative of `tan 2Theta`.
Its approximation singular values are the double-angle tangents of the
principal angles of the quarter-acute pair. -/
noncomputable def tanTwoThetaGraphCoordinateOperator
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    U →L[ℂ] Uᗮ := by
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  letI : CompleteSpace (Uᗮ : Submodule ℂ E) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  exact TauCeti.DavisKahan.doubleAngleTangentOperator
    (TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate U V hquarter)
    (TauCeti.DavisKahanExt.norm_quarterAcuteAngularCoordinate_lt_one U V hquarter)

omit [CompleteSpace E] in
/-- Mapping the two summands into one another is exactly the ambient
off-diagonal condition consumed by the Riccati block API. -/
private theorem isOffDiagonal_of_maps_orthogonal
    (H : E →L[ℂ] E) (U : Submodule ℂ E)
    [U.HasOrthogonalProjection]
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    Submodule.IsOffDiagonal U H := by
  change U.diagonalPart H = 0
  apply ContinuousLinearMap.ext
  intro x
  have hPzero : U.starProjection (H (U.starProjection x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).2
      (hHU (U.starProjection x) (U.starProjection_apply_mem x))
  have hQzero : Uᗮ.starProjection (H (Uᗮ.starProjection x)) = 0 := by
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr
        (hHUperp (Uᗮ.starProjection x) (Uᗮ.starProjection_apply_mem x)),
      sub_self]
  simp only [Submodule.diagonalPart, ContinuousLinearMap.comp_apply,
    add_apply, hPzero, hQzero, add_zero, zero_apply]

/-- The finite-dimensional sharp operator-norm theorem gives the strict
quarter-turn branch from the source hypotheses. -/
private theorem isQuarterAcute_of_orderedFormGap_finiteDimensional
    [FiniteDimensional ℂ E]
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    IsQuarterAcute U V := by
  have hAsym : A.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAHself : IsSelfAdjoint (A + H) := hA.add hH
  have hAHsym : (A + H).toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAHself
  have hdiagU : ∀ x ∈ U, ∀ y ∈ U,
      ⟪x, ((A + H).toLinearMap - A.toLinearMap) y⟫_ℂ = 0 := by
    intro x hx y hy
    have horth : ⟪x, H y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal U (H y)).mp (hHU y hy) x hx
    have hdiff : ((A + H).toLinearMap - A.toLinearMap) y = H y := by
      change (A + H) y - A y = H y
      simp only [add_apply]
      abel
    rwa [hdiff]
  have hdiagUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ,
      ⟪x, ((A + H).toLinearMap - A.toLinearMap) y⟫_ℂ = 0 := by
    intro x hx y hy
    have horth : ⟪x, H y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal' U x).mp hx (H y) (hHUperp y hy)
    have hdiff : ((A + H).toLinearMap - A.toLinearMap) y = H y := by
      change (A + H) y - A y = H y
      simp only [add_apply]
      abel
    rwa [hdiff]
  have hpert : ∀ x : E,
      ‖((A + H).toLinearMap - A.toLinearMap) x‖ ≤ ‖H‖ * ‖x‖ := by
    intro x
    have hdiff : ((A + H).toLinearMap - A.toLinearMap) x = H x := by
      change (A + H) x - A x = H x
      simp only [add_apply]
      abel
    rw [hdiff]
    exact H.le_opNorm x
  have hbranch := TauCeti.tan_two_theta_norm_sub_le
    (T := A.toLinearMap) (S := (A + H).toLinearMap)
    hAsym hAHsym hAU hAplusH_V hab (norm_nonneg H)
    hUhigh hUperpLow hVhigh hVperpLow hdiagU hdiagUperp hpert
  change ‖U.starProjection - V.starProjection‖ < Real.sqrt 2 / 2
  have hsq : ‖U.starProjection - V.starProjection‖ ^ 2 < (1 : ℝ) / 2 :=
    hbranch.1
  have hthresholdSq : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hthresholdPos : 0 < Real.sqrt 2 / 2 := by positivity
  by_contra hnot
  have hle : Real.sqrt 2 / 2 ≤ ‖U.starProjection - V.starProjection‖ :=
    le_of_not_gt hnot
  have hsqle := pow_le_pow_left₀ hthresholdPos.le hle 2
  rw [hthresholdSq] at hsqle
  exact (not_le_of_gt hsq) hsqle

/-- The ambient extension by zero of the upper-right perturbation block is the
corresponding double compression of the full perturbation. -/
private theorem ambientUpperRightBlock_eq
    (H : E →L[ℂ] E) (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] 
    [CompleteSpace (Uᗮ : Submodule ℂ E)]
    (B01 : Uᗮ →L[ℂ] U)
    (hB01 : B01 =
      U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL) :
    U.subtypeL ∘L B01 ∘L Uᗮ.subtypeL.adjoint =
      U.starProjection ∘L H ∘L Uᗮ.starProjection := by
  rw [hB01, Submodule.adjoint_subtypeL]
  apply ContinuousLinearMap.ext
  intro x
  rfl


/-- Post-branch paper estimate.  This is the genuinely arbitrary-Hilbert-space
part of the proof: once the strict quarter-acute graph branch is known, the
Riccati equation, approximation-number Ky Fan estimate, and Fan-dominance
promotion require no finite-dimensional hypothesis. -/
private theorem tanTwoThetaGraphCoordinate_bound_of_quarterAcute
    (N : SymmetricNormingFunction)
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H)
    (hquarter : IsQuarterAcute U V) :
    N.Mem (tanTwoThetaGraphCoordinateOperator U V hquarter) ∧
      (b - a) * N.gauge (tanTwoThetaGraphCoordinateOperator U V hquarter) ≤
        2 * N.gauge H := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ E) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAsym : A.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hHsym : H.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hAHsym : (A + H).IsSymmetric := by
    have h := hAsym.add hHsym
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  have hUreduces : A.Reduces U := ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAsym hAU
  have hVreduces : ContinuousLinearMap.Reduces (A + H) V :=
    ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAHsym hAplusH_V
  have hoff : Submodule.IsOffDiagonal U H :=
    isOffDiagonal_of_maps_orthogonal H U hHU hHUperp
  let B : BlockOperatorData (𝕜 := ℂ) (E0 := U) (E1 := Uᗮ) :=
    TauCeti.DavisKahanExt.subspaceBlockOperatorData (A + H) U hAHsym
  let X : U →L[ℂ] Uᗮ :=
    TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate U V hquarter
  let C := TauCeti.DavisKahanExt.negBlockOperatorData B
  let D := TauCeti.DavisKahanExt.shiftBlockOperatorData C (-b)
  have hsolveB : SolvesRiccati B X := by
    simpa only [B, X] using
      TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate_solvesRiccati
        A H hAsym hHsym U V hVreduces hquarter
  have hsolveC : SolvesRiccati C X :=
    (TauCeti.DavisKahanExt.solvesRiccati_negBlockOperatorData_iff B X).2 hsolveB
  have hsolveD : SolvesRiccati D X :=
    (TauCeti.DavisKahanExt.solvesRiccati_shiftBlockOperatorData_iff C (-b) X).2 hsolveC
  have hB0 : B.A0 = compressOperator U A := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_A0_add_offDiagonal
        A H U hAHsym hoff
  have hB1 : B.A1 = compressOperator Uᗮ A := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_A1_add_offDiagonal
        A H U hAHsym hoff
  have hB01 : B.B01 =
      U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_B01_add_of_reduces
        A H U hAHsym hUreduces
  have hB0high : ∀ z : U,
      b * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A0 z, z⟫_ℂ := by
    intro z
    rw [hB0]
    have hAz : A (z : E) ∈ U := hAU (z : E) z.property
    change b * ‖(z : E)‖ ^ 2 ≤
      RCLike.re ⟪U.orthogonalProjectionOnto (A (z : E)), z⟫_ℂ
    rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_eq_self_iff.mpr hAz]
    exact hUhigh (z : E) z.property
  have hB1low : ∀ z : Uᗮ,
      RCLike.re ⟪B.A1 z, z⟫_ℂ ≤ a * ‖z‖ ^ 2 := by
    intro z
    rw [hB1]
    have hAz : A (z : E) ∈ Uᗮ := hUreduces.2 (z : E) z.property
    change RCLike.re
        ⟪Uᗮ.orthogonalProjectionOnto (A (z : E)), z⟫_ℂ ≤
      a * ‖(z : E)‖ ^ 2
    rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_eq_self_iff.mpr hAz]
    exact hUperpLow (z : E) z.property
  have hC0upper : ∀ z : U,
      RCLike.re ⟪C.A0 z, z⟫_ℂ ≤ (-b) * ‖z‖ ^ 2 := by
    intro z
    have hz := hB0high z
    dsimp only [C, TauCeti.DavisKahanExt.negBlockOperatorData]
    simp only [neg_apply, inner_neg_left, map_neg]
    linarith
  have hC1lower : ∀ z : Uᗮ,
      ((-b) + (b - a)) * ‖z‖ ^ 2 ≤ RCLike.re ⟪C.A1 z, z⟫_ℂ := by
    intro z
    have hz := hB1low z
    dsimp only [C, TauCeti.DavisKahanExt.negBlockOperatorData]
    simp only [neg_apply, inner_neg_left, map_neg]
    linarith
  have hD0 : ∀ z : U, RCLike.re ⟪D.A0 z, z⟫_ℂ ≤ 0 := by
    simpa only [D] using
      TauCeti.DavisKahanExt.shiftBlockOperatorData_A0_nonpos C (-b) hC0upper
  have hD1 : ∀ z : Uᗮ,
      (b - a) * ‖z‖ ^ 2 ≤ RCLike.re ⟪D.A1 z, z⟫_ℂ := by
    simpa only [D] using
      TauCeti.DavisKahanExt.shiftBlockOperatorData_A1_lower
        C (-b) (b - a) hC1lower
  let Camb : E →L[ℂ] E := U.starProjection ∘L H ∘L Uᗮ.starProjection
  have hCambMem : N.Mem Camb := by
    dsimp only [Camb]
    exact N.comp_mem hHmem U.starProjection Uᗮ.starProjection
  have hCambGauge : N.gauge Camb ≤ N.gauge H := by
    dsimp only [Camb]
    exact N.gauge_comp_le_of_contractions hHmem
      U.starProjection Uᗮ.starProjection
      U.starProjection_norm_le Uᗮ.starProjection_norm_le
  have hseqB : SameApproximationSingularSequence Camb B.B01 := by
    have hseq := sameApproximationSingularValues_ambientSubspaceBlock Uᗮ U B.B01
    have hext : U.subtypeL ∘L B.B01 ∘L Uᗮ.subtypeL.adjoint = Camb := by
      simpa only [Camb] using ambientUpperRightBlock_eq H U B.B01 hB01
    rw [hext] at hseq
    exact hseq
  have htransport := hseqB.normingMem_iff_and_gauge_eq N
  have hBmem : N.Mem B.B01 := htransport.1.mp hCambMem
  have hBgauge : N.gauge B.B01 = N.gauge Camb := htransport.2.symm
  have hCmem : N.Mem C.B01 := by
    have hnegmem : N.Mem ((-1 : ℂ) • B.B01) := by
      unfold SymmetricNormingFunction.Mem at hBmem ⊢
      rw [N.extendedGauge_smul]
      norm_num
      exact hBmem
    simpa only [C, TauCeti.DavisKahanExt.negBlockOperatorData,
      neg_one_smul] using hnegmem
  have hC_B01_gauge : N.gauge C.B01 = N.gauge B.B01 := by
    have hnegGauge : N.gauge ((-1 : ℂ) • B.B01) = N.gauge B.B01 := by
      rw [N.gauge_smul (-1 : ℂ) hBmem]
      norm_num
    simpa only [C, TauCeti.DavisKahanExt.negBlockOperatorData,
      neg_one_smul] using hnegGauge
  have hDB01 : D.B01 = C.B01 := rfl
  have hDmem : N.Mem D.B01 := by rw [hDB01]; exact hCmem
  have hcontractive : ‖X‖ < 1 := by
    simpa only [X] using
      TauCeti.DavisKahanExt.norm_quarterAcuteAngularCoordinate_lt_one U V hquarter
  have hsharp := sharp_symmetricNormingFunction
    N D (sub_pos.mpr hab) hD0 hD1 hsolveD hcontractive hDmem
  change N.Mem (tanTwoThetaGraphCoordinateOperator U V hquarter) ∧
      (b - a) * N.gauge (tanTwoThetaGraphCoordinateOperator U V hquarter) ≤
        2 * N.gauge H
  have hrepresentative :
      tanTwoThetaGraphCoordinateOperator U V hquarter =
        TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive := rfl
  rw [hrepresentative]
  refine ⟨hsharp.1, hsharp.2.trans ?_⟩
  calc
    2 * N.gauge D.B01 = 2 * N.gauge C.B01 := by rw [hDB01]
    _ = 2 * N.gauge B.B01 := by rw [hC_B01_gauge]
    _ = 2 * N.gauge Camb := by rw [hBgauge]
    _ ≤ 2 * N.gauge H :=
      mul_le_mul_of_nonneg_left hCambGauge (by norm_num)

/-- **Duplicate finite derivation retained as a regression proof.**

The main Davis--Kahan tree already contains the finite-dimensional Section 7
unitarily-invariant-norm theorem.  This theorem is deliberately retained
because it independently routes the same finite source hypotheses through the
new approximation-number/Riccati stack.  It is not the completion target and
must not be cited as the arbitrary-Hilbert-space theorem. -/
theorem tanTwoTheta_uiNorm_finite_alternate
    [FiniteDimensional ℂ E]
    (N : SymmetricNormingFunction)
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    ∃ hquarter : IsQuarterAcute U V,
      N.Mem (tanTwoThetaGraphCoordinateOperator U V hquarter) ∧
        (b - a) * N.gauge (tanTwoThetaGraphCoordinateOperator U V hquarter) ≤
          2 * N.gauge H := by
  have hquarter : IsQuarterAcute U V :=
    isQuarterAcute_of_orderedFormGap_finiteDimensional A H U V hA hH hAU hAplusH_V hab
      hUhigh hUperpLow hVhigh hVperpLow hHU hHUperp
  exact ⟨hquarter,
    tanTwoThetaGraphCoordinate_bound_of_quarterAcute N A H U V hA hH hAU
      hAplusH_V hab hUhigh hUperpLow hHU hHUperp hHmem hquarter⟩

/-- **Full bounded Davis--Kahan 1970 `tan 2Theta` theorem.**

No finite-dimensional or finite-carrier hypothesis is present.  The theorem
starts from the two reducing subspaces and the fully off-diagonal perturbation,
derives the strict quarter-angle branch, and proves the sharp estimate for the
directed `directedTanTwoAngleOperatorC` in every symmetric norming function.
-/
theorem tanTwoTheta_selectedBranch_symmetricNorming
    (N : SymmetricNormingFunction)
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    ∃ hquarter : IsQuarterAcute U V,
      N.Mem (directedTanTwoAngleOperatorC U V hquarter) ∧
        (b - a) * N.gauge (directedTanTwoAngleOperatorC U V hquarter) ≤
          2 * N.gauge H := by
  have hquarter : IsQuarterAcute U V :=
    isQuarterAcute_of_orderedFormGap A H U V hA hH hAU hAplusH_V
      hab hUhigh hUperpLow hVhigh hVperpLow hHU hHUperp
  have hgraph := tanTwoThetaGraphCoordinate_bound_of_quarterAcute
    N A H U V hA hH hAU hAplusH_V hab hUhigh hUperpLow
      hHU hHUperp hHmem hquarter
  have hseq : SameApproximationSingularSequence
      (directedTanTwoAngleOperatorC U V hquarter)
      (tanTwoThetaGraphCoordinateOperator U V hquarter) := by
    simpa only [tanTwoThetaGraphCoordinateOperator] using
      canonicalTanTwoAngle_hasSameApproximationNumbers_graphCoordinate U V hquarter
  have htransport := hseq.normingMem_iff_and_gauge_eq N
  refine ⟨hquarter, htransport.1.mpr hgraph.1, ?_⟩
  rw [htransport.2]
  exact hgraph.2

end

end DavisKahan
end TauCeti
