/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Sylvester.Basic
import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Operator.Restriction
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.DavisKahan.SinTheta.SpectralBridge

/-! # Restriction -/

open TauCeti.DavisKahan.Sylvester

/-!
# Restricted blocks for the infinite-dimensional sine theorems

The rectangular residual and perturbation blocks use Mathlib's `codRestrict`
and `restrict` directly. Their Sylvester equations and spectral separation
properties feed the infinite-dimensional sine estimates.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

omit [CompleteSpace E] in
/-- The closed-operator real resolvent set of a bounded operator's full-domain
realization is exactly the invertibility locus of `X - lam` in the bounded
operator algebra. -/
theorem mem_realResolventSet_ofBounded_iff (X : E →L[𝕜] E) (lam : ℝ) :
    lam ∈ TauCeti.LinearPMap.realResolventSet
        ((X.toLinearMap.toPMap ⊤)) ↔
      IsUnit (X - (lam : 𝕜) • (1 : E →L[𝕜] E)) := by
  constructor
  · rintro ⟨R, hleft, hright⟩
    refine ⟨⟨X - (lam : 𝕜) • (1 : E →L[𝕜] E), R, ?_, ?_⟩, rfl⟩
    · apply ContinuousLinearMap.ext
      intro y
      obtain ⟨h, hy⟩ := hright y
      have hy' : X (R y) - (lam : 𝕜) • R y = y := hy
      simpa [mul_apply_eq_comp, sub_apply,
        smul_apply, one_apply_eq_self] using hy'
    · apply ContinuousLinearMap.ext
      intro x
      have hx' : R (X x - (lam : 𝕜) • x) = x := hleft ⟨x, Submodule.mem_top⟩
      simpa [mul_apply_eq_comp, sub_apply,
        smul_apply, one_apply_eq_self] using hx'
  · rintro ⟨u, hu⟩
    have hval : (↑u : E →L[𝕜] E) = X - (lam : 𝕜) • (1 : E →L[𝕜] E) := hu
    refine ⟨↑u⁻¹, ?_, ?_⟩
    · intro x
      change (↑u⁻¹ : E →L[𝕜] E) (X (x : E) - (lam : 𝕜) • (x : E)) = (x : E)
      have hinv : (↑u⁻¹ : E →L[𝕜] E) * (X - (lam : 𝕜) • (1 : E →L[𝕜] E)) = 1 := by
        rw [← hval]; exact u.inv_mul
      have hpt := ContinuousLinearMap.ext_iff.mp hinv (x : E)
      simpa [mul_apply_eq_comp, sub_apply,
        smul_apply, one_apply_eq_self] using hpt
    · intro y
      refine ⟨Submodule.mem_top, ?_⟩
      change X ((↑u⁻¹ : E →L[𝕜] E) y) - (lam : 𝕜) • ((↑u⁻¹ : E →L[𝕜] E) y) = y
      have hinv : (X - (lam : 𝕜) • (1 : E →L[𝕜] E)) * (↑u⁻¹ : E →L[𝕜] E) = 1 := by
        rw [← hval]; exact u.mul_inv
      have hpt := ContinuousLinearMap.ext_iff.mp hinv y
      simpa [mul_apply_eq_comp, sub_apply,
        smul_apply, one_apply_eq_self] using hpt

omit [CompleteSpace E] in
/-- The bounded-realization real spectrum used by the `sin Θ` interval/exterior
bridge coincides with the Banach-algebra real spectrum used by the abstract
separation predicates. -/
theorem boundedRealSpectrum_eq_realSpectrum (X : E →L[𝕜] E) :
    TauCeti.DavisKahan.ExactSinTheta.boundedRealSpectrum X =
      TauCeti.DavisKahan.Foundation.realSpectrum X := by
  ext lam
  change lam ∈ (TauCeti.LinearPMap.realResolventSet
      ((X.toLinearMap.toPMap ⊤)))ᶜ ↔
    (lam : 𝕜) ∈ spectrum 𝕜 X
  rw [Set.mem_compl_iff, mem_realResolventSet_ofBounded_iff, spectrum.mem_iff,
    Algebra.algebraMap_eq_smul_one, ← IsUnit.neg_iff, neg_sub]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Orthogonal projection on the left is contractive in operator norm. -/
theorem projection_comp_opNorm_le
    (U : Submodule 𝕜 F) [U.HasOrthogonalProjection]
    (T : E →L[𝕜] F) :
    ‖U.starProjection ∘L T‖ ≤ ‖T‖ := by
  calc
    ‖U.starProjection ∘L T‖ ≤ ‖U.starProjection‖ * ‖T‖ :=
      U.starProjection.opNorm_comp_le T
    _ ≤ 1 * ‖T‖ := by
      gcongr
      exact U.starProjection_norm_le
    _ = ‖T‖ := one_mul _

omit [CompleteSpace E] [CompleteSpace F] in
/-- The rectangular projection--operator--inclusion block is contractive. -/
theorem restricted_projection_sandwich_norm_le
    (U : Submodule 𝕜 E) 
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] F) :
    ‖((Vᗮ.starProjection ∘L T ∘L U.subtypeL)).codRestrict Vᗮ
      (fun _x => Vᗮ.starProjection_apply_mem _)‖ ≤ ‖T‖ := by
  -- Explicit arguments: with the operator left as a metavariable, `rw` cannot solve it from
  -- the membership proof, whose type is only definitionally the expected one.
  rw [ContinuousLinearMap.opNorm_codRestrict_eq (Vᗮ.starProjection ∘L T ∘L U.subtypeL) Vᗮ
    (fun x => Vᗮ.starProjection_apply_mem _)]
  calc
    ‖Vᗮ.starProjection ∘L T ∘L U.subtypeL‖
        ≤ ‖Vᗮ.starProjection‖ * ‖T‖ * ‖U.subtypeL‖ := by
          refine (Vᗮ.starProjection.opNorm_comp_le (T ∘L U.subtypeL)).trans ?_
          rw [mul_assoc]
          gcongr
          exact T.opNorm_comp_le U.subtypeL
    _ ≤ 1 * ‖T‖ * 1 := by
      gcongr
      · exact Vᗮ.starProjection_norm_le
      · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
        intro x
        simp
    _ = ‖T‖ := by ring

omit [CompleteSpace E] in
/-- The directed projection gap is the norm of the rectangular cross block. -/
theorem directedGap_eq_restrictedBlock_norm
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖((Vᗮ.starProjection ∘L U.subtypeL)).codRestrict Vᗮ
      (fun _x => Vᗮ.starProjection_apply_mem _)‖ = U.directedProjectionGap V := by
  let T : U →L[𝕜] Vᗮ :=
    ((Vᗮ.starProjection ∘L U.subtypeL)).codRestrict Vᗮ (fun x => Vᗮ.starProjection_apply_mem _)
  have hle1 : ‖T‖ ≤ ‖Vᗮ.starProjection ∘L U.starProjection‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (Vᗮ.starProjection ∘L U.starProjection)) ?_
    intro x
    have hPx : U.starProjection (x : E) = (x : E) :=
      Submodule.starProjection_eq_self_iff.mpr x.property
    have h := (Vᗮ.starProjection ∘L U.starProjection).le_opNorm (x : E)
    -- Corestriction does not change the norm of the underlying vector.
    change ‖Vᗮ.starProjection (x : E)‖ ≤
      ‖Vᗮ.starProjection ∘L U.starProjection‖ * ‖(x : E)‖
    simpa [hPx] using h
  have hle2 : ‖Vᗮ.starProjection ∘L U.starProjection‖ ≤ ‖T‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro x
    let ux : U := ⟨U.starProjection x, U.starProjection_apply_mem x⟩
    have hTx := T.le_opNorm ux
    have hproj : ‖U.starProjection x‖ ≤ ‖x‖ :=
      U.norm_starProjection_apply_le x
    calc
      ‖(Vᗮ.starProjection ∘L U.starProjection) x‖ = ‖T ux‖ := by rfl
      _ ≤ ‖T‖ * ‖ux‖ := hTx
      _ ≤ ‖T‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hproj (norm_nonneg T)
  change ‖T‖ = ‖Vᗮ.starProjection ∘L U.starProjection‖
  exact le_antisymm hle1 hle2

omit [CompleteSpace E] [CompleteSpace F] in
/-- The directed residual block satisfies the restricted Sylvester equation. -/
theorem directedResidual_sylvesterEquation
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : A.Reduces U)
    {X : F →L[𝕜] E} {M : F →L[𝕜] F} :
    ContinuousLinearMap.sylvesterOperator (A.restrict hU.2) M
      (((Uᗮ.starProjection ∘L X)).codRestrict Uᗮ (fun _x => Uᗮ.starProjection_apply_mem _)) =
      ((Uᗮ.starProjection ∘L DavisKahan.residual A X M)).codRestrict Uᗮ
        (fun _x => Uᗮ.starProjection_apply_mem _) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  have hUperp : A.Reduces Uᗮ := ContinuousLinearMap.IsSymmetric.reduces_of_invariant hA hU.2
  have hcomm := ContinuousLinearMap.starProjection_apply_comm_of_reduces A Uᗮ hUperp (X x)
  change A (Uᗮ.starProjection (X x)) - Uᗮ.starProjection (X (M x)) =
    Uᗮ.starProjection (A (X x) - X (M x))
  rw [map_sub, hcomm]

omit [CompleteSpace E] in
/-- The directed perturbation block satisfies its restricted Sylvester
equation. -/
theorem directedPerturbation_sylvesterEquation
    {A B : E →L[𝕜] E}
    (_hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E}
     [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V) :
    ContinuousLinearMap.sylvesterOperator (B.restrict hV.2)
      (A.restrict hU.1)
      (((Vᗮ.starProjection ∘L U.subtypeL)).codRestrict Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _)) =
      ((Vᗮ.starProjection ∘L (B - A) ∘L U.subtypeL)).codRestrict Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ContinuousLinearMap.sylvesterOperator, sub_apply, ContinuousLinearMap.comp_apply]
  have hVperp : B.Reduces Vᗮ := ContinuousLinearMap.IsSymmetric.reduces_of_invariant hB hV.2
  have hcomm := ContinuousLinearMap.starProjection_apply_comm_of_reduces B Vᗮ hVperp (x : E)
  change B (Vᗮ.starProjection (x : E)) - Vᗮ.starProjection (A (x : E)) =
    Vᗮ.starProjection (B (x : E) - A (x : E))
  rw [map_sub, hcomm]

omit [CompleteSpace E] in
/-- Hybrid separation transports to the two actual restricted operators. -/
theorem hybridGap_restrictions
    {A B : E →L[𝕜] E}
    {U V : Submodule 𝕜 E}
     
    (_hA : A.IsSymmetric) (_hB : B.IsSymmetric)
    (hU : A.Reduces U) (hV : B.Reduces V)
    {d : ℝ} (hgap : HybridGap A B U V d) :
    SpectraSeparated (B.restrict hV.2) ⊤
      (A.restrict hU.1) ⊤ d := by
  refine ⟨by intro x hx; trivial, by intro x hx; trivial, ?_⟩
  intro b hb a ha
  have hb' : b ∈ restrictedSpectrum B Vᗮ := by
    rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum B Vᗮ hV.2]
    rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_top] at hb
    exact hb
  have ha' : a ∈ restrictedSpectrum A U := by
    rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum A U hU.1]
    rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_top] at ha
    exact ha
  simpa [abs_sub_comm] using hgap.2.2 a ha' b hb'

omit [CompleteSpace E] in
/-- Interval/exterior data transports to the restriction-level gap used by the
rectangular ideal theorem. -/
theorem intervalExteriorSeparated_restrictions
    {A B : E →L[𝕜] E}
    {U V : Submodule 𝕜 E}
     
    (_hA : A.IsSymmetric) (_hB : B.IsSymmetric)
    (hU : A.Reduces U) (hV : B.Reduces V)
    {left right d : ℝ}
    (hgap : IntervalExteriorSeparated A U B Vᗮ left right d) :
    TauCeti.DavisKahan.ExactSinTheta.IntervalExteriorGap
      (B.restrict hV.2) (A.restrict hU.1)
      left right d := by
  right
  constructor
  · intro a ha
    have ha' : a ∈ restrictedSpectrum A U := by
      rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum A U hU.1]
      rw [boundedRealSpectrum_eq_realSpectrum] at ha
      exact ha
    exact hgap.1.2 ha'
  · intro b hb
    have hb' : b ∈ restrictedSpectrum B Vᗮ := by
      rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum B Vᗮ hV.2]
      rw [boundedRealSpectrum_eq_realSpectrum] at hb
      exact hb
    exact hgap.2.2 hb'

end
end DavisKahanExt
end TauCeti
