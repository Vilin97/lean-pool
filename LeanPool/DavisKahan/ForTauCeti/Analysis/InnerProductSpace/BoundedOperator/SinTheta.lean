/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducedExtension
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.QuadraticFormBounds
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Operator

/-!
# Dimension-free Davis--Kahan `sin Θ`

The supported scalar-generic coercive theorem.  Spectral hypotheses are
converted to these form bounds by the generic `TauCeti.SpectralOrder` API.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/BoundedOperator/SinTheta.lean`
before the dependency-closed base of the sin-Θ core moved
into the staging layer.

**Renamespaced.**  The theorem below is
generic operator geometry — two self-adjoint operators, two reducing subspaces,
a form gap — and it was filed under `TauCeti.DavisKahan`, the namespace of the
paper that happened to need it.  `ForTauCeti/README.md` §2 asks for `TauCeti` or
the canonical Mathlib namespace of the object extended; the conclusion's head
symbol is `Submodule.starProjection`, so it is now in `Submodule`.  The statement
and the proof are unchanged apart from spelling the compatibility aliases
`Reduces`, `projection` and `norm_sylvester_le_of_coercive` as the canonical
`ContinuousLinearMap.Reduces`, `Submodule.starProjection` and
`TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq` they forwarded
to. Consumers now use these canonical declarations directly.
-/

public section

namespace Submodule

open TauCeti
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- **The quadratic form of a reduced extension splits**, for an extension
packaged from a bounded `T` and a reducing subspace.

The mathematics is `TauCeti.re_inner_reducedExtension_self`, which is stated at
the value `T (P x) + κ • (x - P x)` and assumes only invariance; this wrapper
supplies the packaging and drops `Reduces` to its invariance half. -/
private theorem re_inner_reducedExtension_self {T : E →L[𝕜] E}
    {W : Submodule 𝕜 E} [W.HasOrthogonalProjection] (hW : T.Reduces W)
    (κ : ℝ) (x : E) :
    RCLike.re ⟪(T ∘L W.starProjection
        + ((κ : ℝ) : 𝕜) • (1 - W.starProjection)) x, x⟫_𝕜
      = RCLike.re ⟪T (W.starProjection x), W.starProjection x⟫_𝕜
        + κ * ‖x - W.starProjection x‖ ^ 2 := by
  have hval : (T ∘L W.starProjection
      + ((κ : ℝ) : 𝕜) • (1 - W.starProjection)) x
      = T (W.starProjection x) + ((κ : ℝ) : 𝕜) • (x - W.starProjection x) := by
    simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, sub_apply,
      one_apply_eq_self]
  rw [hval]
  exact TauCeti.re_inner_reducedExtension_self (R := (T : E →ₗ[𝕜] E)) hW.1 κ x

/-- **The dimension-free operator-norm Davis--Kahan `sin Θ` theorem, coercivity
form.**  For self-adjoint `A, B` on an arbitrary Hilbert space, `U` reducing `A`
with quadratic form `≥ (c+g)‖·‖²` on `U`, and `V` reducing `B` with quadratic
form `≤ c‖·‖²` on `V`,

`‖P_V P_U‖ ≤ ‖B − A‖ / g`.

This is the genuine infinite-dimensional `sin Θ` bound: the analytic core is the
integral-free Sylvester estimate
`TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq` (no spectral
measure, no dimension or completeness hypothesis on the *bound* itself), and the
block construction `A ∘L P + (c+g)(1−P)`, `B ∘L Q + c(1−Q)` uses only the
dimension-free projection commutation
`ContinuousLinearMap.starProjection_apply_comm_of_reduces`.  The
spectrum-predicate forms (`sinTheta_perturbation`, `IntervalExteriorSeparated`)
follow from this once a bounded spectral theorem converts spectral separation to
these coercivity bounds. -/
theorem sinTheta_directed_coercive
    {A B : E →L[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hVc : ∀ x ∈ V, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖ ≤ ‖B - A‖ / g := by
  set P := U.starProjection with hP
  set Q := V.starProjection with hQ
  set A' : E →L[𝕜] E := A ∘L P + ((c + g : ℝ) : 𝕜) • (1 - P) with hA'
  set B' : E →L[𝕜] E := B ∘L Q + ((c : ℝ) : 𝕜) • (1 - Q) with hB'
  set X : E →L[𝕜] E := P ∘L Q with hX
  set Y : E →L[𝕜] E := P ∘L (A - B) ∘L Q with hY
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hAsa : IsSelfAdjoint A := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA
  have hBsa : IsSelfAdjoint B := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hcgsa : IsSelfAdjoint ((c + g : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hcsa : IsSelfAdjoint ((c : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hone : IsSelfAdjoint (1 : E →L[𝕜] E) := IsSelfAdjoint.one _
  -- commutations
  have hcommA : A ∘L P = P ∘L A := by
    ext x; simp only [ContinuousLinearMap.comp_apply]
    exact (ContinuousLinearMap.starProjection_apply_comm_of_reduces A U hU x).symm
  have hcommB : B ∘L Q = Q ∘L B := by
    ext x; simp only [ContinuousLinearMap.comp_apply]
    exact (ContinuousLinearMap.starProjection_apply_comm_of_reduces B V hV x).symm
  -- self-adjointness of A', B'
  have hA'sa : IsSelfAdjoint A' := by
    have h1 : IsSelfAdjoint (A ∘L P) := (IsSelfAdjoint.commute_iff hAsa hPsa).mp hcommA
    have h2 : IsSelfAdjoint (((c + g : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - P)) := by
      rw [isSelfAdjoint_iff, star_smul, hcgsa.star_eq, (hone.sub hPsa).star_eq]
    exact hA' ▸ h1.add h2
  have hB'sa : IsSelfAdjoint B' := by
    have h1 : IsSelfAdjoint (B ∘L Q) := (IsSelfAdjoint.commute_iff hBsa hQsa).mp hcommB
    have h2 : IsSelfAdjoint (((c : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - Q)) := by
      rw [isSelfAdjoint_iff, star_smul, hcsa.star_eq, (hone.sub hQsa).star_eq]
    exact hB' ▸ h1.add h2
  have hA'sym : A'.IsSymmetric := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hA'sa
  have hB'sym : B'.IsSymmetric := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hB'sa
  -- coercivity of A'
  have hA'c : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A' x, x⟫_𝕜 := by
    intro x
    have hpx : P x ∈ U := U.starProjection_apply_mem x
    have hre : RCLike.re ⟪A' x, x⟫_𝕜
        = RCLike.re ⟪A (P x), P x⟫_𝕜 + (c + g) * ‖x - P x‖ ^ 2 := by
      rw [hA', hP]; exact re_inner_reducedExtension_self hU (c + g) x
    have hpyth : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
      rw [hP]; exact TauCeti.norm_sq_eq_starProjection_add_sub x
    rw [hre, hpyth]
    nlinarith [hUc (P x) hpx]
  -- upper bound for B'
  have hB'c : ∀ x, RCLike.re ⟪B' x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
    intro x
    have hqx : Q x ∈ V := V.starProjection_apply_mem x
    have hre : RCLike.re ⟪B' x, x⟫_𝕜
        = RCLike.re ⟪B (Q x), Q x⟫_𝕜 + c * ‖x - Q x‖ ^ 2 := by
      rw [hB', hQ]; exact re_inner_reducedExtension_self hV c x
    have hpyth : ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := by
      rw [hQ]; exact TauCeti.norm_sq_eq_starProjection_add_sub x
    rw [hre, hpyth]
    nlinarith [hVc (Q x) hqx]
  -- Sylvester relation A' X - X B' = Y
  have hsylv : ContinuousLinearMap.sylvesterOperator A' B' X = Y := by
    change A' ∘L X - X ∘L B' = Y
    ext x
    have hQxV : Q x ∈ V := V.starProjection_apply_mem x
    have hPP : P (P (Q x)) = P (Q x) :=
      U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem (Q x))
    have hQrest : Q (x - Q x) = 0 := by
      have hQQ : Q (Q x) = Q x := V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
      rw [map_sub, hQQ, sub_self]
    have hQBQ : Q (B (Q x)) = B (Q x) := V.starProjection_eq_self_iff.mpr (hV.1 _ hQxV)
    have hAP : A (P (Q x)) = P (A (Q x)) :=
      (ContinuousLinearMap.starProjection_apply_comm_of_reduces A U hU (Q x)).symm
    have hAX : (A' ∘L X) x = A (P (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hA', add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, hPP, sub_self, smul_zero, add_zero]
    have hXB : (X ∘L B') x = P (B (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hB', add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, map_add, map_smul, hQBQ, hQrest, map_zero, smul_zero, add_zero]
    have hYx : Y x = P (A (Q x)) - P (B (Q x)) := by
      simp only [hY, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    rw [sub_apply, hAX, hXB, hYx, hAP]
  -- norm bound
  have hYnorm : ‖Y‖ ≤ ‖B - A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hc : ‖P ((A - B) (Q x))‖ ≤ ‖(A - B) (Q x)‖ := by
      rw [hP]; exact U.norm_starProjection_apply_le _
    calc ‖Y x‖ = ‖P ((A - B) (Q x))‖ := by simp only [hY, ContinuousLinearMap.comp_apply]
      _ ≤ ‖(A - B) (Q x)‖ := hc
      _ = ‖(B - A) (Q x)‖ := by rw [show A - B = -(B - A) by abel, neg_apply, norm_neg]
      _ ≤ ‖B - A‖ * ‖Q x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B - A‖ * ‖x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [hQ]; exact V.norm_starProjection_apply_le x
  have hXbound : ‖X‖ ≤ ‖B - A‖ / g :=
    (TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq
        hA'sym hB'sym hg hA'c hB'c hsylv).trans (by gcongr)
  have hstar : star (Q ∘L P : E →L[𝕜] E) = P ∘L Q := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      hPsa.star_eq, hQsa.star_eq]
  have : ‖(Q ∘L P : E →L[𝕜] E)‖ = ‖X‖ := by rw [hX, ← hstar]; exact (norm_star _).symm
  calc ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖
      = ‖(Q ∘L P : E →L[𝕜] E)‖ := by rw [hP, hQ]
    _ = ‖X‖ := this
    _ ≤ ‖B - A‖ / g := hXbound


/-- Directed `sin Θ` bound stated with reusable subspace form-bound predicates. -/
theorem sinTheta_directed_of_formBounds
    {A B : E →L[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : A.LowerFormBoundOn U (c + g))
    (hVlo : B.UpperFormBoundOn V c) :
    ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖ ≤ ‖B - A‖ / g :=
  sinTheta_directed_coercive hA hB hU hV hg hUhi hVlo


end Submodule
