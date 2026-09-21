/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.ShiftedInverse
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.Neumann
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Ideal-gauge shifted-inverse estimates

The bounded shift extension and the exterior-left/interval-right ideal-gauge
Sylvester estimate built from it.
-/

namespace TauCeti
namespace DavisKahan
namespace Sylvester


open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **Bounded extension of the centered interval block.**  A symmetric dense
partial map whose quadratic form lies in `[β, α]` has a bounded shift `B - c`
on its domain (`c = (α+β)/2`, radius `r = (α-β)/2`), which therefore extends
to a bounded operator on the whole space with the same norm bound. -/
theorem exists_bounded_shift_extension
    {B : F →ₗ.[𝕜] F} (hsym : TauCeti.LinearPMap.IsSymmetric B)
    (hBdense : Dense (B.domain : Set F)) {β α : ℝ} (hβα : β ≤ α)
    (hlow : TauCeti.LinearPMap.SemiboundedBelow B β)
    (hhigh : TauCeti.LinearPMap.SemiboundedAbove B α) :
    ∃ S : F →L[𝕜] F, ‖S‖ ≤ (α - β) / 2 ∧
      ∀ y : B.domain, S (y : F) =
        B y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := by
  have hr0 : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  set g : B.domain →ₗ[𝕜] F :=
    { toFun := fun y => B y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F)
      map_add' := by
        intro x y
        rw [_root_.LinearPMap.map_add B x y]
        simp only [Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro a y
        rw [_root_.LinearPMap.map_smul B a y]
        simp only [Submodule.coe_smul, smul_sub, RingHom.id_apply]
        rw [smul_comm] } with hgdef
  have hgapply : ∀ y : B.domain,
      g y = B y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := by
    intro y
    simp [hgdef]
  have hgbound : ∀ y : B.domain, ‖g y‖ ≤ (α - β) / 2 * ‖y‖ := by
    intro y
    rw [hgapply y]
    exact norm_shift_apply_le_of_form_bounds hsym hBdense hβα hlow hhigh y
  set f : B.domain →L[𝕜] F := g.mkContinuous ((α - β) / 2) hgbound with hfdef
  have hrange : Set.range ((B.domain.subtypeL : B.domain →L[𝕜] F)) =
      (B.domain : Set F) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hdense : DenseRange ((B.domain.subtypeL : B.domain →L[𝕜] F)) := by
    show Dense (Set.range _)
    rw [hrange]
    exact hBdense
  have hui : IsUniformInducing ((B.domain.subtypeL : B.domain →L[𝕜] F)) :=
    isometry_subtype_coe.isUniformInducing
  refine ⟨f.extend (B.domain.subtypeL), ?_, ?_⟩
  · have h1 : ‖f.extend (B.domain.subtypeL)‖ ≤ ((1 : NNReal) : ℝ) * ‖f‖ := by
      refine ContinuousLinearMap.opNorm_extend_le f hdense fun x => ?_
      rw [NNReal.coe_one, one_mul]
      exact le_of_eq rfl
    have h2 : ‖f‖ ≤ (α - β) / 2 :=
      LinearMap.mkContinuous_norm_le g hr0 hgbound
    calc ‖f.extend (B.domain.subtypeL)‖
        ≤ ((1 : NNReal) : ℝ) * ‖f‖ := h1
      _ = ‖f‖ := by rw [NNReal.coe_one, one_mul]
      _ ≤ (α - β) / 2 := h2
  · intro y
    have h := ContinuousLinearMap.extend_eq f hdense hui y
    calc (f.extend (B.domain.subtypeL)) (y : F)
        = f y := h
      _ = B y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := hgapply y

/- The two one-unbounded Neumann engines and the bounded-realization
transfer lemma live in `Core.UnboundedSpectral`, below this source-facing
assembly layer. -/

/-- **Ideal-gauge interval/exterior Sylvester estimate, exterior block on
the left.**  The interval block `B` (quadratic form in `[β, α]`) is realized
bounded through its shift extension and the equation transfers by density;
the exterior block `A` carries a proof-carrying two-sided shifted inverse.
Both closed blocks may be genuinely unbounded a priori. -/
theorem mem_and_gauge_le_of_exteriorLeft_intervalRight
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    (hAclosed : A.IsClosed) (hBdense : Dense (B.domain : Set F))
    {X C : F →L[𝕜] E} {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsym : TauCeti.LinearPMap.IsSymmetric B)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow B β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B α)
    (hAres : TauCeti.LinearPMap.TwoSidedShiftedInverseBound A ((α + β) / 2)
      ((α - β) / 2 + δ))
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gaugeReal X ≤ N.gaugeReal C := by
  have hr0 : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  obtain ⟨S, hSnorm, hSeq⟩ :=
    exists_bounded_shift_extension hBsym hBdense hβα hBlow hBhigh
  obtain ⟨J, hdom, hleft, hright, hJnorm⟩ := hAres
  -- the bounded realization of `B` and the transferred equation
  set T : F →L[𝕜] F :=
    S + (((α + β) / 2 : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F with hTdef
  have hT : ∀ y : B.domain, T (y : F) = B y := by
    intro y
    simp only [hTdef, add_apply, smul_apply, ContinuousLinearMap.id_apply]
    rw [hSeq y]
    abel
  have hEqT : TauCeti.LinearPMap.SylvesterEquation
      A (T.toLinearMap.toPMap ⊤) X C :=
    SylvesterEquation_boundedRealization hAclosed hBdense hEq hT
  -- shift both blocks by the center
  set c𝕜 : 𝕜 := (((α + β) / 2 : ℝ) : 𝕜) with hc𝕜
  set A' : E →ₗ.[𝕜] E :=
    TauCeti.LinearPMap.addBounded A
      (-(c𝕜 • ContinuousLinearMap.id 𝕜 E)) with hA'def
  have hA'apply : ∀ x : A.domain,
      A' x = A x - c𝕜 • (x : E) := by
    intro x
    change A x + (-(c𝕜 • ContinuousLinearMap.id 𝕜 E)) (x : E) =
      A x - c𝕜 • (x : E)
    simp [sub_eq_add_neg]
  have hEq' : TauCeti.LinearPMap.SylvesterEquation
      A' (S.toLinearMap.toPMap ⊤) X C := by
    refine ⟨fun x => hEqT.mapsTo_domain x, fun x => ?_⟩
    have h1 : A ⟨X (x : F), hEqT.mapsTo_domain x⟩ -
        X (T (x : F)) = C (x : F) := hEqT.equation x
    have h2 : A' ⟨X (x : F), hEqT.mapsTo_domain x⟩ =
        A ⟨X (x : F), hEqT.mapsTo_domain x⟩ -
          c𝕜 • X (x : F) :=
      hA'apply ⟨X (x : F), hEqT.mapsTo_domain x⟩
    have h3 : X (S (x : F)) = X (T (x : F)) - c𝕜 • X (x : F) := by
      have : S (x : F) = T (x : F) - c𝕜 • (x : F) := by
        simp only [hTdef, add_apply, smul_apply, ContinuousLinearMap.id_apply]
        abel
      rw [this, map_sub, map_smul]
    change A' ⟨X (x : F), hEqT.mapsTo_domain x⟩ -
      X (S (x : F)) = C (x : F)
    rw [h2, h3, ← h1]
    abel
  -- the everywhere-defined inverse of the shifted exterior block
  refine Sylvester_mem_and_gauge_le_of_unbounded_bound_inverse N
    (⟨J, hdom, ?_, ?_⟩ : TauCeti.LinearPMap.HasBoundedEverywhereInverse A') S hr0 hδ
    hJnorm hSnorm hEq' hC
  · intro y
    change A ⟨J y, hdom y⟩ + -(c𝕜 • J y) = y
    have h := hright y
    rw [sub_eq_add_neg] at h
    exact h
  · intro x
    change J (A x + -(c𝕜 • (x : E))) = (x : E)
    have h := hleft x
    rw [sub_eq_add_neg] at h
    exact h

end Sylvester
end DavisKahan
end TauCeti
