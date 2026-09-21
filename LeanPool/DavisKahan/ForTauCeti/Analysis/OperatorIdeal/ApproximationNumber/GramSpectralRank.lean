/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralVectorBounds

/-!
# Spectral ranks of Gram cutoffs

This module is the rank-theoretic input for finite spectral-band selection.
For the positive Gram operator `X†X`, approximation-number thresholds control
the dimensions of the upper spectral ranges:

* if `r < a_n(X)`, the closed upper range `[r², ∞)` has rank at least `n+1`;
* if `a_n(X) < r`, the open upper range `(r², ∞)` has rank at most `n`.

The proofs are explicit min--max arguments.  No tactic search, compactness, or
singular-vector attainment is used.  The spectral measure is Tau Ceti's native
`LinearPMap.spectralPVM`; no Spectra self-adjoint wrapper or Stone group is
introduced for this bounded operator.

## Provenance

*Moved, not restated.*  This module was written in the `FinishTanTwoTheta`
completion workspace and reached its present home in two steps, the second of
which is the one a reader should know about: **its imports are three `ForTauCeti`
leaves and nothing else**, so it had been sitting in a library it did not depend
on.  Statements, proofs and the `TauCeti.ApproximationNumber` namespace are
unchanged throughout; only the enclosing library and the consumers' import lines
moved.  `FinishTanTwoTheta.GroundedImports` was dropped along the way because it
imports the whole Davis--Kahan aggregate and so could not travel.

**The vector-local half-line bounds left in a third step.**  They are now
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralVectorBounds.lean`, in
the `TauCeti.LinearPMap` namespace, which is where the second paragraph below
already said they belonged.  The Rayleigh--Ritz rank counting needs them without
needing anything about approximation numbers.

**Two hypotheses the move falsified, recorded because they are the argument for
making such moves early.**  Under the stricter options this library is built with,
the file needed `sub_apply` in place of a deprecated
`ContinuousLinearMap.sub_apply` twice; and by *dependency* it is not
approximation-number material at all — it imports `LinearPMap.Constructions` and
`LinearPMap.SpectralFormBounds`, so it is submittable only after the unbounded
spectral measure, not with the `a`-numbers its name suggests.
-/

public section

namespace TauCeti
namespace ApproximationNumber

open scoped InnerProductSpace
open Set

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]



/-- The bounded positive Gram operator. -/
@[expose]
def gramOperator (X : E0 →L[ℂ] E1) : E0 →L[ℂ] E0 :=
  X.adjoint ∘L X

/-- The Gram operator is self-adjoint. -/
theorem gramOperator_isSelfAdjoint (X : E0 →L[ℂ] E1) :
    IsSelfAdjoint (gramOperator X) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪X.adjoint (X x), y⟫_ℂ = ⟪x, X.adjoint (X y)⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- The Gram quadratic form is the squared image norm. -/
theorem re_inner_gramOperator (X : E0 →L[ℂ] E1) (x : E0) :
    RCLike.re ⟪gramOperator X x, x⟫_ℂ = ‖X x‖ ^ 2 := by
  change RCLike.re ⟪X.adjoint (X x), x⟫_ℂ = ‖X x‖ ^ 2
  rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The bounded Gram operator viewed as an everywhere-defined partial map. -/
@[expose]
def gramLinearPMap (X : E0 →L[ℂ] E1) : E0 →ₗ.[ℂ] E0 :=
  ((gramOperator X : E0 →ₗ[ℂ] E0).toPMap ⊤)

/-- The Gram partial map is everywhere defined: it comes from a bounded operator. -/
@[simp] theorem gramLinearPMap_domain (X : E0 →L[ℂ] E1) :
    (gramLinearPMap X).domain = ⊤ := rfl

/-- On its domain the Gram partial map is the bounded Gram operator. -/
@[simp] theorem gramLinearPMap_apply (X : E0 →L[ℂ] E1)
    (x : (gramLinearPMap X).domain) :
    gramLinearPMap X x = gramOperator X (x : E0) := rfl

/-- The native Tau Ceti self-adjointness proof for the Gram partial map. -/
theorem gramLinearPMap_isSelfAdjoint (X : E0 →L[ℂ] E1) :
    IsSelfAdjoint (gramLinearPMap X) :=
  LinearPMap.isSelfAdjoint_toPMap_top (gramOperator_isSelfAdjoint X)

/-- The native Tau Ceti spectral PVM of `X†X`. -/
noncomputable def gramSpectralPVM (X : E0 →L[ℂ] E1) : ProjValMeasure E0 :=
  LinearPMap.spectralPVM (gramLinearPMap_isSelfAdjoint X)

/-- Definitional bridge between the named Gram PVM and Tau Ceti's pointwise
spectral-projection API.  Keeping this as a named equality avoids repeatedly
asking the elaborator to unfold the full spectral construction through a
`change` tactic. -/
theorem gramSpectralPVM_proj_eq_specProjection (X : E0 →L[ℂ] E1)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (gramSpectralPVM X).proj B hB =
      TauCeti.LinearPMap.specProjection (gramLinearPMap_isSelfAdjoint X) B hB := by
  rw [TauCeti.LinearPMap.specProjection_def]
  rfl

/-- A strict lower threshold for `a_n(X)` forces at least `n+1` dimensions in
`E_{X†X}([r²,∞))`. -/
theorem natCast_succ_le_rank_gramProjection_Ici_of_lt_approximationNumber
    (X : E0 →L[ℂ] E1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < X.approximationNumber n) :
    ((n + 1 : ℕ) : Cardinal) ≤
      ((gramSpectralPVM X).proj (Set.Ici (r ^ 2)) measurableSet_Ici).rank := by
  classical
  let P : E0 →L[ℂ] E0 :=
    (gramSpectralPVM X).proj (Set.Ici (r ^ 2)) measurableSet_Ici
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    X.exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex n hr0 hr
  let V : Submodule ℂ E0 := Submodule.span ℂ (Set.range v)
  let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hv
  let W : Submodule ℂ E0 := P.range
  let f : V →ₗ[ℂ] W :=
    { toFun := fun x => ⟨P x, ⟨x, rfl⟩⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro c x; apply Subtype.ext; simp }
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    let z : E0 := (x : E0) - (y : E0)
    have hzV : z ∈ V := V.sub_mem x.property y.property
    have hPz : P z = 0 := by
      have hval := congrArg Subtype.val hxy
      change P (x : E0) = P (y : E0) at hval
      simpa [z, map_sub] using sub_eq_zero.mpr hval
    have hzDom : z ∈ (gramLinearPMap X).domain := by
      rw [gramLinearPMap_domain]
      exact Submodule.mem_top
    have henergy := LinearPMap.re_inner_le_of_specProjection_Ici_apply_eq_zero
      (gramLinearPMap_isSelfAdjoint X) (⟨z, hzDom⟩ : (gramLinearPMap X).domain) (by
        rw [← gramSpectralPVM_proj_eq_specProjection X
          (Set.Ici (r ^ 2)) measurableSet_Ici]
        simpa only [P] using hPz)
    have hupper : ‖X z‖ ^ 2 ≤ r ^ 2 * ‖z‖ ^ 2 := by
      calc
        ‖X z‖ ^ 2 = RCLike.re ⟪gramOperator X z, z⟫_ℂ := by
          symm
          exact re_inner_gramOperator X z
        _ = RCLike.re
            ⟪gramLinearPMap X (⟨z, hzDom⟩ : (gramLinearPMap X).domain), z⟫_ℂ := by
          rw [gramLinearPMap_apply]
        _ ≤ r ^ 2 * ‖z‖ ^ 2 := henergy
    have hlower : s * ‖z‖ ≤ ‖X z‖ := hV z hzV
    have hs0 : 0 ≤ s := hr0.trans hrs.le
    have hupper' : ‖X z‖ ^ 2 ≤ (r * ‖z‖) ^ 2 := by
      simpa only [mul_pow] using hupper
    have hupperLinear : ‖X z‖ ≤ r * ‖z‖ :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg z))).1 hupper'
    have hz0 : ‖z‖ = 0 := by
      nlinarith [hlower.trans hupperLinear, norm_nonneg z]
    have hz : (x : E0) - (y : E0) = 0 := by
      simpa only [z] using norm_eq_zero.mp hz0
    exact sub_eq_zero.mp hz
  have hfb : LinearIndependent ℂ (f ∘ fun i => b i) := by
    exact b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf_injective)
  have hrankW : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ W :=
    (Module.le_rank_iff).2 ⟨fun i => f (b i), hfb⟩
  change ((n + 1 : ℕ) : Cardinal) ≤ P.rank at hrankW
  simpa only [P] using hrankW

/-- A strict upper threshold for `a_n(X)` forces the open upper Gram range
`E_{X†X}((r²,∞))` to have rank at most `n`. -/
theorem rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt
    (X : E0 →L[ℂ] E1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : X.approximationNumber n < r) :
    ((gramSpectralPVM X).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi).rank ≤
      (n : Cardinal) := by
  classical
  let P : E0 →L[ℂ] E0 :=
    (gramSpectralPVM X).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi
  by_contra hnot
  have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hnot
  have hnrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ P.range := by
    change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
    rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one] at hlt
    exact hlt
  obtain ⟨g, hg⟩ := (Module.le_rank_iff).1 hnrank
  let v : Fin (n + 1) → E0 := P.range.subtype ∘ g
  have hv : LinearIndependent ℂ v := by
    exact hg.map' P.range.subtype
      (LinearMap.ker_eq_bot.mpr P.range.injective_subtype)
  have hrle : r ≤ X.approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent X n v hv
    intro x hxspan hxnorm
    have hspan_le : Submodule.span ℂ (Set.range v) ≤ P.range := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      exact (g i).property
    have hxP : x ∈ P.range := hspan_le hxspan
    have hPx : P x = x := by
      rcases hxP with ⟨y, rfl⟩
      change P (P y) = P y
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : E0 →L[ℂ] E0 => T y)
          ((gramSpectralPVM X).proj_idem (Set.Ioi (r ^ 2)) measurableSet_Ioi)
    have hzlow :
        (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic x = 0 := by
      let Q : E0 →L[ℂ] E0 :=
        (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic
      have hinter : Set.Iic (r ^ 2) ∩ Set.Ioi (r ^ 2) = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi,
          Set.mem_empty_iff_false, iff_false]
        exact fun ht => (not_lt_of_ge ht.1) ht.2
      have hQP_raw :
          (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic *
              (gramSpectralPVM X).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi = 0 := by
        rw [(gramSpectralPVM X).proj_inter,
          (gramSpectralPVM X).proj_congr hinter
            (measurableSet_Iic.inter measurableSet_Ioi) MeasurableSet.empty,
          (gramSpectralPVM X).proj_empty]
      have hQP : Q * P = 0 := by
        simpa only [Q, P] using hQP_raw
      have hQPx := congrArg (fun T : E0 →L[ℂ] E0 => T x) hQP
      calc
        (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic x =
            (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic (P x) := by
          rw [hPx]
        _ = 0 := by
          simpa only [Q, _root_.mul_apply_eq_comp, zero_apply] using hQPx
    have hxDom : x ∈ (gramLinearPMap X).domain := by
      rw [gramLinearPMap_domain]
      exact Submodule.mem_top
    have henergy := LinearPMap.le_re_inner_of_specProjection_Iic_apply_eq_zero
      (gramLinearPMap_isSelfAdjoint X) (⟨x, hxDom⟩ : (gramLinearPMap X).domain) (by
        rw [← gramSpectralPVM_proj_eq_specProjection X
          (Set.Iic (r ^ 2)) measurableSet_Iic]
        exact hzlow)
    have hlowerSq : r ^ 2 * ‖x‖ ^ 2 ≤ ‖X x‖ ^ 2 := by
      calc
        r ^ 2 * ‖x‖ ^ 2 ≤
            RCLike.re
              ⟪gramLinearPMap X (⟨x, hxDom⟩ : (gramLinearPMap X).domain), x⟫_ℂ :=
          henergy
        _ = RCLike.re ⟪gramOperator X x, x⟫_ℂ := by
          rw [gramLinearPMap_apply]
        _ = ‖X x‖ ^ 2 := re_inner_gramOperator X x
    have hlowerSq' : (r * ‖x‖) ^ 2 ≤ ‖X x‖ ^ 2 := by
      simpa only [mul_pow] using hlowerSq
    have : r * ‖x‖ ≤ ‖X x‖ :=
      (sq_le_sq₀ (mul_nonneg hr0 (norm_nonneg x)) (norm_nonneg _)).1 hlowerSq'
    simpa only [hxnorm, mul_one] using this
  exact (not_le_of_gt hr) hrle

end

end ApproximationNumber
end TauCeti
