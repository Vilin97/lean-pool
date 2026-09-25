/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


/-
The dense-range lemma below is adapted from Adam Bornemann's private lemma
`denseRange_of_selfAdjoint_injective` in
`Spectra/Modular/Tomita/BoundedPicture.lean`, Spectra commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.  It is made public here because
it is the exact bounded-to-unbounded bridge used by variational resolvents.
The original and adapted files are Apache-2.0 licensed.
-/

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.PositiveSurjectiveCriterion
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
public import Mathlib.Tactic

/-!
# Unbounded inverse of a bounded positive resolvent

A coercive-form realization naturally produces a bounded positive solution
operator `R : H →L[𝕜] H`.  When `R` is self-adjoint and injective, its range is
dense.  The inverse on `range R` is therefore a densely defined closed
operator.  If `R` is also positive, that inverse is positive and self-adjoint.

This file constructs the inverse as a genuine `DavisKahanExt.PartialMap`
and proves the required properties.  It converts the form method into the
operator model already used throughout the Davis--Kahan development.
-/

@[expose] public section

open scoped InnerProductSpace
open Set Filter Topology

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- A bounded self-adjoint injective operator has dense range. -/
theorem denseRange_of_adjoint_eq_self_injective
    {R : H →L[𝕜] H}
    (hR : ContinuousLinearMap.adjoint R = R)
    (hinj : Function.Injective R) :
    DenseRange R := by
  have hker : R.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hinj
  have horth : R.rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range, hR, hker]
  have hdense : Dense ((R.range : Submodule 𝕜 H) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr horth)
  simpa [DenseRange, LinearMap.coe_range] using hdense

/-- Domain of the unbounded inverse of `R`. -/
noncomputable def inverseDomain (R : H →L[𝕜] H) : Submodule 𝕜 H :=
  LinearMap.range R.toLinearMap

/-- The injective bounded operator as a linear equivalence onto its range. -/
noncomputable def rangeEquiv (R : H →L[𝕜] H)
    (hinj : Function.Injective R) :
    H ≃ₗ[𝕜] inverseDomain R :=
  LinearEquiv.ofInjective R.toLinearMap hinj

/-- Algebraic inverse of `R` on `range R`. -/
noncomputable def rangeInverse (R : H →L[𝕜] H)
    (hinj : Function.Injective R) :
    inverseDomain R →ₗ[𝕜] H :=
  (rangeEquiv R hinj).symm.toLinearMap

omit [CompleteSpace H] in
/-- The range equivalence acts as the underlying vector. -/
@[simp] theorem rangeEquiv_coe_apply
    (R : H →L[𝕜] H) (hinj : Function.Injective R) (x : H) :
    ((rangeEquiv R hinj x : inverseDomain R) : H) = R x := by
  rfl

omit [CompleteSpace H] in
/-- Applying the range inverse after `R` returns the input. -/
@[simp] theorem rangeInverse_mk_apply
    (R : H →L[𝕜] H) (hinj : Function.Injective R) (x : H) :
    rangeInverse R hinj
      ⟨R x, LinearMap.mem_range_self R.toLinearMap x⟩ = x := by
  change (rangeEquiv R hinj).symm (rangeEquiv R hinj x) = x
  exact (rangeEquiv R hinj).symm_apply_apply x

omit [CompleteSpace H] in
/-- Applying `R` after the range inverse returns the domain vector. -/
@[simp] theorem apply_rangeInverse
    (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (x : inverseDomain R) :
    R (rangeInverse R hinj x) = (x : H) := by
  have h := (rangeEquiv R hinj).apply_symm_apply x
  exact congrArg Subtype.val h

omit [CompleteSpace H] in
/-- The graph of the range inverse is closed. -/
theorem isClosed_graph_rangeInverse
    (R : H →L[𝕜] H) (hinj : Function.Injective R) :
    IsClosed (Set.range fun x : inverseDomain R =>
      ((x : H), rangeInverse R hinj x)) := by
  apply IsSeqClosed.isClosed
  rintro φ ⟨x, y⟩ hmem hlim
  choose xn hxn using hmem
  have hfst : (fun n => ((xn n : inverseDomain R) : H)) =
      fun n => (φ n).1 := by
    funext n
    exact congrArg Prod.fst (hxn n)
  have hsnd : (fun n => rangeInverse R hinj (xn n)) =
      fun n => (φ n).2 := by
    funext n
    exact congrArg Prod.snd (hxn n)
  have hx : Tendsto (fun n => ((xn n : inverseDomain R) : H))
      atTop (𝓝 x) := by
    rw [hfst]
    exact hlim.fst_nhds
  have hy : Tendsto (fun n => rangeInverse R hinj (xn n))
      atTop (𝓝 y) := by
    rw [hsnd]
    exact hlim.snd_nhds
  have hRy : Tendsto
      (fun n => R (rangeInverse R hinj (xn n)))
      atTop (𝓝 (R y)) :=
    (R.continuous.tendsto y).comp hy
  have hseq :
      (fun n => R (rangeInverse R hinj (xn n))) =
        fun n => ((xn n : inverseDomain R) : H) := by
    funext n
    exact apply_rangeInverse R hinj (xn n)
  rw [hseq] at hRy
  have hRyx : R y = x := tendsto_nhds_unique hRy hx
  let z : inverseDomain R :=
    ⟨x, LinearMap.mem_range.mpr ⟨y, hRyx⟩⟩
  have hzinv : rangeInverse R hinj z = y := by
    apply hinj
    rw [apply_rangeInverse]
    simpa [z] using hRyx.symm
  refine ⟨z, ?_⟩
  ext
  · rfl
  · exact hzinv

/-- Unbounded inverse of a bounded injective self-adjoint operator, as a
partial map.  Density and graph closedness are the two lemmas below. -/
noncomputable def inversePartialMap
    (R : H →L[𝕜] H)
    (_hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) :
    H →ₗ.[𝕜] H where
  domain := inverseDomain R
  toFun := rangeInverse R hinj

/-- The constructed inverse is densely defined: the range of an injective
self-adjoint bounded operator is dense. -/
theorem inversePartialMap_dense
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R) (hinj : Function.Injective R) :
    Dense (((inversePartialMap R hR hinj).domain : Submodule 𝕜 H) : Set H) := by
  have hadj : ContinuousLinearMap.adjoint R = R := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hR.star_eq
  have hdense := denseRange_of_adjoint_eq_self_injective hadj hinj
  simpa [inversePartialMap, inverseDomain, DenseRange, LinearMap.coe_range]
    using hdense

/-- The constructed inverse has a closed graph. -/
theorem inversePartialMap_isClosed
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R) (hinj : Function.Injective R) :
    (inversePartialMap R hR hinj).IsClosed := by
  have h := isClosed_graph_rangeInverse R hinj
  change IsClosed ((inversePartialMap R hR hinj).graph : Set (H × H))
  have hgraph : ((inversePartialMap R hR hinj).graph : Set (H × H)) =
      Set.range fun x : (inverseDomain R) => ((x : H), rangeInverse R hinj x) := by
    ext q
    change q ∈ (inversePartialMap R hR hinj).graph ↔ _
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨x, hx, hy⟩; exact ⟨x, Prod.ext hx hy⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  rw [hgraph]
  exact h

/-- The domain of the constructed inverse is the range of `R`. -/
@[simp] theorem inversePartialMap_domain
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) :
    (inversePartialMap R hR hinj).domain = inverseDomain R := rfl

/-- The constructed inverse undoes `R`; this is the defining property of the unbounded inverse
of a bounded injective operator. -/
@[simp] theorem inversePartialMap_apply
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R)
    (x : (inversePartialMap R hR hinj).domain) :
    (inversePartialMap R hR hinj) x =
      rangeInverse R hinj x := rfl

/-- `R` is a right inverse of the unbounded inverse on its domain. -/
@[simp] theorem inversePartialMap_apply_R
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) (x : H) :
    (inversePartialMap R hR hinj)
      ⟨R x, LinearMap.mem_range_self R.toLinearMap x⟩ = x := by
  exact rangeInverse_mk_apply R hinj x

/-- `R` recovers every vector in the inverse domain. -/
theorem R_inversePartialMap_apply
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R)
    (x : (inversePartialMap R hR hinj).domain) :
    R ((inversePartialMap R hR hinj) x) = (x : H) := by
  exact apply_rangeInverse R hinj x

/-- The inverse of a bounded self-adjoint injective map is symmetric. -/
theorem inversePartialMap_isSymmetric
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) :
    TauCeti.LinearPMap.IsSymmetric (inversePartialMap R hR hinj) := by
  intro x y
  calc
    ⟪(inversePartialMap R hR hinj) x, (y : H)⟫_𝕜 =
        ⟪(inversePartialMap R hR hinj) x,
          R ((inversePartialMap R hR hinj) y)⟫_𝕜 := by
            -- `IsSymmetric` presents the domain as `.domain`, which is only
            -- definitionally the `.domain` the rewrite lemma is stated for; `rw` will not
            -- match across that, so close the step by a congruence `exact` instead.
            exact congrArg₂ (inner 𝕜) rfl
              (R_inversePartialMap_apply R hR hinj y).symm
    _ = ⟪R ((inversePartialMap R hR hinj) x),
          (inversePartialMap R hR hinj) y⟫_𝕜 := by
            exact (hR.isSymmetric _ _).symm
    _ = ⟪(x : H),
          (inversePartialMap R hR hinj) y⟫_𝕜 := by
            exact congrArg₂ (inner 𝕜) (R_inversePartialMap_apply R hR hinj x) rfl

/-- Positivity passes from `R` to its unbounded inverse. -/
theorem inversePartialMap_nonnegative
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R)
    (hRpos : ∀ y : H, 0 ≤ RCLike.re ⟪R y, y⟫_𝕜)
    (x : (inversePartialMap R hR hinj).domain) :
    0 ≤ RCLike.re
      ⟪(inversePartialMap R hR hinj) x, (x : H)⟫_𝕜 := by
  rw [← R_inversePartialMap_apply R hR hinj x]
  rw [inner_re_symm]
  exact hRpos ((inversePartialMap R hR hinj) x)

/-- Surjectivity of `1 + R⁻¹` follows from bounded coercivity of `1 + R`. -/
theorem inversePartialMap_one_add_surjective
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R)
    (hRpos : ∀ y : H, 0 ≤ RCLike.re ⟪R y, y⟫_𝕜) :
    ∀ h : H, ∃ x : (inversePartialMap R hR hinj).domain,
      (inversePartialMap R hR hinj) x + (x : H) = h := by
  have hunit : IsUnit (1 + R) := by
    apply ContinuousLinearMap.isUnit_of_coercive one_pos
    intro z
    have hNz : (1 + R) z = z + R z := rfl
    rw [one_mul, hNz, inner_add_left, map_add, inner_self_eq_norm_sq]
    nlinarith [hRpos z]
  intro h
  let y : H := Ring.inverse (1 + R) h
  let x : (inversePartialMap R hR hinj).domain :=
    ⟨R y, LinearMap.mem_range_self R.toLinearMap y⟩
  refine ⟨x, ?_⟩
  have hmul : (1 + R) * Ring.inverse (1 + R) = 1 :=
    Ring.mul_inverse_cancel (1 + R) hunit
  have happ := DFunLike.congr_fun hmul h
  change y + R y = h at happ
  change (inversePartialMap R hR hinj)
      ⟨R y, LinearMap.mem_range_self R.toLinearMap y⟩ + R y = h
  rw [inversePartialMap_apply_R]
  exact happ

/-- The densely defined inverse of a bounded positive self-adjoint injective
 operator is self-adjoint. -/
theorem inversePartialMap_isSelfAdjoint
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R)
    (hRpos : ∀ y : H, 0 ≤ RCLike.re ⟪R y, y⟫_𝕜) :
    _root_.IsSelfAdjoint (inversePartialMap R hR hinj) := by
  apply DavisKahanExt.PartialMap.isSelfAdjoint_of_nonnegative_one_add_surjective
  · exact inversePartialMap_isSymmetric R hR hinj
  · exact inversePartialMap_nonnegative R hR hinj hRpos
  · exact inversePartialMap_one_add_surjective R hR hinj hRpos

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
