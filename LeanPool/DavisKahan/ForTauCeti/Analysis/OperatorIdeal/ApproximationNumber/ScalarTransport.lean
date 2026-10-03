/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Staged for Tau Ceti, roadmap topic T09.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track — additions to `Mathlib/Analysis/OperatorIdeal/`.

Formalized by Claude Opus 5 (claude-opus-5[1m]).

Approximation numbers, linear independence and spans are unchanged by the
transport of a Hilbert space along an isomorphism of `RCLike` fields; hence the
min--max lower-bound property holds at every `RCLike` field.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMaxReal

/-! # Scalar Transport -/

@[expose] public section

/-! # Approximation numbers under a scalar transport

`TauCeti.ScalarTransport` renames the scalar field of a Hilbert space without
touching its vectors, its norm, or its topology.  Everything an approximation
number sees is therefore unchanged, and this file says so:
`ScalarTransport.approximationNumber_clm`.

The payoff is `ContinuousLinearMap.hasMinMaxLowerBoundEverywhere`, the instance at
an **arbitrary** `RCLike` field.  That property was the one input to the
approximation-number localization theory that depended on the scalar field, with
instances at `ℝ` and at `ℂ` and nothing in between; `RCLike` has exactly those two
models, so the case split closes it.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: none.  Written directly here, 2026-09-01.
* Extraction class: **new**.  It completes `MinMaxReal`: that module carries the
  min--max lower bound over `ℝ` by complexification, and this one carries it from
  `ℝ` and `ℂ` to every `RCLike` field, which is what makes
  `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere` an instance rather than a
  hypothesis.
* Namespaces: `TauCeti.ScalarTransport` for the transport lemmas, and
  `ContinuousLinearMap` for the instance, which is a fact about a
  `ContinuousLinearMap`.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/

open scoped InnerProductSpace

universe u w v v'

namespace TauCeti
namespace ScalarTransport

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type v'} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The transport does not change an approximation number: it is an infimum of
operator norms over the maps of bounded rank, and the transport is a
rank-preserving, norm-preserving bijection of those. -/
theorem approximationNumber_clm (T : E →L[𝕜] F) (n : ℕ) :
    (clm (e := e) T).approximationNumber n = T.approximationNumber n := by
  rw [ContinuousLinearMap.approximationNumber_eq_iInf,
    ContinuousLinearMap.approximationNumber_eq_iInf]
  refine (Equiv.iInf_congr (Equiv.subtypeEquiv (clmEquiv (e := e)) fun R => ?_) fun R => ?_).symm
  · rw [show ((clmEquiv (e := e)) R : ScalarTransport e E →L[𝕂] ScalarTransport e F) =
      clm (e := e) R from rfl, rank_clm_eq]
  · rw [Equiv.subtypeEquiv_apply]
    exact (clm_norm (e := e) (T - (R : E →L[𝕜] F))).symm

/-- Linear independence is unchanged: the two scalar actions differ by `e`. -/
theorem linearIndependent_of_iff {ι : Type*} (v : ι → E) :
    LinearIndependent 𝕂 (fun i => of (e := e) (v i)) ↔ LinearIndependent 𝕜 v := by
  classical
  constructor
  · intro h
    refine linearIndependent_iff'.mpr fun s g hg i hi => ?_
    have := linearIndependent_iff'.mp h s (fun j => e (g j)) ?_ i hi
    · simpa using congrArg e.toRingEquiv.symm this
    · have : ∀ j, e (g j) • of (e := e) (v j) = of (e := e) (g j • v j) := by
        intro j
        rw [smul_def, e.toRingEquiv.symm_apply_apply]
        rfl
      simp only [this]
      exact congrArg (of (e := e)) hg
  · intro h
    refine linearIndependent_iff'.mpr fun s g hg i hi => ?_
    have hgs : ∀ j, g j • of (e := e) (v j) =
        of (e := e) ((e.toRingEquiv.symm (g j)) • v j) := fun j => rfl
    have := linearIndependent_iff'.mp h s (fun j => e.toRingEquiv.symm (g j)) ?_ i hi
    · simpa using congrArg e.toRingEquiv this
    · simp only [hgs] at hg
      exact hg

/-- Spans are unchanged: the transported span has the original carrier. -/
theorem span_of {ι : Type*} (v : ι → E) :
    Submodule.span 𝕂 (Set.range fun i => of (e := e) (v i)) =
      submodule (e := e) (Submodule.span 𝕜 (Set.range v)) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact mem_submodule.mpr (Submodule.subset_span ⟨i, rfl⟩)
  · have key : ∀ y : E, y ∈ Submodule.span 𝕜 (Set.range v) →
        of (e := e) y ∈ Submodule.span 𝕂 (Set.range fun i => of (e := e) (v i)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
          have hc : of (e := e) (c • a) = e c • of (e := e) a := by
            rw [smul_def, e.toRingEquiv.symm_apply_apply]; rfl
          exact hc ▸ Submodule.smul_mem _ _ ha
    exact fun x hx => key (out x) hx

end ScalarTransport

end TauCeti

namespace ContinuousLinearMap

open TauCeti TauCeti.ScalarTransport

/-- The min--max lower-bound property transports along an isomorphism of `RCLike`
fields: it mentions only approximation numbers, norms, linear independence and
spans, and the transport changes none of them. -/
theorem hasMinMaxLowerBound_of_transport {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂]
    (e : RCLikeIso 𝕜 𝕂) {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {F : Type v'} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (h : HasMinMaxLowerBound 𝕂 (ScalarTransport e E) (ScalarTransport e F)) :
    HasMinMaxLowerBound 𝕜 E F := by
  intro T n r hr0 hr
  obtain ⟨s, hrs, w, hw, hbound⟩ :=
    h (clm (e := e) T) n hr0 (by rwa [approximationNumber_clm])
  refine ⟨s, hrs, fun i => out (w i), ?_, fun x hx => ?_⟩
  · rw [← linearIndependent_of_iff (e := e)]
    exact hw
  · have hx' : of (e := e) x ∈
        Submodule.span 𝕂 (Set.range fun i => of (e := e) (out (w i))) := by
      rw [span_of]
      exact hx
    exact hbound (of (e := e) x) hx'

/-- **The min--max lower-bound property holds at every `RCLike` field.**

`RCLike` is an open class, but `RCLike.I_eq_zero_or_im_I_eq_one` says it has
exactly two models.  Transporting a `𝕜`-Hilbert space to the corresponding `ℝ`- or
`ℂ`-Hilbert space changes no vector, no norm, no approximation number, no linear
independence and no span, so the two fixed-field instances give the general one.

This removes `[HasMinMaxLowerBoundEverywhere 𝕜]` from every downstream statement
that carried it as a hypothesis. -/
theorem hasMinMaxLowerBound_rclike (𝕜 : Type u) [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type v'} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    HasMinMaxLowerBound 𝕜 E F := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · exact hasMinMaxLowerBound_of_transport (RCLikeIso.real h)
      TauCeti.ApproximationNumber.hasMinMaxLowerBound_real
  · exact hasMinMaxLowerBound_of_transport (RCLikeIso.complex h) hasMinMaxLowerBound_complex

/-- The single-universe class form of `hasMinMaxLowerBound_rclike`, so that the
statements carrying `[HasMinMaxLowerBoundEverywhere 𝕜]` resolve it by instance
search rather than by hypothesis. -/
instance hasMinMaxLowerBoundEverywhere (𝕜 : Type u) [RCLike 𝕜] :
    HasMinMaxLowerBoundEverywhere.{u, v} 𝕜 where
  out := by
    intro E _ _ _ F _ _ _
    exact hasMinMaxLowerBound_rclike 𝕜

/-- Ky Fan subadditivity on Hilbert spaces over any `RCLike` field.

The min--max localization is an internal theorem, not a public capability hypothesis. -/
theorem kyFanGauge_add_le {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type v'} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (S T : E →L[𝕜] F) (k : ℕ) :
    (S + T).kyFanGauge k ≤ S.kyFanGauge k + T.kyFanGauge k :=
  kyFanGauge_add_le_of_hasMinMaxLowerBound (hasMinMaxLowerBound_rclike 𝕜) S T k

end ContinuousLinearMap
