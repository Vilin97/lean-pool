/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin, Joseph K. Miller
-/
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Picard-Lindelöf with explicit confinement conjunct (vendored from Mathlib)

This file is **vendored** from `Mathlib/Analysis/ODE/PicardLindelof.lean`
(Yury Kudryashov, Winston Yin): it copies two upstream theorems and adds **one**
conjunct to each public conclusion; the proofs are otherwise the upstream proofs.
The two upstream sources were
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`
and `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`
(present in `Mathlib/Analysis/ODE/PicardLindelof.lean` through mathlib
v4.29.1; the local-flow refactor later moved these public wrappers to
`Mathlib/Analysis/ODE/ExistUnique.lean`, which this file does not import,
while keeping the `FunSpace` machinery this file's proofs actually use —
`exists_isFixedPt_next`, `compProj_*`, `hasDerivWithinAt_picard_Icc`,
`exists_forall_closedBall_funSpace_dist_le_mul` — in place, so the proofs
below still elaborate against current mathlib unchanged).  The single difference from each
original is marked inline below with a `Vendored addition` comment.

The new conjunct exposes `FunSpace.compProj_mem_closedBall`'s guarantee at the
public theorem level: every flow trajectory `α x t` stays inside
`closedBall x₀ a` (the outer ball where the field is Lipschitz). The underlying
property is already proved upstream in Mathlib; in fact, the upstream public
proof of `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`
(now in `Mathlib/Analysis/ODE/ExistUnique.lean`)
already invokes `compProj_mem_closedBall hf.mul_max_le` internally (to
constrain the iterate to the Lipschitz region). We are only re-exporting that
invariant through the public conclusion.

**Intended upstreaming**: this file is structured as a near-mechanical patch
to `Mathlib/Analysis/ODE/PicardLindelof.lean`; the eventual Mathlib PR would
drop the `_confined` suffix and replace the two original theorems with their
strengthened forms (no API breaks for downstream consumers, since the
conclusion only grows).

**In-project consumer**: `Vlasov.OT.CharacteristicFlow` (where
`exists_vlasov_extend_one_window` threads the confinement conjunct through
to Helper 1, `vlasov_window_confinement`).
-/

namespace IsPicardLindelof

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology
open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

open Classical in
/-- **Picard-Lindelöf with confinement** (vendored from Mathlib, awaiting
upstream PR). Same conclusion as
`exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` plus an
additional conjunct `∀ t ∈ Icc tmin tmax, α x t ∈ closedBall x₀ a` —
exposing the FunSpace confinement guarantee at the public API level. The
underlying property is already proved upstream (the existing proof of
`_lipschitzOnWith` invokes `FunSpace.compProj_mem_closedBall hf.mul_max_le`
internally to constrain the iterate to the Lipschitz region); we only
re-export it. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_confined
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      -- Vendored addition (absent from the upstream `_lipschitzOnWith`): the flow
      -- stays confined to `closedBall x₀ a`, the region where `f` is Lipschitz.
      (∀ t ∈ Icc tmin tmax, α x t ∈ closedBall x₀ a)) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  have (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, FunSpace.compProj_apply]
    apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  · -- Vendored addition — confinement: α' x t = (α x hx).compProj t ∈ closedBall x₀ a.
    -- Discharged by `FunSpace.compProj_mem_closedBall`, the invariant the upstream proof
    -- already uses internally; here it is re-exported through the public conclusion.
    rw [hα']
    beta_reduce
    rw [dif_pos hx]
    exact α x hx |>.compProj_mem_closedBall hf.mul_max_le
  · obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp_rw [hα']
    rw [dif_pos hx, dif_pos hy, FunSpace.compProj_apply, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

/-- **Picard-Lindelöf with confinement, thin wrapper** (vendored). Drops the
Lipschitz-in-initial-point conjunct from `_lipschitzOnWith_confined`. This is
the form `exists_vlasov_extend_one_window` consumes — Vlasov doesn't need the
flow's Lipschitz dependence on the initial point. -/
theorem exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      -- Vendored addition (absent from the upstream
      -- `exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`): the flow
      -- stays confined to `closedBall x₀ a`.
      (∀ t ∈ Icc tmin tmax, α x t ∈ closedBall x₀ a) :=
  have ⟨α, hα⟩ := exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith_confined hf
  ⟨α, hα.1⟩

end IsPicardLindelof
