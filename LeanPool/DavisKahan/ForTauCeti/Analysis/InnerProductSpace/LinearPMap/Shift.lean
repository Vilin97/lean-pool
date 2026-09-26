/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ResolventBound
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Shifted ranges of partially defined self-adjoint operators

The closed-range and adjoint-domain arguments use only `RCLike` scalars.
They are shared by the real-shift lower-bound criterion and the complex non-real
resolvent theorem. The latter supplies its bound from the imaginary part of the shift;
the former takes the lower bound as a hypothesis.

These arguments are extracted from `LinearPMap.SelfAdjointResolvent` and generalized
in place; no second shifted-map or resolvent representation is introduced.
-/

@[expose] public section

namespace TauCeti.LinearPMap

open scoped InnerProductSpace ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a symmetric operator the quadratic form is real. -/
theorem inner_apply_self_isReal {A : E →ₗ.[𝕜] E} (hsym : A.IsFormalAdjoint A)
    (x : A.domain) : (starRingEnd 𝕜) ⟪A x, (x : E)⟫_𝕜 = ⟪A x, (x : E)⟫_𝕜 := by
  rw [inner_conj_symm]
  exact (hsym x x).symm

/-- **Orthogonality to the shifted range identifies the adjoint's action.**

`⟪y, A x - z x⟫ = 0` for every `x` says exactly `⟪conj z • y, x⟫ = ⟪y, A x⟫`,
which is what puts `y` in the adjoint's domain.  Used identically here and in
`RealLowerBound`. -/
theorem inner_conj_smul_eq_of_orthogonal_shiftRange {A : E →ₗ.[𝕜] E} {z : 𝕜} {y : E}
    (hy : ∀ x : A.domain, ⟪y, A x - z • (x : E)⟫_𝕜 = 0) (x : A.domain) :
    ⟪(starRingEnd 𝕜) z • y, (x : E)⟫_𝕜 = ⟪y, A x⟫_𝕜 := by
  have h := hy x
  rw [inner_sub_right, inner_smul_right, sub_eq_zero] at h
  rw [inner_smul_left, starRingEnd_self_apply]
  exact h.symm

/-- `A - z` as a linear map out of the domain of `A`. -/
@[expose]
def shiftMap (A : E →ₗ.[𝕜] E) (z : 𝕜) : A.domain →ₗ[𝕜] E :=
  A.toFun - z • A.domain.subtype

/-- The shifted map `A - z`, unfolded. -/
@[simp] theorem shiftMap_apply (A : E →ₗ.[𝕜] E) (z : 𝕜) (x : A.domain) :
    shiftMap A z x = A x - z • (x : E) := (rfl)

/-- **The shifted range has trivial orthogonal complement**, given that nothing
nonzero is orthogonal to it.

The `Submodule.eq_bot_iff` unfolding and the `inner_eq_zero_symm` flip are the
same at both call sites; only the reason a vector orthogonal to the range must
vanish differs, so that is the hypothesis. -/
theorem orthogonal_range_shiftMap_eq_bot {A : E →ₗ.[𝕜] E} {z : 𝕜}
    (h0 : ∀ y : E, (∀ x : A.domain, ⟪y, A x - z • (x : E)⟫_𝕜 = 0) → y = 0) :
    (LinearMap.range (shiftMap A z))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  refine h0 y fun x => ?_
  have h := hy (shiftMap A z x) ⟨x, rfl⟩
  rwa [inner_eq_zero_symm] at h

variable [CompleteSpace E]

/-- A lower bound and self-adjointness make the shifted range closed. -/
theorem isClosed_range_shiftMap_of_lower_bound {A : E →ₗ.[𝕜] E} {z : 𝕜} {c : ℝ}
    (hA : IsSelfAdjoint A) (hc : 0 < c)
    (hbd : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖) :
    IsClosed (Set.range (shiftMap A z)) := by
  apply IsSeqClosed.isClosed
  intro w a hw hlim
  choose x hx using hw
  have hwCauchy : CauchySeq w := hlim.cauchySeq
  have hCauchy : CauchySeq fun n => ((x n : E)) := by
    rw [Metric.cauchySeq_iff] at hwCauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hwCauchy (c * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hest := hbd (x m - x n)
    have hcoe : ((x m - x n : A.domain) : E) = (x m : E) - (x n : E) := rfl
    have hAsub : A (x m - x n) = A (x m) - A (x n) := map_sub _ _ _
    have hval : A (x m - x n) - z • ((x m - x n : A.domain) : E) = w m - w n := by
      rw [hAsub, hcoe, smul_sub, ← hx m, ← hx n]
      simp only [shiftMap_apply]
      abel
    rw [hval, hcoe] at hest
    have hd : dist (w m) (w n) < c * ε := hN m hm n hn
    rw [dist_eq_norm] at hd ⊢
    nlinarith [norm_nonneg ((x m : E) - (x n : E))]
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hAx : Filter.Tendsto (fun n => A (x n)) Filter.atTop (nhds (a + z • p)) := by
    have hval : ∀ n, A (x n) = w n + z • ((x n : E)) := by
      intro n; rw [← hx n]; simp only [shiftMap_apply]; abel
    simp only [hval]
    exact hlim.add ((continuous_const_smul z).continuousAt.tendsto.comp hp)
  have hgraph : ((p, a + z • p) : E × E) ∈ A.graph := by
    refine (hA.isClosed).mem_of_tendsto (b := Filter.atTop)
      (f := fun n => ((x n : E), A (x n))) ?_ ?_
    · exact hp.prodMk_nhds hAx
    · filter_upwards with n using A.mem_graph (x n)
  obtain ⟨q, hq⟩ := (A.mem_graph_iff).mp hgraph
  refine ⟨q, ?_⟩
  have hq1 : (q : E) = p := hq.1
  have hq2 : A q = a + z • p := hq.2
  simp only [shiftMap_apply, hq1, hq2]
  abel


end TauCeti.LinearPMap
