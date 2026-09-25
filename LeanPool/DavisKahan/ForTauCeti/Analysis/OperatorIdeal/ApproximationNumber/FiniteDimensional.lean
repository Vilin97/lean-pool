/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.Values
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Rank
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer

/-!
# Approximation numbers on finite-dimensional Hilbert spaces

This module begins the bridge between the finite-dimensional singular-value
library and approximation numbers defined by finite-rank operator-norm
approximation.

The main result is the finite-dimensional Eckart--Young identification: the
`n`th approximation number equals the `n`th singular value. The lower bound
uses the Courant--Fischer `(n+1)`-dimensional right singular subspace and
dimension counting against the kernel of an arbitrary rank-at-most-`n`
approximant. The upper bound projects onto the first `n` right singular
directions and controls the complementary spectral tail.

## Main declarations

* `ContinuousLinearMap.approximationNumber_eq_singularValues`: the
  identification `aₙ(T) = σₙ(T)`, index for index — the whole point of the
  zero-based convention (see `ApproximationNumber/Basic.lean`).
* `ContinuousLinearMap.singularValues_le_norm_sub_of_rank_le`: the sharp lower
  bound against an *arbitrary* rank-at-most-`n` approximant.  It is strictly
  stronger than the inequality below, which is its infimum form.
* `ContinuousLinearMap.singularValues_le_approximationNumber`: the half of the
  identification that does not depend on the truncation construction, and so
  the half that has a shape in infinite dimensions.

The reverse inequality is private: it is the half that exists only to be
combined into the identification.  See the declaration for the reasoning.

## Namespace note

These declarations extend the existing Mathlib namespace `ContinuousLinearMap`
rather than living under `TauCeti`, so that dot notation
(`T.approximationNumber_eq_singularValues`) resolves and the names match the
eventual Mathlib upstreaming target. Lean field projection binds `T.foo` only to
the literal `ContinuousLinearMap.foo` and does not consult the enclosing
`TauCeti` namespace. The Courant--Fischer helpers imported here, by contrast,
live under `TauCeti`. This is a deliberate API choice, flagged for Tau Ceti
maintainer review.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module:
  `ForMathlib/Analysis/Normed/Operator/ApproximationNumberSingularValues.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations: `ContinuousLinearMap.approximationNumber_eq_singularValues`
  and the Eckart--Young bounds in the same namespace.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
  Declaration names are unchanged (they already extend the canonical Mathlib
  namespace); references to the Courant--Fischer helpers track the redesigned
  API (`OrthonormalBasis.spanIndices` in `BasisSpan.lean` and the
  `LinearMap.IsSymmetric`-namespace eigenvalue results).  No mathematical
  change.
* Spectra influence: **none** — this module imports only Mathlib and the
  sibling `Basic` and `CourantFischer` staging modules.
-/

@[expose] public section

namespace ContinuousLinearMap

open Module (finrank)
open scoped InnerProductSpace

noncomputable section

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Lower Eckart--Young inequality in operator-norm form: an operator of rank
at most `n` cannot approximate `T` more closely than the `n`th singular value
of `T`. -/
theorem singularValues_le_norm_sub_of_rank_le
    (T R : E →L[𝕜] F) (n : ℕ)
    (hR : R.rank ≤ (n : Cardinal)) :
    T.singularValues n ≤ ‖T - R‖ := by
  rw [← toLinearMap_singularValues]
  by_cases hn : finrank 𝕜 E ≤ n
  · rw [T.toLinearMap.singularValues_of_finrank_le hn]
    exact norm_nonneg _
  · have hnlt : n < finrank 𝕜 E := Nat.lt_of_not_ge hn
    let k : Fin (finrank 𝕜 E) := ⟨n, hnlt⟩
    obtain ⟨V, hVdim, hVlow⟩ :=
      LinearMap.IsSymmetric.exists_submodule_forall_unit_eigenvalue_le_re_inner
        T.toLinearMap.isSymmetric_adjoint_comp_self rfl k
    have hVdim' : finrank 𝕜 V = n + 1 := by
      simpa [k] using hVdim
    have hRcard : (finrank 𝕜 R.range : Cardinal) ≤ (n : Cardinal) := by
      calc
        (finrank 𝕜 R.range : Cardinal) = R.rank :=
          Module.finrank_eq_rank' 𝕜 R.range
        _ ≤ (n : Cardinal) := hR
    have hRfin : finrank 𝕜 R.range ≤ n := by
      exact_mod_cast hRcard
    have hRker : finrank 𝕜 R.ker = finrank 𝕜 E - finrank 𝕜 R.range := by
      have hnull := R.toLinearMap.finrank_range_add_finrank_ker
      omega
    have hinf : V ⊓ R.ker ≠ ⊥ := by
      intro hbot
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq V R.ker
      rw [hbot, finrank_bot, add_zero, hVdim', hRker] at hdim
      have hsup : finrank 𝕜 (V ⊔ R.ker : Submodule 𝕜 E) ≤ finrank 𝕜 E :=
        Submodule.finrank_le _
      omega
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
    obtain ⟨hzV, hzker⟩ := Submodule.mem_inf.mp hz
    have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    let x : E := ((‖z‖⁻¹ : ℝ) : 𝕜) • z
    have hxV : x ∈ V := V.smul_mem _ hzV
    have hxNorm : ‖x‖ = 1 := by
      simp only [x, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hzNorm
    have hRx : R x = 0 := by
      have hRz : R z = 0 := LinearMap.mem_ker.mp hzker
      simp [x, hRz]
    have hsq : T.toLinearMap.singularValues n ^ 2 ≤ ‖T - R‖ ^ 2 := by
      calc
        T.toLinearMap.singularValues n ^ 2
            = T.toLinearMap.isSymmetric_adjoint_comp_self.eigenvalues rfl k :=
          T.toLinearMap.sq_singularValues_fin rfl k
        _ ≤ RCLike.re
              ⟪(T.toLinearMap.adjoint ∘ₗ T.toLinearMap) x, x⟫_𝕜 :=
          hVlow x hxV hxNorm
        _ = ‖T x‖ ^ 2 := by
          rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
            inner_self_eq_norm_sq]
          rfl
        _ = ‖(T - R) x‖ ^ 2 := by
          rw [sub_apply, hRx, sub_zero]
        _ ≤ ‖T - R‖ ^ 2 := by
          have hxop := (T - R).le_opNorm x
          rw [hxNorm, mul_one] at hxop
          nlinarith [norm_nonneg ((T - R) x), norm_nonneg (T - R)]
    exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- The `n`th finite-dimensional singular value is bounded by the `n`th
approximation number. This is the lower half of the finite-dimensional
Eckart--Young identification. -/
theorem singularValues_le_approximationNumber
    (T : E →L[𝕜] F) (n : ℕ) :
    T.singularValues n ≤
      T.approximationNumber n := by
  refine T.le_approximationNumber_iff.mpr ?_
  intro R hR
  exact_mod_cast singularValues_le_norm_sub_of_rank_le T R n hR

/-- Upper Eckart--Young inequality: projection onto the first `n` right
singular directions gives a rank-at-most-`n` approximant whose error is bounded
by the `n`th singular value.

Private, unlike its converse `singularValues_le_approximationNumber`.  The
asymmetry is deliberate and evidence-based rather than an oversight: this
direction has no consumer outside the identification it feeds, while the
converse has independent ones, and the two are not equally general — the
converse bounds an arbitrary approximant from below and is the shape that
survives into infinite dimensions, whereas this one is built from the singular
value decomposition and is finite-dimensional in an essential way.  Make it
public if a consumer ever needs the truncation bound on its own. -/
private theorem approximationNumber_le_singularValues
    (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n ≤
      T.singularValues n := by
  rw [← toLinearMap_singularValues]
  classical
  by_cases hn : finrank 𝕜 E ≤ n
  · -- The rank of `T` lives in the codomain universe and `Module.rank 𝕜 E` in
    -- the domain universe, so compare them through `Cardinal.lift`.
    have hTrank : T.rank ≤ (n : Cardinal) := by
      refine Cardinal.lift_le_natCast.mp
        ((lift_rank_range_le T.toLinearMap).trans ?_)
      calc
        Cardinal.lift.{w} (Module.rank 𝕜 E)
            = Cardinal.lift.{w} ((finrank 𝕜 E : Cardinal)) := by
          rw [← Module.finrank_eq_rank' 𝕜 E]
        _ = ((finrank 𝕜 E : ℕ) : Cardinal) := Cardinal.lift_natCast _
        _ ≤ (n : Cardinal) := by exact_mod_cast hn
    have hle : T.approximationNumber n ≤ 0 := by
      simpa using T.approximationNumber_le_norm_sub (R := T) hTrank
    exact hle.trans (T.toLinearMap.singularValues_nonneg n)
  · have hnlt : n < finrank 𝕜 E := Nat.lt_of_not_ge hn
    let A : E →ₗ[𝕜] F := T.toLinearMap
    let hGram : (A.adjoint ∘ₗ A).IsSymmetric := A.isSymmetric_adjoint_comp_self
    let b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := hGram.eigenvectorBasis rfl
    let W : Submodule 𝕜 E :=
      b.spanIndices {i : Fin (finrank 𝕜 E) | (i : ℕ) < n}
    let k : Fin (finrank 𝕜 E) := ⟨n, hnlt⟩
    have hWdim : finrank 𝕜 W = n := by
      dsimp only [W]
      rw [b.finrank_spanIndices_set, Set.toFinset_ofPred, Finset.card_filter_lt hnlt.le]
    have hPrank : W.starProjection.rank = (n : Cardinal) := by
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change Module.rank 𝕜 W.starProjection.range = (n : Cardinal)
      rw [Submodule.range_starProjection, ← Module.finrank_eq_rank' 𝕜 W, hWdim]
    let R : E →L[𝕜] F := T ∘L W.starProjection
    -- Cross-universe once the codomain is independent, so route the bound
    -- through the natural-number rank estimate.
    have hRrank : R.rank ≤ (n : Cardinal) :=
      ContinuousLinearMap.rank_comp_le_natCast_right W.starProjection T
        hPrank.le
    have htail : Wᗮ = b.spanIndices
        {i : Fin (finrank 𝕜 E) | (i : ℕ) < n}ᶜ := by
      exact b.orthogonal_spanIndices {i : Fin (finrank 𝕜 E) | (i : ℕ) < n}
    have htailQuad {y : E} (hy : y ∈ Wᗮ) :
        RCLike.re ⟪(A.adjoint ∘ₗ A) y, y⟫_𝕜 ≤
          A.singularValues n ^ 2 * ‖y‖ ^ 2 := by
      have hy' : y ∈ b.spanIndices
          {i : Fin (finrank 𝕜 E) | (i : ℕ) < n}ᶜ := by
        rw [← htail]
        exact hy
      have hbound := hGram.re_inner_apply_self_le_of_mem_spanIndices rfl
        (s := {i : Fin (finrank 𝕜 E) | (i : ℕ) < n}ᶜ)
        (c := hGram.eigenvalues rfl k)
        (fun i hi => hGram.eigenvalues_antitone rfl (by
          rw [Set.mem_compl_iff, Set.mem_ofPred_eq] at hi
          -- states the goal with the definition unfolded, in the shape the next step needs;
          -- there is no `_apply` lemma to rewrite with here.
          change n ≤ (i : ℕ)
          exact Nat.le_of_not_gt hi))
        hy'
      calc
        RCLike.re ⟪(A.adjoint ∘ₗ A) y, y⟫_𝕜 ≤
            hGram.eigenvalues rfl k * ‖y‖ ^ 2 := hbound
        _ = A.singularValues n ^ 2 * ‖y‖ ^ 2 := by
          rw [← A.sq_singularValues_fin rfl k]
    have htailNorm {y : E} (hy : y ∈ Wᗮ) :
        ‖T y‖ ≤ A.singularValues n * ‖y‖ := by
      have hsq : ‖T y‖ ^ 2 ≤ A.singularValues n ^ 2 * ‖y‖ ^ 2 := by
        calc
          ‖T y‖ ^ 2 = RCLike.re ⟪(A.adjoint ∘ₗ A) y, y⟫_𝕜 := by
            rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
              inner_self_eq_norm_sq]
            rfl
          _ ≤ A.singularValues n ^ 2 * ‖y‖ ^ 2 := htailQuad hy
      have hsq' : ‖T y‖ ^ 2 ≤ (A.singularValues n * ‖y‖) ^ 2 := by
        calc
          ‖T y‖ ^ 2 ≤ A.singularValues n ^ 2 * ‖y‖ ^ 2 := hsq
          _ = (A.singularValues n * ‖y‖) ^ 2 := by ring
      exact le_of_sq_le_sq hsq'
        (mul_nonneg (A.singularValues_nonneg n) (norm_nonneg y))
    have htailOpNorm : ‖T ∘L Wᗮ.starProjection‖ ≤ A.singularValues n := by
      refine (T ∘L Wᗮ.starProjection).opNorm_le_bound
        (A.singularValues_nonneg n) ?_
      intro x
      have hy : Wᗮ.starProjection x ∈ Wᗮ := Wᗮ.starProjection_apply_mem x
      calc
        ‖(T ∘L Wᗮ.starProjection) x‖ = ‖T (Wᗮ.starProjection x)‖ := (rfl)
        _ ≤ A.singularValues n * ‖Wᗮ.starProjection x‖ := htailNorm hy
        _ ≤ A.singularValues n * ‖x‖ :=
          mul_le_mul_of_nonneg_left (Wᗮ.norm_starProjection_apply_le x)
            (A.singularValues_nonneg n)
    have herr : T - R = T ∘L Wᗮ.starProjection := by
      ext x
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change T x - T (W.starProjection x) = T (Wᗮ.starProjection x)
      rw [Submodule.starProjection_orthogonal_val, map_sub]
    have htailOpNorm' :
        ‖T ∘L Wᗮ.starProjection‖ ≤ T.toLinearMap.singularValues n := by
      simpa [A] using htailOpNorm
    have happrox :
        T.approximationNumber n ≤ ‖T ∘L Wᗮ.starProjection‖ := by
      simpa only [herr] using T.approximationNumber_le_norm_sub hRrank
    exact happrox.trans htailOpNorm'

/-- Finite-dimensional Eckart--Young identification for the zero-based
approximation-number convention used in this project: `aₙ(T) = σₙ(T)`, with no
index shift on either side.

Deliberately **not** `@[simp]`.  It would fire on every `approximationNumber`
goal that happens to sit under `FiniteDimensional` instances, rewriting the
object this development is *about* into Mathlib's, which is the wrong normal
form for a downstream perturbation argument; and unlike the other direction
there is no cheap way for a consumer to opt out once it is global. -/
theorem approximationNumber_eq_singularValues
    (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n =
      T.singularValues n := by
  apply le_antisymm
  · exact approximationNumber_le_singularValues T n
  · exact singularValues_le_approximationNumber T n

/-- **Weyl's inequality for singular values:** `|σₙ(T) − σₙ(S)| ≤ ‖T − S‖`.

Every singular value is `1`-Lipschitz in the operator norm — the singular-value
counterpart of Weyl's eigenvalue inequality, and the standard sharp form: there
is no auxiliary bound on `T` or `S`, and no factor depending on their size.

The proof is not an argument about singular values at all.  It is
`abs_approximationNumber_sub_approximationNumber_le`, which holds over any
normed space with no inner product, transported through the Eckart--Young
identification above.  That is the payoff of stating the `s`-number layer
field-generically: the Hilbert-space theorem is a corollary of a Banach-space
one. -/
theorem abs_singularValues_sub_singularValues_le (T S : E →L[𝕜] F) (n : ℕ) :
    |T.singularValues n - S.singularValues n| ≤ ‖T - S‖ := by
  rw [← T.approximationNumber_eq_singularValues n,
    ← S.approximationNumber_eq_singularValues n]
  exact abs_approximationNumber_sub_approximationNumber_le T S n

/-- Singular values have the same exact rank cutoff as approximation numbers. -/
theorem singularValues_eq_zero_iff_rank_le (T : E →L[𝕜] F) (n : ℕ) :
    T.singularValues n = 0 ↔ T.rank ≤ (n : Cardinal) := by
  rw [← approximationNumber_eq_singularValues]
  exact T.approximationNumber_eq_zero_iff_rank_le n

end

end ContinuousLinearMap

end
