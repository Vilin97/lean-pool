/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Cutoff
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The min--max theorem for approximation numbers

`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean` proves the easy half of
the Courant--Fischer characterisation: a uniform lower modulus on a test subspace of rank
greater than `n` bounds `aₙ(T)` from below.  This module proves the **converse**, which is
the half that carries the content:

```
r < aₙ(T)  →  ∃ s > r, ∃ n + 1 independent vectors spanning a subspace on which ‖T x‖ ≥ s ‖x‖.
```

Together the two say that `aₙ(T)` *is* the supremum, over `(n+1)`-dimensional subspaces, of
the lower modulus of `T` there — for an arbitrary bounded operator between complex Hilbert
spaces, with no compactness, separability or finite-dimensionality hypothesis.

## Why this is not a spectral theorem

The classical proof cuts the spectrum of `|T|` at `s` with a projection-valued measure.
This one does not: `ForTauCeti/Analysis/InnerProductSpace/SpectralCutoff.lean` gets the same
splitting of `E` from the *continuous* functional calculus, as the kernel of `(|T| - s)₊` and
its orthogonal complement.  The proof here is then a dichotomy on that complement `M`:

* if `M` has rank greater than `n`, it contains `n + 1` independent vectors, and `|T|` — hence
  `T`, by `ContinuousLinearMap.norm_modulus_apply` — is bounded below by `s` on it;
* otherwise `M` is finite-dimensional of dimension at most `n`, so `T ∘L M.starProjection`
  is an admissible rank-`≤ n` approximant, and it is within `s` of `T` because `1 - P_M` lands
  in the kernel where `|T|` is bounded *above* by `s`.  That forces `aₙ(T) ≤ s`, contradicting
  the hypothesis.

Only the second branch can fail, and it fails into a contradiction, so the first branch always
holds.

## Consequences

This unblocks the results that had been routed through `vendor/Spectra`'s min--max bridge:
the Ky Fan gauge triangle inequality, and with it the Ky Fan and symmetric-gauge operator
ideals, and the orthogonal block-sum merge formulas.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none in the proof.**  The statement is the one
  `DavisKahan/Interop/Spectra/ApproximationNumberMinMax.lean` carried as
  `exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex`, whose proof
  used Spectra's projection-valued measures; nothing of that proof is reused here.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

noncomputable section

section RankHelpers

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A module of rank at least `n` carries `n` independent vectors.

Mathlib has the one-step extension `exists_linearIndependent_snoc_of_lt_rank`; this is the
iterate, which is what a "there are `n + 1` independent vectors" statement needs. -/
theorem exists_fin_linearIndependent_of_le_rank (n : ℕ)
    (h : (n : Cardinal) ≤ Module.rank ℂ V) :
    ∃ v : Fin n → V, LinearIndependent ℂ v := by
  induction n with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type⟩
  | succ m ih =>
    have hm : (m : Cardinal) < Module.rank ℂ V :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) h
    obtain ⟨v, hv⟩ := ih hm.le
    obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_rank hv (by exact_mod_cast hm)
    exact ⟨Fin.snoc v x, hx⟩

/-- A module of rank greater than `n` carries `n + 1` independent vectors. -/
theorem exists_fin_succ_linearIndependent_of_lt_rank (n : ℕ)
    (h : (n : Cardinal) < Module.rank ℂ V) :
    ∃ v : Fin (n + 1) → V, LinearIndependent ℂ v := by
  obtain ⟨v, hv⟩ := exists_fin_linearIndependent_of_le_rank n h.le
  obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_rank hv (by exact_mod_cast h)
  exact ⟨Fin.snoc v x, hx⟩

end RankHelpers

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The min--max upper bound for approximation numbers.**  If `r` is strictly below the
`n`th approximation number of `T`, then `T` is bounded below by some `s > r` on a subspace
spanned by `n + 1` independent vectors.

This is the converse of `ContinuousLinearMap.le_approximationNumber_of_linearIndependent`,
and the two together characterise `aₙ(T)` as a supremum of lower moduli.  No compactness or
finite-dimensionality is assumed. -/
theorem exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < T.approximationNumber n) :
    ∃ s : ℝ, r < s ∧ ∃ v : Fin (n + 1) → E, LinearIndependent ℂ v ∧
      ∀ x ∈ Submodule.span ℂ (Set.range v), s * ‖x‖ ≤ ‖T x‖ := by
  obtain ⟨s, hrs, hsa⟩ := exists_between hr
  have hs0 : 0 ≤ s := hr0.trans hrs.le
  set A : E →L[ℂ] E := T.modulus with hAdef
  have hA : (0 : E →L[ℂ] E) ≤ A := T.modulus_nonneg
  set K : Submodule ℂ E := LinearMap.ker (A.spectralCutoff s : E →ₗ[ℂ] E) with hKdef
  have hKclosed : IsClosed (K : Set E) := by
    simpa [hKdef] using (A.spectralCutoff s).isClosed_ker
  have : CompleteSpace (K : Type _) := hKclosed.completeSpace_coe
  have hlow : ∀ y ∈ Kᗮ, s * ‖y‖ ≤ ‖T y‖ := by
    intro y hy
    rw [← T.norm_modulus_apply]
    exact le_norm_apply_of_mem_orthogonal_ker_spectralCutoff hA hy
  rcases lt_or_ge (n : Cardinal) (Module.rank ℂ (Kᗮ : Submodule ℂ E)) with hbig | hsmall
  · obtain ⟨v, hv⟩ :=
      exists_fin_succ_linearIndependent_of_lt_rank (V := (Kᗮ : Submodule ℂ E)) n hbig
    refine ⟨s, hrs, fun i => ((v i : Kᗮ) : E), hv.map' (Kᗮ).subtype (Kᗮ).ker_subtype, ?_⟩
    intro x hx
    refine hlow x ?_
    refine Submodule.span_le.mpr ?_ hx
    rintro _ ⟨i, rfl⟩
    exact (v i).2
  · exfalso
    have : FiniteDimensional ℂ (Kᗮ : Submodule ℂ E) :=
      Module.rank_lt_aleph0_iff.mp (hsmall.trans_lt (Cardinal.natCast_lt_aleph0 (n := n)))
    have hfr : Module.finrank ℂ (Kᗮ : Submodule ℂ E) ≤ n := by
      have hrk := Module.finrank_eq_rank' ℂ (Kᗮ : Submodule ℂ E)
      rw [← hrk] at hsmall
      exact_mod_cast hsmall
    have hrangeeq :
        LinearMap.range ((T ∘L (Kᗮ : Submodule ℂ E).starProjection) : E →ₗ[ℂ] F) =
          Submodule.map (T : E →ₗ[ℂ] F) (Kᗮ) := by
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change LinearMap.range ((T : E →ₗ[ℂ] F).comp
          (((Kᗮ : Submodule ℂ E).starProjection : E →ₗ[ℂ] E))) = _
      rw [LinearMap.range_comp, Submodule.range_starProjection]
    have : FiniteDimensional ℂ (Submodule.map (T : E →ₗ[ℂ] F) (Kᗮ)) := inferInstance
    have hrank : (T ∘L (Kᗮ : Submodule ℂ E).starProjection).rank ≤ (n : Cardinal) := by
      rw [LinearMap.rank, hrangeeq,
        ← Module.finrank_eq_rank' ℂ (Submodule.map (T : E →ₗ[ℂ] F) (Kᗮ))]
      exact_mod_cast le_trans (Submodule.finrank_map_le _ _) hfr
    have hnorm : ‖T - T ∘L (Kᗮ : Submodule ℂ E).starProjection‖ ≤ s := by
      refine ContinuousLinearMap.opNorm_le_bound _ hs0 fun x => ?_
      have hsplit : x - (Kᗮ : Submodule ℂ E).starProjection x = K.starProjection x := by
        rw [K.starProjection_orthogonal']
        simp
      have hval : (T - T ∘L (Kᗮ : Submodule ℂ E).starProjection) x
          = T (x - (Kᗮ : Submodule ℂ E).starProjection x) := by
        simp [map_sub]
      rw [hval, hsplit, ← T.norm_modulus_apply]
      refine le_trans (norm_apply_le_of_spectralCutoff_apply_eq_zero hA hs0
        (K.starProjection_apply_mem x)) ?_
      gcongr
      exact K.norm_starProjection_apply_le x
    have hle := T.approximationNumber_le_norm_sub hrank
    linarith

end

end ContinuousLinearMap
