/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer

/-!
# Min--max lower bounds for approximation numbers

This module proves the infinite-dimensional lower half of the
Courant--Fischer characterization for approximation numbers. A uniform lower
modulus on an `(n+1)`-dimensional test subspace forces the `n`th approximation
number to be at least that modulus.

The other half — every strict lower bound for `aₙ(T)` is realized as such a
modulus — is
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`.

## Namespace note

These declarations extend the existing Mathlib namespace `ContinuousLinearMap`
rather than living under `TauCeti`, so that dot notation resolves and the names
match the eventual Mathlib upstreaming target. Lean field projection binds
`T.foo` only to the literal `ContinuousLinearMap.foo` and does not consult the
enclosing `TauCeti` namespace. This is a deliberate API choice, flagged for Tau
Ceti maintainer review.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module:
  `ForMathlib/Analysis/Normed/Operator/ApproximationNumberMinMax.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations:
  `ContinuousLinearMap.le_approximationNumber_of_finrank_lt` and
  `ContinuousLinearMap.le_approximationNumber_of_linearIndependent`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
  Declaration names are unchanged (they already extend the canonical Mathlib
  namespace).  No mathematical change.
* Spectra influence: **none** — this module imports only Mathlib and the
  sibling `Basic` and `CourantFischer` staging modules.
-/

public section

namespace ContinuousLinearMap

open Module (finrank)
open scoped InnerProductSpace

noncomputable section

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]

section InfiniteDimensionalMinMaxLower

variable {E₁ : Type v} {F₁ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]

/-- **Courant--Fischer lower bound for approximation numbers.**  If `T` is
bounded below by `c` on a test subspace of rank greater than `n`, then the `n`th
approximation number is at least `c`.

The hypothesis is stated on `Module.rank`, not `finrank`, and the bound is
homogeneous rather than restricted to unit vectors.  Both matter:

* rank rather than dimension means the test subspace need not be
  finite-dimensional, so there is no `[FiniteDimensional 𝕜 V]` instance to
  supply — an infinite-dimensional `V` satisfies `n < Module.rank 𝕜 V` for every
  `n`.  The proof never uses more than "`V` is too big to be killed by a rank
  `≤ n` map";
* the homogeneous bound `c * ‖x‖ ≤ ‖T x‖` says something at `x = 0` and scales,
  where a unit-vector premise does neither.  `le_approximationNumber_of_finrank_lt`
  below converts from the unit-vector form, which needs no sign hypothesis on
  `c`.

Unlike the finite-dimensional Eckart--Young identification, the ambient source
and target spaces need not be finite-dimensional either.

The converse is
`ContinuousLinearMap.exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex`
in `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`, so
the characterization is complete; an earlier version of this docstring said only
this half held unconditionally in infinite dimensions, which was a statement
about the then-available proof, not about the mathematics. -/
theorem le_approximationNumber_of_lt_rank
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (V : Submodule 𝕜 E₁) {c : ℝ}
    (hVrank : (n : Cardinal) < Module.rank 𝕜 V)
    (hV : ∀ x : V, c * ‖(x : E₁)‖ ≤ ‖T (x : E₁)‖) :
    c ≤ T.approximationNumber n := by
  refine T.le_approximationNumber_iff.mpr ?_
  intro R hR
  let RV : V →L[𝕜] F₁ := R.comp V.subtypeL
  have hRVrank : RV.rank ≤ (n : Cardinal) := by
    calc
      RV.rank ≤ R.rank := by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change LinearMap.rank
            (R.toLinearMap.comp V.subtypeL.toLinearMap) ≤ R.rank
        exact LinearMap.rank_comp_le_left V.subtypeL.toLinearMap R.toLinearMap
      _ ≤ (n : Cardinal) := hR
  have hker : RV.ker ≠ ⊥ := by
    intro hkerbot
    -- The rank-nullity identity compares the rank of the range, which lives in
    -- the codomain universe, with the rank of the domain.  Those universes are
    -- independent, so argue through injectivity and `Cardinal.lift` instead: an
    -- injective map identifies the domain with its range.
    have hinj : Function.Injective RV.toLinearMap :=
      LinearMap.ker_eq_bot.mp hkerbot
    have hequiv :
        Cardinal.lift.{w} (Module.rank 𝕜 V) =
          Cardinal.lift.{v}
            (Module.rank 𝕜 (LinearMap.range RV.toLinearMap)) :=
      (LinearEquiv.ofInjective RV.toLinearMap hinj).lift_rank_eq
    have hbad : Module.rank 𝕜 V ≤ (n : Cardinal) := by
      refine Cardinal.lift_le_natCast.mp ?_
      calc
        Cardinal.lift.{w} (Module.rank 𝕜 V)
            = Cardinal.lift.{v} (LinearMap.rank RV.toLinearMap) := hequiv
        _ ≤ Cardinal.lift.{v} ((n : ℕ) : Cardinal) := Cardinal.lift_le.mpr hRVrank
        _ = ((n : ℕ) : Cardinal) := Cardinal.lift_natCast n
    exact absurd hbad (not_le.mpr hVrank)
  obtain ⟨z, hzker, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let x : V := ((‖z‖⁻¹ : ℝ) : 𝕜) • z
  have hxker : x ∈ RV.ker := RV.ker.smul_mem _ hzker
  have hxNorm : ‖(x : E₁)‖ = 1 := by
    simp only [x, Submodule.coe_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hzNorm
  have hRx : R (x : E₁) = 0 := by
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change RV x = 0
    exact LinearMap.mem_ker.mp hxker
  calc
    c = c * ‖(x : E₁)‖ := by rw [hxNorm, mul_one]
    _ ≤ ‖T (x : E₁)‖ := hV x
    _ = ‖(T - R) (x : E₁)‖ := by rw [sub_apply, hRx, sub_zero]
    _ ≤ ‖T - R‖ * ‖(x : E₁)‖ := (T - R).le_opNNNorm (x : E₁)
    _ = ‖T - R‖ := by rw [hxNorm, mul_one]

/-- Finite-dimensional form of `le_approximationNumber_of_lt_rank`, with the
unit-vector premise the classical statement uses.

Nothing is assumed about the sign of `c`: at `x = 0` the homogeneous bound reads
`c * 0 ≤ 0`, and elsewhere it follows by rescaling to a unit vector. -/
theorem le_approximationNumber_of_finrank_lt
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (V : Submodule 𝕜 E₁)
    [FiniteDimensional 𝕜 V] {c : ℝ} (hVdim : n < finrank 𝕜 V)
    (hV : ∀ x : V, ‖(x : E₁)‖ = 1 → c ≤ ‖T (x : E₁)‖) :
    c ≤ T.approximationNumber n := by
  refine le_approximationNumber_of_lt_rank T n V ?_ ?_
  · rw [← Module.finrank_eq_rank' 𝕜 V]
    exact_mod_cast hVdim
  · intro x
    rcases eq_or_ne (x : E₁) 0 with hx | hx
    · simp [hx]
    · -- Rescale `x` to the unit sphere of `V` and use homogeneity of both sides.
      have hxn : ‖(x : E₁)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      set y : V := ((‖(x : E₁)‖⁻¹ : ℝ) : 𝕜) • x with hy
      have hyNorm : ‖(y : E₁)‖ = 1 := by
        simp only [hy, Submodule.coe_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
        exact inv_mul_cancel₀ hxn
      have hTy : ‖T (y : E₁)‖ = ‖(x : E₁)‖⁻¹ * ‖T (x : E₁)‖ := by
        simp [hy, norm_smul]
      have hstep := hV y hyNorm
      rw [hTy] at hstep
      calc c * ‖(x : E₁)‖
          ≤ (‖(x : E₁)‖⁻¹ * ‖T (x : E₁)‖) * ‖(x : E₁)‖ :=
            mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
        _ = ‖T (x : E₁)‖ := by field_simp

/-- Family form of `le_approximationNumber_of_finrank_lt`: a linearly independent
family of `n + 1` vectors determines the required test subspace.

This is not a forgetful wrapper — it is how every downstream consumer in this
repository applies the bound, since a spanning family is what the perturbation
arguments produce. -/
theorem le_approximationNumber_of_linearIndependent
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (v : Fin (n + 1) → E₁)
    (hv : LinearIndependent 𝕜 v) {c : ℝ}
    (hV : ∀ x ∈ Submodule.span 𝕜 (Set.range v),
      ‖x‖ = 1 → c ≤ ‖T x‖) :
    c ≤ T.approximationNumber n := by
  let V : Submodule 𝕜 E₁ := Submodule.span 𝕜 (Set.range v)
  let b : Module.Basis (Fin (n + 1)) 𝕜 V := Module.Basis.span hv
  let : FiniteDimensional 𝕜 V := b.finiteDimensional_of_finite
  have hVdim : n < finrank 𝕜 V := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    exact Nat.lt_succ_self n
  refine le_approximationNumber_of_finrank_lt T n V hVdim ?_
  intro x hx
  exact hV (x : E₁) x.2 hx

/-! ### The orthogonal-tail upper bound

Roadmap topic T09 §B4 asks for the intrinsic equality
`aₙ(T) = ⨅ {‖T ∘L (Vᗮ).starProjection‖ : finrank V ≤ n}`.  This is the `≤` half:
every subspace of dimension at most `n` supplies an admissible approximation, so
the approximation number is below every orthogonal tail. -/

/-- **Every orthogonal tail bounds the approximation number.**  Compressing away a
subspace `V` of dimension at most `n` leaves an admissible rank-`≤ n`
approximation, so `aₙ(T) ≤ ‖T ∘L (Vᗮ).starProjection‖`.

This is the easy half of the orthogonal-tail formula (T09 §B4); the reverse
inequality — that the infimum over such `V` is *attained down to* `aₙ(T)` — is not
proved here.  The subspace lies in the **source**, and the dimension bound is
`finrank V ≤ n` under the zero-based indexing this development uses. -/
theorem approximationNumber_le_norm_comp_starProjection_orthogonal
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (V : Submodule 𝕜 E₁)
    [V.HasOrthogonalProjection] [Vᗮ.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 V] (hV : finrank 𝕜 V ≤ n) :
    T.approximationNumber n ≤ ‖T ∘L Vᗮ.starProjection‖ := by
  have hrangeeq :
      LinearMap.range ((T ∘L V.starProjection) : E₁ →ₗ[𝕜] F₁) =
        Submodule.map (T : E₁ →ₗ[𝕜] F₁) V := by
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change LinearMap.range ((T : E₁ →ₗ[𝕜] F₁).comp
        ((V.starProjection : E₁ →ₗ[𝕜] E₁))) = _
    rw [LinearMap.range_comp, Submodule.range_starProjection]
  have : FiniteDimensional 𝕜 (Submodule.map (T : E₁ →ₗ[𝕜] F₁) V) := inferInstance
  have hrank : (T ∘L V.starProjection).rank ≤ (n : Cardinal) := by
    rw [LinearMap.rank, hrangeeq,
      ← Module.finrank_eq_rank' 𝕜 (Submodule.map (T : E₁ →ₗ[𝕜] F₁) V)]
    exact_mod_cast le_trans (Submodule.finrank_map_le _ _) hV
  have hsub : T - T ∘L V.starProjection = T ∘L Vᗮ.starProjection := by
    ext x
    have hsplit : x - V.starProjection x = Vᗮ.starProjection x := by
      rw [V.starProjection_orthogonal']
      simp
    have hval : (T - T ∘L V.starProjection) x = T (x - V.starProjection x) := by
      simp [map_sub]
    rw [hval, hsplit]
    rfl
  calc T.approximationNumber n ≤ ‖T - T ∘L V.starProjection‖ :=
        T.approximationNumber_le_norm_sub hrank
    _ = ‖T ∘L Vᗮ.starProjection‖ := by rw [hsub]

/-! ### The orthogonal-tail lower bound

This is the reverse inequality of T09 §B4: no admissible subspace's orthogonal
tail sits below `aₙ(T)`, so together with
`approximationNumber_le_norm_comp_starProjection_orthogonal` the approximation
number **is** the infimum of the tails.

The witness is the one §B4 names: given a rank-`≤ n` approximation `R`, take
`V := (ker R)ᗮ`.  Its dimension is at most the rank of `R`, and `Vᗮ = ker R`, on
which `R` vanishes — so the tail of `T` over `V` is the tail of `T - R`, which is
bounded by `‖T - R‖`.

Completeness of the source is used exactly once, to know that the closed subspace
`ker R` carries an orthogonal projection. -/

section OrthogonalTailLower

variable [CompleteSpace E₁]

/-- The kernel of a bounded operator is closed, so in a complete space it carries
an orthogonal projection.  Registered as an instance because every statement
below mentions `(ker R).starProjection`. -/
instance hasOrthogonalProjection_ker (R : E₁ →L[𝕜] F₁) :
    (LinearMap.ker (R : E₁ →ₗ[𝕜] F₁)).HasOrthogonalProjection := by
  have : CompleteSpace (LinearMap.ker (R : E₁ →ₗ[𝕜] F₁)) :=
    R.isClosed_ker.completeSpace_coe
  infer_instance

/-- **An approximation is invisible on the orthogonal complement of its kernel's
complement.**  `R` vanishes on `ker R`, so compressing `T` to `ker R` is the same
as compressing `T - R`, and the compression cannot increase the norm. -/
theorem norm_comp_starProjection_ker_le_norm_sub (T R : E₁ →L[𝕜] F₁) :
    ‖T ∘L (LinearMap.ker (R : E₁ →ₗ[𝕜] F₁)).starProjection‖ ≤ ‖T - R‖ := by
  set K := LinearMap.ker (R : E₁ →ₗ[𝕜] F₁) with hK
  have hcomp : T ∘L K.starProjection = (T - R) ∘L K.starProjection := by
    ext x
    have hmem : K.starProjection x ∈ K := K.starProjection_apply_mem x
    have hzero : R (K.starProjection x) = 0 := LinearMap.mem_ker.mp hmem
    simp [hzero]
  have hP : ‖K.starProjection‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa using K.norm_starProjection_apply_le x
  calc ‖T ∘L K.starProjection‖ = ‖(T - R) ∘L K.starProjection‖ := by rw [hcomp]
    _ ≤ ‖T - R‖ * ‖K.starProjection‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T - R‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hP (norm_nonneg _)
    _ = ‖T - R‖ := mul_one _

omit [CompleteSpace E₁] in
/-- **The orthogonal complement of the kernel is no bigger than the rank.**
`R` is injective on `(ker R)ᗮ`, which identifies that subspace with a submodule
of the range.

The proof goes through `Cardinal.lift` rather than rank--nullity because the
source and target live in independent universes, exactly as in
`le_approximationNumber_of_lt_rank` above. -/
theorem rank_orthogonal_ker_le_of_rank_le (R : E₁ →L[𝕜] F₁) {n : ℕ}
    (hR : R.rank ≤ (n : Cardinal)) :
    Module.rank 𝕜 (LinearMap.ker (R : E₁ →ₗ[𝕜] F₁))ᗮ ≤ (n : Cardinal) := by
  set K := LinearMap.ker (R : E₁ →ₗ[𝕜] F₁) with hK
  let RK : Kᗮ →L[𝕜] F₁ := R.comp Kᗮ.subtypeL
  have hinj : Function.Injective RK.toLinearMap := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_iff _ |>.mpr fun x hx => ?_
    have hxK : (x : E₁) ∈ K := LinearMap.mem_ker.mp hx
    have hxKperp : (x : E₁) ∈ Kᗮ := x.2
    have := (Submodule.orthogonal_disjoint K).le_bot ⟨hxK, hxKperp⟩
    exact Subtype.ext (by simpa using this)
  have hRKrank : LinearMap.rank RK.toLinearMap ≤ (n : Cardinal) :=
    le_trans (LinearMap.rank_comp_le_left Kᗮ.subtypeL.toLinearMap
      (R : E₁ →ₗ[𝕜] F₁)) hR
  have hequiv :
      Cardinal.lift.{w} (Module.rank 𝕜 Kᗮ) =
        Cardinal.lift.{v} (Module.rank 𝕜 (LinearMap.range RK.toLinearMap)) :=
    (LinearEquiv.ofInjective RK.toLinearMap hinj).lift_rank_eq
  refine Cardinal.lift_le_natCast.mp ?_
  calc
    Cardinal.lift.{w} (Module.rank 𝕜 Kᗮ)
        = Cardinal.lift.{v} (LinearMap.rank RK.toLinearMap) := hequiv
    _ ≤ Cardinal.lift.{v} ((n : ℕ) : Cardinal) := Cardinal.lift_le.mpr hRKrank
    _ = ((n : ℕ) : Cardinal) := Cardinal.lift_natCast n

/-- **Every rank-`≤ n` approximation is beaten by an admissible orthogonal
tail.**  This is the witness half of T09 §B4's reverse inequality: the subspace
`V := (ker R)ᗮ` lies in the source, has `finrank 𝕜 V ≤ n` under zero-based
indexing, and its tail is no worse than `R`. -/
theorem exists_finrank_le_norm_comp_starProjection_orthogonal_le
    (T : E₁ →L[𝕜] F₁) {n : ℕ} (R : E₁ →L[𝕜] F₁) (hR : R.rank ≤ (n : Cardinal)) :
    ∃ V : Submodule 𝕜 E₁, ∃ _ : FiniteDimensional 𝕜 V,
      ∃ _ : Vᗮ.HasOrthogonalProjection,
        finrank 𝕜 V ≤ n ∧ ‖T ∘L Vᗮ.starProjection‖ ≤ ‖T - R‖ := by
  set K := LinearMap.ker (R : E₁ →ₗ[𝕜] F₁) with hK
  have hrank : Module.rank 𝕜 Kᗮ ≤ (n : Cardinal) := rank_orthogonal_ker_le_of_rank_le R hR
  have : FiniteDimensional 𝕜 Kᗮ := by
    refine Module.rank_lt_aleph0_iff.mp ?_
    exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0)
  have hfinrank : finrank 𝕜 Kᗮ ≤ n := by
    have := Module.finrank_eq_rank' 𝕜 Kᗮ
    rw [← this] at hrank
    exact_mod_cast hrank
  have hperp : Kᗮᗮ = K := K.orthogonal_orthogonal
  refine ⟨Kᗮ, inferInstance, ?_, hfinrank, ?_⟩
  · rw [hperp]; infer_instance
  · simp only [hperp]
    exact T.norm_comp_starProjection_ker_le_norm_sub R

/-- **The orthogonal tails bound the approximation number from below.**  If a
constant sits below every admissible tail, it sits below `aₙ(T)`.

With `approximationNumber_le_norm_comp_starProjection_orthogonal` this completes
T09 §B4's exact equality: `aₙ(T)` is the greatest lower bound of
`‖T ∘L Vᗮ.starProjection‖` over subspaces `V` of the source with
`finrank 𝕜 V ≤ n`.

The single-statement form is
`approximationNumber_eq_sInf_norm_comp_starProjection_orthogonal` below, and
§B4's other two conditions follow it. -/
theorem le_approximationNumber_of_forall_norm_comp_starProjection_orthogonal
    (T : E₁ →L[𝕜] F₁) (n : ℕ) {c : ℝ}
    (h : ∀ V : Submodule 𝕜 E₁, ∀ _ : FiniteDimensional 𝕜 V,
      ∀ _ : Vᗮ.HasOrthogonalProjection,
      finrank 𝕜 V ≤ n → c ≤ ‖T ∘L Vᗮ.starProjection‖) :
    c ≤ T.approximationNumber n := by
  refine T.le_approximationNumber_iff.mpr fun R hR => ?_
  obtain ⟨V, _, _, hVdim, hVle⟩ :=
    T.exists_finrank_le_norm_comp_starProjection_orthogonal_le R hR
  exact le_trans (h V ‹_› ‹_› hVdim) hVle

/-- **The min--max formula in orthogonal-tail form (T09 §B4).**  The `n`th
approximation number *is* the infimum of `‖T ∘L Vᗮ.starProjection‖` over
finite-dimensional subspaces `V` of the source with `finrank 𝕜 V ≤ n`.

The three conditions §B4 requires of the statement are visible in it: the
subspace `V` lies in the **source**, the dimension condition is `finrank 𝕜 V ≤ n`
under zero-based indexing, and the infimum is over a nonempty bounded-below set
of reals so `sInf` means what it says (`V = ⊥` is always admissible and gives
`‖T‖`).

The infimum need not be attained, which is why this is a `sInf` and not an
existence statement; the two halves it is assembled from —
`approximationNumber_le_norm_comp_starProjection_orthogonal` and
`exists_finrank_le_norm_comp_starProjection_orthogonal_le` — are the usable
forms.

§B4's remaining two conditions are the two theorems just below:
`approximationNumber_eq_zero_of_finrank_source_le` for the behaviour once `n`
reaches the dimension of the source, and
`norm_comp_starProjection_orthogonal_eq_sSup_unitClosedBall` for the equivalence
with the sup formulation — on the closed unit ball of `Vᗮ` rather than its unit
sphere, for the reason that theorem's docstring gives. -/
theorem approximationNumber_eq_sInf_norm_comp_starProjection_orthogonal
    (T : E₁ →L[𝕜] F₁) (n : ℕ) :
    T.approximationNumber n =
      sInf {r : ℝ | ∃ V : Submodule 𝕜 E₁, ∃ _ : FiniteDimensional 𝕜 V,
        ∃ _ : Vᗮ.HasOrthogonalProjection,
        finrank 𝕜 V ≤ n ∧ r = ‖T ∘L Vᗮ.starProjection‖} := by
  set S : Set ℝ := {r : ℝ | ∃ V : Submodule 𝕜 E₁, ∃ _ : FiniteDimensional 𝕜 V,
    ∃ _ : Vᗮ.HasOrthogonalProjection,
    finrank 𝕜 V ≤ n ∧ r = ‖T ∘L Vᗮ.starProjection‖} with hS
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨V, _, _, _, rfl⟩
    exact norm_nonneg _
  have hne : S.Nonempty := by
    refine ⟨‖T ∘L (⊥ : Submodule 𝕜 E₁)ᗮ.starProjection‖,
      ⊥, inferInstance, inferInstance, ?_, rfl⟩
    simp
  refine le_antisymm (le_csInf hne ?_) ?_
  · rintro r ⟨V, _, _, hVdim, rfl⟩
    have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
    exact T.approximationNumber_le_norm_comp_starProjection_orthogonal n V hVdim
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨R, hR, hRlt⟩ :=
      T.exists_rank_le_norm_sub_lt_approximationNumber_add n hε
    obtain ⟨V, _, _, hVdim, hVle⟩ :=
      T.exists_finrank_le_norm_comp_starProjection_orthogonal_le R hR
    have hmem : ‖T ∘L Vᗮ.starProjection‖ ∈ S := ⟨V, ‹_›, ‹_›, hVdim, rfl⟩
    exact le_trans (csInf_le hbdd hmem) (le_trans hVle hRlt.le)

omit [CompleteSpace E₁] in
/-- **The infimum collapses once `n` reaches the dimension of the source (T09
§B4).**  `V = ⊤` is then admissible, its orthogonal complement is `⊥`, and the
tail of `T` over `⊥` is the zero operator — so the infimum, and therefore
`aₙ(T)`, is `0`.

This is proved from the orthogonal-tail bound rather than from the rank
characterisation, which is the point: it is a statement *about the infimum* in
§B4's sense, and reading it off the tail formula is what shows the formula
behaves. -/
theorem approximationNumber_eq_zero_of_finrank_source_le
    [FiniteDimensional 𝕜 E₁] (T : E₁ →L[𝕜] F₁) {n : ℕ} (hn : finrank 𝕜 E₁ ≤ n) :
    T.approximationNumber n = 0 := by
  refine le_antisymm ?_ (T.approximationNumber_nonneg n)
  have h := T.approximationNumber_le_norm_comp_starProjection_orthogonal n ⊤
    (by simpa using hn)
  simpa using h

omit [CompleteSpace E₁] in
/-- **Compressing by the projection is restricting to the subspace.**  The
orthogonal projection maps the unit ball of `E₁` onto the unit ball of `Vᗮ` and
fixes `Vᗮ`, so the two operator norms coincide. -/
theorem norm_comp_starProjection_orthogonal_eq_norm_comp_subtypeL
    (T : E₁ →L[𝕜] F₁) (V : Submodule 𝕜 E₁) [Vᗮ.HasOrthogonalProjection] :
    ‖T ∘L Vᗮ.starProjection‖ = ‖T ∘L Vᗮ.subtypeL‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hmem : Vᗮ.starProjection x ∈ Vᗮ := Vᗮ.starProjection_apply_mem x
    have hval : (T ∘L Vᗮ.starProjection) x =
        (T ∘L Vᗮ.subtypeL) (⟨Vᗮ.starProjection x, hmem⟩ : Vᗮ) := rfl
    calc ‖(T ∘L Vᗮ.starProjection) x‖
        = ‖(T ∘L Vᗮ.subtypeL) (⟨Vᗮ.starProjection x, hmem⟩ : Vᗮ)‖ := by rw [hval]
      _ ≤ ‖T ∘L Vᗮ.subtypeL‖ * ‖(⟨Vᗮ.starProjection x, hmem⟩ : Vᗮ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖T ∘L Vᗮ.subtypeL‖ * ‖x‖ := by
          gcongr
          exact Vᗮ.norm_starProjection_apply_le x
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    have hfix : Vᗮ.starProjection (y : E₁) = (y : E₁) :=
      Vᗮ.starProjection_eq_self_iff.mpr y.2
    have hval : (T ∘L Vᗮ.subtypeL) y = (T ∘L Vᗮ.starProjection) (y : E₁) := by
      simp [ContinuousLinearMap.comp_apply, hfix]
    rw [hval]
    exact ContinuousLinearMap.le_opNorm _ _

omit [CompleteSpace E₁] in
/-- **The unit-ball formulation of the orthogonal tail (T09 §B4).**  The tail is
the supremum of `‖T x‖` over the closed unit ball of `Vᗮ`, so
`approximationNumber_eq_sInf_norm_comp_starProjection_orthogonal` is literally
an `inf-sup` formula.

Stated on the closed **ball** rather than the unit **sphere**, deliberately: on
`Vᗮ = ⊥` the sphere is empty and its supremum is not the tail, whereas the ball
form holds for every `V`. -/
theorem norm_comp_starProjection_orthogonal_eq_sSup_unitClosedBall
    (T : E₁ →L[𝕜] F₁) (V : Submodule 𝕜 E₁) [Vᗮ.HasOrthogonalProjection] :
    ‖T ∘L Vᗮ.starProjection‖ =
      sSup ((fun x : Vᗮ => ‖T (x : E₁)‖) '' Metric.closedBall 0 1) := by
  rw [T.norm_comp_starProjection_orthogonal_eq_norm_comp_subtypeL V]
  exact ((T ∘L Vᗮ.subtypeL).sSup_unitClosedBall_eq_norm).symm

/-- **A spectral band bounds an approximation number.**

If `P` is an orthogonal projection of rank at most `r` and `T` is bounded by `δ`
off its range, then `aᵣ(T) ≤ δ`.  The competitor is `T ∘L P`, whose rank is at
most `P`'s.

**`0 ≤ δ` is not defensive padding.**  Without it the statement is false: at
`P = 1` the band hypothesis reads `0 ≤ 0` and holds for *any* `δ`, and taking
`r ≥ finrank E` makes the conclusion `0 ≤ δ`, which fails at `δ = -1`.  The
submitted roadmap omitted the hypothesis; it was corrected against this
counterexample, and the two signatures now agree.

`hidem` and `hsa` are used in exactly one place: they make `1 - P` a star
projection, hence a contraction, which is what turns the band bound
`δ * ‖x - P x‖` into `δ * ‖x‖`. -/
theorem approximationNumber_le_of_spectral_band [CompleteSpace F₁]
    {T : E₁ →L[𝕜] F₁} {P : E₁ →L[𝕜] E₁} {r : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hidem : IsIdempotentElem P) (hsa : IsSelfAdjoint P)
    (hrank : P.rank ≤ (r : Cardinal))
    (hband : ∀ x : E₁, ‖T (x - P x)‖ ≤ δ * ‖x - P x‖) :
    T.approximationNumber r ≤ δ := by
  -- `1 - P` is a star projection, hence a contraction.
  have hproj : IsStarProjection (1 - P : E₁ →L[𝕜] E₁) :=
    IsStarProjection.one_sub ⟨hidem, hsa⟩
  have hcontr : ∀ x : E₁, ‖x - P x‖ ≤ ‖x‖ := by
    intro x
    have hle : ‖(1 - P : E₁ →L[𝕜] E₁)‖ ≤ 1 := IsStarProjection.norm_le _ hproj
    calc ‖x - P x‖ = ‖(1 - P : E₁ →L[𝕜] E₁) x‖ := by simp
      _ ≤ ‖(1 - P : E₁ →L[𝕜] E₁)‖ * ‖x‖ := (1 - P : E₁ →L[𝕜] E₁).le_opNorm x
      _ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  -- The competitor `T ∘L P` has rank at most `r` and misses by at most `δ`.
  refine le_trans (T.approximationNumber_le_norm_sub (R := T ∘L P) ?_) ?_
  · exact ContinuousLinearMap.rank_comp_le_natCast_right P T hrank
  · refine ContinuousLinearMap.opNorm_le_bound _ hδ fun x => ?_
    have hval : (T - T ∘L P) x = T (x - P x) := by simp
    rw [hval]
    exact (hband x).trans (mul_le_mul_of_nonneg_left (hcontr x) hδ)

end OrthogonalTailLower

end InfiniteDimensionalMinMaxLower

end

end ContinuousLinearMap

end
