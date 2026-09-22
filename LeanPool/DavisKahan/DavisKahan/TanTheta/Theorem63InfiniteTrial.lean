/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63FiniteSource
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.AlmostInvariant
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.PrescribedSequence
import LeanPool.DavisKahan.ForTauCeti.Analysis.SpecialFunctions.TanArcsin

/-! # Theorem63Infinite Trial -/

open TauCeti.DavisKahan.Sylvester

/-!
# Theorem 6.3 with an infinite-dimensional trial space

The compiled Theorem 6.3 chain in `DavisKahan/TanTheta/Theorem63FiniteSource.lean` proves
the Ky Fan tangent inequalities for a **finite-dimensional** trial coordinate space.  The
Section 2 tangent theorem also claims the equal-dimensional infinite and noncompact case,
and the paper's Appendix supplies it by a finite-projector limiting argument.  This module
formalizes that passage.

## The argument

Fix a prefix length `k`.  For any finite-dimensional `F ≤ Z` that is `ε`-almost invariant
under the Ritz compression of `Z`:

* the form bounds restrict from `Z` to `F` verbatim, because on both subspaces the
  compression's quadratic form is the quadratic form of the ambient operator;
* the finite-trial Ky Fan core applies to `F`;
* the Ritz residual of `F` differs from the restricted residual of `Z` by the leakage of
  the compression out of `F`, so
  `kyFan_k (residual F) ≤ kyFan_k (residual Z) + k · ε`.

The sine side is controlled without any operator limit: every approximation singular value
of the directed sine block of `Z` is the supremum of those of its finite-dimensional
restrictions (the min–max localization), the restrictions are monotone in the subspace,
and the almost-invariant enlargement of
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/AlmostInvariant.lean` provides a
single finite `F` that simultaneously nearly attains all `k` sine values and nearly
commutes with the compression.  Letting the two tolerances shrink gives the Ky Fan core at
arbitrary trial dimension.  The transfer `s ↦ tan (arcsin s)` is handled by the scalar
facts in `ForTauCeti/Analysis/SpecialFunctions/TanArcsin.lean`; the pole at `s = 1` never
occurs, because the same finite inequalities force every sine value strictly below one.

## Main results

* `theorem6_3_all_kyFan_core_infiniteTrial`: the Ky Fan tangent inequalities for an
  arbitrary complete trial subspace;
* `approximationSingularValue_sineBlock_lt_one_infiniteTrial`: under the source gap the
  directed sine block of the full trial space has every approximation singular value
  strictly below one;
* `HasTheorem63DirectedTangentApproximationNumbersInfinite` and
  `theorem6_3_infiniteTrial_of_formBounds`: the Fan-dominance ideal-gauge endpoint for any
  tangent representative with the paper's approximation numbers.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open Module (finrank)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ### Plumbing: restrictions, localization, and the compression's quadratic form -/

omit [CompleteSpace H] in
/-- The quadratic form of the Ritz compression is the quadratic form of the ambient
operator.  This is what lets the form bounds of Theorem 6.3 restrict from the full trial
space to any subspace of it. -/
theorem re_inner_theorem63Compression_eq
    (T : H →L[ℂ] H) (W : Submodule ℂ H) [W.HasOrthogonalProjection] (w : W) :
    RCLike.re ⟪theorem63Compression T W w, w⟫_ℂ =
      RCLike.re ⟪T (w : H), (w : H)⟫_ℂ := by
  have h : ⟪theorem63Compression T W w, w⟫_ℂ = ⟪T (w : H), (w : H)⟫_ℂ := by
    rw [Submodule.coe_inner]
    have hc : ((theorem63Compression T W w : W) : H) =
        W.starProjection (T (w : H)) := rfl
    rw [hc, W.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr w.2]
  rw [h]

omit [CompleteSpace H] in
/-- The Ritz residual, applied to a vector: the ambient action minus its projection back
into the trial subspace. -/
theorem theorem63Residual_apply_eq
    (T : H →L[ℂ] H) (W : Submodule ℂ H) [W.HasOrthogonalProjection] (x : W) :
    theorem63Residual T W x = T (x : H) - W.starProjection (T (x : H)) := by
  have h := congrArg (fun L : W →L[ℂ] H => L x)
    (theorem63Residual_eq_complementaryProjection T W)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h]
  exact Submodule.starProjection_orthogonal_apply _ _

omit [CompleteSpace H] in
/-- Distance to a subspace is bounded by the distance to any of its members. -/
theorem norm_sub_starProjection_le_of_mem
    {W : Submodule ℂ H} [W.HasOrthogonalProjection] (u : H) {w : H} (hw : w ∈ W) :
    ‖u - W.starProjection u‖ ≤ ‖u - w‖ := by
  rw [W.starProjection_minimal u]
  exact ciInf_le ⟨0, by rintro r ⟨v, rfl⟩; exact norm_nonneg _⟩ (⟨w, hw⟩ : W)

omit [CompleteSpace H] in
/-- **Finite-dimensional localization inside a fixed subspace.**  Every strict lower bound
for an approximation singular value of a restriction `K ∘L Z.subtypeL` is beaten by the
restriction to some finite-dimensional subspace of `Z`. -/
theorem exists_finiteDimensional_le_lt_approximationSingularValue
    {H₂ : Type u} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : H →L[ℂ] H₂) (Z : Submodule ℂ H) [CompleteSpace Z] (n : ℕ)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hlt : c < approximationSingularValue n (K ∘L Z.subtypeL)) :
    ∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧ F ≤ Z ∧
      c < approximationSingularValue n (K ∘L F.subtypeL) := by
  classical
  obtain ⟨s, hcs, v, hv, hmod⟩ :=
    (ContinuousLinearMap.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
      (K ∘L Z.subtypeL) n hc0).mp hlt
  have hspanfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range v)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  refine ⟨(Submodule.span ℂ (Set.range v)).map Z.subtype, inferInstance,
    Submodule.map_subtype_le Z _, ?_⟩
  have hbound : s ≤ approximationSingularValue n
      (K ∘L ((Submodule.span ℂ (Set.range v)).map Z.subtype).subtypeL) := by
    set F : Submodule ℂ H := (Submodule.span ℂ (Set.range v)).map Z.subtype with hF_def
    set v' : Fin (n + 1) → F := fun i =>
      ⟨((v i : Z) : H),
        Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self i))⟩
      with hv'_def
    have hv' : LinearIndependent ℂ v' := by
      have hmapped : LinearIndependent ℂ ((Z.subtype : Z →ₗ[ℂ] H) ∘ v) :=
        hv.map' Z.subtype (Submodule.ker_subtype Z)
      refine LinearIndependent.of_comp (F.subtype) ?_
      have hcomp : (F.subtype : F →ₗ[ℂ] H) ∘ v' = (Z.subtype : Z →ₗ[ℂ] H) ∘ v := rfl
      rw [hcomp]
      exact hmapped
    refine ContinuousLinearMap.le_approximationNumber_of_linearIndependent
      (K ∘L F.subtypeL) n v' hv' ?_
    intro x _ hxnorm
    obtain ⟨ξ, hξ, hξx⟩ := (Submodule.mem_map).mp x.2
    have hξx' : ((ξ : Z) : H) = ((x : F) : H) := hξx
    have hnormξ : ‖ξ‖ = 1 := by
      calc ‖ξ‖ = ‖((ξ : Z) : H)‖ := rfl
        _ = ‖((x : F) : H)‖ := by rw [hξx']
        _ = ‖x‖ := rfl
        _ = 1 := hxnorm
    have happ : (K ∘L Z.subtypeL) ξ = (K ∘L F.subtypeL) x := by
      change K ((ξ : Z) : H) = K ((x : F) : H)
      rw [hξx']
    have h := hmod ξ hξ
    rw [hnormξ, mul_one, happ] at h
    exact h
  exact lt_of_lt_of_le hcs hbound

/-- Under the source gap, **every** approximation singular value of the directed sine
block of a finite-dimensional trial space is strictly below one. -/
theorem approximationSingularValue_sineBlock_lt_one_of_finite
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V F : Submodule ℂ H) [V.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    [FiniteDimensional ℂ F]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : F,
      RCLike.re ⟪theorem63Compression T F z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock F V) < 1 := by
  by_cases hn : n < finrank ℂ F
  · have hlt := theorem63_singularValues_sine_lt_one T hT V F hV hdelta
      hCompressionUpper hUnwantedLower ⟨n, hn⟩
    have hb := approximationSingularValue_eq_finiteSourceSingularValue
      (theorem63DirectedSineBlock F V) ⟨n, hn⟩
    simpa using hb ▸ hlt
  · have h0 := approximationSingularValue_eq_zero_of_finrank_le_complex
      (Z := F) (theorem63DirectedSineBlock F V) (le_of_not_gt hn)
    rw [h0]
    exact one_pos

/-- The Ritz residual of a subspace `F ≤ Z` is the restriction of the residual of `Z` plus
the leakage of the compression of `Z` out of `F`; at the Ky Fan level the leakage costs at
most `k · ε`. -/
theorem kyFanApproximationGauge_theorem63Residual_le_add
    (T : H →L[ℂ] H) (Z F : Submodule ℂ H)
    [Z.HasOrthogonalProjection] [F.HasOrthogonalProjection]
     [CompleteSpace F]
    (hFZ : F ≤ Z) {ε : ℝ} (hε : 0 ≤ ε)
    (hleak : ∀ f : F, ‖Z.starProjection (T (f : H)) -
        F.starProjection (Z.starProjection (T (f : H)))‖ ≤ ε * ‖(f : H)‖)
    (k : ℕ) :
    kyFanApproximationGauge k (theorem63Residual T F) ≤
      kyFanApproximationGauge k (theorem63Residual T Z) + (k : ℝ) * ε := by
  classical
  set J : F →L[ℂ] Z := (Submodule.inclusion hFZ).mkContinuous 1 (fun x => by
    change ‖((x : F) : H)‖ ≤ 1 * ‖x‖
    simp) with hJ_def
  have hJnorm : ‖J‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    change ‖((x : F) : H)‖ ≤ 1 * ‖x‖
    simp
  set G : F →L[ℂ] H :=
    Z.starProjection ∘L T ∘L F.subtypeL -
      F.starProjection ∘L Z.starProjection ∘L T ∘L F.subtypeL with hG_def
  have hGnorm : ‖G‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε fun f => ?_
    have hGf : G f = Z.starProjection (T (f : H)) -
        F.starProjection (Z.starProjection (T (f : H))) := rfl
    rw [hGf]
    exact hleak f
  have hsplit : theorem63Residual T F = theorem63Residual T Z ∘L J + G := by
    apply ContinuousLinearMap.ext
    intro f
    have hJf : ((J f : Z) : H) = (f : H) := rfl
    have hL := theorem63Residual_apply_eq T F f
    have hR := theorem63Residual_apply_eq T Z (J f)
    have hPF : F.starProjection (T (f : H)) =
        F.starProjection (Z.starProjection (T (f : H))) := by
      have h := congrArg (fun L : H →L[ℂ] H => L (T (f : H)))
        (Submodule.starProjection_comp_starProjection_of_le hFZ)
      simpa using h.symm
    have hGf : G f = Z.starProjection (T (f : H)) -
        F.starProjection (Z.starProjection (T (f : H))) := rfl
    have hlhs : (theorem63Residual T Z ∘L J + G) f =
        theorem63Residual T Z (J f) + G f := rfl
    rw [hlhs, hL, hR, hGf, hJf, hPF]
    abel
  calc
    kyFanApproximationGauge k (theorem63Residual T F) =
        kyFanApproximationGauge k (theorem63Residual T Z ∘L J + G) := by rw [hsplit]
    _ ≤ kyFanApproximationGauge k (theorem63Residual T Z ∘L J) +
        kyFanApproximationGauge k G :=
      kyFanApproximationGauge_add_le_complex k _ _
    _ ≤ kyFanApproximationGauge k (theorem63Residual T Z) + (k : ℝ) * ε := by
      have h1 : kyFanApproximationGauge k (theorem63Residual T Z ∘L J) ≤
          kyFanApproximationGauge k (theorem63Residual T Z) := by
        have h := kyFanApproximationGauge_comp_le k
          (ContinuousLinearMap.id ℂ H) (theorem63Residual T Z) J
        rw [ContinuousLinearMap.id_comp] at h
        refine h.trans ?_
        have hid : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        have hnn := kyFanApproximationGauge_nonneg k (theorem63Residual T Z)
        calc
          ‖ContinuousLinearMap.id ℂ H‖ *
              kyFanApproximationGauge k (theorem63Residual T Z) * ‖J‖ ≤
              1 * kyFanApproximationGauge k (theorem63Residual T Z) * ‖J‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg J)
            exact mul_le_mul_of_nonneg_right hid hnn
          _ ≤ 1 * kyFanApproximationGauge k (theorem63Residual T Z) * 1 := by
            apply mul_le_mul_of_nonneg_left hJnorm
            simpa using hnn
          _ = kyFanApproximationGauge k (theorem63Residual T Z) := by ring
      have h2 : kyFanApproximationGauge k G ≤ (k : ℝ) * ε := by
        refine (kyFanApproximationGauge_le_nat_mul_opNorm k G).trans ?_
        exact mul_le_mul_of_nonneg_left hGnorm (Nat.cast_nonneg k)
      linarith

/-- **Almost-invariant finite-dimensional enlargement inside a trial subspace**, phrased
through the ambient projections: the enlargement `F` contains a prescribed
finite-dimensional `F₀ ≤ Z`, stays inside `Z`, and the compression of `T` to `Z` leaks out
of `F` by at most `ε` on `F`. -/
theorem exists_finiteDimensional_superset_leak
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z : Submodule ℂ H) [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (F₀ : Submodule ℂ H) (hF₀Z : F₀ ≤ Z) [FiniteDimensional ℂ F₀]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧ F₀ ≤ F ∧ F ≤ Z ∧
      ∀ f : F, ∃ y ∈ F, ‖Z.starProjection (T (f : H)) - y‖ ≤ ε * ‖(f : H)‖ := by
  classical
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hMsa : IsSelfAdjoint (theorem63Compression T Z) := by
    simpa [theorem63Compression, DavisKahan.Sylvester.compressOperator] using
      DavisKahan.Sylvester.isSelfAdjoint_compressOperator hTsa Z
  have : FiniteDimensional ℂ (F₀.comap Z.subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hF₀Z).symm
  obtain ⟨F', hF'fin, hF₀'F', hleak'⟩ :=
    TauCeti.BorelCalculus.exists_finiteDimensional_le_almostInvariant hMsa
      (F₀.comap Z.subtype) hε
  have := hF'fin
  refine ⟨F'.map Z.subtype, inferInstance, ?_, Submodule.map_subtype_le Z F', ?_⟩
  · have hmapeq : (F₀.comap Z.subtype).map Z.subtype = F₀ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.mpr hF₀Z
    rw [← hmapeq]
    exact Submodule.map_mono hF₀'F'
  · intro f
    obtain ⟨x, hxF', hxf⟩ := (Submodule.mem_map).mp f.2
    have hxf' : ((x : Z) : H) = (f : H) := hxf
    obtain ⟨y, hyF', hy⟩ := hleak' x hxF'
    have hyH : (y : H) ∈ F'.map Z.subtype := Submodule.mem_map_of_mem hyF'
    refine ⟨(y : H), hyH, ?_⟩
    have hMx : ((theorem63Compression T Z x : Z) : H) =
        Z.starProjection (T (f : H)) := by
      have hc : ((theorem63Compression T Z x : Z) : H) =
          Z.starProjection (T ((x : Z) : H)) := rfl
      rw [hc, hxf']
    have hnorm_eq : ‖Z.starProjection (T (f : H)) - (y : H)‖ =
        ‖theorem63Compression T Z x - y‖ := by
      rw [← hMx]
      rfl
    have hxnorm : ‖x‖ = ‖(f : H)‖ := by
      calc ‖x‖ = ‖((x : Z) : H)‖ := rfl
        _ = ‖(f : H)‖ := by rw [hxf']
    calc
      ‖Z.starProjection (T (f : H)) - (y : H)‖ =
          ‖theorem63Compression T Z x - y‖ := hnorm_eq
      _ ≤ ε * ‖x‖ := hy
      _ = ε * ‖(f : H)‖ := by rw [hxnorm]

/-! ### The infinite-trial Ky Fan core -/

section CoreAssembly

variable (T : H →L[ℂ] H) (V Z : Submodule ℂ H)
  [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection] [CompleteSpace Z]

omit [CompleteSpace H] [CompleteSpace Z] in
/-- Form bounds on the compression restrict to every subspace of the trial space. -/
private theorem compression_upper_transfer {alpha : ℝ}
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] :
    ∀ z : F, RCLike.re ⟪theorem63Compression T F z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2 := by
  intro z
  rw [re_inner_theorem63Compression_eq]
  have h := hCompressionUpper ⟨(z : H), hFZ z.2⟩
  rw [re_inner_theorem63Compression_eq] at h
  simpa using h

omit [CompleteSpace ↥Z] in
/-- The finite leakage step: an almost-invariant finite-dimensional subspace of the trial
space obeys the target Ky Fan bound up to the leakage error. -/
private theorem finite_leak_step (hT : T.IsSymmetric)
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (k' : ℕ) (F : Submodule ℂ H) (hFZ : F ≤ Z)
    [F.HasOrthogonalProjection] [FiniteDimensional ℂ F]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hleak : ∀ f : F, ‖Z.starProjection (T (f : H)) -
      F.starProjection (Z.starProjection (T (f : H)))‖ ≤ ε * ‖(f : H)‖) :
    delta * ∑ n ∈ Finset.range k', Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V))) ≤
      kyFanApproximationGauge k' (theorem63Residual T Z) + (k' : ℝ) * ε := by
  have hCU := compression_upper_transfer T Z hCompressionUpper F hFZ
  have hcore := theorem6_3_all_kyFan_core_directedTangent F V T hT hV hdelta
    hCU hUnwantedLower k'
  have htanvals := hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent
    F V (fun i => theorem63_singularValues_sine_lt_one T hT V F hV hdelta
      hCU hUnwantedLower i)
  have hKyTan : kyFanApproximationGauge k' (theorem63DirectedTangent F V) =
      ∑ n ∈ Finset.range k', Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := htanvals n
    unfold approximationSingularValue at h
    exact h
  calc
    delta * ∑ n ∈ Finset.range k', Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V))) =
        delta * kyFanApproximationGauge k' (theorem63DirectedTangent F V) := by
      rw [hKyTan]
    _ ≤ kyFanApproximationGauge k' (theorem63Residual T F) := hcore
    _ ≤ kyFanApproximationGauge k' (theorem63Residual T Z) + (k' : ℝ) * ε :=
      kyFanApproximationGauge_theorem63Residual_le_add T Z F hFZ hε hleak k'

/-- Under the source gap the directed sine block of the **full** trial space has every
approximation singular value strictly below one, so the paper's tangent list has no pole.
This is not an extra hypothesis: it follows from the same finite inequalities that drive
the limiting argument, because a sine value at one would force the tangent bound past
every threshold. -/
theorem approximationSingularValue_sineBlock_lt_one_infiniteTrial (hT : T.IsSymmetric)
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ) (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock Z V) < 1 := by
  classical
  by_contra hcon
  have ha_le : approximationSingularValue n (theorem63DirectedSineBlock Z V) ≤ 1 := by
    refine (approximationSingularValue_le_opNorm _ _).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [one_mul]
    exact theorem63DirectedSineBlock_apply_norm_le Z V z
  have haeq : approximationSingularValue n (theorem63DirectedSineBlock Z V) = 1 :=
    le_antisymm ha_le (le_of_not_gt fun h => hcon h)
  set B' : ℝ := kyFanApproximationGauge (n + 1) (theorem63Residual T Z) with hB'_def
  have hB'0 : 0 ≤ B' := kyFanApproximationGauge_nonneg _ _
  set C : ℝ := B' / delta + 1 with hC_def
  have hC0 : 0 ≤ C := by positivity
  set c : ℝ := Real.sin (Real.arctan C) with hc_def
  have hc0 : 0 ≤ c := Real.sin_arctan_nonneg.mpr hC0
  have hclt : c < approximationSingularValue n (theorem63DirectedSineBlock Z V) := by
    rw [haeq]
    exact TanArcsin.sin_arctan_lt_one C
  obtain ⟨F₁, hF₁fin, hF₁Z, hF₁⟩ :=
    exists_finiteDimensional_le_lt_approximationSingularValue
      (Vᗮ.starProjection) Z n hc0 hclt
  have := hF₁fin
  have hεp : (0 : ℝ) < delta / (2 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨F, hFfin, hF₁F, hFZ, hleak₀⟩ :=
    exists_finiteDimensional_superset_leak T hT Z F₁ hF₁Z hεp
  have := hFfin
  have : F.HasOrthogonalProjection := inferInstance
  have hleak : ∀ f : F, ‖Z.starProjection (T (f : H)) -
      F.starProjection (Z.starProjection (T (f : H)))‖ ≤
      delta / (2 * ((n : ℝ) + 1)) * ‖(f : H)‖ := by
    intro f
    obtain ⟨y, hyF, hy⟩ := hleak₀ f
    exact (norm_sub_starProjection_le_of_mem _ hyF).trans hy
  have hmono : approximationSingularValue n (theorem63DirectedSineBlock F₁ V) ≤
      approximationSingularValue n (theorem63DirectedSineBlock F V) :=
    approximationSingularValue_restrict_mono (Vᗮ.starProjection) n hF₁F
  have hcF : c < approximationSingularValue n (theorem63DirectedSineBlock F V) :=
    lt_of_lt_of_le hF₁ hmono
  have hFlt1 : approximationSingularValue n (theorem63DirectedSineBlock F V) < 1 :=
    approximationSingularValue_sineBlock_lt_one_of_finite T hT V F hV hdelta
      (compression_upper_transfer T Z hCompressionUpper F hFZ) hUnwantedLower n
  have hgc : Real.tan (Real.arcsin c) ≤ Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlock F V))) :=
    TanArcsin.tanArcsin_le_tanArcsin hc0 hcF.le hFlt1
  have hsum : Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlock F V))) ≤
      ∑ m ∈ Finset.range (n + 1), Real.tan (Real.arcsin
        (approximationSingularValue m (theorem63DirectedSineBlock F V))) := by
    refine Finset.single_le_sum
      (f := fun m => Real.tan (Real.arcsin
        (approximationSingularValue m (theorem63DirectedSineBlock F V))))
      (fun m _ => TanArcsin.tanArcsin_nonneg (approximationSingularValue_nonneg _ _))
      (Finset.self_mem_range_succ n)
  have hfinal := finite_leak_step T V Z hT hV hdelta hCompressionUpper hUnwantedLower
    (n + 1) F hFZ hεp.le hleak
  have hCval : Real.tan (Real.arcsin c) = C := TanArcsin.tanArcsin_sin_arctan C
  have hchain : delta * C ≤ B' + delta / 2 := by
    have h1 : delta * Real.tan (Real.arcsin c) ≤
        delta * ∑ m ∈ Finset.range (n + 1), Real.tan (Real.arcsin
          (approximationSingularValue m (theorem63DirectedSineBlock F V))) :=
      mul_le_mul_of_nonneg_left (hgc.trans hsum) hdelta.le
    have h2 : ((n : ℝ) + 1) * (delta / (2 * ((n : ℝ) + 1))) = delta / 2 := by
      field_simp
    rw [hCval] at h1
    calc
      delta * C ≤ delta * ∑ m ∈ Finset.range (n + 1), Real.tan (Real.arcsin
          (approximationSingularValue m (theorem63DirectedSineBlock F V))) := h1
      _ ≤ B' + ((n : ℝ) + 1) * (delta / (2 * ((n : ℝ) + 1))) := by
        push_cast at hfinal ⊢
        linarith
      _ = B' + delta / 2 := by rw [h2]
  have hCeq : delta * C = B' + delta := by
    rw [hC_def]
    field_simp
  linarith

/-- **The Ky Fan tangent inequalities for an arbitrary complete trial subspace** — the
Davis--Kahan 1970 Appendix finite-projector limiting passage.

The trial subspace `Z` carries no dimension hypothesis: only completeness, so that its
Ritz compression is an operator on a Hilbert space.  The conclusion is the family of
prefix inequalities that Fan dominance promotes to every supported unitarily invariant
ideal gauge. -/
theorem theorem6_3_all_kyFan_core_infiniteTrial (hT : T.IsSymmetric)
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ) (k : ℕ) :
    delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
      kyFanApproximationGauge k (theorem63Residual T Z) := by
  classical
  have ha_lt_one : ∀ n, approximationSingularValue n
      (theorem63DirectedSineBlock Z V) < 1 := fun n =>
    approximationSingularValue_sineBlock_lt_one_infiniteTrial T V Z hT hV hdelta
      hCompressionUpper hUnwantedLower n
  -- The main limit: for every positive slack the target bound holds.
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    exact kyFanApproximationGauge_nonneg _ _
  refine le_of_forall_pos_le_add fun κ hκ => ?_
  have hk0R : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkpos
  set κ' : ℝ := κ / (2 * delta * (k : ℝ)) with hκ'_def
  have hκ'0 : 0 < κ' := by positivity
  -- Per-index nearly-attaining finite subspaces.
  have hkey : ∀ n ∈ Finset.range k, ∃ Fn : Submodule ℂ H,
      FiniteDimensional ℂ Fn ∧ Fn ≤ Z ∧
      ∀ (F : Submodule ℂ H), Fn ≤ F → F ≤ Z →
        ∀ [F.HasOrthogonalProjection] [FiniteDimensional ℂ F],
        Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
        Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock F V))) + κ' := by
    intro n _
    set an : ℝ := approximationSingularValue n (theorem63DirectedSineBlock Z V)
      with han_def
    have han0 : 0 ≤ an := approximationSingularValue_nonneg _ _
    rcases eq_or_lt_of_le han0 with hzero | hpos
    · refine ⟨⊥, inferInstance, bot_le, ?_⟩
      intro F _ hFZ _ _
      have h0 : Real.tan (Real.arcsin an) = 0 := by
        rw [← hzero, Real.arcsin_zero, Real.tan_zero]
      rw [h0]
      have := TanArcsin.tanArcsin_nonneg
        (approximationSingularValue_nonneg n (theorem63DirectedSineBlock F V))
      linarith
    · have hcont := TanArcsin.continuousAt_tanArcsin han0 (ha_lt_one n)
      obtain ⟨d, hd0, hd⟩ := Metric.continuousAt_iff.mp hcont κ' hκ'0
      set cn : ℝ := max (an - d / 2) 0 with hcn_def
      have hcn0 : 0 ≤ cn := le_max_right _ _
      have hcnlt : cn < an := by
        rcases le_or_gt (an - d / 2) 0 with hle | hgt
        · rw [hcn_def, max_eq_right hle]
          exact hpos
        · rw [hcn_def, max_eq_left hgt.le]
          linarith
      have hcnnear : dist cn an < d := by
        rw [Real.dist_eq, abs_lt]
        constructor
        · rcases le_or_gt (an - d / 2) 0 with hle | hgt
          · rw [hcn_def, max_eq_right hle]
            simp only [zero_sub, neg_lt_neg_iff]
            linarith
          · rw [hcn_def, max_eq_left hgt.le]
            linarith
        · linarith [hcnlt]
      have hnear := hd hcnnear
      rw [Real.dist_eq, abs_lt] at hnear
      obtain ⟨Fn, hFnfin, hFnZ, hFn⟩ :=
        exists_finiteDimensional_le_lt_approximationSingularValue
          (Vᗮ.starProjection) Z n hcn0 hcnlt
      refine ⟨Fn, hFnfin, hFnZ, ?_⟩
      intro F hFnF hFZ _ _
      have := hFnfin
      have hmono : approximationSingularValue n (theorem63DirectedSineBlock Fn V) ≤
          approximationSingularValue n (theorem63DirectedSineBlock F V) :=
        approximationSingularValue_restrict_mono (Vᗮ.starProjection) n hFnF
      have hcF : cn ≤ approximationSingularValue n (theorem63DirectedSineBlock F V) :=
        (lt_of_lt_of_le hFn hmono).le
      have hFlt1 : approximationSingularValue n (theorem63DirectedSineBlock F V) < 1 :=
        approximationSingularValue_sineBlock_lt_one_of_finite T hT V F hV hdelta
          (compression_upper_transfer T Z hCompressionUpper F hFZ) hUnwantedLower n
      have hgmono : Real.tan (Real.arcsin cn) ≤ Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock F V))) :=
        TanArcsin.tanArcsin_le_tanArcsin hcn0 hcF hFlt1
      linarith [hnear.1, hnear.2]
  choose Fn hFnfin hFnZ hFnbound using hkey
  -- One finite subspace containing all the per-index choices.
  set F₀ : Submodule ℂ H :=
    (Finset.range k).attach.sup (fun p => Fn p.1 p.2) with hF₀_def
  have : ∀ p : { x // x ∈ Finset.range k }, FiniteDimensional ℂ (Fn p.1 p.2) :=
    fun p => hFnfin p.1 p.2
  have hF₀fin : FiniteDimensional ℂ F₀ :=
    Submodule.finiteDimensional_finset_sup _ _
  have hF₀Z : F₀ ≤ Z := Finset.sup_le fun p _ => hFnZ p.1 p.2
  have hεp : (0 : ℝ) < κ / (2 * (k : ℝ)) := by positivity
  obtain ⟨F, hFfin, hF₀F, hFZ, hleak₀⟩ :=
    exists_finiteDimensional_superset_leak T hT Z F₀ hF₀Z hεp
  have := hFfin
  have : F.HasOrthogonalProjection := inferInstance
  have hleak : ∀ f : F, ‖Z.starProjection (T (f : H)) -
      F.starProjection (Z.starProjection (T (f : H)))‖ ≤
      κ / (2 * (k : ℝ)) * ‖(f : H)‖ := by
    intro f
    obtain ⟨y, hyF, hy⟩ := hleak₀ f
    exact (norm_sub_starProjection_le_of_mem _ hyF).trans hy
  have hperterm : ∀ n ∈ Finset.range k,
      Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
      Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V))) + κ' := by
    intro n hn
    have hFnF : Fn n hn ≤ F := by
      refine le_trans ?_ hF₀F
      exact Finset.le_sup (f := fun p : { x // x ∈ Finset.range k } => Fn p.1 p.2)
        (Finset.mem_attach _ ⟨n, hn⟩)
    exact hFnbound n hn F hFnF hFZ
  have hsumbound : ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
      (∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock F V)))) +
        (k : ℝ) * κ' := by
    calc
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
          ∑ n ∈ Finset.range k, (Real.tan (Real.arcsin
            (approximationSingularValue n (theorem63DirectedSineBlock F V))) + κ') :=
        Finset.sum_le_sum hperterm
      _ = (∑ n ∈ Finset.range k, Real.tan (Real.arcsin
            (approximationSingularValue n (theorem63DirectedSineBlock F V)))) +
          (k : ℝ) * κ' := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
  have hfinstep := finite_leak_step T V Z hT hV hdelta hCompressionUpper
    hUnwantedLower k F hFZ hεp.le hleak
  have hδκ' : delta * ((k : ℝ) * κ') = κ / 2 := by
    rw [hκ'_def]
    field_simp
  have hkε : (k : ℝ) * (κ / (2 * (k : ℝ))) = κ / 2 := by
    field_simp
  calc
    delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
        delta * ((∑ n ∈ Finset.range k, Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock F V)))) +
            (k : ℝ) * κ') :=
      mul_le_mul_of_nonneg_left hsumbound hdelta.le
    _ = delta * (∑ n ∈ Finset.range k, Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock F V)))) +
        delta * ((k : ℝ) * κ') := by ring
    _ ≤ (kyFanApproximationGauge k (theorem63Residual T Z) +
          (k : ℝ) * (κ / (2 * (k : ℝ)))) + delta * ((k : ℝ) * κ') := by
      linarith [hfinstep]
    _ = kyFanApproximationGauge k (theorem63Residual T Z) + κ := by
      rw [hkε, hδκ']
      ring

end CoreAssembly

/-! ### Fan-dominance endpoint for the infinite trial space -/

/-- The paper's instruction that `tan Θ₀` have singular values `tan θ_j`, at arbitrary
trial dimension: the tangent representative's approximation numbers are the tangents of
the arcsines of the directed sine block's approximation numbers. -/
def HasTheorem63DirectedTangentApproximationNumbersInfinite
    (Z V : Submodule ℂ H)  [V.HasOrthogonalProjection]
    (tanTheta0 : Z →L[ℂ] H) : Prop :=
  ∀ n, approximationSingularValue n tanTheta0 =
    Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlock Z V)))

/-- **Theorem 6.3 at ideal-gauge scope with an arbitrary complete trial subspace.**

The trial space carries no dimension hypothesis.  Any tangent representative with the
paper's approximation numbers obeys the ideal-gauge bound in every Fan-dominant unitarily
invariant ideal family. -/
theorem theorem6_3_infiniteTrial_of_formBounds
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem (theorem63Residual T Z)) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) := by
  refine ExactSinTheta.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N.toFanDominantIdealFamily hdelta hResidual fun k => ?_
  have hcore := theorem6_3_all_kyFan_core_infiniteTrial T V Z hT hV hdelta
    hCompressionUpper hUnwantedLower k
  have hKyTan : kyFanApproximationGauge k tanTheta0 =
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := htan n
    unfold approximationSingularValue at h
    exact h
  rw [hKyTan]
  exact hcore

/-! ### The tangent representative exists at every trial dimension -/

omit [CompleteSpace H] in
/-- Composing with the trial-space inclusion moves no approximation singular value; the
finite-source file proves this under a finiteness instance, and this is the general form.
-/
theorem approximationSingularValue_subtypeL_comp_infinite
    (Z : Submodule ℂ H) [Z.HasOrthogonalProjection] 
    (A : Z →L[ℂ] Z) (k : ℕ) :
    approximationSingularValue k (Z.subtypeL ∘L A) = approximationSingularValue k A := by
  have hmem : ∀ x : Z, (Z.subtypeL ∘L A) x ∈ Z := fun x => (A x).property
  have hcomp : Z.orthogonalProjectionOnto ∘L (Z.subtypeL ∘L A) = A := by
    ext x
    change Z.starProjection ((A x : H)) = ((A x : H))
    exact Submodule.starProjection_eq_self_iff.mpr (A x).property
  calc
    approximationSingularValue k (Z.subtypeL ∘L A) =
        approximationSingularValue k
          (Z.orthogonalProjectionOnto ∘L (Z.subtypeL ∘L A)) :=
      (approximationSingularValue_orthogonalProjectionOnto_comp_eq Z
        (Z.subtypeL ∘L A) hmem k).symm
    _ = approximationSingularValue k A := by rw [hcomp]

/-- **The directed tangent representative exists at every trial dimension.**  Under the
no-pole condition — every sine value strictly below one — some bounded operator from the
trial space has exactly the tangent approximation numbers the paper prescribes.

For a finite-dimensional trial space this is the diagonal representative of
`DavisKahan/TanTheta/Theorem63FiniteSource.lean`; for an infinite-dimensional one, the
prescribed antitone sequence is realised by
`TauCeti.ApproximationNumber.exists_approximationNumber_eq_of_antitone` inside the trial
space and included into the ambient space. -/
theorem exists_hasTheorem63DirectedTangentApproximationNumbersInfinite
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hlt : ∀ n, approximationSingularValue n (theorem63DirectedSineBlock Z V) < 1) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 := by
  classical
  by_cases hfin : FiniteDimensional ℂ Z
  · refine ⟨theorem63DirectedTangent Z V, ?_⟩
    have h := hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent
      Z V (fun i => by
        have hb := approximationSingularValue_eq_finiteSourceSingularValue
          (theorem63DirectedSineBlock Z V) i
        rw [← hb]
        exact hlt i)
    exact h
  · set d : ℕ → ℝ := fun n => Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlock Z V))) with hd_def
    have h0 : ∀ n, 0 ≤ d n := fun n =>
      TanArcsin.tanArcsin_nonneg (approximationSingularValue_nonneg _ _)
    have hanti : Antitone d := by
      intro m n hmn
      exact TanArcsin.tanArcsin_le_tanArcsin
        (approximationSingularValue_nonneg _ _)
        (approximationSingularValue_antitone (theorem63DirectedSineBlock Z V) hmn)
        (hlt m)
    obtain ⟨D₀, hD₀⟩ :=
      TauCeti.ApproximationNumber.exists_approximationNumber_eq_of_antitone
        (E := Z) hfin d h0 hanti
    refine ⟨Z.subtypeL ∘L D₀, fun n => ?_⟩
    rw [approximationSingularValue_subtypeL_comp_infinite Z D₀ n]
    have h := hD₀ n
    unfold approximationSingularValue
    exact h

/-! ### Unconditional Fan-dominance endpoints -/

/-- **Theorem 6.3 at ideal-gauge scope and arbitrary trial dimension,
unconditionally**: the tangent representative is exhibited, not assumed.  This is the
equal-dimensional infinite/noncompact half of the Section 2 tangent theorem, in form-bound
shape. -/
theorem theorem6_3_infiniteTrial_of_formBounds_exists
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (hResidual : N.Mem (theorem63Residual T Z)) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V
      (fun n => approximationSingularValue_sineBlock_lt_one_infiniteTrial T V Z hT hV
        hdelta hCompressionUpper hUnwantedLower n)
  obtain ⟨hmem, hbound⟩ := theorem6_3_infiniteTrial_of_formBounds N T hT V Z hV hdelta
    hCompressionUpper hUnwantedLower tanTheta0 htan hResidual
  exact ⟨tanTheta0, htan, hmem, hbound⟩

omit [CompleteSpace H] in
/-- The finite-trial and arbitrary-trial tangent conditions are **the same
proposition**.

`HasTheorem63DirectedTangentApproximationNumbers` carries a `[FiniteDimensional ℂ Z]`
instance binder, but `theorem63DirectedSineBlock` does not depend on it and neither
does the body, so the two definitions unfold to one another.  Consequently the
finite-dimensional trial hypothesis is not part of what the source condition *says*; it
only restricts where the condition can be *stated*.  This is what lets
`theorem6_3_infiniteTrial_ideal` below subsume the finite-trial source facade. -/
theorem hasTheorem63DirectedTangentApproximationNumbers_iff_infinite
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
     (tanTheta0 : Z →L[ℂ] H) :
    HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0 ↔
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 :=
  Iff.rfl

/-- **Davis--Kahan 1970, Theorem 6.3, source-facing spectral form at arbitrary trial
dimension.**

This is the printed generalized `tan Θ` theorem at the printed unitarily-invariant-norm
scope: the Ritz compression's spectrum lies in `[β, α]`, the spectrum of the restriction
to the unwanted exact subspace lies in `[α + δ, ∞)`, the tangent representative is
quantified over exactly as the paper quantifies it ("let `sin Θ₀` be *any* operator whose
singular values are the same as those of `E₀*F₁`"), and the conclusion is
`δ ‖tan Θ₀‖ ≤ ‖R‖` in every Fan-dominant unitarily invariant ideal family.

Unlike `theorem6_3_generalizedTanTheta_ideal`, the trial coordinate space carries
**no** finite-dimensionality typeclass: `[CompleteSpace Z]` is the only structure
assumed, and it already follows from `[Z.HasOrthogonalProjection]` with `H` complete.

The printed hypothesis `dim 𝒳(E₀) < dim 𝒳(F₀)` is **not** assumed, because it is not
needed: in the directed formulation the sine block is `P_{Vᗮ}|_Z` itself, and the Ky Fan
core holds at every relative dimension.  The strict-dimension binder in the finite-trial
chain was already inert — `theorem6_3_generalizedTanTheta_of_formBounds` binds it as
`_hStrictDimension` and never uses it.  Dropping an unused hypothesis strengthens the
statement; it does not narrow it. -/
theorem theorem6_3_infiniteTrial_ideal
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hV : T.Reduces V)
    {beta alpha delta : ℝ} (_hbetaalpha : beta ≤ alpha) (hdelta : 0 < delta)
    (hCompressionSpectrum :
      spectrum ℝ (theorem63Compression T Z) ⊆ Set.Icc beta alpha)
    (hUnwantedSpectrum :
      spectrum ℝ (T.restrict (hV.orthogonalComplement).1) ⊆
        Set.Ici (alpha + delta))
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem (theorem63Residual T Z)) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hMsa : IsSelfAdjoint (theorem63Compression T Z) := by
    simpa [theorem63Compression, DavisKahan.Sylvester.compressOperator] using
      DavisKahan.Sylvester.isSelfAdjoint_compressOperator hTsa Z
  have hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2 := by
    intro z
    refine SpectralOrder.re_inner_le_of_spectrum_subset_Iic
      (theorem63Compression T Z) hMsa ?_ z
    intro r hr
    exact (hCompressionSpectrum hr).2
  have hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := fun y hy =>
    SpectralOrder.le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
      hT (hV.orthogonalComplement).1 hUnwantedSpectrum hy
  exact theorem6_3_infiniteTrial_of_formBounds N T hT V Z hV hdelta
    hCompressionUpper hUnwantedLower tanTheta0 htan hResidual

/-- The finite-trial source facade
`theorem6_3_generalizedTanTheta_ideal` is subsumed: its
`[FiniteDimensional ℂ Z]` instance and its strict-rank hypothesis are both discardable,
and its tangent hypothesis is definitionally the arbitrary-trial one.  Stating that
collapse as a theorem keeps it machine-checked rather than asserted in prose. -/
theorem theorem6_3_generalizedTanTheta_ideal_of_infiniteTrial
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : T.Reduces V)
    (_hStrictDimension : Module.rank ℂ Z < Module.rank ℂ V)
    {beta alpha delta : ℝ} (hbetaalpha : beta ≤ alpha) (hdelta : 0 < delta)
    (hCompressionSpectrum :
      spectrum ℝ (theorem63Compression T Z) ⊆ Set.Icc beta alpha)
    (hUnwantedSpectrum :
      spectrum ℝ (T.restrict (hV.orthogonalComplement).1) ⊆
        Set.Ici (alpha + delta))
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    (hResidual : N.Mem (theorem63Residual T Z)) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) :=
  theorem6_3_infiniteTrial_ideal N T hT V Z hV hbetaalpha hdelta
    hCompressionSpectrum hUnwantedSpectrum tanTheta0 htan hResidual

/-- **Theorem 6.3 at ideal-gauge scope and arbitrary trial dimension, in the source's
spectral form.**  The Ritz compression's spectrum lies in `[β, α]`, the unwanted
restriction's spectrum in `[α + δ, ∞)`, and the conclusion is the ideal-gauge tangent
bound for an exhibited representative — the Section 2 tangent theorem's residual half
with **no** dimension hypothesis on the trial space. -/
theorem theorem6_3_infiniteTrial_spectral_exists
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hV : T.Reduces V)
    {beta alpha delta : ℝ} (_hbetaalpha : beta ≤ alpha) (hdelta : 0 < delta)
    (hCompressionSpectrum :
      spectrum ℝ (theorem63Compression T Z) ⊆ Set.Icc beta alpha)
    (hUnwantedSpectrum :
      spectrum ℝ (T.restrict (hV.orthogonalComplement).1) ⊆
        Set.Ici (alpha + delta))
    (hResidual : N.Mem (theorem63Residual T Z)) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hMsa : IsSelfAdjoint (theorem63Compression T Z) := by
    simpa [theorem63Compression, DavisKahan.Sylvester.compressOperator] using
      DavisKahan.Sylvester.isSelfAdjoint_compressOperator hTsa Z
  have hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2 := by
    intro z
    refine SpectralOrder.re_inner_le_of_spectrum_subset_Iic
      (theorem63Compression T Z) hMsa ?_ z
    intro r hr
    exact (hCompressionSpectrum hr).2
  have hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := fun y hy =>
    SpectralOrder.le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
      hT (hV.orthogonalComplement).1 hUnwantedSpectrum hy
  exact theorem6_3_infiniteTrial_of_formBounds_exists N T hT V Z hV hdelta
    hCompressionUpper hUnwantedLower hResidual

end TanTheta
end DavisKahan
end TauCeti
