/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrialData
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.AlmostInvariant
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.PrescribedSequence
public import LeanPool.DavisKahan.ForTauCeti.Analysis.SpecialFunctions.TanArcsin

/-! # Theorem63Infinite Trial -/

@[expose] public section

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
  exact Theorem63TrialData.approximationSingularValue_sineBlock_lt_one_infiniteData
    (Theorem63TrialData.ofBounded T hT Z V) hdelta hCompressionUpper
      (Theorem63TrialData.ofBounded_crossed_lower T hT Z V hV hUnwantedLower) n

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
  exact Theorem63TrialData.all_kyFan_core_of_formBounds_infinite
    (Theorem63TrialData.ofBounded T hT Z V) hdelta hCompressionUpper
      (Theorem63TrialData.ofBounded_crossed_lower T hT Z V hV hUnwantedLower) k

end CoreAssembly

/-- The paper's instruction that `tan Θ₀` have singular values `tan θ_j`, at arbitrary
trial dimension: the tangent representative's approximation numbers are the tangents of
the arcsines of the directed sine block's approximation numbers. -/
def HasTheorem63DirectedTangentApproximationNumbersInfinite
    (Z V : Submodule ℂ H) [V.HasOrthogonalProjection]
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

omit [CompleteSpace H] in
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
    (Z V : Submodule ℂ H) [V.HasOrthogonalProjection]
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
