/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.AmbientReal
import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrial
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport

/-! # Directed Real -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Directed Section 2 bounds over real Hilbert spaces

This module transports the directed Section 2 tangent theorem from the complex
Hilbert-space implementation back to real Hilbert spaces. The transport is at
the finite-Ky-Fan level, where approximation numbers are exactly preserved by
complexification; source unitarily invariant norms are recovered afterward by
Fan dominance.

The infinite-dimensional tangent representative is constructed over the real
trial space itself. This uses the scalar-generic prescribed-approximation-number
construction in ForTauCeti rather than comparing scalar-fixed ideal families
across the real and complex fields.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation
open TauCeti.DavisKahan.TanTheta
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! ## Real trial blocks and complexification transport -/

/-- Real directed sine block used by the Theorem 6.3 tangent estimate. -/
noncomputable def theorem63DirectedSineBlockReal
    (Z V : Submodule ℝ E)
    [V.HasOrthogonalProjection] : Z →L[ℝ] E :=
  V.orthogonal.starProjection.comp Z.subtypeL

/-- Real Rayleigh--Ritz residual, in complementary-projection form. -/
noncomputable def theorem63ResidualReal
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] : Z →L[ℝ] E :=
  (Z.orthogonal.starProjection.comp T).comp Z.subtypeL

omit [CompleteSpace E] in
/-- The real residual is the usual action-minus-compression residual. -/
theorem theorem63ResidualReal_eq_action_sub_compression
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] :
    theorem63ResidualReal T Z =
      T.comp Z.subtypeL - Z.subtypeL.comp (compressOperatorReal Z T) := by
  apply ContinuousLinearMap.ext
  intro z
  change Z.orthogonal.starProjection (T (z : E)) =
    T (z : E) - Z.subtypeL (Z.orthogonalProjectionOnto (T (z : E)))
  rw [Submodule.starProjection_orthogonal_apply]
  rfl

omit [CompleteSpace E] in
/-- Through the canonical subspace adapter, the complex directed sine block is
exactly the complexification of the real directed sine block. -/
theorem theorem63DirectedSineBlock_complexify_equiv
    (Z V : Submodule ℝ E)
    [V.HasOrthogonalProjection] :
    (theorem63DirectedSineBlock (complexifySubmodule Z) (complexifySubmodule V)).comp
        (complexifySubmoduleEquiv Z).toContinuousLinearEquiv.toContinuousLinearMap =
      complexify (theorem63DirectedSineBlockReal Z V) := by
  apply ContinuousLinearMap.ext
  intro w
  change (complexifySubmodule V).orthogonal.starProjection
      (((complexifySubmoduleEquiv Z w : complexifySubmodule Z) : RealComplexification E)) =
    complexify (V.orthogonal.starProjection.comp Z.subtypeL) w
  rw [starProjection_complexifySubmodule_orthogonal,
    coe_complexifySubmoduleEquiv_eq_complexify_subtypeL,
    RealComplexification.complexify_comp]
  rfl

omit [CompleteSpace E] in
/-- Through the same adapter, the complex Ritz residual is the complexification
of the real Ritz residual. -/
theorem theorem63Residual_complexify_equiv
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] :
    (theorem63Residual (complexify T) (complexifySubmodule Z)).comp
        (complexifySubmoduleEquiv Z).toContinuousLinearEquiv.toContinuousLinearMap =
      complexify (theorem63ResidualReal T Z) := by
  rw [theorem63Residual_eq_complementaryProjection]
  apply ContinuousLinearMap.ext
  intro w
  change (complexifySubmodule Z).orthogonal.starProjection
      ((complexify T)
        (((complexifySubmoduleEquiv Z w : complexifySubmodule Z) : RealComplexification E))) =
    complexify ((Z.orthogonal.starProjection.comp T).comp Z.subtypeL) w
  rw [starProjection_complexifySubmodule_orthogonal,
    coe_complexifySubmoduleEquiv_eq_complexify_subtypeL,
    RealComplexification.complexify_comp,
    RealComplexification.complexify_comp]
  rfl

/-- Approximation singular values of the directed sine block are preserved by
real complexification and the canonical trial-subspace coordinate change. -/
theorem approximationSingularValue_theorem63DirectedSineBlock_complexify
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (n : Nat) :
    approximationSingularValue n
        (theorem63DirectedSineBlock (complexifySubmodule Z) (complexifySubmodule V)) =
      approximationSingularValue n (theorem63DirectedSineBlockReal Z V) := by
  let U := LinearIsometryEquiv.refl Complex (RealComplexification E)
  let W := complexifySubmoduleEquiv Z
  have hcoord :
      (U.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (complexify (theorem63DirectedSineBlockReal Z V))).comp
          W.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        theorem63DirectedSineBlock (complexifySubmodule Z) (complexifySubmodule V) := by
    apply ContinuousLinearMap.ext
    intro z
    let w := W.symm z
    have hw : W w = z := W.apply_symm_apply z
    have h := congrArg (fun L => L w)
      (theorem63DirectedSineBlock_complexify_equiv Z V)
    simpa [U, W, w, hw] using h.symm
  have hsame := SameApproximationSingularValues.of_isometricEquiv_comp U W hcoord
  exact (hsame n).symm.trans
    (approximationSingularValue_complexify (theorem63DirectedSineBlockReal Z V) n)

/-- Approximation singular values of the real Ritz residual are likewise
preserved under the complexified Theorem 6.3 configuration. -/
theorem approximationSingularValue_theorem63Residual_complexify
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] (n : Nat) :
    approximationSingularValue n
        (theorem63Residual (complexify T) (complexifySubmodule Z)) =
      approximationSingularValue n (theorem63ResidualReal T Z) := by
  let U := LinearIsometryEquiv.refl Complex (RealComplexification E)
  let W := complexifySubmoduleEquiv Z
  have hcoord :
      (U.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (complexify (theorem63ResidualReal T Z))).comp
          W.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        theorem63Residual (complexify T) (complexifySubmodule Z) := by
    apply ContinuousLinearMap.ext
    intro z
    let w := W.symm z
    have hw : W w = z := W.apply_symm_apply z
    have h := congrArg (fun L => L w)
      (theorem63Residual_complexify_equiv T Z)
    simpa [U, W, w, hw] using h.symm
  have hsame := SameApproximationSingularValues.of_isometricEquiv_comp U W hcoord
  exact (hsame n).symm.trans
    (approximationSingularValue_complexify (theorem63ResidualReal T Z) n)

/-- The finite Ky Fan residual gauge is exactly preserved by the real-to-complex
Theorem 6.3 transport. -/
theorem kyFanApproximationGauge_theorem63Residual_complexify
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] (k : Nat) :
    kyFanApproximationGauge k
        (theorem63Residual (complexify T) (complexifySubmodule Z)) =
      kyFanApproximationGauge k (theorem63ResidualReal T Z) := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_congr rfl fun n _ =>
    approximationSingularValue_theorem63Residual_complexify T Z n

/-! ## Real infinite-trial tangent theorem -/

/-- The complex infinite-trial Ky Fan theorem descends without loss to a real
Hilbert space. This is the scalar-transport core; no scalar-fixed ideal family
is compared across fields. -/
theorem theorem6_3_all_kyFan_core_infiniteTrial_real
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z, ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (k : Nat) :
    delta * Finset.sum (Finset.range k) (fun n =>
      Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))) <=
      kyFanApproximationGauge k (theorem63ResidualReal T Z) := by
  have hTC : (complexify T).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff T).2 hT)
  have hVC : (complexify T).Reduces (complexifySubmodule V) :=
    (complexify_reduces_iff T V).2 hV
  have hcore := theorem6_3_all_kyFan_core_infiniteTrial
    (complexify T) (complexifySubmodule V) (complexifySubmodule Z)
    hTC hVC hdelta
    (fun z => by
      simpa [theorem63Compression, TauCeti.DavisKahan.Sylvester.compressOperator] using
        re_inner_compressOperator_le Z T hCompressionUpper z)
    (fun y hy => by
      rw [← complexifySubmodule_orthogonal V] at hy
      exact le_re_inner_of_mem_complexifySubmodule hUnwantedLower hy)
    k
  simpa only [
    approximationSingularValue_theorem63DirectedSineBlock_complexify,
    kyFanApproximationGauge_theorem63Residual_complexify] using hcore

/-- Under the real source gap every directed sine approximation value is below
one, so the real tangent sequence has no pole. -/
theorem approximationSingularValue_sineBlock_lt_one_infiniteTrial_real
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z, ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (n : Nat) :
    approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1 := by
  have hTC : (complexify T).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff T).2 hT)
  have hVC : (complexify T).Reduces (complexifySubmodule V) :=
    (complexify_reduces_iff T V).2 hV
  have hlt := approximationSingularValue_sineBlock_lt_one_infiniteTrial
    (complexify T) (complexifySubmodule V) (complexifySubmodule Z)
    hTC hVC hdelta
    (fun z => by
      simpa [theorem63Compression, TauCeti.DavisKahan.Sylvester.compressOperator] using
        re_inner_compressOperator_le Z T hCompressionUpper z)
    (fun y hy => by
      rw [← complexifySubmodule_orthogonal V] at hy
      exact le_re_inner_of_mem_complexifySubmodule hUnwantedLower hy)
    n
  simpa only [approximationSingularValue_theorem63DirectedSineBlock_complexify] using hlt

/-- A real tangent representative has exactly the approximation numbers
prescribed by the paper's directed angle. -/
def HasTheorem63DirectedTangentApproximationNumbersInfiniteReal
    (Z V : Submodule ℝ E)  [V.HasOrthogonalProjection]
    (tanTheta0 : Z →L[ℝ] E) : Prop :=
  ∀ n, approximationSingularValue n tanTheta0 =
    Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))

omit [CompleteSpace E] in
/-- Inclusion of a closed real trial subspace preserves every approximation
singular value of an endomorphism of that subspace. -/
theorem approximationSingularValue_subtypeL_comp_real
    (Z : Submodule ℝ E) [Z.HasOrthogonalProjection]
    (A : Z →L[ℝ] Z) (k : Nat) :
    approximationSingularValue k (Z.subtypeL.comp A) =
      approximationSingularValue k A := by
  have hmem : ∀ x : Z, (Z.subtypeL.comp A) x ∈ Z :=
    fun x => (A x).property
  have hcomp : Z.orthogonalProjectionOnto.comp (Z.subtypeL.comp A) = A := by
    ext x
    change Z.starProjection ((A x : E)) = ((A x : E))
    exact Submodule.starProjection_eq_self_iff.mpr (A x).property
  calc
    approximationSingularValue k (Z.subtypeL.comp A) =
        approximationSingularValue k
          (Z.orthogonalProjectionOnto.comp (Z.subtypeL.comp A)) :=
      (approximationSingularValue_orthogonalProjectionOnto_comp_eq Z
        (Z.subtypeL.comp A) hmem k).symm
    _ = approximationSingularValue k A := by rw [hcomp]

/-- On an infinite-dimensional real trial space, the tangent representative
with the paper's complete singular-value sequence exists as a real operator. -/
theorem exists_hasTheorem63DirectedTangentApproximationNumbersInfiniteReal
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hinf : Not (FiniteDimensional ℝ Z))
    (hlt : ∀ n,
      approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1) :
    Exists (fun tanTheta0 : Z →L[ℝ] E =>
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0) := by
  let d : Nat → ℝ := fun n => Real.tan (Real.arcsin
    (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))
  have h0 : forall n, 0 <= d n := fun n =>
    TanArcsin.tanArcsin_nonneg (approximationSingularValue_nonneg _ _)
  have hanti : Antitone d := by
    intro m n hmn
    exact TanArcsin.tanArcsin_le_tanArcsin
      (approximationSingularValue_nonneg _ _)
      (approximationSingularValue_antitone (theorem63DirectedSineBlockReal Z V) hmn)
      (hlt m)
  obtain ⟨D0, hD0⟩ :=
    TauCeti.ApproximationNumber.exists_approximationNumber_eq_of_antitone
      (E := Z) hinf d h0 hanti
  refine ⟨Z.subtypeL ∘L D0, fun n => ?_⟩
  rw [approximationSingularValue_subtypeL_comp_real Z D0 n]
  exact hD0 n

/-! ## The finite-dimensional real trial space

`exists_approximationNumber_eq_of_antitone` builds a representative only on an
infinite-dimensional space.  On a finite-dimensional real trial space the
representative is instead written down: it is diagonal, with the prescribed
tangents on the diagonal, in an arbitrary orthonormal basis.  A diagonal
operator with antitone nonnegative diagonal has that diagonal as its singular
values, and beyond `finrank Z` both sequences vanish for rank reasons, so the
two cases together cover every real trial subspace. -/

/-- Diagonal entries of the real directed tangent on a finite-dimensional trial
space: tangents of the directed angles, read off the sine block. -/
noncomputable def theorem63DirectedTangentDiagonalReal
    (Z V : Submodule ℝ E)  [V.HasOrthogonalProjection]
    (i : Fin (Module.finrank ℝ Z)) : ℝ :=
  Real.tan (Real.arcsin
    (approximationSingularValue (i : Nat) (theorem63DirectedSineBlockReal Z V)))

/-- A real directed tangent representative on a finite-dimensional trial space,
diagonal in an arbitrary orthonormal basis of that space. -/
noncomputable def theorem63DirectedTangentReal
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [FiniteDimensional ℝ Z] : Z →L[ℝ] E :=
  Z.subtypeL ∘L
    (TauCeti.diagOp (stdOrthonormalBasis ℝ Z)
      (theorem63DirectedTangentDiagonalReal Z V)).toContinuousLinearMap

omit [CompleteSpace E] in
/-- Above the dimension of a finite-dimensional real trial space every
approximation singular value of a map out of it vanishes. -/
theorem approximationSingularValue_eq_zero_of_finrank_le_real
    (Z : Submodule ℝ E) [FiniteDimensional ℝ Z]
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [CompleteSpace Z] (A : Z →L[ℝ] G) {k : Nat} (hk : Module.finrank ℝ Z ≤ k) :
    approximationSingularValue k A = 0 := by
  refine approximationSingularValue_eq_zero_of_rank_le_nat
    (r := Module.finrank ℝ Z) ?_ hk
  calc (A : Z →ₗ[ℝ] G).rank ≤ Module.rank ℝ Z := LinearMap.rank_le_domain _
    _ = ((Module.finrank ℝ Z : Nat) : Cardinal) := (Module.finrank_eq_rank ℝ Z).symm

/-- The finite-dimensional real representative has exactly the approximation
numbers the paper's directed tangent prescribes. -/
theorem hasTheorem63DirectedTangentApproximationNumbersInfiniteReal_theorem63DirectedTangentReal
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [FiniteDimensional ℝ Z]
    (hlt : ∀ n,
      approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1) :
    HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V
      (theorem63DirectedTangentReal Z V) := by
  have ht0 : ∀ i, 0 ≤ theorem63DirectedTangentDiagonalReal Z V i := fun i =>
    TanArcsin.tanArcsin_nonneg (approximationSingularValue_nonneg _ _)
  have htanti : Antitone (theorem63DirectedTangentDiagonalReal Z V) := by
    intro i j hij
    exact TanArcsin.tanArcsin_le_tanArcsin
      (approximationSingularValue_nonneg _ _)
      (approximationSingularValue_antitone (theorem63DirectedSineBlockReal Z V)
        (by exact_mod_cast hij))
      (hlt (i : Nat))
  intro k
  by_cases hk : k < Module.finrank ℝ Z
  · have hkfin : ((⟨k, hk⟩ : Fin (Module.finrank ℝ Z)) : Nat) = k := rfl
    calc
      approximationSingularValue k (theorem63DirectedTangentReal Z V)
        = approximationSingularValue k
            (TauCeti.diagOp (stdOrthonormalBasis ℝ Z)
              (theorem63DirectedTangentDiagonalReal Z V)).toContinuousLinearMap :=
          approximationSingularValue_subtypeL_comp_real Z _ k
      _ = (TauCeti.diagOp (stdOrthonormalBasis ℝ Z)
            (theorem63DirectedTangentDiagonalReal Z V)).singularValues k :=
          approximationSingularValue_eq_singularValues _ k
      _ = theorem63DirectedTangentDiagonalReal Z V ⟨k, hk⟩ := by
          simpa only [hkfin] using
            TauCeti.singularValues_diagOp (𝕜 := ℝ) (E := Z)
              (n := Module.finrank ℝ Z) rfl (stdOrthonormalBasis ℝ Z)
              htanti ht0 ⟨k, hk⟩
      _ = Real.tan (Real.arcsin (approximationSingularValue k
            (theorem63DirectedSineBlockReal Z V))) := rfl
  · have hkge : Module.finrank ℝ Z ≤ k := Nat.le_of_not_lt hk
    rw [approximationSingularValue_eq_zero_of_finrank_le_real Z
        (theorem63DirectedTangentReal Z V) hkge,
      approximationSingularValue_eq_zero_of_finrank_le_real Z
        (theorem63DirectedSineBlockReal Z V) hkge]
    simp

/-- **The real directed tangent representative exists on every real trial
subspace**, of finite or infinite dimension. -/
theorem exists_hasTheorem63DirectedTangentApproximationNumbersReal
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hlt : ∀ n,
      approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1) :
    Exists (fun tanTheta0 : Z →L[ℝ] E =>
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0) := by
  classical
  by_cases hfin : FiniteDimensional ℝ Z
  · exact ⟨theorem63DirectedTangentReal Z V,
      hasTheorem63DirectedTangentApproximationNumbersInfiniteReal_theorem63DirectedTangentReal
        Z V hlt⟩
  · exact exists_hasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V hfin hlt

/-- **Real directed Theorem 6.3 at every source unitarily invariant norm, on a
real Hilbert space of arbitrary dimension and an arbitrary closed real trial
subspace.**

The paper's hypotheses, unweakened: `T` self-adjoint, `V` reducing, the
Rayleigh--Ritz upper bound `alpha` on the compression, the one-sided lower
bound `alpha + delta` on the unwanted part, and membership of the Ritz residual
in the chosen source norm.  The conclusion exhibits a directed tangent
representative with the paper's complete singular-value sequence, concludes its
membership, and gives `delta * N(tan Theta_0) <= N(R)`.

The complex Theorem 6.3 proof supplies the Ky Fan inequalities; exact
complexification transport reads them back over the reals -- at the finite Ky
Fan level, where approximation numbers are preserved on the nose, so no
scalar-fixed ideal family is compared across fields; the tangent representative
is then constructed over the real trial space itself, in either dimension; and
Fan dominance supplies the source norm. -/
theorem tanTheta_directed_bounded_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z, ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (hResidual : N.Mem (theorem63ResidualReal T Z)) :
    Exists (fun tanTheta0 : Z →L[ℝ] E =>
      And (HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
        (And (N.Mem tanTheta0)
          (delta * N.gauge tanTheta0 <= N.gauge (theorem63ResidualReal T Z)))) := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersReal Z V
      (fun n => approximationSingularValue_sineBlock_lt_one_infiniteTrial_real
        T hT V Z hV hdelta hCompressionUpper hUnwantedLower n)
  have hky : ∀ k : Nat,
      delta * kyFanApproximationGauge k tanTheta0 <=
        kyFanApproximationGauge k (theorem63ResidualReal T Z) := by
    intro k
    have hcore := theorem6_3_all_kyFan_core_infiniteTrial_real
      T hT V Z hV hdelta hCompressionUpper hUnwantedLower k
    have htanKy : kyFanApproximationGauge k tanTheta0 =
        Finset.sum (Finset.range k) (fun n =>
          Real.tan (Real.arcsin
            (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))) := by
      unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
      exact Finset.sum_congr rfl fun n _ => htan n
    rw [htanKy]
    exact hcore
  obtain ⟨hmem, hbound⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual hky
  exact ⟨tanTheta0, htan, hmem, hbound⟩

/-- Real directed half of the Section 2 tan-theta theorem at every source
unitarily invariant norm, for an arbitrary infinite-dimensional trial space.

The infinite-dimensional trial restriction is no longer needed; this is the
recorded specialization of `tanTheta_directed_bounded_symmetricNorming_real`, kept because it
is the form the census cites. -/
theorem tanTheta_directed_bounded_arbitraryDimension_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (_hinf : Not (FiniteDimensional ℝ Z))
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z, ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (hResidual : N.Mem (theorem63ResidualReal T Z)) :
    Exists (fun tanTheta0 : Z →L[ℝ] E =>
      And (HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
        (And (N.Mem tanTheta0)
          (delta * N.gauge tanTheta0 <= N.gauge (theorem63ResidualReal T Z)))) :=
  tanTheta_directed_bounded_symmetricNorming_real N T hT V Z hV hdelta hCompressionUpper
    hUnwantedLower hResidual

/-! ### The printed spectral orientation over a real Hilbert space

The hypotheses Davis and Kahan actually print are spectral placements, not quadratic-form
bounds: the Rayleigh--Ritz compression has spectrum in `[β, α]` and the restriction to the
unwanted exact subspace has spectrum in `[α + δ, ∞)`.  Over `ℂ` the conversion is
`SpectralOrder`; the real conversion is `TauCeti.SpectralOrder`, which proves the
same two bridges by a Rayleigh shift because Mathlib has no `StarOrderedRing (E →L[ℝ] E)`. -/

/-- **Real directed Theorem 6.3 at every source unitarily invariant norm, in the printed
spectral orientation.**

The Ritz compression's spectrum lies in `[β, α]`, the spectrum of the restriction to the
unwanted exact subspace lies in `[α + δ, ∞)`, and the conclusion is `δ N(tan Θ₀) ≤ N(R)` for
the paper's norm class, with the tangent representative exhibited and its membership
concluded.  Real Hilbert space of arbitrary dimension, arbitrary closed real trial subspace.

Grounded on `tanTheta_directed_bounded_symmetricNorming_real`; the spectral placement is converted to the
form bounds by the two `TauCeti.SpectralOrder` bridges, exactly as
`tanTheta_directed_bounded_spectralGap_symmetricNorming_complex` uses their complex twins. -/
theorem tanTheta_directed_bounded_spectralGap_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hV : T.Reduces V)
    {beta alpha delta : ℝ} (_hbetaalpha : beta ≤ alpha) (hdelta : 0 < delta)
    (hCompressionSpectrum :
      spectrum ℝ (compressOperatorReal Z T) ⊆ Set.Icc beta alpha)
    (hUnwantedSpectrum :
      spectrum ℝ (T.restrict hV.2) ⊆ Set.Ici (alpha + delta))
    (hResidual : N.Mem (theorem63ResidualReal T Z)) :
    Exists (fun tanTheta0 : Z →L[ℝ] E =>
      And (HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
        (And (N.Mem tanTheta0)
          (delta * N.gauge tanTheta0 ≤ N.gauge (theorem63ResidualReal T Z)))) := by
  have hTsym : T.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hMsa : IsSelfAdjoint (compressOperatorReal Z T) :=
    isSelfAdjoint_compressOperator hT Z
  have hCompressionUpper : ∀ z : Z,
      ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2 := fun z =>
    SpectralOrder.upperFormBoundOn_top_of_spectrum_subset_Iic
      (compressOperatorReal Z T) hMsa
      (fun r hr => (hCompressionSpectrum hr).2) z Submodule.mem_top
  have hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ :=
    SpectralOrder.lowerFormBoundOn_of_restriction_spectrum_subset_Ici
      hTsym hV.2 hUnwantedSpectrum
  exact tanTheta_directed_bounded_symmetricNorming_real N T hT V Z hV hdelta hCompressionUpper
    hUnwantedLower hResidual

/-! ### The perturbation companion over a real Hilbert space

The printed tangent theorem's residual form bounds `tan Θ₀` by the Rayleigh--Ritz residual of
the trial space.  Its perturbation companion bounds it by the perturbation itself, when the
trial space is invariant for the perturbed operator.  The bridge is one line of algebra and
no new estimate, exactly as over `ℂ`. -/

omit [CompleteSpace E] in
/-- **The real Ritz residual of an invariant trial space is the compressed perturbation.**

If `Z` is invariant for `T + P` then `P_Zᗮ (T + P)|_Z = 0`, so the real residual of `T` on
`Z` is exactly `−P_Zᗮ P|_Z`.  The real twin of
`Experimental.MathAhead.Section2.theorem63Residual_eq_neg_of_invariant`. -/
theorem theorem63ResidualReal_eq_neg_of_invariant
    (T P : E →L[ℝ] E) (Z : Submodule ℝ E) [Z.HasOrthogonalProjection]
    (hinv : ∀ x ∈ Z, (T + P) x ∈ Z) :
    theorem63ResidualReal T Z = -(Zᗮ.starProjection ∘L (P ∘L Z.subtypeL)) := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : ((T + P) (z : E)) ∈ Z := hinv (z : E) z.property
  have hzero : Zᗮ.starProjection ((T + P) (z : E)) = 0 := by
    refine (Submodule.starProjection_apply_eq_zero_iff Zᗮ).mpr ?_
    rw [Submodule.orthogonal_orthogonal]
    exact hz
  have hsplit : Zᗮ.starProjection (T (z : E)) + Zᗮ.starProjection (P (z : E)) = 0 := by
    rw [← map_add]
    simpa using hzero
  have hres : theorem63ResidualReal T Z z = Zᗮ.starProjection (T (z : E)) := rfl
  rw [hres]
  have hneg : Zᗮ.starProjection (T (z : E)) = -Zᗮ.starProjection (P (z : E)) :=
    eq_neg_of_add_eq_zero_left hsplit
  simpa using hneg

omit [CompleteSpace E] in
/-- Termwise domination of the real residual's approximation numbers by those of the
restricted perturbation.  The residual is a contraction applied to `P|_Z`, so no estimate is
involved. -/
theorem approximationSingularValue_theorem63ResidualReal_le_of_invariant
    (T P : E →L[ℝ] E) (Z : Submodule ℝ E) [Z.HasOrthogonalProjection]
    (hinv : ∀ x ∈ Z, (T + P) x ∈ Z) (n : Nat) :
    approximationSingularValue n (theorem63ResidualReal T Z) ≤
      approximationSingularValue n (P ∘L Z.subtypeL) := by
  rw [theorem63ResidualReal_eq_neg_of_invariant T P Z hinv,
    approximationSingularValue_neg]
  have hcomp := approximationSingularValue_comp_le (𝕜 := ℝ) n
    (Zᗮ.starProjection) (P ∘L Z.subtypeL) (1 : Z →L[ℝ] Z)
  have hid : (Zᗮ.starProjection ∘L ((P ∘L Z.subtypeL) ∘L
      (1 : Z →L[ℝ] Z))) = Zᗮ.starProjection ∘L (P ∘L Z.subtypeL) := by
    ext x
    simp
  rw [hid] at hcomp
  refine hcomp.trans ?_
  have hP : ‖(Zᗮ.starProjection : E →L[ℝ] E)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa only [one_mul] using Submodule.norm_starProjection_apply_le Zᗮ x
  have hone : ‖(1 : Z →L[ℝ] Z)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hnn : 0 ≤ approximationSingularValue n (P ∘L Z.subtypeL) :=
    approximationSingularValue_nonneg _ _
  calc
    ‖(Zᗮ.starProjection : E →L[ℝ] E)‖ *
        approximationSingularValue n (P ∘L Z.subtypeL) *
          ‖(1 : Z →L[ℝ] Z)‖ ≤
        1 * approximationSingularValue n (P ∘L Z.subtypeL) * 1 := by
      have h1 : ‖(Zᗮ.starProjection : E →L[ℝ] E)‖ *
          approximationSingularValue n (P ∘L Z.subtypeL) ≤
          1 * approximationSingularValue n (P ∘L Z.subtypeL) :=
        mul_le_mul_of_nonneg_right hP hnn
      exact mul_le_mul h1 hone (norm_nonneg (1 : Z →L[ℝ] Z)) (by linarith)
    _ = approximationSingularValue n (P ∘L Z.subtypeL) := by ring

/-- **Real directed Theorem 6.3, perturbation form, at every source unitarily invariant
norm.**

If the real trial space `Z` is invariant for the perturbed operator `T + P`, and `T` reduces
`V` with the source gap, then `δ N(tan Θ₀) ≤ N(P|_Z)` for every `SymmetricNormingFunction`,
with the tangent representative exhibited and its membership concluded.  Real Hilbert space
of arbitrary dimension, arbitrary closed real trial subspace.

The right-hand side is the perturbation *restricted to the trial space*: `P` and `P|_Z` live
in different spaces, so a norm on an ideal cannot compare them, and the restriction is both
what the estimate controls and the sharper statement.

This is the real counterpart of
`Experimental.MathAhead.Section2.theorem6_3_perturbation_infiniteTrial`, at the paper's own
norm class rather than at a scalar-fixed ideal family. -/
theorem tanTheta_directed_bounded_perturbation_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (T P : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z, ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (hinv : ∀ x ∈ Z, (T + P) x ∈ Z)
    (hPmem : N.Mem (P ∘L Z.subtypeL)) :
    Exists (fun tanTheta0 : Z →L[ℝ] E =>
      And (HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
        (And (N.Mem tanTheta0)
          (delta * N.gauge tanTheta0 ≤ N.gauge (P ∘L Z.subtypeL)))) := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersReal Z V
      (fun n => approximationSingularValue_sineBlock_lt_one_infiniteTrial_real
        T hT V Z hV hdelta hCompressionUpper hUnwantedLower n)
  have hky : ∀ k : Nat,
      delta * kyFanApproximationGauge k tanTheta0 ≤
        kyFanApproximationGauge k (P ∘L Z.subtypeL) := by
    intro k
    have hcore := theorem6_3_all_kyFan_core_infiniteTrial_real
      T hT V Z hV hdelta hCompressionUpper hUnwantedLower k
    have htanKy : kyFanApproximationGauge k tanTheta0 =
        Finset.sum (Finset.range k) (fun n =>
          Real.tan (Real.arcsin
            (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))) := by
      unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
      exact Finset.sum_congr rfl fun n _ => htan n
    have hres : kyFanApproximationGauge k (theorem63ResidualReal T Z) ≤
        kyFanApproximationGauge k (P ∘L Z.subtypeL) := by
      unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
      exact Finset.sum_le_sum fun n _ =>
        approximationSingularValue_theorem63ResidualReal_le_of_invariant T P Z hinv n
    rw [htanKy]
    exact hcore.trans hres
  obtain ⟨hmem, hbound⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hdelta hPmem hky
  exact ⟨tanTheta0, htan, hmem, hbound⟩

/-! ### Uniform transversality over a real Hilbert space is derived, not assumed

The real twin of `norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent`.  The
quantitative half is the real directed estimate above; the printed standing assumption
(3.5) upgrades the directed gap to the symmetric one that `sin Θ` measures. -/

/-- **Davis--Kahan 1970, Section 2 over a REAL Hilbert space: uniform transversality is a
consequence.**

`‖sin Θ‖ < 1` follows from the tangent theorem's own form bounds together with the printed
standing assumption (3.5).  The ambient directed block `P_{V^⊥} P_U` factors through the
trial block `P_{V^⊥} P_U|_U`, whose approximation singular values are already known to be
strictly below one, and (3.5) identifies the symmetric gap with the directed one. -/
theorem norm_sinAngleOperatorR_lt_one_of_crossedDefectsEquivalent
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U, ⟪compressOperatorReal U T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V) :
    ‖sinAngleOperatorR U V‖ < 1 := by
  have hdirected := approximationSingularValue_sineBlock_lt_one_infiniteTrial_real
    T hT V U hV hdelta hCompressionUpper hUnwantedLower 0
  rw [approximationSingularValue_zero] at hdirected
  have hfactor : Vᗮ.starProjection ∘L U.starProjection =
      theorem63DirectedSineBlockReal U V ∘L U.orthogonalProjectionOnto := rfl
  have hnorm : ‖Vᗮ.starProjection ∘L U.starProjection‖ < 1 := by
    rw [hfactor]
    calc ‖theorem63DirectedSineBlockReal U V ∘L U.orthogonalProjectionOnto‖
        ≤ ‖theorem63DirectedSineBlockReal U V‖ * ‖U.orthogonalProjectionOnto‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖theorem63DirectedSineBlockReal U V‖ * 1 :=
          mul_le_mul_of_nonneg_left U.orthogonalProjectionOnto_norm_le
            (ContinuousLinearMap.opNorm_nonneg (theorem63DirectedSineBlockReal U V))
      _ < 1 := by rwa [mul_one]
  rw [norm_sinAngleOperatorR,
    DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
      U V h35]
  exact hnorm

/-- **The whole-space `tan Θ` theorem over a REAL Hilbert space, for every source unitarily
invariant norm, under the printed standing assumptions only.**

Identical to `tanTheta_ambient_bounded_symmetricNorming_real_of_transversality` except that uniform transversality is no
longer a hypothesis: it is derived from the form bounds and the printed (3.5). -/
theorem tanTheta_ambient_bounded_symmetricNorming_real_of_crossedDefects
    (N : SymmetricNormingFunction)
    {A T : E →L[ℝ] E} {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hT : IsSelfAdjoint T) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U, ⟪compressOperatorReal U T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hMem : N.Mem (T - A)) :
    ‖sinAngleOperatorR U V‖ < 1 ∧
      N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge (T - A) :=
  ⟨norm_sinAngleOperatorR_lt_one_of_crossedDefectsEquivalent T hT U V hV hdelta
      hCompressionUpper hUnwantedLower h35,
    tanTheta_ambient_bounded_symmetricNorming_real_of_transversality N hT hA hV hAU hdelta hCompressionUpper
      hUnwantedLower
      (norm_sinAngleOperatorR_lt_one_of_crossedDefectsEquivalent T hT U V hV hdelta
        hCompressionUpper hUnwantedLower h35) hMem⟩

end
end DavisKahan1970
end TauCeti
