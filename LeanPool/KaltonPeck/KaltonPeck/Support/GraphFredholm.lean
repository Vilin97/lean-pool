/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.Symplectic
import LeanPool.KaltonPeck.KaltonPeck.Support.CanonicalPairing
import LeanPool.KaltonPeck.KaltonPeck.Support.CgpBlockExtraction
import LeanPool.KaltonPeck.KaltonPeck.Support.CgpCompactRestriction
import LeanPool.KaltonPeck.KaltonPeck.Support.CgpStrictlySingularLifting
import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm
import LeanPool.KaltonPeck.KaltonPeck.Support.HilbertGlidingHump
import LeanPool.KaltonPeck.KaltonPeck.Support.KernelNuclearCorrection
import LeanPool.KaltonPeck.KaltonPeck.Support.PathParity
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularAdd
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularHilbert
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularHilbertCompact

/-!
# Fredholm analysis of canonical graph operators

This file combines strict singularity, block extraction, and compact-factorization arguments to
establish the main Fredholm results for canonical operators on the Kalton--Peck space.
-/


namespace KaltonPeck.Support.GraphFredholm

noncomputable
section

open Coordinates Symplectic
open HilbertGlidingHump
open StrictlySingular
open Filter Function
open scoped ENNReal NNReal Topology lp BigOperators InnerProductSpace

universe uX uY

/-- An operator with infinite-dimensional kernel has an infinite-dimensional compact
restriction.
Blueprint label: `lem:infinite-kernel-compact-restriction`. -/
theorem hasInfiniteDimensionalCompactRestriction_of_infiniteDimensional_kernel
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (hker : ¬ FiniteDimensional ℝ T.toLinearMap.ker) :
    HasInfiniteDimensionalCompactRestriction T := by
  refine ⟨T.toLinearMap.ker, T.isClosed_ker, hker, ?_⟩
  have hzero : T.comp T.toLinearMap.ker.subtypeL = 0 := by
    ext x
    exact x.property
  rw [hzero]
  exact isCompactOperator_zero

/-- If an operator has finite-dimensional kernel and nonclosed range, then on a closed
infinite-dimensional complement of its kernel it admits a normalized approximate-kernel
sequence whose image norms are summable.
Blueprint label: `lem:nonclosed-range-approximate-kernel`. -/
theorem exists_summableApproximateKernelSequence_of_finiteDimensional_ker
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T : X →L[ℝ] Y) (hkerT : FiniteDimensional ℝ T.toLinearMap.ker)
    (hrangeT : ¬ IsClosed (T.toLinearMap.range : Set Y)) :
    ∃ Z : Submodule ℝ X, IsClosed (Z : Set X) ∧
      Submodule.IsTopCompl T.toLinearMap.ker Z ∧
      ¬ FiniteDimensional ℝ Z ∧
      ∃ z : ℕ → Z, (∀ n, ‖z n‖ = 1) ∧
        Summable (fun n ↦ ‖(T.comp Z.subtypeL) (z n)‖) := by
  let : FiniteDimensional ℝ T.toLinearMap.ker := hkerT
  let hker : T.toLinearMap.ker.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional T.toLinearMap.ker
  let Z : Submodule ℝ X := hker.complement
  have htop : Submodule.IsTopCompl T.toLinearMap.ker Z :=
    hker.isTopCompl_complement
  have hZclosed : IsClosed (Z : Set X) := hker.isClosed_complement
  let : CompleteSpace Z := hZclosed.completeSpace_coe
  let S : Z →L[ℝ] X := Z.subtypeL
  have hTSinjective : Function.Injective (T.comp S) := by
    intro x y hxy
    apply Subtype.ext
    have hkerxy : (x : X) - (y : X) ∈ T.toLinearMap.ker := by
      change T ((x : X) - (y : X)) = 0
      rw [map_sub, sub_eq_zero]
      simpa [S] using hxy
    have hZxy : (x : X) - (y : X) ∈ Z :=
      Z.sub_mem x.property y.property
    have hzero : (x : X) - (y : X) ∈ (⊥ : Submodule ℝ X) :=
      htop.isCompl.disjoint.le_bot ⟨hkerxy, hZxy⟩
    simpa only [Submodule.mem_bot, sub_eq_zero] using hzero
  have hrange : Set.range (T.comp S) = (T.toLinearMap.range : Set Y) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨x, rfl⟩
      have hx : x ∈ T.toLinearMap.ker ⊔ Z := by
        rw [htop.isCompl.sup_eq_top]
        exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hx with ⟨k, hk, z, hz, hkz⟩
      refine ⟨⟨z, hz⟩, ?_⟩
      change T z = T x
      rw [← hkz, map_add, show T k = 0 from hk, zero_add]
  have hTSrange : ¬ IsClosed (Set.range (T.comp S)) := by
    simpa only [hrange] using hrangeT
  have hZ : ¬ FiniteDimensional ℝ Z := by
    intro hZfin
    let : FiniteDimensional ℝ Z := hZfin
    have : FiniteDimensional ℝ (T.comp S).toLinearMap.range := inferInstance
    exact hTSrange (T.comp S).toLinearMap.range.closed_of_finiteDimensional
  have hnanti : ¬ ∃ K, AntilipschitzWith K (T.comp S) := by
    intro hanti
    exact hTSrange
      (((T.comp S).isClosed_range_iff_antilipschitz_of_injective hTSinjective).2 hanti)
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ x : Z, ‖(T.comp S) x‖ < ε * ‖x‖ := by
    rw [antilipschitzWith_iff_exists_mul_le_norm] at hnanti
    push Not at hnanti
    exact hnanti
  have hraw : ∀ n : ℕ, ∃ x : Z,
      ‖(T.comp S) x‖ < (1 / 2 / 2 ^ n) * ‖x‖ := by
    intro n
    exact hsmall (1 / 2 / 2 ^ n) (by positivity)
  choose x hx using hraw
  have hx0 (n : ℕ) : x n ≠ 0 := by
    intro h
    simpa [h] using hx n
  let z : ℕ → Z := fun n ↦ ‖x n‖⁻¹ • x n
  have hznorm (n : ℕ) : ‖z n‖ = 1 := by
    simp [z, norm_smul, hx0 n]
  have hzbound (n : ℕ) :
      ‖(T.comp S) (z n)‖ < 1 / 2 / 2 ^ n := by
    calc
      ‖(T.comp S) (z n)‖ =
          ‖x n‖⁻¹ * ‖(T.comp S) (x n)‖ := by
            simp [z, norm_smul]
      _ < ‖x n‖⁻¹ * ((1 / 2 / 2 ^ n) * ‖x n‖) :=
        mul_lt_mul_of_pos_left (hx n)
          (inv_pos.mpr (norm_pos_iff.mpr (hx0 n)))
      _ = 1 / 2 / 2 ^ n := by
        rw [mul_comm (1 / 2 / 2 ^ n) ‖x n‖, ← mul_assoc,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hx0 n)), one_mul]
  have hzsum : Summable (fun n ↦ ‖(T.comp S) (z n)‖) :=
    Summable.of_nonneg_of_le
      (fun n ↦ norm_nonneg ((T.comp S) (z n)))
      (fun n ↦ (hzbound n).le) (summable_geometric_two' 1)
  refine ⟨Z, hZclosed, htop, hZ, z, hznorm, ?_⟩
  simpa [S] using hzsum

/-- Failure of upper semi-Fredholmness yields either an infinite-dimensional compact restriction
or a summable normalized approximate-kernel sequence on a closed kernel complement.
Blueprint label: `lem:not-upper-semi-dichotomy`. -/
theorem compactRestriction_or_summableApproximateKernelSequence
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T : X →L[ℝ] Y) (hT : ¬ IsUpperSemiFredholm T) :
    HasInfiniteDimensionalCompactRestriction T ∨
      ∃ Z : Submodule ℝ X, IsClosed (Z : Set X) ∧
        Submodule.IsTopCompl T.toLinearMap.ker Z ∧
        ¬ FiniteDimensional ℝ Z ∧
        ∃ z : ℕ → Z, (∀ n, ‖z n‖ = 1) ∧
          Summable (fun n ↦ ‖(T.comp Z.subtypeL) (z n)‖) := by
  by_cases hker : FiniteDimensional ℝ T.toLinearMap.ker
  · right
    exact
      exists_summableApproximateKernelSequence_of_finiteDimensional_ker
        T hker (fun hrange ↦ hT ⟨hker, hrange⟩)
  · left
    exact
      hasInfiniteDimensionalCompactRestriction_of_infiniteDimensional_kernel
        T hker

/-- A linear lift of `Q` whose error from the Kalton--Peck centralizer is square-summable and
uniformly bounded.
Blueprint label: `def:bounded-centralizer-lift`. -/
def HasBoundedCentralizerLift
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] CanonicalL2) : Prop :=
  ∃ (a : Z →ₗ[ℝ] (ℕ → ℝ)) (C : ℝ), 0 ≤ C ∧ ∀ z,
      IsSquareSummable (a z - centralizer (fun n ↦ Q z n)) ∧
        l2Norm (a z - centralizer (fun n ↦ Q z n)) ≤ C * ‖z‖

/-- A bounded linear approximation to the Kalton--Peck centralizer on a Hilbert subspace.
Blueprint label: `def:bounded-centralizer-approximation`. -/
def HasBoundedCentralizerApproximation
    (M : Submodule ℝ CanonicalL2) : Prop :=
  ∃ (b : M →ₗ[ℝ] (ℕ → ℝ)) (C : ℝ), 0 ≤ C ∧ ∀ y,
      IsSquareSummable
        (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) ∧
      l2Norm (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) ≤
        C * ‖y‖

universe u

/-- Every bounded operator into the canonical Kalton--Peck model supplies a bounded centralizer
lift of its second-coordinate map.
Blueprint label: `lem:canonical-centralizer-lift`. -/
theorem hasBoundedCentralizerLift_canonicalL2Quotient_comp
    {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : Z →L[ℝ] CanonicalRealKaltonPeck) :
    HasBoundedCentralizerLift (canonicalL2Quotient.comp S) := by
  let Q : Z →L[ℝ] CanonicalL2 := canonicalL2Quotient.comp S
  let a : Z →ₗ[ℝ] (ℕ → ℝ) :=
    { toFun := fun z ↦
        (canonicalRealKaltonPeckPresentation.coordinates (S z)).1
      map_add' := by
        intro z w
        simp
      map_smul' := by
        intro r z
        simp }
  obtain ⟨c, C, hc, hC, hnorm⟩ :=
    canonicalRealKaltonPeckPresentation.norm_equivalent
  refine ⟨a, ‖S‖ / c, div_nonneg (norm_nonneg S) hc.le, ?_⟩
  intro z
  have hQ :
      (fun n ↦ Q z n) =
        (canonicalRealKaltonPeckPresentation.coordinates (S z)).2 := by
    funext n
    exact canonicalL2Quotient_apply (S z) n
  have hdefect :
      a z - centralizer (fun n ↦ Q z n) =
        (canonicalRealKaltonPeckPresentation.coordinates (S z)).1 -
          centralizer
            (canonicalRealKaltonPeckPresentation.coordinates (S z)).2 := by
    rw [hQ]
    rfl
  constructor
  · rw [hdefect]
    exact (canonicalRealKaltonPeckPresentation.coordinates_mem (S z)).2
  · rw [hdefect]
    have hq :
        kaltonPeckQuasiNorm
            (canonicalRealKaltonPeckPresentation.coordinates (S z)) ≤
          ‖S z‖ / c :=
      (le_div_iff₀ hc).2 (by
        simpa [mul_comm] using (hnorm (S z)).1)
    calc
      l2Norm
          ((canonicalRealKaltonPeckPresentation.coordinates (S z)).1 -
            centralizer
              (canonicalRealKaltonPeckPresentation.coordinates (S z)).2) ≤
          kaltonPeckQuasiNorm
            (canonicalRealKaltonPeckPresentation.coordinates (S z)) := by
        exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
      _ ≤ ‖S z‖ / c := hq
      _ ≤ (‖S‖ * ‖z‖) / c := by
        exact (div_le_div_iff_of_pos_right hc).2 (S.le_opNorm z)
      _ = (‖S‖ / c) * ‖z‖ := by ring

/-- A bounded-below map with a bounded centralizer lift produces a bounded approximation on its
closed infinite-dimensional Hilbert range.
Blueprint label: `lem:centralizer-lift-to-subspace`. -/
theorem no_boundedCentralizerLift_of_subspace_obstruction
    (hSubspace :
      ∀ M : Submodule ℝ CanonicalL2,
        IsClosed (M : Set CanonicalL2) →
          ¬ FiniteDimensional ℝ M →
            ¬ HasBoundedCentralizerApproximation M)
    {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (hZ : ¬ FiniteDimensional ℝ Z)
    (Q : Z →L[ℝ] CanonicalL2) (hQ : ∃ K, AntilipschitzWith K Q) :
    ¬ HasBoundedCentralizerLift Q := by
  rintro ⟨a, C, hC, ha⟩
  obtain ⟨K, hK⟩ := hQ
  have hQinj : Function.Injective Q := hK.injective
  have hQclosed : IsClosed (Q.range : Set CanonicalL2) := by
    exact hK.isClosed_range Q.uniformContinuous
  let e : Z ≃ₗ[ℝ] Q.range :=
    LinearEquiv.ofInjective Q.toLinearMap hQinj
  have hQrange : ¬ FiniteDimensional ℝ Q.range := by
    intro hfinite
    let : FiniteDimensional ℝ Q.range := hfinite
    let : FiniteDimensional ℝ Z :=
      @LinearEquiv.finiteDimensional ℝ Q.range _ _ _ Z _ _ e.symm
        inferInstance
    exact hZ inferInstance
  apply hSubspace Q.range hQclosed hQrange
  let b : Q.range →ₗ[ℝ] (ℕ → ℝ) := a.comp e.symm.toLinearMap
  refine ⟨b, C * (K : ℝ), mul_nonneg hC (NNReal.coe_nonneg K), ?_⟩
  intro y
  let z : Z := e.symm y
  have hQzL2 : Q z = (y : CanonicalL2) := by
    have he : e z = y := by
      exact e.apply_symm_apply y
    exact congrArg Subtype.val he
  have hQz :
      (fun n ↦ Q z n) = (fun n ↦ (y : CanonicalL2) n) := by
    funext n
    exact congrArg (fun v : CanonicalL2 ↦ v n) hQzL2
  have hb : b y = a z := by
    rfl
  have hz : ‖z‖ ≤ (K : ℝ) * ‖y‖ := by
    have hz' := hK.le_mul_dist z 0
    simp only [dist_zero_right, map_zero] at hz'
    rw [hQzL2] at hz'
    exact hz'
  constructor
  · rw [hb, ← hQz]
    exact (ha z).1
  · rw [hb, ← hQz]
    calc
      l2Norm (a z - centralizer (fun n ↦ Q z n)) ≤ C * ‖z‖ :=
        (ha z).2
      _ ≤ C * ((K : ℝ) * ‖y‖) :=
        mul_le_mul_of_nonneg_left hz hC
      _ = (C * (K : ℝ)) * ‖y‖ := by ring

/-- Strict singularity of the canonical quotient reduces to the analytic Kalton--Peck
centralizer obstruction.
Blueprint label: `lem:canonical-quotient-strictly-singular-reduction`. -/
theorem canonicalL2Quotient_strictlySingular_of_centralizer_obstruction
    (hKP :
      ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
        [CompleteSpace Z],
        ¬ FiniteDimensional ℝ Z →
          ∀ Q : Z →L[ℝ] CanonicalL2,
            (∃ K, AntilipschitzWith K Q) →
              ¬ HasBoundedCentralizerLift Q) :
    IsStrictlySingular.{0, 0, 0, u} canonicalL2Quotient := by
  intro Z _ _ _ hZ S _ hQS
  let Q : Z →L[ℝ] CanonicalL2 := canonicalL2Quotient.comp S
  apply hKP Z hZ Q hQS
  exact hasBoundedCentralizerLift_canonicalL2Quotient_comp S

/-- The canonical quotient is strictly singular once the centralizer obstruction is known on
every closed infinite-dimensional Hilbert subspace.
Blueprint label: `lem:canonical-quotient-strictly-singular-reduction`. -/
theorem canonicalL2Quotient_strictlySingular_of_subspace_obstruction
    (hSubspace :
      ∀ M : Submodule ℝ CanonicalL2,
        IsClosed (M : Set CanonicalL2) →
          ¬ FiniteDimensional ℝ M →
            ¬ HasBoundedCentralizerApproximation M) :
    IsStrictlySingular.{0, 0, 0, u} canonicalL2Quotient := by
  apply canonicalL2Quotient_strictlySingular_of_centralizer_obstruction
  intro Z _ _ _ hZ Q hQ
  exact no_boundedCentralizerLift_of_subspace_obstruction
    hSubspace hZ Q hQ

private lemma squareSummable_coe (x : CanonicalL2) :
    IsSquareSummable (fun n ↦ x n) := by
  rw [IsSquareSummable]
  have hx := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp x.2
  simpa [Real.norm_eq_abs, sq_abs] using hx

private lemma l2Norm_coe_eq_norm (x : CanonicalL2) :
    l2Norm (fun n ↦ x n) = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (p := (2 : ENNReal)) (by norm_num)]
  change Real.sqrt (∑' n, x n ^ 2) =
    (∑' n, |x n| ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply tsum_congr
  intro n
  calc
    x n ^ (2 : ℕ) = |x n| ^ (2 : ℕ) := (sq_abs (x n)).symm
    _ = |x n| ^ (2 : ℝ) := (Real.rpow_natCast |x n| 2).symm

private def centralizerLiftVector
    (M : Submodule ℝ CanonicalL2)
    (b : M →ₗ[ℝ] (ℕ → ℝ))
    (hb : ∀ y, IsSquareSummable
      (b y - centralizer (fun n ↦ (y : CanonicalL2) n))) (y : M) :
    CanonicalRealKaltonPeck := by
  refine ⟨(b y, fun n ↦ (y : CanonicalL2) n), ?_⟩
  exact ⟨squareSummable_coe y, hb y⟩

private def centralizerLiftLinear
    (M : Submodule ℝ CanonicalL2)
    (b : M →ₗ[ℝ] (ℕ → ℝ))
    (hb : ∀ y, IsSquareSummable
      (b y - centralizer (fun n ↦ (y : CanonicalL2) n))) :
    M →ₗ[ℝ] CanonicalRealKaltonPeck where
  toFun := centralizerLiftVector M b hb
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · exact b.map_add x y
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · exact b.map_smul a x
    · rfl

private theorem centralizerLiftLinear_norm_le
    (M : Submodule ℝ CanonicalL2)
    (b : M →ₗ[ℝ] (ℕ → ℝ)) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ y,
      IsSquareSummable
        (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) ∧
      l2Norm (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) ≤
        C * ‖y‖) :
    ∃ D > 0, ∀ y,
      ‖centralizerLiftLinear M b (fun y ↦ (hb y).1) y‖ ≤
        D * (C + 1) * ‖y‖ := by
  obtain ⟨c, D, hc, hD, hmodel⟩ :=
    canonicalRealKaltonPeckPresentation.norm_equivalent
  refine ⟨D, hD, ?_⟩
  intro y
  apply (hmodel (centralizerLiftLinear M b (fun y ↦ (hb y).1) y)).2.trans
  change D * (l2Norm
      (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) +
        l2Norm (fun n ↦ (y : CanonicalL2) n)) ≤
    D * (C + 1) * ‖y‖
  rw [l2Norm_coe_eq_norm]
  calc
    D * (l2Norm
        (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) + ‖y‖) ≤
        D * (C * ‖y‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (hb y).2 (le_refl ‖y‖)) hD.le
    _ = D * (C + 1) * ‖y‖ := by ring

private def centralizerLiftCLM
    (M : Submodule ℝ CanonicalL2)
    (b : M →ₗ[ℝ] (ℕ → ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ y,
      IsSquareSummable
        (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) ∧
      l2Norm (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) ≤
        C * ‖y‖) :
    M →L[ℝ] CanonicalRealKaltonPeck := by
  let D : ℝ :=
    Classical.choose (centralizerLiftLinear_norm_le M b C hC hb)
  have hD :=
    Classical.choose_spec (centralizerLiftLinear_norm_le M b C hC hb)
  exact (centralizerLiftLinear M b (fun y ↦ (hb y).1)).mkContinuous
    (D * (C + 1)) hD.2

private theorem canonicalL2Quotient_centralizerLiftCLM
    (M : Submodule ℝ CanonicalL2)
    (b : M →ₗ[ℝ] (ℕ → ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ y,
      IsSquareSummable
        (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) ∧
      l2Norm (b y - centralizer (fun n ↦ (y : CanonicalL2) n)) ≤
        C * ‖y‖)
    (y : M) :
    canonicalL2Quotient (centralizerLiftCLM M b C hC hb y) =
      (y : CanonicalL2) := by
  apply Subtype.ext
  funext n
  rw [canonicalL2Quotient_apply]
  rfl

private def signedL2 (N : ℕ) (σ : ℕ → ℝ) : CanonicalL2 :=
  ∑ i ∈ Finset.range N,
    (σ i / Real.sqrt N) • (lp.single 2 i 1 : CanonicalL2)

private lemma signedL2_apply
    (N : ℕ) (σ : ℕ → ℝ) (k : ℕ) :
    signedL2 N σ k =
      if k < N then σ k / Real.sqrt N else 0 := by
  dsimp only [signedL2]
  rw [lp.coeFn_sum, Finset.sum_apply]
  by_cases hk : k < N
  · rw [Finset.sum_eq_single k]
    · simp [lp.single_apply, hk]
    · intro i hi hik
      simp [lp.single_apply, Ne.symm hik]
    · exact fun h ↦ (h (Finset.mem_range.mpr hk)).elim
  · rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro i hi
      have hik : i ≠ k := by
        intro h
        subst i
        exact hk (Finset.mem_range.mp hi)
      simp [lp.single_apply, Ne.symm hik]

private lemma signedL2_norm
    {N : ℕ} (hN : 0 < N) (σ : ℕ → ℝ)
    (hσ : ∀ k < N, σ k = 1 ∨ σ k = -1) :
    ‖signedL2 N σ‖ = 1 := by
  apply norm_signed_average_single N hN σ
  intro k hk
  rcases hσ k hk with h | h <;> simp [h]

private lemma signedL2_centralizer
    {N : ℕ} (hN : 0 < N) (σ : ℕ → ℝ)
    (hσ : ∀ k < N, σ k = 1 ∨ σ k = -1) :
    centralizer (fun k ↦ signedL2 N σ k) =
      (-Real.log N) • (fun k ↦ signedL2 N σ k) := by
  have hl2 : l2Norm (fun k ↦ signedL2 N σ k) = 1 := by
    rw [l2Norm_coe_eq_norm, signedL2_norm hN σ hσ]
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNreal
  have hlogsqrt : Real.log (Real.sqrt (N : ℝ)) = Real.log N / 2 :=
    Real.log_sqrt hNreal.le
  funext k
  by_cases hk : k < N
  · have habsσ : |σ k| = 1 := by
      rcases hσ k hk with h | h <;> simp [h]
    have hratio :
        |signedL2 N σ k| / l2Norm (fun j ↦ signedL2 N σ j) =
          1 / Real.sqrt (N : ℝ) := by
      rw [signedL2_apply, ite_eq_left hk, hl2, div_one, abs_div, habsσ,
        abs_of_pos hsqrt]
    have hlog :
        Real.log (1 / Real.sqrt (N : ℝ)) = -(Real.log N / 2) := by
      rw [Real.log_div one_ne_zero hsqrt.ne', Real.log_one, hlogsqrt]
      ring
    rw [centralizer, hratio, hlog]
    change 2 * signedL2 N σ k * (-(Real.log N / 2)) =
      -Real.log N * signedL2 N σ k
    ring
  · simp [centralizer, signedL2_apply, hk]

private def signedSecondVector
    (N : ℕ) (σ : ℕ → ℝ) : CanonicalRealKaltonPeck :=
  ∑ k ∈ Finset.range N,
    (σ k / Real.sqrt N) • canonicalSecondBasisVector k

private lemma signedSecondVector_coordinates
    {N : ℕ} (_hN : 0 < N) (σ : ℕ → ℝ) :
    canonicalRealKaltonPeckPresentation.coordinates
        (signedSecondVector N σ) =
      (0, fun k ↦ signedL2 N σ k) := by
  rw [signedSecondVector, map_sum]
  simp_rw [map_smul, (canonicalBasisCoordinates _).2]
  apply Prod.ext
  · funext k
    simp [Prod.fst_sum, Prod.smul_mk]
  · funext k
    simp only [Prod.snd_sum, Prod.smul_mk]
    by_cases hk : k < N
    · change
        (∑ i ∈ Finset.range N,
          (σ i / Real.sqrt (N : ℝ)) • standardBasisSequence i) k =
            signedL2 N σ k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp [standardBasisSequence, signedL2_apply, hk]
      · intro i hi hik
        simp [standardBasisSequence, Ne.symm hik]
      · exact fun h ↦ (h (Finset.mem_range.mpr hk)).elim
    · change
        (∑ i ∈ Finset.range N,
          (σ i / Real.sqrt (N : ℝ)) • standardBasisSequence i) k =
            signedL2 N σ k
      rw [Finset.sum_apply, signedL2_apply, ite_eq_right hk]
      apply Finset.sum_eq_zero
      intro i hi
      have hik : i ≠ k := by
        intro h
        subst i
        exact hk (Finset.mem_range.mp hi)
      simp [standardBasisSequence, Ne.symm hik]

private lemma signedSecondVector_quasiNorm
    {N : ℕ} (hN : 0 < N) (σ : ℕ → ℝ)
    (hσ : ∀ k < N, σ k = 1 ∨ σ k = -1) :
    kaltonPeckQuasiNorm
        (canonicalRealKaltonPeckPresentation.coordinates
          (signedSecondVector N σ)) =
      Real.log N + 1 := by
  rw [signedSecondVector_coordinates hN]
  change
    l2Norm (0 - centralizer (fun k ↦ signedL2 N σ k)) +
      l2Norm (fun k ↦ signedL2 N σ k) = Real.log N + 1
  rw [signedL2_centralizer hN σ hσ]
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hseq :
      0 - (-Real.log N) • (fun k ↦ signedL2 N σ k) =
        Real.log N • (fun k ↦ signedL2 N σ k) := by
    funext k
    simp
  rw [hseq]
  have hscaled :
      l2Norm (Real.log N • (fun k ↦ signedL2 N σ k)) =
        Real.log N := by
    change l2Norm (fun k ↦ (Real.log N • signedL2 N σ) k) =
      Real.log N
    rw [l2Norm_coe_eq_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hlog, signedL2_norm hN σ hσ, mul_one]
  rw [hscaled]
  change Real.log N + l2Norm (fun k ↦ signedL2 N σ k) =
    Real.log N + 1
  rw [l2Norm_coe_eq_norm, signedL2_norm hN σ hσ]

private theorem exists_sign_sum_sq_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ℕ) (v : ℕ → H) :
    ∃ ε : ℕ → ℝ,
      (∀ i ∈ s, ε i = 1 ∨ ε i = -1) ∧
        ‖∑ i ∈ s, ε i • v i‖ ^ 2 ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ ↦ 1, ?_, ?_⟩
      · simp
      · simp
  | @insert a s ha ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      let x : H := ∑ i ∈ s, ε i • v i
      by_cases hinner : ⟪x, v a⟫_ℝ ≤ 0
      · let ε' : ℕ → ℝ := fun i ↦ if i = a then 1 else ε i
        refine ⟨ε', ?_, ?_⟩
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp [ε']
          · have hia : i ≠ a := fun h ↦ ha (h ▸ hi)
            simpa [ε', hia] using hε i hi
        · have hrest : ∑ i ∈ s, ε' i • v i = x := by
            apply Finset.sum_congr rfl
            intro i hi
            have hia : i ≠ a := fun h ↦ ha (h ▸ hi)
            simp [ε', hia]
          rw [Finset.sum_insert ha, Finset.sum_insert ha, hrest]
          simp only [ε', ite_eq_left, one_smul]
          rw [add_comm (v a) x, norm_add_sq_real]
          calc
            ‖x‖ ^ 2 + 2 * ⟪x, v a⟫_ℝ + ‖v a‖ ^ 2 ≤
                ‖x‖ ^ 2 + ‖v a‖ ^ 2 := by linarith
            _ ≤ (∑ i ∈ s, ‖v i‖ ^ 2) + ‖v a‖ ^ 2 := by
              simpa [x] using add_le_add_right hbound (‖v a‖ ^ 2)
            _ = ‖v a‖ ^ 2 + ∑ i ∈ s, ‖v i‖ ^ 2 := by ring
      · have hinner' : 0 ≤ ⟪x, v a⟫_ℝ := le_of_not_ge hinner
        let ε' : ℕ → ℝ := fun i ↦ if i = a then -1 else ε i
        refine ⟨ε', ?_, ?_⟩
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp [ε']
          · have hia : i ≠ a := fun h ↦ ha (h ▸ hi)
            simpa [ε', hia] using hε i hi
        · have hrest : ∑ i ∈ s, ε' i • v i = x := by
            apply Finset.sum_congr rfl
            intro i hi
            have hia : i ≠ a := fun h ↦ ha (h ▸ hi)
            simp [ε', hia]
          rw [Finset.sum_insert ha, Finset.sum_insert ha, hrest]
          simp only [ε', ite_eq_left, neg_smul, one_smul]
          rw [neg_add_eq_sub, norm_sub_sq_real]
          calc
            ‖x‖ ^ 2 - 2 * ⟪x, v a⟫_ℝ + ‖v a‖ ^ 2 ≤
                ‖x‖ ^ 2 + ‖v a‖ ^ 2 := by linarith
            _ ≤ (∑ i ∈ s, ‖v i‖ ^ 2) + ‖v a‖ ^ 2 := by
              simpa [x] using add_le_add_right hbound (‖v a‖ ^ 2)
            _ = ‖v a‖ ^ 2 + ∑ i ∈ s, ‖v i‖ ^ 2 := by ring

private lemma canonicalSecondBasisVector_quasiNorm (n : ℕ) :
    kaltonPeckQuasiNorm
        (canonicalRealKaltonPeckPresentation.coordinates
          (canonicalSecondBasisVector n)) = 1 := by
  rw [(canonicalBasisCoordinates n).2]
  have hsquare : IsSquareSummable (standardBasisSequence n) := by
    apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton n).subset ?_
    intro k hk
    change standardBasisSequence n k ^ 2 ≠ 0 at hk
    change k = n
    by_contra hkn
    exact hk (by simp [standardBasisSequence, hkn])
  have hl2 : l2Norm (standardBasisSequence n) = 1 := by
    rw [l2Norm, tsum_eq_single n]
    · simp [standardBasisSequence]
    · intro k hk
      simp [standardBasisSequence, hk]
  have hcentral : centralizer (standardBasisSequence n) = 0 := by
    funext k
    by_cases hk : k = n
    · simp [centralizer, standardBasisSequence, hk, hl2]
    · simp [centralizer, standardBasisSequence, hk]
  rw [kaltonPeckQuasiNorm, hcentral, hl2]
  simp [l2Norm]

private lemma exists_uniform_canonicalSecondBasisVector_bound :
    ∃ D > 0, ∀ n, ‖canonicalSecondBasisVector n‖ ≤ D := by
  obtain ⟨c, D, hc, hD, hmodel⟩ :=
    canonicalRealKaltonPeckPresentation.norm_equivalent
  refine ⟨D, hD, fun n ↦ ?_⟩
  simpa [canonicalSecondBasisVector_quasiNorm n] using
    (hmodel (canonicalSecondBasisVector n)).2

private theorem exists_sign_average_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (hN : 0 < N) (v : ℕ → H) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i < N, ‖v i‖ ≤ B) :
    ∃ σ : ℕ → ℝ,
      (∀ i < N, σ i = 1 ∨ σ i = -1) ∧
        ‖∑ i ∈ Finset.range N,
          (σ i / Real.sqrt N) • v i‖ ≤ B := by
  obtain ⟨σ, hσ, hraw⟩ :=
    exists_sign_sum_sq_le (Finset.range N) v
  have hsum :
      ∑ i ∈ Finset.range N, ‖v i‖ ^ 2 ≤ (N : ℝ) * B ^ 2 := by
    calc
      ∑ i ∈ Finset.range N, ‖v i‖ ^ 2 ≤
          ∑ i ∈ Finset.range N, B ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            exact pow_le_pow_left₀ (norm_nonneg _)
              (hv i (Finset.mem_range.mp hi)) 2
      _ = (N : ℝ) * B ^ 2 := by simp
  let raw : H := ∑ i ∈ Finset.range N, σ i • v i
  have hraw_sq : ‖raw‖ ^ 2 ≤ (N : ℝ) * B ^ 2 :=
    hraw.trans hsum
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNreal
  have hsqrt_sq : Real.sqrt (N : ℝ) ^ 2 = N :=
    Real.sq_sqrt hNreal.le
  have hraw_norm : ‖raw‖ ≤ Real.sqrt N * B := by
    have hright : 0 ≤ Real.sqrt N * B := mul_nonneg hsqrt.le hB
    nlinarith [norm_nonneg raw]
  refine ⟨σ, fun i hi ↦ hσ i (Finset.mem_range.mpr hi), ?_⟩
  have havg :
      ∑ i ∈ Finset.range N, (σ i / Real.sqrt N) • v i =
        (Real.sqrt N)⁻¹ • raw := by
    dsimp only [raw]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul]
    congr 1
    field_simp
  rw [havg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt]
  calc
    (Real.sqrt N)⁻¹ * ‖raw‖ ≤
        (Real.sqrt N)⁻¹ * (Real.sqrt N * B) :=
      mul_le_mul_of_nonneg_left hraw_norm (inv_nonneg.mpr hsqrt.le)
    _ = B := by field_simp

/-- Signed block averages bound the centralizer's logarithmic growth by a fixed constant. -/
private theorem signed_log_bound
    (M : Submodule ℝ CanonicalL2) (L : M →L[ℝ] CanonicalRealKaltonPeck)
    (y : ℕ → M) (W : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (error : ℕ → ℝ) (hsum : Summable error) (herror : ∀ n, 0 ≤ error n)
    (hy_signed : ∀ (N : ℕ), 0 < N → ∀ σ : ℕ → ℝ, (∀ i < N, |σ i| = 1) →
      ‖∑ i ∈ Finset.range N, (σ i / Real.sqrt N) • (y i : CanonicalL2)‖ ≤ 1 + ∑' n, error n)
    (k : ℕ → canonicalL2Quotient.ker) (h : ℕ → CanonicalL2)
    (hih : ∀ n, canonicalL2Inclusion (h n) = (k n : CanonicalRealKaltonPeck))
    (K B c : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) (hh_bound : ∀ n, ‖h n‖ ≤ B)
    (hclose : ∀ n, ‖L (y n) - W (canonicalSecondBasisVector n) -
      (k n : CanonicalRealKaltonPeck)‖ ≤ K * error n)
    (hmodel : ∀ s, c * kaltonPeckQuasiNorm
      (canonicalRealKaltonPeckPresentation.coordinates s) ≤ ‖s‖)
    (hWleft : canonicalKaltonSwansonForm.adjoint W * W = 1) (N : ℕ) (hN : 0 < N) :
    c * (Real.log N + 1) ≤ ‖canonicalKaltonSwansonForm.adjoint W‖ *
      (‖L‖ * (1 + ∑' n, error n) + ‖canonicalL2Inclusion‖ * B + K * ∑' n, error n) := by
  let w : ℕ → CanonicalRealKaltonPeck := fun n ↦ L (y n)
  let z : ℕ → CanonicalRealKaltonPeck := fun n ↦ W (canonicalSecondBasisVector n)
  let r : ℕ → CanonicalRealKaltonPeck := fun n ↦ w n - z n
  let errorSum : ℝ := ∑' n, error n
  let U : ℝ := ‖L‖ * (1 + errorSum) + ‖canonicalL2Inclusion‖ * B + K * errorSum
  obtain ⟨σ, hσ, hhavg⟩ :=
    exists_sign_average_norm_le hN h hB (fun i _ ↦ hh_bound i)
  have habsσ : ∀ i < N, |σ i| = 1 := by
    intro i hi
    rcases hσ i hi with h | h <;> simp [h]
  let s : CanonicalRealKaltonPeck := signedSecondVector N σ
  let wsum : CanonicalRealKaltonPeck :=
    ∑ i ∈ Finset.range N, (σ i / Real.sqrt N) • w i
  let zsum : CanonicalRealKaltonPeck :=
    ∑ i ∈ Finset.range N, (σ i / Real.sqrt N) • z i
  let rsum : CanonicalRealKaltonPeck :=
    ∑ i ∈ Finset.range N, (σ i / Real.sqrt N) • r i
  let ksum : CanonicalRealKaltonPeck :=
    ∑ i ∈ Finset.range N,
      (σ i / Real.sqrt N) • (k i : CanonicalRealKaltonPeck)
  have hwsum :
      ‖wsum‖ ≤ ‖L‖ * (1 + errorSum) := by
    have hmap :
        wsum = L
          (∑ i ∈ Finset.range N,
            (σ i / Real.sqrt N) • y i) := by
      dsimp only [wsum, w]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
    rw [hmap]
    have hsource := hy_signed N hN σ habsσ
    have hsource' :
        ‖∑ i ∈ Finset.range N,
          (σ i / Real.sqrt N) • y i‖ ≤ 1 + errorSum := by
      have hcoe :
          ((↑(∑ i ∈ Finset.range N,
              (σ i / Real.sqrt N) • y i) : CanonicalL2)) =
            ∑ i ∈ Finset.range N,
              (σ i / Real.sqrt N) • (y i : CanonicalL2) := by
        simp
      change
        ‖((↑(∑ i ∈ Finset.range N,
            (σ i / Real.sqrt N) • y i) : CanonicalL2))‖ ≤
          1 + errorSum
      rw [hcoe]
      exact hsource
    exact (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hsource' (norm_nonneg L))
  have hzsum : zsum = W s := by
    dsimp only [zsum, z, s, signedSecondVector]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul]
  have hrsum : rsum = wsum - zsum := by
    dsimp only [rsum, r, wsum, zsum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_sub]
  have hksum :
      ksum = canonicalL2Inclusion
        (∑ i ∈ Finset.range N,
          (σ i / Real.sqrt N) • h i) := by
    dsimp only [ksum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, hih]
  have hksum_norm :
      ‖ksum‖ ≤ ‖canonicalL2Inclusion‖ * B := by
    rw [hksum]
    exact (canonicalL2Inclusion.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hhavg
        (norm_nonneg canonicalL2Inclusion))
  have hrsum_ksum :
      ‖rsum - ksum‖ ≤ K * errorSum := by
    have heq :
        rsum - ksum =
          ∑ i ∈ Finset.range N,
            (σ i / Real.sqrt N) •
              (r i - (k i : CanonicalRealKaltonPeck)) := by
      dsimp only [rsum, ksum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_sub]
      dsimp only [r]
      module
    rw [heq]
    apply (norm_sum_le _ _).trans
    calc
      ∑ i ∈ Finset.range N,
          ‖(σ i / Real.sqrt N) •
            (r i - (k i : CanonicalRealKaltonPeck))‖ ≤
          K * ∑ i ∈ Finset.range N, error i := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
        have hiN := Finset.mem_range.mp hi
        have hsqrt : 1 ≤ Real.sqrt (N : ℝ) :=
          Real.one_le_sqrt.mpr (by exact_mod_cast hN)
        have hsqrtPos : 0 < Real.sqrt (N : ℝ) :=
          lt_of_lt_of_le (by norm_num) hsqrt
        have hcoeff : |σ i / Real.sqrt N| ≤ 1 := by
          rw [abs_div, habsσ i hiN, abs_of_pos hsqrtPos]
          exact (div_le_one hsqrtPos).2 hsqrt
        have hclose :
            ‖r i - (k i : CanonicalRealKaltonPeck)‖ ≤
              K * error i := by
          exact hclose i
        exact
          (mul_le_of_le_one_left (norm_nonneg _) hcoeff).trans hclose
      _ ≤ K * errorSum :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum (Finset.range N)
            (fun i _ ↦ herror i)) hK
  have hrsum_norm :
      ‖rsum‖ ≤ ‖canonicalL2Inclusion‖ * B + K * errorSum := by
    calc
      ‖rsum‖ = ‖(rsum - ksum) + ksum‖ := by rw [sub_add_cancel]
      _ ≤ ‖rsum - ksum‖ + ‖ksum‖ := norm_add_le _ _
      _ ≤ K * errorSum + ‖canonicalL2Inclusion‖ * B :=
        add_le_add hrsum_ksum hksum_norm
      _ = ‖canonicalL2Inclusion‖ * B + K * errorSum := by ring
  have hzsum_norm : ‖zsum‖ ≤ U := by
    rw [hrsum] at hrsum_norm
    have hz : zsum = wsum - (wsum - zsum) := by abel
    rw [hz]
    calc
      ‖wsum - (wsum - zsum)‖ ≤ ‖wsum‖ + ‖wsum - zsum‖ :=
        norm_sub_le _ _
      _ ≤ ‖L‖ * (1 + errorSum) +
          (‖canonicalL2Inclusion‖ * B + K * errorSum) :=
        add_le_add hwsum hrsum_norm
      _ = U := by simp [U]; ring
  have hs_left :
      s = canonicalKaltonSwansonForm.adjoint W (W s) := by
    have happly := congrArg
      (fun T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck ↦
        T s)
      hWleft
    simpa only [mul_apply_eq_comp, one_apply_eq_self]
      using happly.symm
  calc
    c * (Real.log N + 1) =
        c * kaltonPeckQuasiNorm
          (canonicalRealKaltonPeckPresentation.coordinates s) := by
      rw [signedSecondVector_quasiNorm hN σ hσ]
    _ ≤ ‖s‖ := hmodel s
    _ = ‖canonicalKaltonSwansonForm.adjoint W (W s)‖ :=
      congrArg norm hs_left
    _ ≤ ‖canonicalKaltonSwansonForm.adjoint W‖ * ‖W s‖ :=
      (canonicalKaltonSwansonForm.adjoint W).le_opNorm _
    _ = ‖canonicalKaltonSwansonForm.adjoint W‖ * ‖zsum‖ := by
      rw [hzsum]
    _ ≤ ‖canonicalKaltonSwansonForm.adjoint W‖ * U :=
      mul_le_mul_of_nonneg_left hzsum_norm (norm_nonneg _)

/-- No infinite-dimensional Hilbert subspace admits a uniformly bounded linear approximation
to the Kalton--Peck centralizer.

The proof is the direct `p = 2` logarithmic obstruction: a gliding-hump sequence gives bounded
signed block averages, while the corresponding second-coordinate vectors have quasi-norm
`log N + 1`.
Blueprint label: `thm:canonical-centralizer-obstruction`. -/
theorem no_boundedCentralizerApproximation
    (M : Submodule ℝ CanonicalL2)
    (_hMclosed : IsClosed (M : Set CanonicalL2))
    (hM : ¬ FiniteDimensional ℝ M) :
    ¬ HasBoundedCentralizerApproximation M := by
  rintro ⟨b, C, hC, hb⟩
  let L : M →L[ℝ] CanonicalRealKaltonPeck :=
    centralizerLiftCLM M b C hC hb
  obtain ⟨y, v, hv, hy_norm, hsum, hy_signed⟩ :=
    exists_successiveBlock_with_uniform_signed_average_bound M hM
  let W : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck :=
    canonicalBlockOperator v hv
  let w : ℕ → CanonicalRealKaltonPeck := fun n ↦ L (y n)
  let z : ℕ → CanonicalRealKaltonPeck :=
    fun n ↦ W (canonicalSecondBasisVector n)
  let r : ℕ → CanonicalRealKaltonPeck := fun n ↦ w n - z n
  let error : ℕ → ℝ := fun n ↦
    ‖(y n : CanonicalL2) -
      canonicalL2BlockEmbedding v hv (lp.single 2 n 1)‖
  let errorSum : ℝ := ∑' n, error n
  have herrorSum : 0 ≤ errorSum := by
    dsimp only [errorSum, error]
    exact tsum_nonneg fun _ ↦ norm_nonneg _
  have herror_le (n : ℕ) : error n ≤ errorSum := by
    dsimp only [errorSum, error]
    exact hsum.le_tsum n (fun _ _ ↦ norm_nonneg _)
  have hqz (n : ℕ) :
      canonicalL2Quotient (z n) =
        canonicalL2BlockEmbedding v hv (lp.single 2 n 1) := by
    apply Subtype.ext
    funext k
    rw [canonicalL2Quotient_apply]
    change
      (canonicalRealKaltonPeckPresentation.coordinates
        (W (canonicalSecondBasisVector n))).2 k =
          canonicalL2BlockEmbedding v hv (lp.single 2 n 1) k
    rw [(canonicalNormalizedBlock v hv).2.1 n]
    exact (canonicalL2BlockEmbedding_single_apply v hv n k).symm
  have hqr (n : ℕ) :
      canonicalL2Quotient (r n) =
        (y n : CanonicalL2) -
          canonicalL2BlockEmbedding v hv (lp.single 2 n 1) := by
    dsimp only [r, w, z]
    rw [map_sub, canonicalL2Quotient_centralizerLiftCLM M b C hC hb, hqz]
  obtain ⟨K, hK, hkernel⟩ :=
    canonicalL2Quotient_kernel_approximation
  let k : ℕ → canonicalL2Quotient.ker :=
    fun n ↦ Classical.choose (hkernel (r n))
  have hk_close (n : ℕ) :
      ‖r n - (k n : CanonicalRealKaltonPeck)‖ ≤
        K * ‖canonicalL2Quotient (r n)‖ :=
    Classical.choose_spec (hkernel (r n))
  have hk_range (n : ℕ) :
      (k n : CanonicalRealKaltonPeck) ∈ canonicalL2Inclusion.range := by
    rw [canonicalL2Inclusion_range]
    exact (k n).property
  let h : ℕ → CanonicalL2 :=
    fun n ↦ Classical.choose (hk_range n)
  have hih (n : ℕ) :
      canonicalL2Inclusion (h n) = (k n : CanonicalRealKaltonPeck) :=
    Classical.choose_spec (hk_range n)
  have hi_closed :
      IsClosed (canonicalL2Inclusion.range : Set CanonicalRealKaltonPeck) := by
    rw [canonicalL2Inclusion_range]
    exact canonicalL2Quotient.isClosed_ker
  obtain ⟨Q, hQ⟩ :=
    canonicalL2Inclusion.antilipschitz_of_injective_of_isClosed_range
      canonicalL2Inclusion_injective hi_closed
  obtain ⟨D, hD, hsecond⟩ :=
    exists_uniform_canonicalSecondBasisVector_bound
  let R : ℝ := ‖L‖ + ‖W‖ * D
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hr_bound (n : ℕ) : ‖r n‖ ≤ R := by
    dsimp only [r, w, z, R]
    calc
      ‖L (y n) - W (canonicalSecondBasisVector n)‖ ≤
          ‖L (y n)‖ + ‖W (canonicalSecondBasisVector n)‖ :=
        norm_sub_le _ _
      _ ≤ ‖L‖ * ‖y n‖ + ‖W‖ * ‖canonicalSecondBasisVector n‖ :=
        add_le_add (L.le_opNorm _) (W.le_opNorm _)
      _ ≤ ‖L‖ * 1 + ‖W‖ * D := by
        rw [hy_norm]
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
          (hsecond n) (norm_nonneg W))
      _ = ‖L‖ + ‖W‖ * D := by ring
  have hqr_le (n : ℕ) :
      ‖canonicalL2Quotient (r n)‖ ≤ errorSum := by
    rw [hqr]
    exact herror_le n
  have hk_bound (n : ℕ) :
      ‖(k n : CanonicalRealKaltonPeck)‖ ≤ R + K * errorSum := by
    calc
      ‖(k n : CanonicalRealKaltonPeck)‖ =
          ‖r n - (r n - (k n : CanonicalRealKaltonPeck))‖ := by
        congr 1
        abel
      _ ≤ ‖r n‖ + ‖r n - (k n : CanonicalRealKaltonPeck)‖ :=
        norm_sub_le _ _
      _ ≤ R + K * ‖canonicalL2Quotient (r n)‖ :=
        add_le_add (hr_bound n) (hk_close n)
      _ ≤ R + K * errorSum :=
        add_le_add (le_refl R)
          (mul_le_mul_of_nonneg_left (hqr_le n) hK.le)
  let B : ℝ := (Q : ℝ) * (R + K * errorSum)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (NNReal.coe_nonneg Q)
      (add_nonneg hR (mul_nonneg hK.le herrorSum))
  have hh_bound (n : ℕ) : ‖h n‖ ≤ B := by
    have hanti := hQ.le_mul_dist (h n) 0
    simp only [dist_zero_right, map_zero] at hanti
    rw [hih n] at hanti
    exact hanti.trans
      (mul_le_mul_of_nonneg_left (hk_bound n) (NNReal.coe_nonneg Q))
  obtain ⟨c, E, hc, hE, hmodel⟩ :=
    canonicalRealKaltonPeckPresentation.norm_equivalent
  let U : ℝ :=
    ‖L‖ * (1 + errorSum) +
      ‖canonicalL2Inclusion‖ * B + K * errorSum
  have hU : 0 ≤ U := by
    dsimp only [U]
    positivity
  have hWleft :
      canonicalKaltonSwansonForm.adjoint W * W = 1 :=
    (canonicalNormalizedBlock v hv).2.2.2.2.2.1
  have hbound_every_N (N : ℕ) (hN : 0 < N) :
      c * (Real.log N + 1) ≤ ‖canonicalKaltonSwansonForm.adjoint W‖ * U := by
    apply signed_log_bound M L y W error hsum (fun _ => norm_nonneg _) hy_signed
      k h hih K B c hK.le hB hh_bound _ (fun s => (hmodel s).1) hWleft N hN
    intro n
    calc
      ‖r n - (k n : CanonicalRealKaltonPeck)‖ ≤
          K * ‖canonicalL2Quotient (r n)‖ := hk_close n
      _ = K * error n := by rw [hqr]
  let G : ℝ :=
    (‖canonicalKaltonSwansonForm.adjoint W‖ * U) / c
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (Real.exp G)
  have hN : 0 < N := by
    have hexp : 0 < Real.exp G := Real.exp_pos G
    exact_mod_cast lt_trans hexp hNlarge
  have hlog : G < Real.log N :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast hN)).2 hNlarge
  have hupper := hbound_every_N N hN
  have hdiv :
      Real.log N + 1 ≤ G := by
    dsimp only [G]
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hupper)
  linarith

/-- The canonical quotient `Z₂ → ℓ₂` is strictly singular.
Blueprint label: `thm:canonical-centralizer-obstruction`. -/
theorem canonicalL2Quotient_isStrictlySingular :
    IsStrictlySingular canonicalL2Quotient :=
  canonicalL2Quotient_strictlySingular_of_subspace_obstruction
    no_boundedCentralizerApproximation

/-- CGP Proposition 5.3(b): strict singularity on the canonical Hilbert kernel forces strict
singularity on the whole canonical Kalton--Peck space. -/
theorem canonical_isStrictlySingular_of_inclusion
    (T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hTi : IsStrictlySingular.{0, 0, 0, 0}
      (T.comp canonicalL2Inclusion)) :
    IsStrictlySingular.{0, 0, 0, 0} T :=
  canonical_isStrictlySingular_of_inclusion_of_quotient
    canonicalL2Quotient_isStrictlySingular T hTi

/-- Corrected CGP Proposition 5.3(c), in contrapositive form: failure of upper
semi-Fredholmness persists on the canonical Hilbert kernel. -/
theorem canonical_not_upperSemi_comp_canonicalL2Inclusion_of_not_upper
    (B : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hB : ¬ IsUpperSemiFredholm B) :
    ¬ IsUpperSemiFredholm (B.comp canonicalL2Inclusion) :=
  Canonical.not_upperSemi_comp_canonicalL2Inclusion_of_not_upper
    canonicalL2Quotient_isStrictlySingular B hB

/-- Every bounded operator vanishing on the canonical kernel factors continuously through the
canonical quotient. -/
theorem canonical_factor_through_quotient
    (R : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hR : R.comp canonicalL2Inclusion = 0) :
    ∃ L : CanonicalL2 →L[ℝ] CanonicalRealKaltonPeck,
      R = L.comp canonicalL2Quotient := by
  have hker :
      canonicalL2Quotient.ker ≤ R.ker := by
    intro z hz
    have hzrange : z ∈ canonicalL2Inclusion.range := by
      rw [canonicalL2Inclusion_range]
      exact hz
    obtain ⟨x, rfl⟩ := hzrange
    change R (canonicalL2Inclusion x) = 0
    exact DFunLike.congr_fun hR x
  let Rbar :
      (CanonicalRealKaltonPeck ⧸ canonicalL2Quotient.ker) →L[ℝ]
        CanonicalRealKaltonPeck :=
    canonicalL2Quotient.ker.liftQL R hker
  let qbar :
      (CanonicalRealKaltonPeck ⧸ canonicalL2Quotient.ker) →L[ℝ]
        CanonicalL2 :=
    canonicalL2Quotient.ker.liftQL canonicalL2Quotient le_rfl
  have hqbar_ker : qbar.ker = ⊥ := by
    change LinearMap.ker
        (canonicalL2Quotient.ker.liftQ
          canonicalL2Quotient.toLinearMap le_rfl) = ⊥
    exact Submodule.ker_liftQ_eq_bot' _ _ rfl
  have hqbar_surjective : Function.Surjective qbar := by
    intro y
    obtain ⟨z, hz⟩ := canonicalL2Quotient_surjective y
    refine ⟨canonicalL2Quotient.ker.mkQ z, ?_⟩
    exact hz
  have hqbar_range : qbar.range = ⊤ :=
    LinearMap.range_eq_top.mpr hqbar_surjective
  let : IsClosed
      (canonicalL2Quotient.ker : Set CanonicalRealKaltonPeck) :=
    canonicalL2Quotient.isClosed_ker
  let e :
      (CanonicalRealKaltonPeck ⧸ canonicalL2Quotient.ker) ≃L[ℝ]
        CanonicalL2 :=
    ContinuousLinearEquiv.ofBijective qbar hqbar_ker hqbar_range
  let L : CanonicalL2 →L[ℝ] CanonicalRealKaltonPeck :=
    Rbar.comp e.symm.toContinuousLinearMap
  refine ⟨L, ?_⟩
  ext z
  change R z = Rbar (e.symm (canonicalL2Quotient z))
  have he_apply :
      e (canonicalL2Quotient.ker.mkQ z) =
        canonicalL2Quotient z := by
    rfl
  rw [← he_apply, e.symm_apply_apply]
  rfl

/-- If a canonical operator vanishes on the canonical kernel, then the range of its
symplectic adjoint lies in that kernel. -/
theorem canonical_symplecticAdjoint_range_le_quotientKernel
    (R : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hR : R.comp canonicalL2Inclusion = 0) :
    (canonicalKaltonSwansonForm.adjoint R).range ≤
      canonicalL2Quotient.ker := by
  rintro z ⟨x, rfl⟩
  change
    canonicalL2Quotient (canonicalKaltonSwansonForm.adjoint R x) = 0
  apply ext_inner_left ℝ
  intro y
  have hskew (a b : CanonicalRealKaltonPeck) :
      canonicalKaltonSwansonForm.toDual a b =
        -canonicalKaltonSwansonForm.toDual b a := by
    have h := canonicalKaltonSwansonForm.alternating (a + b)
    simp only [map_add, add_apply, canonicalKaltonSwansonForm.alternating,
      add_zero, zero_add] at h
    linarith
  calc
    inner ℝ y
        (canonicalL2Quotient
          (canonicalKaltonSwansonForm.adjoint R x)) =
        canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion y)
          (canonicalKaltonSwansonForm.adjoint R x) := by
      rw [Symplectic.canonicalKaltonSwansonForm_inclusion_left]
    _ = -canonicalKaltonSwansonForm.toDual
          (canonicalKaltonSwansonForm.adjoint R x)
          (canonicalL2Inclusion y) :=
      hskew _ _
    _ = -canonicalKaltonSwansonForm.toDual x
          (R (canonicalL2Inclusion y)) := by
      rw [Forms.adjoint_apply]
    _ = 0 := by
      have hy : R (canonicalL2Inclusion y) = 0 := by
        simpa only [ContinuousLinearMap.comp_apply, zero_apply] using
          DFunLike.congr_fun hR y
      rw [hy, map_zero, neg_zero]
    _ = inner ℝ y 0 := by simp

/-- If a canonical operator vanishes on the canonical kernel, then its symplectic adjoint
factors continuously through the inclusion of that kernel. -/
theorem canonical_symplecticAdjoint_factor_through_inclusion
    (R : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hR : R.comp canonicalL2Inclusion = 0) :
    ∃ L : CanonicalRealKaltonPeck →L[ℝ] CanonicalL2,
      canonicalKaltonSwansonForm.adjoint R =
        canonicalL2Inclusion.comp L := by
  have hiClosed : IsClosed
      (Set.range
        (canonicalL2Inclusion :
          CanonicalL2 → CanonicalRealKaltonPeck)) := by
    change IsClosed
      (↑(LinearMap.range canonicalL2Inclusion.toLinearMap) :
        Set CanonicalRealKaltonPeck)
    rw [canonicalL2Inclusion_range]
    exact canonicalL2Quotient.isClosed_ker
  let e : CanonicalL2 ≃L[ℝ] canonicalL2Inclusion.range :=
    ContinuousLinearMap.equivRange
      canonicalL2Inclusion_injective hiClosed
  have hrange :=
    canonical_symplecticAdjoint_range_le_quotientKernel R hR
  let Rker :
      CanonicalRealKaltonPeck →L[ℝ] canonicalL2Inclusion.range :=
    (canonicalKaltonSwansonForm.adjoint R).codRestrict
      canonicalL2Inclusion.range (fun x => by
        rw [canonicalL2Inclusion_range]
        exact hrange ⟨x, rfl⟩)
  let L : CanonicalRealKaltonPeck →L[ℝ] CanonicalL2 :=
    e.symm.toContinuousLinearMap.comp Rker
  refine ⟨L, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  change canonicalKaltonSwansonForm.adjoint R x =
    canonicalL2Inclusion (e.symm (Rker x))
  have he : e (e.symm (Rker x)) = Rker x :=
    e.apply_symm_apply (Rker x)
  exact (congrArg Subtype.val he).symm

/-- The adjoint cross-term of a quotient-factorized remainder and a kernel-intertwining
operator is the included Hilbert adjoint of its quotient compression. -/
theorem canonical_remainderAdjoint_kernel_formula
    (R V : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (L : CanonicalL2 →L[ℝ] CanonicalRealKaltonPeck)
    (iv : CanonicalL2 →L[ℝ] CanonicalL2)
    (hR : R = L.comp canonicalL2Quotient)
    (hV :
      V.comp canonicalL2Inclusion = canonicalL2Inclusion.comp iv) :
    (canonicalKaltonSwansonForm.adjoint R * V).comp
        canonicalL2Inclusion =
      canonicalL2Inclusion.comp
        ((ContinuousLinearMap.adjoint
          (canonicalL2Quotient.comp L)).comp iv) := by
  apply ContinuousLinearMap.ext
  intro x
  apply canonicalKaltonSwansonForm.toDual.injective
  apply ContinuousLinearMap.ext
  intro z
  calc
    canonicalKaltonSwansonForm.toDual
        (((canonicalKaltonSwansonForm.adjoint R * V).comp
          canonicalL2Inclusion) x) z =
        canonicalKaltonSwansonForm.toDual
          (V (canonicalL2Inclusion x)) (R z) := by
      change canonicalKaltonSwansonForm.toDual
        (canonicalKaltonSwansonForm.adjoint R
          (V (canonicalL2Inclusion x))) z = _
      rw [Forms.adjoint_apply]
    _ = canonicalKaltonSwansonForm.toDual
          (canonicalL2Inclusion (iv x))
          (L (canonicalL2Quotient z)) := by
      have hvx :
          V (canonicalL2Inclusion x) =
            canonicalL2Inclusion (iv x) := by
        simpa only [ContinuousLinearMap.comp_apply] using
          DFunLike.congr_fun hV x
      rw [hvx, hR]
      rfl
    _ = inner ℝ (iv x)
          (canonicalL2Quotient (L (canonicalL2Quotient z))) := by
      rw [Symplectic.canonicalKaltonSwansonForm_inclusion_left]
    _ = inner ℝ
          (ContinuousLinearMap.adjoint
            (canonicalL2Quotient.comp L) (iv x))
          (canonicalL2Quotient z) := by
      rw [(canonicalL2Quotient.comp L).adjoint_inner_left]
      rfl
    _ = canonicalKaltonSwansonForm.toDual
          (canonicalL2Inclusion
            (ContinuousLinearMap.adjoint
              (canonicalL2Quotient.comp L) (iv x))) z := by
      rw [Symplectic.canonicalKaltonSwansonForm_inclusion_left]
    _ = canonicalKaltonSwansonForm.toDual
          ((canonicalL2Inclusion.comp
            ((ContinuousLinearMap.adjoint
              (canonicalL2Quotient.comp L)).comp iv)) x) z := by
      rfl

/-- Compression of the symplectic adjoint to the canonical kernel and quotient is the
negative Hilbert-space adjoint of the corresponding compression. -/
theorem canonical_symplecticAdjoint_kernelCompression
    (T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck) :
    canonicalL2Quotient.comp
        ((canonicalKaltonSwansonForm.adjoint T).comp canonicalL2Inclusion) =
      -(ContinuousLinearMap.adjoint
        (canonicalL2Quotient.comp (T.comp canonicalL2Inclusion))) := by
  let S : CanonicalL2 →L[ℝ] CanonicalL2 :=
    canonicalL2Quotient.comp (T.comp canonicalL2Inclusion)
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  have hskew (a b : CanonicalRealKaltonPeck) :
      canonicalKaltonSwansonForm.toDual a b =
        -canonicalKaltonSwansonForm.toDual b a := by
    have h := canonicalKaltonSwansonForm.alternating (a + b)
    simp only [map_add, add_apply, canonicalKaltonSwansonForm.alternating,
      add_zero, zero_add] at h
    linarith
  calc
    inner ℝ y
        ((canonicalL2Quotient.comp
          ((canonicalKaltonSwansonForm.adjoint T).comp
            canonicalL2Inclusion)) x) =
        canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion y)
          (canonicalKaltonSwansonForm.adjoint T
            (canonicalL2Inclusion x)) := by
          rw [Symplectic.canonicalKaltonSwansonForm_inclusion_left]
          rfl
    _ = -canonicalKaltonSwansonForm.toDual
          (canonicalKaltonSwansonForm.adjoint T
            (canonicalL2Inclusion x)) (canonicalL2Inclusion y) :=
      hskew _ _
    _ = -canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion x)
          (T (canonicalL2Inclusion y)) := by
      rw [Forms.adjoint_apply]
    _ = -inner ℝ x (S y) := by
      rw [Symplectic.canonicalKaltonSwansonForm_inclusion_left]
      rfl
    _ = inner ℝ y ((-ContinuousLinearMap.adjoint S) x) := by
      rw [neg_apply, inner_neg_right, S.adjoint_inner_right]
      rw [real_inner_comm]

/-- Every kernel-to-quotient compression of a canonical operator is strictly singular. -/
theorem canonical_quotient_operator_inclusion_isStrictlySingular
    (T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck) :
    IsStrictlySingular.{0, 0, 0, 0}
      (canonicalL2Quotient.comp (T.comp canonicalL2Inclusion)) := by
  rw [← ContinuousLinearMap.comp_assoc]
  exact (canonicalL2Quotient_isStrictlySingular.precomp T).precomp
    canonicalL2Inclusion

/-- The kernel-to-quotient compression of a canonical symplectic adjoint is strictly
singular. -/
theorem canonical_quotient_symplecticAdjoint_inclusion_isStrictlySingular
    (T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck) :
    IsStrictlySingular.{0, 0, 0, 0}
      (canonicalL2Quotient.comp
        ((canonicalKaltonSwansonForm.adjoint T).comp canonicalL2Inclusion)) := by
  rw [canonical_symplecticAdjoint_kernelCompression]
  exact
    (canonical_quotient_operator_inclusion_isStrictlySingular T).hilbert_adjoint.neg

/-- Every canonical normalized block operator is upper semi-Fredholm.
Blueprint label: `lem:cgp-primary-reduction`. -/
theorem canonicalBlockOperator_isUpperSemiFredholm
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w) :
    IsUpperSemiFredholm (canonicalBlockOperator w hw) := by
  let W := canonicalBlockOperator w hw
  have hleftIdentity :
      canonicalKaltonSwansonForm.adjoint W * W = 1 :=
    (canonicalNormalizedBlock w hw).2.2.2.2.2.1
  have hWleft : W.HasLeftInverse := by
    refine ⟨canonicalKaltonSwansonForm.adjoint W, ?_⟩
    intro z
    change (canonicalKaltonSwansonForm.adjoint W * W) z = z
    rw [hleftIdentity]
    rfl
  have hkernelRange := Fredholm.leftInverseKernelRange W hWleft
  exact ⟨hkernelRange.2.1, hkernelRange.2.2⟩

/-- The exact retained output of the upper-specific Kalton block factorization needed by the
compact-Gram proof. -/
def HasUpperCompactGramFactorization : Prop :=
  ∀ T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
    IsUpperSemiFredholm T →
      ∃ (W V R K :
          CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
        (iw iv : CanonicalL2 →L[ℝ] CanonicalL2) (α : ℝ),
        α ≠ 0 ∧
        W.comp canonicalL2Inclusion = canonicalL2Inclusion.comp iw ∧
        V.comp canonicalL2Inclusion = canonicalL2Inclusion.comp iv ∧
        canonicalKaltonSwansonForm.adjoint V * V = 1 ∧
        T.comp W = α • V + R + K ∧
        R.comp canonicalL2Inclusion = 0 ∧
        IsCompactOperator K ∧
        IsCompactOperator (canonicalKaltonSwansonForm.adjoint K)

private def factorizationL2Basis (n : ℕ) : CanonicalL2 :=
  lp.single 2 n 1

private lemma inclusion_factorizationL2Basis (n : ℕ) :
    canonicalL2Inclusion (factorizationL2Basis n) =
      canonicalFirstBasisVector n := by
  apply canonicalRealKaltonPeckPresentation.coordinates_injective
  rw [canonicalL2Inclusion_coordinates, (canonicalBasisCoordinates n).1]
  apply Prod.ext
  · funext k
    simp [factorizationL2Basis, standardBasisSequence, lp.single_apply,
      Pi.single_apply]
  · rfl

private theorem continuousLinearMap_ext_factorizationL2Basis
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A B : CanonicalL2 →L[ℝ] Y)
    (hAB : ∀ n,
      A (factorizationL2Basis n) = B (factorizationL2Basis n)) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro x
  have hx :=
    lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) x
  have hA := hx.map A A.continuous
  have hB := hx.map B B.continuous
  apply hA.unique
  apply HasSum.congr_fun hB
  intro n
  change A (lp.single 2 n (x n)) = B (lp.single 2 n (x n))
  have hsingle :
      lp.single 2 n (x n) = (x n) • factorizationL2Basis n := by
    apply Subtype.ext
    funext k
    simp [factorizationL2Basis, lp.single_apply, Pi.single_apply]
  rw [hsingle, map_smul, map_smul, hAB]

/-- Pairing a canonical kernel vector with the `k`th quotient-basis vector evaluates its
`k`th Hilbert coordinate. -/
theorem canonical_pairing_inclusion_secondBasis
    (x : CanonicalL2) (k : ℕ) :
    canonicalKaltonSwansonForm.toDual
        (canonicalL2Inclusion x) (canonicalSecondBasisVector k) =
      x k := by
  rw [Symplectic.canonicalKaltonSwansonForm_inclusion_left]
  have hq :
      canonicalL2Quotient (canonicalSecondBasisVector k) =
        lp.single 2 k (1 : ℝ) := by
    apply Subtype.ext
    funext j
    rw [canonicalL2Quotient_apply, (canonicalBasisCoordinates k).2]
    simp [standardBasisSequence, lp.single_apply, Pi.single_apply]
  rw [hq, lp.inner_single_right]
  simp

/-- Applying a fixed canonical symplectic functional after a bounded operator to successive
normalized Hilbert blocks tends to zero. -/
theorem tendsto_canonical_pairing_apply_block_zero
    (A : CanonicalL2 →L[ℝ] CanonicalRealKaltonPeck)
    (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
    (z : CanonicalRealKaltonPeck) :
    Filter.Tendsto
      (fun n =>
        canonicalKaltonSwansonForm.toDual
          (A
            (canonicalL2BlockEmbedding w hw
              (lp.single 2 n (1 : ℝ))))
          z)
      Filter.atTop (𝓝 0) := by
  let g : StrongDual ℝ CanonicalRealKaltonPeck :=
    ((ContinuousLinearMap.apply ℝ ℝ) z).comp
      canonicalKaltonSwansonForm.toDual.toContinuousLinearMap
  let f : StrongDual ℝ CanonicalL2 :=
    g.comp (A.comp (canonicalL2BlockEmbedding w hw))
  have hf :=
    HilbertGlidingHump.tendsto_dual_canonicalL2Basis_zero f
  convert hf using 1
  ext n
  rfl

private theorem compact_prod
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X →L[ℝ] Y} {g : X →L[ℝ] Z}
    (hf : IsCompactOperator f) (hg : IsCompactOperator g) :
    IsCompactOperator (f.prod g) := by
  obtain ⟨K, hK, hfK⟩ := hf
  obtain ⟨L, hL, hgL⟩ := hg
  refine ⟨K ×ˢ L, hK.prod hL, ?_⟩
  filter_upwards [hfK, hgL] with x hxK hxL
  exact ⟨hxK, hxL⟩

private theorem exists_pos_mul_norm_sub_starProjection_le
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : CanonicalL2 →L[ℝ] Y)
    (_hker : FiniteDimensional ℝ A.ker)
    (hrange : IsClosed (A.range : Set Y)) :
    ∃ c > 0, ∀ x : CanonicalL2,
      c * ‖x - A.ker.starProjection x‖ ≤ ‖A x‖ := by
  let : FiniteDimensional ℝ A.ker := _hker
  let S : A.kerᗮ →L[ℝ] Y := A.domRestrict A.kerᗮ
  have hS_injective : Function.Injective S := by
    intro x y hxy
    apply Subtype.ext
    have hker_sub : (x : CanonicalL2) - (y : CanonicalL2) ∈ A.ker := by
      change A ((x : CanonicalL2) - (y : CanonicalL2)) = 0
      rw [map_sub, sub_eq_zero]
      exact hxy
    have horth_sub : (x : CanonicalL2) - (y : CanonicalL2) ∈ A.kerᗮ :=
      A.kerᗮ.sub_mem x.property y.property
    have hbot : (x : CanonicalL2) - (y : CanonicalL2) ∈
        (⊥ : Submodule ℝ CanonicalL2) :=
      A.ker.orthogonal_disjoint.le_bot ⟨hker_sub, horth_sub⟩
    simpa only [Submodule.mem_bot, sub_eq_zero] using hbot
  have hS_range : Set.range S = (A.range : Set Y) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨A.kerᗮ.orthogonalProjectionOnto x, ?_⟩
      change A (A.kerᗮ.orthogonalProjectionOnto x : CanonicalL2) = A x
      rw [Submodule.orthogonalProjectionOnto_orthogonal]
      change A (x - A.ker.starProjection x) = A x
      rw [map_sub, show A (A.ker.starProjection x) = 0 from
        A.ker.starProjection_apply_mem x, sub_zero]
  have hS_closed : IsClosed (Set.range S) := by
    rw [hS_range]
    exact hrange
  have hanti : ∃ K, AntilipschitzWith K S :=
    S.antilipschitz_of_injective_of_isClosed_range hS_injective hS_closed
  rw [antilipschitzWith_iff_exists_mul_le_norm] at hanti
  obtain ⟨c, hc, hbound⟩ := hanti
  refine ⟨c, hc, fun x ↦ ?_⟩
  let y : A.kerᗮ := A.kerᗮ.orthogonalProjectionOnto x
  have hy : (y : CanonicalL2) = x - A.ker.starProjection x := by
    exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_orthogonal x)
  have hynorm : ‖y‖ = ‖x - A.ker.starProjection x‖ := by
    change ‖(y : CanonicalL2)‖ = _
    rw [hy]
  rw [← hynorm]
  simpa only [S, ContinuousLinearMap.domRestrict_apply, hy, map_sub,
    show A (A.ker.starProjection x) = 0 from A.ker.starProjection_apply_mem x,
    sub_zero] using hbound y

private theorem blockSupportBefore'
    (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) {n m : ℕ} (hnm : n < m)
    {i j : ℕ} (hi : w n i ≠ 0) (hj : w m j ≠ 0) : i < j := by
  revert j
  induction m, hnm using Nat.le_induction with
  | base =>
      intro j hj
      exact hw.2.2 n i j hi hj
  | succ m hnm ih =>
      intro j hj
      obtain ⟨k, hk⟩ := hw.1 m |>.2
      change w m k ≠ 0 at hk
      exact lt_trans (ih hk) (hw.2.2 m k j hk hj)

private theorem IsSuccessiveNormalizedBlockSequence.comp_strictMono
    {w : ℕ → ℕ → ℝ} (hw : IsSuccessiveNormalizedBlockSequence w)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsSuccessiveNormalizedBlockSequence (fun n => w (φ n)) := by
  constructor
  · intro n
    exact hw.1 (φ n)
  constructor
  · intro n
    exact hw.2.1 (φ n)
  · intro n i j hi hj
    exact blockSupportBefore' w hw (hφ (Nat.lt_succ_self n)) hi hj

private theorem inclusion_standardBasis (n : ℕ) :
    canonicalL2Inclusion (lp.single 2 n (1 : ℝ)) =
      canonicalFirstBasisVector n := by
  apply canonicalRealKaltonPeckPresentation.coordinates_injective
  rw [canonicalL2Inclusion_coordinates,
    (canonicalBasisCoordinates n).1]
  apply Prod.ext
  · funext k
    simp [lp.single_apply, Pi.single_apply,
      standardBasisSequence, eq_comm]
  · rfl

/-- The sequence-selection output needed from the upper-specific Kalton block argument:
after passing to canonical normalized source and target blocks, the kernel-column error is
absolutely summable. -/
def HasUpperSummableKernelBlockApproximation : Prop :=
  ∀ T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
    IsUpperSemiFredholm T →
      ∃ (w v : ℕ → ℕ → ℝ)
        (hw : IsSuccessiveNormalizedBlockSequence w)
        (hv : IsSuccessiveNormalizedBlockSequence v) (α : ℝ),
        α ≠ 0 ∧
        Summable (fun n =>
          ‖T (canonicalBlockOperator w hw
                (canonicalFirstBasisVector n)) -
            α • canonicalBlockOperator v hv
                (canonicalFirstBasisVector n)‖)

/-- An upper semi-Fredholm operator has kernel approximants with positive bounded norms. -/
private theorem exists_bounded_kernel_approximants
    (T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck) (hT : IsUpperSemiFredholm T) :
    ∃ (w : ℕ → ℕ → ℝ) (hw : IsSuccessiveNormalizedBlockSequence w)
      (a : ℕ → CanonicalL2) (δ B : ℝ) (N₀ : ℕ), 0 < δ ∧
      (∀ n, N₀ ≤ n → δ ≤ ‖a n‖) ∧ (∀ n, N₀ ≤ n → ‖a n‖ ≤ B) ∧
      Summable (fun n => ‖(T.comp canonicalL2Inclusion)
        (canonicalL2BlockEmbedding w hw (lp.single 2 n (1 : ℝ))) -
          canonicalL2Inclusion (a n)‖) := by
  let A : CanonicalL2 →L[ℝ] CanonicalRealKaltonPeck :=
    T.comp canonicalL2Inclusion
  have hInclusionUpper : IsUpperSemiFredholm canonicalL2Inclusion := by
    constructor
    · have hker : canonicalL2Inclusion.toLinearMap.ker = ⊥ :=
        LinearMap.ker_eq_bot.mpr canonicalL2Inclusion_injective
      rw [hker]
      infer_instance
    · rw [canonicalL2Inclusion_range]
      exact canonicalL2Quotient.isClosed_ker
  have hA : IsUpperSemiFredholm A := by
    exact hInclusionUpper.comp hT
  let M : Submodule ℝ CanonicalL2 := A.ker
  let : FiniteDimensional ℝ M := hA.1
  let Q : CanonicalL2 →L[ℝ] CanonicalL2 :=
    canonicalL2Quotient.comp A
  have hQstrict : IsStrictlySingular Q := by
    exact canonicalL2Quotient_isStrictlySingular.precomp A
  have hQcompact : IsCompactOperator Q :=
    canonicalL2_isCompact_of_isStrictlySingular Q hQstrict
  let P : CanonicalL2 →L[ℝ] M := M.orthogonalProjectionOnto
  have hPcompact : IsCompactOperator P :=
    isCompactOperator_of_locallyCompactSpace_dom P
  let H : CanonicalL2 →L[ℝ] CanonicalL2 × M := Q.prod P
  have hHcompact : IsCompactOperator H := compact_prod hQcompact hPcompact
  have hHnotUpper : ¬ IsUpperSemiFredholm H := by
    intro hHupper
    have hHnotStrict :
        ¬ IsStrictlySingular H :=
      not_isStrictlySingular_of_finiteDimensional_ker_of_isClosed_range
        canonicalL2_not_finiteDimensional H hHupper.1 hHupper.2
    exact hHnotStrict (isStrictlySingular_of_isCompactOperator H hHcompact)
  obtain ⟨w, hw, hHsum⟩ :=
    CgpBlockExtraction.exists_summable_canonicalL2Block_of_not_upperSemi
      H hHnotUpper
  let b : ℕ → CanonicalL2 := fun n =>
    canonicalL2BlockEmbedding w hw (lp.single 2 n (1 : ℝ))
  have hbNorm (n : ℕ) : ‖b n‖ = 1 := by
    change
      ‖canonicalL2BlockEmbedding w hw (lp.single 2 n (1 : ℝ))‖ = 1
    rw [canonicalL2BlockEmbedding_norm]
    simp [lp.norm_single]
  have hQsum : Summable (fun n => ‖Q (b n)‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hHsum
    have hle : ‖(H (b n)).1‖ ≤ ‖H (b n)‖ := norm_fst_le _
    simpa only [H, Q, P, b, ContinuousLinearMap.prod_apply] using hle
  have hPsum : Summable (fun n => ‖P (b n)‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hHsum
    have hle : ‖(H (b n)).2‖ ≤ ‖H (b n)‖ := norm_snd_le _
    simpa only [H, Q, P, b, ContinuousLinearMap.prod_apply] using hle
  obtain ⟨c, hc, hAbound⟩ :=
    exists_pos_mul_norm_sub_starProjection_le A hA.1 hA.2
  have hPzero : Tendsto (fun n => ‖P (b n)‖) atTop (𝓝 0) :=
    hPsum.tendsto_atTop_zero
  have hPeventually : ∀ᶠ n in atTop, ‖P (b n)‖ < (1 / 2 : ℝ) :=
    (tendsto_order.1 hPzero).2 _ (by norm_num)
  rw [eventually_atTop] at hPeventually
  obtain ⟨N, hPN⟩ := hPeventually
  have hAlower (n : ℕ) (hn : N ≤ n) :
      c / 2 ≤ ‖A (b n)‖ := by
    have hPsmall : ‖P (b n)‖ < (1 / 2 : ℝ) := hPN n hn
    have hprojNorm :
        ‖M.starProjection (b n)‖ = ‖P (b n)‖ := by
      rfl
    have hhalf : (1 / 2 : ℝ) < ‖b n - M.starProjection (b n)‖ := by
      have htri :
          ‖b n‖ ≤
            ‖b n - M.starProjection (b n)‖ +
              ‖M.starProjection (b n)‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (b n - M.starProjection (b n))
            (M.starProjection (b n))
      rw [hbNorm n, hprojNorm] at htri
      linarith
    calc
      c / 2 = c * (1 / 2 : ℝ) := by ring
      _ ≤ c * ‖b n - M.starProjection (b n)‖ :=
        mul_le_mul_of_nonneg_left hhalf.le hc.le
      _ ≤ ‖A (b n)‖ := by
        simpa only [M] using hAbound (b n)
  let z : ℕ → CanonicalRealKaltonPeck := fun n => A (b n)
  obtain ⟨C, hC, hkernel⟩ :=
    canonicalL2Quotient_kernel_approximation
  let k : ℕ → canonicalL2Quotient.ker :=
    fun n => Classical.choose (hkernel (z n))
  have hkClose (n : ℕ) :
      ‖z n - (k n : CanonicalRealKaltonPeck)‖ ≤
        C * ‖Q (b n)‖ := by
    simpa only [k, z, Q, ContinuousLinearMap.comp_apply] using
      Classical.choose_spec (hkernel (z n))
  have hkRange (n : ℕ) :
      (k n : CanonicalRealKaltonPeck) ∈ canonicalL2Inclusion.range := by
    rw [canonicalL2Inclusion_range]
    exact (k n).property
  let a : ℕ → CanonicalL2 :=
    fun n => Classical.choose (hkRange n)
  have hia (n : ℕ) :
      canonicalL2Inclusion (a n) =
        (k n : CanonicalRealKaltonPeck) := by
    exact Classical.choose_spec (hkRange n)
  let d : ℕ → ℝ := fun n =>
    ‖z n - canonicalL2Inclusion (a n)‖
  have hdLe (n : ℕ) : d n ≤ C * ‖Q (b n)‖ := by
    simpa only [d, hia] using hkClose n
  have hdSum : Summable d := by
    apply Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) hdLe
    exact hQsum.mul_left C
  have hdZero : Tendsto d atTop (𝓝 0) :=
    hdSum.tendsto_atTop_zero
  have hdEventuallyOne : ∀ᶠ n in atTop, d n < (1 : ℝ) :=
    (tendsto_order.1 hdZero).2 1 zero_lt_one
  have hdEventuallySmall : ∀ᶠ n in atTop, d n < c / 4 :=
    (tendsto_order.1 hdZero).2 (c / 4) (by positivity)
  have hdEventually :
      ∀ᶠ n in atTop, d n < 1 ∧ d n < c / 4 :=
    hdEventuallyOne.and hdEventuallySmall
  rw [eventually_atTop] at hdEventually
  obtain ⟨Nd, hNd⟩ := hdEventually
  let N₀ : ℕ := max N Nd
  have hN₀N : N ≤ N₀ := Nat.le_max_left _ _
  have hN₀d : Nd ≤ N₀ := Nat.le_max_right _ _
  have hiClosed :
      IsClosed
        (canonicalL2Inclusion.range :
          Set CanonicalRealKaltonPeck) := by
    rw [canonicalL2Inclusion_range]
    exact canonicalL2Quotient.isClosed_ker
  obtain ⟨Ki, hKi⟩ :=
    canonicalL2Inclusion.antilipschitz_of_injective_of_isClosed_range
      canonicalL2Inclusion_injective hiClosed
  let δ : ℝ := (c / 4) / (‖canonicalL2Inclusion‖ + 1)
  let B : ℝ := (Ki : ℝ) * (‖A‖ + 1)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have haLower (n : ℕ) (hn : N₀ ≤ n) : δ ≤ ‖a n‖ := by
    have hnN : N ≤ n := hN₀N.trans hn
    have hnd : Nd ≤ n := hN₀d.trans hn
    have hdsmall : d n < c / 4 := (hNd n hnd).2
    have hzLower : c / 2 ≤ ‖z n‖ := by
      simpa only [z] using hAlower n hnN
    have hiLower : c / 4 ≤ ‖canonicalL2Inclusion (a n)‖ := by
      have htri :
          ‖z n‖ ≤
            ‖z n - canonicalL2Inclusion (a n)‖ +
              ‖canonicalL2Inclusion (a n)‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le
            (z n - canonicalL2Inclusion (a n))
            (canonicalL2Inclusion (a n))
      have hdEq :
          ‖z n - canonicalL2Inclusion (a n)‖ = d n := rfl
      rw [hdEq] at htri
      linarith
    rw [show δ = (c / 4) / (‖canonicalL2Inclusion‖ + 1) from rfl,
      div_le_iff₀ (by positivity)]
    calc
      c / 4 ≤ ‖canonicalL2Inclusion (a n)‖ := hiLower
      _ ≤ ‖canonicalL2Inclusion‖ * ‖a n‖ :=
        canonicalL2Inclusion.le_opNorm _
      _ ≤ (‖canonicalL2Inclusion‖ + 1) * ‖a n‖ := by
        nlinarith [norm_nonneg canonicalL2Inclusion, norm_nonneg (a n)]
      _ = ‖a n‖ * (‖canonicalL2Inclusion‖ + 1) := mul_comm _ _
  have haUpper (n : ℕ) (hn : N₀ ≤ n) : ‖a n‖ ≤ B := by
    have hnd : Nd ≤ n := hN₀d.trans hn
    have hdOne : d n < 1 := (hNd n hnd).1
    have hzUpper : ‖z n‖ ≤ ‖A‖ := by
      calc
        ‖z n‖ = ‖A (b n)‖ := rfl
        _ ≤ ‖A‖ * ‖b n‖ := A.le_opNorm _
        _ = ‖A‖ := by rw [hbNorm n, mul_one]
    have hiUpper :
        ‖canonicalL2Inclusion (a n)‖ ≤ ‖A‖ + 1 := by
      have htri :
          ‖canonicalL2Inclusion (a n)‖ ≤
            ‖z n‖ +
              ‖z n - canonicalL2Inclusion (a n)‖ := by
        calc
          ‖canonicalL2Inclusion (a n)‖ =
              ‖z n - (z n - canonicalL2Inclusion (a n))‖ := by
                congr 1
                abel
          _ ≤ ‖z n‖ +
              ‖z n - canonicalL2Inclusion (a n)‖ :=
            norm_sub_le _ _
      change
        ‖canonicalL2Inclusion (a n)‖ ≤ ‖z n‖ + d n
        at htri
      linarith
    have hanti :=
      hKi.le_mul_dist (a n) (0 : CanonicalL2)
    simp only [dist_zero_right, map_zero] at hanti
    calc
      ‖a n‖ ≤ (Ki : ℝ) * ‖canonicalL2Inclusion (a n)‖ := hanti
      _ ≤ (Ki : ℝ) * (‖A‖ + 1) :=
        mul_le_mul_of_nonneg_left hiUpper (NNReal.coe_nonneg Ki)
      _ = B := rfl
  exact ⟨w, hw, a, δ, B, N₀, hδ, haLower, haUpper, hdSum⟩

/-- Three approximation errors control a scalar multiple of an operator image. -/
private theorem norm_sub_smul_image_le
    {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : H →L[ℝ] E) (a u v : H) (α : ℝ) (z : E)
    (ha : a = ‖a‖ • u) (hu : ‖u‖ = 1) :
    ‖z - α • i v‖ ≤ ‖z - i a‖ + ‖i‖ * |‖a‖ - α| +
      (|α| * ‖i‖) * ‖u - v‖ := by
  have hmiddle : ‖i a - α • i u‖ ≤ ‖i‖ * |‖a‖ - α| := by
    rw [show i a = ‖a‖ • i u by rw [← map_smul, ← ha], ← sub_smul,
      norm_smul, Real.norm_eq_abs]
    calc
      |‖a‖ - α| * ‖i u‖ ≤ |‖a‖ - α| * (‖i‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (i.le_opNorm u) (abs_nonneg _)
      _ = ‖i‖ * |‖a‖ - α| := by rw [hu]; ring
  have hlast : ‖α • i u - α • i v‖ ≤ (|α| * ‖i‖) * ‖u - v‖ := by
    rw [← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (i.le_opNorm (u - v)) (abs_nonneg α)
  calc
    ‖z - α • i v‖ ≤ ‖z - i a‖ + ‖i a - α • i v‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖z - i a‖ + (‖i a - α • i u‖ + ‖α • i u - α • i v‖) := by
      gcongr
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖z - i a‖ + (‖i‖ * |‖a‖ - α| + (|α| * ‖i‖) * ‖u - v‖) := by
      gcongr
    _ = ‖z - i a‖ + ‖i‖ * |‖a‖ - α| + (|α| * ‖i‖) * ‖u - v‖ := by ring

/-- Kernel approximants of a successive block image tend to zero in each Hilbert coordinate. -/
private theorem tendsto_kernel_approximation_coordinates_zero
    (A : CanonicalL2 →L[ℝ] CanonicalRealKaltonPeck) (w : ℕ → ℕ → ℝ)
    (hw : IsSuccessiveNormalizedBlockSequence w) (a : ℕ → CanonicalL2)
    (heVec : Tendsto (fun n =>
      A (canonicalL2BlockEmbedding w hw (lp.single 2 n (1 : ℝ))) -
        canonicalL2Inclusion (a n)) atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun n => a n j) atTop (𝓝 0) := by
  let b : ℕ → CanonicalL2 := fun n =>
    canonicalL2BlockEmbedding w hw (lp.single 2 n (1 : ℝ))
  let z : ℕ → CanonicalRealKaltonPeck := fun n => A (b n)
  let y : CanonicalRealKaltonPeck := canonicalSecondBasisVector j
  let F : StrongDual ℝ CanonicalRealKaltonPeck :=
    (ContinuousLinearMap.apply ℝ ℝ y).comp
      canonicalKaltonSwansonForm.toDual.toContinuousLinearMap
  have hFApply (x : CanonicalRealKaltonPeck) :
      F x = canonicalKaltonSwansonForm.toDual x y := rfl
  have hzF :
      Tendsto (fun n => F (z n)) atTop (𝓝 0) := by
    simpa only [hFApply, y, z, b] using
      tendsto_canonical_pairing_apply_block_zero A w hw y
  have heF :
      Tendsto
        (fun n => F
          (z n - canonicalL2Inclusion (a n)))
        atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      (F.continuous.tendsto 0).comp heVec
  have hiF :
      Tendsto
        (fun n => F (canonicalL2Inclusion (a n)))
        atTop (𝓝 0) := by
    have hsub := hzF.sub heF
    convert hsub using 1
    · ext n
      simp only [map_sub]
      ring_nf
    · ring_nf
  simpa only [hFApply, y,
    canonical_pairing_inclusion_secondBasis] using hiF

/-- Every upper semi-Fredholm canonical operator admits an absolutely summable kernel-column
approximation between normalized successive source and target blocks. -/
theorem hasUpperSummableKernelBlockApproximation :
    HasUpperSummableKernelBlockApproximation := by
  intro T hT
  obtain ⟨w, hw, a, δ, B, N₀, hδ, haLower, haUpper, hdSum⟩ :=
    exists_bounded_kernel_approximants T hT
  let A := T.comp canonicalL2Inclusion
  let b : ℕ → CanonicalL2 := fun n =>
    canonicalL2BlockEmbedding w hw (lp.single 2 n (1 : ℝ))
  let z : ℕ → CanonicalRealKaltonPeck := fun n => A (b n)
  let d : ℕ → ℝ := fun n => ‖z n - canonicalL2Inclusion (a n)‖
  have hdZero : Tendsto d atTop (𝓝 0) := hdSum.tendsto_atTop_zero
  let r : ℕ → ℝ := fun n => ‖a (N₀ + n)‖
  have hrange (n : ℕ) : r n ∈ Set.Icc δ B := by
    constructor
    · exact haLower (N₀ + n) (Nat.le_add_right N₀ n)
    · exact haUpper (N₀ + n) (Nat.le_add_right N₀ n)
  obtain ⟨α, hαIcc, φ, hφ, hφConv⟩ :=
    isCompact_Icc.tendsto_subseq hrange
  have hα : 0 < α := hδ.trans_le hαIcc.1
  let ε : ℕ → ℝ := fun n => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp only [ε]
    positivity
  have hεNhds (n : ℕ) : Metric.ball α (ε n) ∈ 𝓝 α :=
    Metric.ball_mem_nhds α (hεpos n)
  obtain ⟨ψ, hψ, hfast⟩ :=
    hφConv.subseq_mem hεNhds
  let κ : ℕ → ℕ := fun n => N₀ + φ (ψ n)
  have hκ : StrictMono κ := by
    exact (hφ.comp hψ).const_add N₀
  have hκN₀ (n : ℕ) : N₀ ≤ κ n :=
    Nat.le_add_right N₀ (φ (ψ n))
  have hnormFast (n : ℕ) :
      |‖a (κ n)‖ - α| < ε n := by
    simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_apply,
      r, κ] using hfast n
  have hεSum : Summable ε := by
    have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    exact hgeom.mul_left (1 / 4 : ℝ)
  have hnormErrorSum :
      Summable (fun n => |‖a (κ n)‖ - α|) := by
    exact Summable.of_nonneg_of_le
      (fun n => abs_nonneg _) (fun n => (hnormFast n).le) hεSum
  have hnormConv :
      Tendsto (fun n => ‖a (κ n)‖) atTop (𝓝 α) := by
    have hcomp := hφConv.comp hψ.tendsto_atTop
    simpa only [Function.comp_def, r, κ] using hcomp
  have heVec :
      Tendsto
        (fun n => z n - canonicalL2Inclusion (a n))
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [d] using hdZero
  have haCoordinateZero (j : ℕ) : Tendsto (fun n => a n j) atTop (𝓝 0) :=
    tendsto_kernel_approximation_coordinates_zero A w hw a heVec j
  let u : ℕ → CanonicalL2 := fun n =>
    ‖a (κ n)‖⁻¹ • a (κ n)
  have haκNormPos (n : ℕ) : 0 < ‖a (κ n)‖ :=
    hδ.trans_le (haLower (κ n) (hκN₀ n))
  have haκNe (n : ℕ) : a (κ n) ≠ 0 :=
    (norm_pos_iff.mp (haκNormPos n))
  have huNorm (n : ℕ) : ‖u n‖ = 1 := by
    change ‖‖a (κ n)‖⁻¹ • a (κ n)‖ = 1
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (haκNormPos n))]
    exact inv_mul_cancel₀ (ne_of_gt (haκNormPos n))
  have hscaleU (n : ℕ) :
      ‖a (κ n)‖ • u n = a (κ n) := by
    change
      ‖a (κ n)‖ •
        (‖a (κ n)‖⁻¹ • a (κ n)) =
          a (κ n)
    rw [smul_smul]
    simp only [mul_inv_cancel₀ (ne_of_gt (haκNormPos n)), one_smul]
  have huCoordinateZero (j : ℕ) :
      Tendsto (fun n => u n j) atTop (𝓝 0) := by
    have hcoordSub :=
      (haCoordinateZero j).comp hκ.tendsto_atTop
    have hinv := hnormConv.inv₀ (ne_of_gt hα)
    have hmul := hinv.mul hcoordSub
    simpa only [u, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      Function.comp_def, mul_zero] using hmul
  obtain ⟨θ, hθ, v, hv, huSum⟩ :=
    exists_summable_successiveBlock_subsequence_approximation
      u huNorm huCoordinateZero
  let idx : ℕ → ℕ := κ ∘ θ
  have hidx : StrictMono idx := hκ.comp hθ
  let w' : ℕ → ℕ → ℝ := fun n => w (idx n)
  let hw' : IsSuccessiveNormalizedBlockSequence w' :=
    IsSuccessiveNormalizedBlockSequence.comp_strictMono hw hidx
  have hsourceBlock (n : ℕ) :
      canonicalL2BlockEmbedding w' hw'
          (lp.single 2 n (1 : ℝ)) =
        b (idx n) := by
    apply Subtype.ext
    funext j
    rw [canonicalL2BlockEmbedding_single_apply,
      canonicalL2BlockEmbedding_single_apply]
  have hsourceOperator (n : ℕ) :
      canonicalBlockOperator w' hw'
          (canonicalFirstBasisVector n) =
        canonicalBlockOperator w hw
          (canonicalFirstBasisVector (idx n)) := by
    apply canonicalRealKaltonPeckPresentation.coordinates_injective
    rw [(canonicalNormalizedBlock w' hw').1 n,
      (canonicalNormalizedBlock w hw).1 (idx n)]
  let V := canonicalBlockOperator v hv
  let Bv := canonicalL2BlockEmbedding v hv
  have htarget (n : ℕ) :
      V (canonicalFirstBasisVector n) =
        canonicalL2Inclusion
          (Bv (lp.single 2 n (1 : ℝ))) := by
    have hmap :=
      DFunLike.congr_fun
        (canonicalBlockOperator_inclusion v hv)
        (lp.single 2 n (1 : ℝ))
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      inclusion_standardBasis] at hmap
    exact hmap
  have hTblock (n : ℕ) :
      T (canonicalBlockOperator w hw
          (canonicalFirstBasisVector n)) =
        z n := by
    have hmap :=
      DFunLike.congr_fun
        (canonicalBlockOperator_inclusion w hw)
        (lp.single 2 n (1 : ℝ))
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      inclusion_standardBasis] at hmap
    rw [hmap]
    rfl
  have hkernelOriginal :
      Summable (fun n =>
        ‖T (canonicalBlockOperator w hw
              (canonicalFirstBasisVector n)) -
          canonicalL2Inclusion (a n)‖) := by
    simpa only [hTblock, d] using hdSum
  have hkernelSub :
      Summable (fun n =>
        ‖T (canonicalBlockOperator w hw
              (canonicalFirstBasisVector (idx n))) -
          canonicalL2Inclusion (a (idx n))‖) := by
    exact hkernelOriginal.comp_injective hidx.injective
  have hnormSub :
      Summable (fun n => |‖a (idx n)‖ - α|) := by
    change Summable
      ((fun n => |‖a (κ n)‖ - α|) ∘ θ)
    exact hnormErrorSum.comp_injective hθ.injective
  have happroxSub :
      Summable (fun n =>
        ‖u (θ n) -
          Bv (lp.single 2 n (1 : ℝ))‖) := by
    simpa only [Bv] using huSum
  let majorant : ℕ → ℝ := fun n =>
    ‖T (canonicalBlockOperator w hw
          (canonicalFirstBasisVector (idx n))) -
        canonicalL2Inclusion (a (idx n))‖ +
      ‖canonicalL2Inclusion‖ * |‖a (idx n)‖ - α| +
      (|α| * ‖canonicalL2Inclusion‖) *
        ‖u (θ n) -
          Bv (lp.single 2 n (1 : ℝ))‖
  have hmajorant : Summable majorant := by
    dsimp only [majorant]
    exact
      (hkernelSub.add
          (hnormSub.mul_left ‖canonicalL2Inclusion‖)).add
        (happroxSub.mul_left
          (|α| * ‖canonicalL2Inclusion‖))
  refine ⟨w', v, hw', hv, α, ne_of_gt hα, ?_⟩
  apply Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => ?_) hmajorant
  rw [hsourceOperator]
  let an : CanonicalL2 := a (idx n)
  let un : CanonicalL2 := u (θ n)
  let vn : CanonicalL2 :=
    Bv (lp.single 2 n (1 : ℝ))
  have hidxApply : idx n = κ (θ n) := rfl
  have hanPos : 0 < ‖an‖ := by
    dsimp only [an]
    rw [hidxApply]
    exact haκNormPos (θ n)
  have hanUn : an = ‖an‖ • un := by
    dsimp only [an, un]
    rw [hidxApply]
    exact (hscaleU (θ n)).symm
  have hunNorm : ‖un‖ = 1 :=
    huNorm (θ n)
  rw [htarget]
  exact norm_sub_smul_image_le canonicalL2Inclusion an un vn α
    (T (canonicalBlockOperator w hw (canonicalFirstBasisVector (idx n)))) hanUn hunNorm

/-- An absolutely summable canonical kernel-block approximation supplies exactly the retained
upper factorization used by the compact-Gram contradiction. -/
theorem hasUpperCompactGramFactorization_of_summableKernelBlockApproximation
    (hBlock : HasUpperSummableKernelBlockApproximation) :
    HasUpperCompactGramFactorization := by
  intro T hT
  obtain ⟨w, v, hw, hv, α, hα, hsum⟩ := hBlock T hT
  let W := canonicalBlockOperator w hw
  let V := canonicalBlockOperator v hv
  let iw := canonicalL2BlockEmbedding w hw
  let iv := canonicalL2BlockEmbedding v hv
  let e : ℕ → CanonicalRealKaltonPeck := fun n =>
    T (W (canonicalFirstBasisVector n)) -
      α • V (canonicalFirstBasisVector n)
  have he : Summable (fun n => ‖e n‖) := by
    simpa only [e, W, V] using hsum
  obtain ⟨K, hK, hKadj, hKbasis⟩ :=
    exists_compact_biadjoint_kernelCorrection e he
  let R : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck :=
    T.comp W - α • V - K
  have hRi : R.comp canonicalL2Inclusion = 0 := by
    apply continuousLinearMap_ext_factorizationL2Basis
    intro n
    rw [zero_apply]
    change R (canonicalL2Inclusion (factorizationL2Basis n)) = 0
    rw [inclusion_factorizationL2Basis]
    change
      T (W (canonicalFirstBasisVector n)) -
          α • V (canonicalFirstBasisVector n) -
        K (canonicalFirstBasisVector n) = 0
    rw [hKbasis n]
    dsimp only [e]
    abel
  refine ⟨W, V, R, K, iw, iv, α, hα, ?_, ?_, ?_, ?_, hRi, hK, hKadj⟩
  · exact canonicalBlockOperator_inclusion w hw
  · exact canonicalBlockOperator_inclusion v hv
  · exact (canonicalNormalizedBlock v hv).2.2.2.2.2.1
  · dsimp only [R]
    abel

/-- The retained-output block factorization forces the Gram restriction of every upper
semi-Fredholm operator to be noncompact. -/
theorem upperSemi_gramKernel_not_compact_of_factorization
    (hFactor : HasUpperCompactGramFactorization)
    (T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hT : IsUpperSemiFredholm T) :
    ¬ IsCompactOperator
      ((canonicalKaltonSwansonForm.adjoint T * T).comp
        canonicalL2Inclusion) := by
  intro hGramCompact
  obtain ⟨W, V, R, K, iw, iv, α, hα, hWi, hVi, hVgram, hfactor,
    hRi, hK, hKadj⟩ := hFactor T hT
  let G := canonicalKaltonSwansonForm.adjoint T * T
  let C := T.comp W
  have hConjugatedCompact :
      IsCompactOperator
        (((canonicalKaltonSwansonForm.adjoint W).comp (G.comp W)).comp
          canonicalL2Inclusion) := by
    have hright :
        (G.comp W).comp canonicalL2Inclusion =
          (G.comp canonicalL2Inclusion).comp iw := by
      rw [ContinuousLinearMap.comp_assoc, hWi,
        ← ContinuousLinearMap.comp_assoc]
    rw [ContinuousLinearMap.comp_assoc, hright]
    exact (hGramCompact.comp_clm iw).clm_comp
      (canonicalKaltonSwansonForm.adjoint W)
  have hConjugatedEq :
      ((canonicalKaltonSwansonForm.adjoint W).comp (G.comp W)).comp
          canonicalL2Inclusion =
        (canonicalKaltonSwansonForm.adjoint C * C).comp
          canonicalL2Inclusion := by
    have hcore :
        (canonicalKaltonSwansonForm.adjoint W).comp (G.comp W) =
          canonicalKaltonSwansonForm.adjoint C * C := by
      calc
        (canonicalKaltonSwansonForm.adjoint W).comp (G.comp W) =
            canonicalKaltonSwansonForm.adjoint (T * W) * (T * W) := by
          rw [Forms.adjoint_mul]
          ext x
          rfl
        _ = canonicalKaltonSwansonForm.adjoint C * C := by rfl
    rw [hcore]
  have hCfactor : C = α • V + R + K := hfactor
  have hVK :
      IsCompactOperator
        ((canonicalKaltonSwansonForm.adjoint V * K).comp
          canonicalL2Inclusion) := by
    exact (hK.comp_clm canonicalL2Inclusion).clm_comp
      (canonicalKaltonSwansonForm.adjoint V)
  have hRK :
      IsCompactOperator
        ((canonicalKaltonSwansonForm.adjoint R * K).comp
          canonicalL2Inclusion) := by
    exact (hK.comp_clm canonicalL2Inclusion).clm_comp
      (canonicalKaltonSwansonForm.adjoint R)
  have hKV :
      IsCompactOperator
        ((canonicalKaltonSwansonForm.adjoint K * V).comp
          canonicalL2Inclusion) := by
    exact hKadj.comp_clm (V.comp canonicalL2Inclusion)
  have hKK :
      IsCompactOperator
        ((canonicalKaltonSwansonForm.adjoint K * K).comp
          canonicalL2Inclusion) := by
    exact (hK.comp_clm canonicalL2Inclusion).clm_comp
      (canonicalKaltonSwansonForm.adjoint K)
  obtain ⟨L, hRL⟩ :=
    canonical_factor_through_quotient R hRi
  have hqLStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        (canonicalL2Quotient.comp L) :=
    canonicalL2Quotient_isStrictlySingular.precomp L
  have hqLAdjointStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        (ContinuousLinearMap.adjoint
          (canonicalL2Quotient.comp L)) :=
    hqLStrict.hilbert_adjoint
  have hRVFormula :=
    canonical_remainderAdjoint_kernel_formula R V L iv hRL hVi
  have hRVStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((canonicalKaltonSwansonForm.adjoint R * V).comp
          canonicalL2Inclusion) := by
    rw [hRVFormula]
    exact
      (hqLAdjointStrict.precomp iv).postcomp
        canonicalL2Inclusion
  let E : CanonicalL2 →L[ℝ] CanonicalRealKaltonPeck :=
    ((α • ((canonicalKaltonSwansonForm.adjoint V * K).comp
        canonicalL2Inclusion) +
      α • ((canonicalKaltonSwansonForm.adjoint R * V).comp
        canonicalL2Inclusion) +
      ((canonicalKaltonSwansonForm.adjoint R * K).comp
        canonicalL2Inclusion)) +
      (α • ((canonicalKaltonSwansonForm.adjoint K * V).comp
        canonicalL2Inclusion) +
      ((canonicalKaltonSwansonForm.adjoint K * K).comp
        canonicalL2Inclusion)))
  have hVKStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((canonicalKaltonSwansonForm.adjoint V * K).comp
          canonicalL2Inclusion) :=
    isStrictlySingular_of_isCompactOperator _ hVK
  have hRKStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((canonicalKaltonSwansonForm.adjoint R * K).comp
          canonicalL2Inclusion) :=
    isStrictlySingular_of_isCompactOperator _ hRK
  have hKVStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((canonicalKaltonSwansonForm.adjoint K * V).comp
          canonicalL2Inclusion) :=
    isStrictlySingular_of_isCompactOperator _ hKV
  have hKKStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((canonicalKaltonSwansonForm.adjoint K * K).comp
          canonicalL2Inclusion) :=
    isStrictlySingular_of_isCompactOperator _ hKK
  have hEStrict :
      IsStrictlySingular.{0, 0, 0, 0} E :=
    (((hVKStrict.smul α).add (hRVStrict.smul α)).add hRKStrict).add
      ((hKVStrict.smul α).add hKKStrict)
  have hExpand :
      (canonicalKaltonSwansonForm.adjoint C * C).comp
          canonicalL2Inclusion =
        (α ^ 2) • canonicalL2Inclusion + E := by
    rw [hCfactor, Forms.adjoint_add, Forms.adjoint_add,
      Forms.adjoint_smul]
    ext x
    have hRix : R (canonicalL2Inclusion x) = 0 :=
      DFunLike.congr_fun hRi x
    have hVgramx :
        (canonicalKaltonSwansonForm.adjoint V)
            (V (canonicalL2Inclusion x)) =
          canonicalL2Inclusion x :=
      DFunLike.congr_fun hVgram (canonicalL2Inclusion x)
    simp only [E, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      mul_apply_eq_comp, map_add, map_smul, hRix,
      hVgramx, add_zero]
    rw [pow_two]
    module
  have hConjugatedStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        (((canonicalKaltonSwansonForm.adjoint W).comp
          (G.comp W)).comp canonicalL2Inclusion) :=
    isStrictlySingular_of_isCompactOperator _ hConjugatedCompact
  have hsumStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((α ^ 2) • canonicalL2Inclusion + E) := by
      rw [← hExpand, ← hConjugatedEq]
      exact hConjugatedStrict
  have hScalarStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((α ^ 2) • canonicalL2Inclusion) := by
    have hdiff := hsumStrict.add hEStrict.neg
    have heq :
        ((α ^ 2) • canonicalL2Inclusion + E) + -E =
          (α ^ 2) • canonicalL2Inclusion := by
      ext x
      simp
    rw [heq] at hdiff
    exact hdiff
  have hαsq : α ^ 2 ≠ 0 := pow_ne_zero _ hα
  have hInclusionStrict :
      IsStrictlySingular.{0, 0, 0, 0} canonicalL2Inclusion := by
    have hrescale :
        (α ^ 2)⁻¹ • ((α ^ 2) • canonicalL2Inclusion) =
          canonicalL2Inclusion := by
      ext x
      simp [hαsq]
    rw [← hrescale]
    exact hScalarStrict.smul (α ^ 2)⁻¹
  have hInclusionUpper : IsUpperSemiFredholm canonicalL2Inclusion := by
    constructor
    · have hker : canonicalL2Inclusion.toLinearMap.ker = ⊥ :=
        LinearMap.ker_eq_bot.mpr canonicalL2Inclusion_injective
      rw [hker]
      infer_instance
    · rw [canonicalL2Inclusion_range]
      exact canonicalL2Quotient.isClosed_ker
  exact
    (hInclusionUpper.not_isStrictlySingular
      canonicalL2_not_finiteDimensional) hInclusionStrict

/-- A self-adjoint upper semi-Fredholm operator on a strongly symplectic Banach space is
Fredholm. -/
private theorem isFredholmOfUpperSemiOfAdjointEq
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (ω : StrongSymplecticForm X) (B : X →L[ℝ] X)
    (hB : IsUpperSemiFredholm B) (hself : ω.adjoint B = B) : IsFredholm B := by
  let : FiniteDimensional ℝ B.toLinearMap.ker := hB.1
  let : IsClosed (B.toLinearMap.range : Set X) := hB.2
  let kernelToAnnihilator :
      B.toLinearMap.ker →ₗ[ℝ] Forms.continuousAnnihilator B.toLinearMap.range :=
    { toFun := fun x => ⟨ω.toDual (x : X), by
          change ((ContinuousLinearMap.compL ℝ B.toLinearMap.range X ℝ).flip
            B.toLinearMap.range.subtypeL) (ω.toDual (x : X)) = 0
          apply ContinuousLinearMap.ext
          rintro ⟨_, y, rfl⟩
          change ω.toDual (x : X) (B y) = 0
          rw [← Forms.adjoint_apply, hself]
          have hx : B (x : X) = 0 := x.property
          rw [hx, map_zero]
          rfl⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact ω.toDual.map_add (x : X) (y : X)
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact ω.toDual.map_smul c (x : X) }
  have hInjective : Function.Injective kernelToAnnihilator := by
    intro x y hxy
    apply Subtype.ext
    apply ω.toDual.injective
    exact congrArg Subtype.val hxy
  have hSurjective : Function.Surjective kernelToAnnihilator := by
    intro φ
    let x : X := ω.toDual.symm (φ : StrongDual ℝ X)
    have hx : x ∈ B.toLinearMap.ker := by
      change B x = 0
      apply ω.toDual.injective
      apply ContinuousLinearMap.ext
      intro y
      simp only [map_zero, zero_apply]
      change ω.toDual (B x) y = 0
      rw [← hself, Forms.adjoint_apply]
      rw [show ω.toDual x = (φ : StrongDual ℝ X) by
        exact ω.toDual.apply_symm_apply (φ : StrongDual ℝ X)]
      have hφ := φ.property
      change ((ContinuousLinearMap.compL ℝ B.toLinearMap.range X ℝ).flip
        B.toLinearMap.range.subtypeL) (φ : StrongDual ℝ X) = 0 at hφ
      exact DFunLike.congr_fun hφ ⟨B y, ⟨y, rfl⟩⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact ω.toDual.apply_symm_apply (φ : StrongDual ℝ X)
  let kernelAnnihilatorEquiv :
      B.toLinearMap.ker ≃ₗ[ℝ] Forms.continuousAnnihilator B.toLinearMap.range :=
    LinearEquiv.ofBijective kernelToAnnihilator ⟨hInjective, hSurjective⟩
  let : FiniteDimensional ℝ (Forms.continuousAnnihilator B.toLinearMap.range) :=
    kernelAnnihilatorEquiv.finiteDimensional
  let quotientDualEquiv :
      StrongDual ℝ (X ⧸ B.toLinearMap.range) ≃ₗ[ℝ]
        Forms.continuousAnnihilator B.toLinearMap.range :=
    (Forms.quotientDualEquivAnnihilator B.toLinearMap.range).toLinearEquiv
  let : FiniteDimensional ℝ (StrongDual ℝ (X ⧸ B.toLinearMap.range)) :=
    @LinearEquiv.finiteDimensional ℝ
      (Forms.continuousAnnihilator B.toLinearMap.range) _ _ _
      (StrongDual ℝ (X ⧸ B.toLinearMap.range)) _ _
      quotientDualEquiv.symm inferInstance
  have hCokernel : FiniteDimensional ℝ (X ⧸ B.toLinearMap.range) :=
    FiniteDimensional.of_injective
      (NormedSpace.inclusionInDoubleDual ℝ (X ⧸ B.toLinearMap.range)).toLinearMap
      (NormedSpace.inclusionInDoubleDualLi ℝ).injective
  exact ⟨hB.1, hB.2, hCokernel⟩

/-- The formal operator-theoretic reduction in CGP Lemma 5.4. Its three hypotheses are precisely
Proposition 5.3(c), Proposition 5.3(b), and Proposition 5.3(a), respectively.
Blueprint label: `lem:cgp-primary-reduction`. -/
theorem canonicalGram_isUpperSemiFredholm_of_cgpPropositions
    (hUpper :
      ∀ T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
        IsUpperSemiFredholm (T.comp canonicalL2Inclusion) →
          IsUpperSemiFredholm T)
    (hRestriction :
      ∀ T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
        IsStrictlySingular.{0, 0, 0, 0}
            (T.comp canonicalL2Inclusion) →
          IsStrictlySingular.{0, 0, 0, 0} T)
    (hGram :
      ∀ T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
        IsStrictlySingular.{0, 0, 0, 0}
            (canonicalKaltonSwansonForm.adjoint T * T) →
          IsStrictlySingular.{0, 0, 0, 0} T)
    (A : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hA : IsUpperSemiFredholm A) :
    IsUpperSemiFredholm (canonicalKaltonSwansonForm.adjoint A * A) := by
  let B := canonicalKaltonSwansonForm.adjoint A * A
  change IsUpperSemiFredholm B
  by_contra hB
  have hBi :
      ¬ IsUpperSemiFredholm (B.comp canonicalL2Inclusion) := by
    intro hBi
    exact hB (hUpper B hBi)
  obtain ⟨w, hw, hcompact⟩ :=
    CgpBlockExtraction.exists_compact_canonicalL2Block_of_not_upperSemi
      (B.comp canonicalL2Inclusion) hBi
  let W := canonicalBlockOperator w hw
  let i_w := canonicalL2BlockEmbedding w hw
  have hintertwines :
      W.comp canonicalL2Inclusion = canonicalL2Inclusion.comp i_w := by
    exact canonicalBlockOperator_inclusion w hw
  have hrestriction :
      (B.comp W).comp canonicalL2Inclusion =
        (B.comp canonicalL2Inclusion).comp i_w := by
    rw [ContinuousLinearMap.comp_assoc, hintertwines,
      ← ContinuousLinearMap.comp_assoc]
  have hBWiCompact :
      IsCompactOperator ((B.comp W).comp canonicalL2Inclusion) := by
    rw [hrestriction]
    exact hcompact
  have hBWiStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((B.comp W).comp canonicalL2Inclusion) :=
    isStrictlySingular_of_isCompactOperator _ hBWiCompact
  have hBWStrict : IsStrictlySingular.{0, 0, 0, 0} (B.comp W) :=
    hRestriction (B.comp W) hBWiStrict
  have hconjugateStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        ((canonicalKaltonSwansonForm.adjoint W).comp (B.comp W)) :=
    hBWStrict.postcomp (canonicalKaltonSwansonForm.adjoint W)
  have hGramEq :
      canonicalKaltonSwansonForm.adjoint (A.comp W) * (A.comp W) =
        (canonicalKaltonSwansonForm.adjoint W).comp (B.comp W) := by
    change
      canonicalKaltonSwansonForm.adjoint (A * W) * (A * W) =
        canonicalKaltonSwansonForm.adjoint W * (B * W)
    rw [Forms.adjoint_mul]
    simp only [B, mul_assoc]
  have hAWGramStrict :
      IsStrictlySingular.{0, 0, 0, 0}
        (canonicalKaltonSwansonForm.adjoint (A.comp W) * (A.comp W)) := by
    rw [hGramEq]
    exact hconjugateStrict
  have hAWStrict : IsStrictlySingular.{0, 0, 0, 0} (A.comp W) :=
    hGram (A.comp W) hAWGramStrict
  have hWUpper : IsUpperSemiFredholm W :=
    canonicalBlockOperator_isUpperSemiFredholm w hw
  have hAWUpper : IsUpperSemiFredholm (A.comp W) :=
    hWUpper.comp hA
  exact
    (hAWUpper.not_isStrictlySingular
      canonicalRealKaltonPeck_not_finiteDimensional) hAWStrict

/-- A target-specific CGP reduction which avoids the global strictly-singular Proposition 5.3
calculus. It needs only the upper-semi restriction implication and noncompactness of the Gram
restriction for upper semi-Fredholm operators.
Blueprint label: `lem:cgp-primary-reduction`. -/
theorem canonicalGram_isUpperSemiFredholm_of_upperRestriction_and_noncompactGram
    (hUpper :
      ∀ T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
        IsUpperSemiFredholm (T.comp canonicalL2Inclusion) →
          IsUpperSemiFredholm T)
    (hUpperGramKernelNoncompact :
      ∀ T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
        IsUpperSemiFredholm T →
          ¬ IsCompactOperator
            ((canonicalKaltonSwansonForm.adjoint T * T).comp
              canonicalL2Inclusion))
    (A : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hA : IsUpperSemiFredholm A) :
    IsUpperSemiFredholm (canonicalKaltonSwansonForm.adjoint A * A) := by
  let B := canonicalKaltonSwansonForm.adjoint A * A
  change IsUpperSemiFredholm B
  by_contra hB
  have hBi :
      ¬ IsUpperSemiFredholm (B.comp canonicalL2Inclusion) := by
    intro hBi
    exact hB (hUpper B hBi)
  obtain ⟨w, hw, hcompact⟩ :=
    CgpBlockExtraction.exists_compact_canonicalL2Block_of_not_upperSemi
      (B.comp canonicalL2Inclusion) hBi
  let W := canonicalBlockOperator w hw
  let i_w := canonicalL2BlockEmbedding w hw
  have hintertwines :
      W.comp canonicalL2Inclusion = canonicalL2Inclusion.comp i_w :=
    canonicalBlockOperator_inclusion w hw
  have hrestriction :
      (B.comp W).comp canonicalL2Inclusion =
        (B.comp canonicalL2Inclusion).comp i_w := by
    rw [ContinuousLinearMap.comp_assoc, hintertwines,
      ← ContinuousLinearMap.comp_assoc]
  have hBWiCompact :
      IsCompactOperator ((B.comp W).comp canonicalL2Inclusion) := by
    rw [hrestriction]
    exact hcompact
  let T := A.comp W
  have hWUpper : IsUpperSemiFredholm W :=
    canonicalBlockOperator_isUpperSemiFredholm w hw
  have hTUpper : IsUpperSemiFredholm T :=
    hWUpper.comp hA
  have hGramEq :
      canonicalKaltonSwansonForm.adjoint T * T =
        (canonicalKaltonSwansonForm.adjoint W).comp (B.comp W) := by
    change
      canonicalKaltonSwansonForm.adjoint (A * W) * (A * W) =
        canonicalKaltonSwansonForm.adjoint W * (B * W)
    rw [Forms.adjoint_mul]
    simp only [B, mul_assoc]
  have hGramKernelCompact :
      IsCompactOperator
        ((canonicalKaltonSwansonForm.adjoint T * T).comp
          canonicalL2Inclusion) := by
    rw [hGramEq, ContinuousLinearMap.comp_assoc]
    exact hBWiCompact.clm_comp (canonicalKaltonSwansonForm.adjoint W)
  exact (hUpperGramKernelNoncompact T hTUpper) hGramKernelCompact

/-- The target-minimal compact-block extraction statement: failure of upper
semi-Fredholmness already produces a compact canonical Hilbert-kernel block. -/
def HasCanonicalKernelCompactBlockExtraction : Prop :=
  ∀ B : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
    ¬ IsUpperSemiFredholm B →
      ∃ w : ℕ → ℕ → ℝ,
        ∃ hw : IsSuccessiveNormalizedBlockSequence w,
          IsCompactOperator
            ((B.comp canonicalL2Inclusion).comp
              (canonicalL2BlockEmbedding w hw))

/-- The corrected compact perturbation argument in CGP Proposition 5.3(c), combined with
canonical Hilbert block extraction, establishes the target-minimal compact-block premise. -/
theorem hasCanonicalKernelCompactBlockExtraction :
    HasCanonicalKernelCompactBlockExtraction := by
  intro B hB
  exact
    Canonical.exists_compact_canonicalL2Block_of_not_upper
      canonicalL2Quotient_isStrictlySingular B hB

/-- The shortest formal CGP reduction: compact block extraction for a failed Gram operator and
noncompactness of Gram restrictions for upper semi-Fredholm operators suffice. -/
theorem canonicalGram_isUpperSemiFredholm_of_compactBlock_and_noncompactGram
    (hExtract : HasCanonicalKernelCompactBlockExtraction)
    (hUpperGramKernelNoncompact :
      ∀ T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck,
        IsUpperSemiFredholm T →
          ¬ IsCompactOperator
            ((canonicalKaltonSwansonForm.adjoint T * T).comp
              canonicalL2Inclusion))
    (A : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hA : IsUpperSemiFredholm A) :
    IsUpperSemiFredholm (canonicalKaltonSwansonForm.adjoint A * A) := by
  let B := canonicalKaltonSwansonForm.adjoint A * A
  change IsUpperSemiFredholm B
  by_contra hB
  obtain ⟨w, hw, hcompact⟩ := hExtract B hB
  let W := canonicalBlockOperator w hw
  let i_w := canonicalL2BlockEmbedding w hw
  have hintertwines :
      W.comp canonicalL2Inclusion = canonicalL2Inclusion.comp i_w :=
    canonicalBlockOperator_inclusion w hw
  have hrestriction :
      (B.comp W).comp canonicalL2Inclusion =
        (B.comp canonicalL2Inclusion).comp i_w := by
    rw [ContinuousLinearMap.comp_assoc, hintertwines,
      ← ContinuousLinearMap.comp_assoc]
  have hBWiCompact :
      IsCompactOperator ((B.comp W).comp canonicalL2Inclusion) := by
    rw [hrestriction]
    exact hcompact
  let T := A.comp W
  have hWUpper : IsUpperSemiFredholm W :=
    canonicalBlockOperator_isUpperSemiFredholm w hw
  have hTUpper : IsUpperSemiFredholm T :=
    hWUpper.comp hA
  have hGramEq :
      canonicalKaltonSwansonForm.adjoint T * T =
        (canonicalKaltonSwansonForm.adjoint W).comp (B.comp W) := by
    change
      canonicalKaltonSwansonForm.adjoint (A * W) * (A * W) =
        canonicalKaltonSwansonForm.adjoint W * (B * W)
    rw [Forms.adjoint_mul]
    simp only [B, mul_assoc]
  have hGramKernelCompact :
      IsCompactOperator
        ((canonicalKaltonSwansonForm.adjoint T * T).comp
          canonicalL2Inclusion) := by
    rw [hGramEq, ContinuousLinearMap.comp_assoc]
    exact hBWiCompact.clm_comp (canonicalKaltonSwansonForm.adjoint W)
  exact (hUpperGramKernelNoncompact T hTUpper) hGramKernelCompact

/-- The two retained target-specific source inputs imply the Gram upper-semi conclusion. -/
theorem canonicalGram_isUpperSemiFredholm_of_targetFactorizations
    (hExtract : HasCanonicalKernelCompactBlockExtraction)
    (hFactor : HasUpperCompactGramFactorization)
    (A : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hA : IsUpperSemiFredholm A) :
    IsUpperSemiFredholm (canonicalKaltonSwansonForm.adjoint A * A) :=
  canonicalGram_isUpperSemiFredholm_of_compactBlock_and_noncompactGram
    hExtract (upperSemi_gramKernel_not_compact_of_factorization hFactor) A hA

/-- The pinned canonical Castillo--González--Pino theorem (arXiv:2207.01069v1, Lemma 5.4).
Blueprint label: `thm:cgp-primary`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem cgpPrimary (A : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hA : IsUpperSemiFredholm A) :
    IsFredholm (canonicalKaltonSwansonForm.adjoint A * A) := by
  apply isFredholmOfUpperSemiOfAdjointEq canonicalKaltonSwansonForm
  · exact
      canonicalGram_isUpperSemiFredholm_of_targetFactorizations
        hasCanonicalKernelCompactBlockExtraction
        (hasUpperCompactGramFactorization_of_summableKernelBlockApproximation
          hasUpperSummableKernelBlockApproximation)
        A hA
  · rw [Forms.adjoint_mul, Forms.adjoint_involutive]

/-- The CGP theorem transported to an arbitrary complete presented real Kalton--Peck model.
Blueprint label: `thm:cgp-transport`; audit ID `EXT-CGP-UPPER-SEMI`. -/
theorem cgpTransport {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (A : X →L[ℝ] X)
    (hA : IsUpperSemiFredholm A) :
    IsFredholm ((transportedKaltonSwansonForm hX).adjoint A * A) := by
  let e := presentationEquiv hX canonicalRealKaltonPeckPresentation
  let Acan : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck :=
    e.toContinuousLinearMap.comp (A.comp e.symm.toContinuousLinearMap)
  have hAcan : IsUpperSemiFredholm Acan := by
    constructor
    · let : FiniteDimensional ℝ A.toLinearMap.ker := hA.1
      exact (Fredholm.kernelEquivOfEquivComp A e e.symm).symm.finiteDimensional
    · have hrange : (Acan.toLinearMap.range : Set CanonicalRealKaltonPeck) =
          e '' (A.toLinearMap.range : Set X) := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨A (e.symm x), ⟨e.symm x, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
          exact ⟨e x, by simp [Acan]⟩
      rw [hrange]
      exact e.toHomeomorph.isClosedMap _ hA.2
  let ω := transportedKaltonSwansonForm hX
  have hadj : canonicalKaltonSwansonForm.adjoint Acan =
      e.toContinuousLinearMap.comp ((ω.adjoint A).comp e.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    apply canonicalKaltonSwansonForm.toDual.injective
    apply ContinuousLinearMap.ext
    intro w
    rw [Forms.adjoint_apply]
    change canonicalKaltonSwansonForm.toDual z (Acan w) =
      canonicalKaltonSwansonForm.toDual (e (ω.adjoint A (e.symm z))) w
    calc
      canonicalKaltonSwansonForm.toDual z (Acan w) =
          ω.toDual (e.symm z) (A (e.symm w)) := by
            simp [ω, Acan, e, transportedKaltonSwansonForm_apply]
      _ = ω.toDual (ω.adjoint A (e.symm z)) (e.symm w) := by
        rw [Forms.adjoint_apply]
      _ = canonicalKaltonSwansonForm.toDual (e (ω.adjoint A (e.symm z))) w := by
        simp [ω, e, transportedKaltonSwansonForm_apply]
  let B : X →L[ℝ] X := ω.adjoint A * A
  have hconj : e.toContinuousLinearMap.comp (B.comp e.symm.toContinuousLinearMap) =
      canonicalKaltonSwansonForm.adjoint Acan * Acan := by
    rw [hadj]
    ext z
    simp [B, Acan]
  have hcanonical := cgpPrimary Acan hAcan
  rw [← hconj] at hcanonical
  exact (Fredholm.isFredholm_equiv_comp B e e.symm).mpr hcanonical

/-- The normalized sequence `n ↦ e₂ₙ`.
Support definition for blueprint label `lem:even-odd-blocks`. -/
def evenBlockSequence : ℕ → ℕ → ℝ := by
  exact fun n ↦ standardBasisSequence (2 * n)

/-- The normalized sequence `n ↦ e₂ₙ₊₁`.
Support definition for blueprint label `lem:even-odd-blocks`. -/
def oddBlockSequence : ℕ → ℕ → ℝ := by
  exact fun n ↦ standardBasisSequence (2 * n + 1)

/-- The even and odd sequences are successive normalized blocks and mutually support-disjoint.
Support theorem for blueprint label `lem:even-odd-blocks`. -/
theorem evenOddBlockSequences :
    IsSuccessiveNormalizedBlockSequence evenBlockSequence ∧
      IsSuccessiveNormalizedBlockSequence oddBlockSequence ∧
        AreMutuallySupportDisjoint evenBlockSequence oddBlockSequence := by
  have hnorm (a : ℕ) : l2Norm (standardBasisSequence a) = 1 := by
    rw [l2Norm, tsum_eq_single a]
    · simp [standardBasisSequence]
    · intro k hk
      simp [standardBasisSequence, hk]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro n
      constructor
      · rw [show {k | evenBlockSequence n k ≠ 0} = {2 * n} by
            ext k
            simp [evenBlockSequence, standardBasisSequence]]
        exact Set.finite_singleton (2 * n)
      · refine ⟨2 * n, ?_⟩
        simp [evenBlockSequence, standardBasisSequence]
    · intro n
      exact hnorm (2 * n)
    · intro n i j hi hj
      have hi' : i = 2 * n := by
        by_contra h
        simp [evenBlockSequence, standardBasisSequence, h] at hi
      have hj' : j = 2 * (n + 1) := by
        by_contra h
        simp [evenBlockSequence, standardBasisSequence, h] at hj
      omega
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro n
      constructor
      · rw [show {k | oddBlockSequence n k ≠ 0} = {2 * n + 1} by
            ext k
            simp [oddBlockSequence, standardBasisSequence]]
        exact Set.finite_singleton (2 * n + 1)
      · refine ⟨2 * n + 1, ?_⟩
        simp [oddBlockSequence, standardBasisSequence]
    · intro n
      exact hnorm (2 * n + 1)
    · intro n i j hi hj
      have hi' : i = 2 * n + 1 := by
        by_contra h
        simp [oddBlockSequence, standardBasisSequence, h] at hi
      have hj' : j = 2 * (n + 1) + 1 := by
        by_contra h
        simp [oddBlockSequence, standardBasisSequence, h] at hj
      omega
  intro n m
  rw [Set.disjoint_left]
  intro k hkEven hkOdd
  have hkEven' : k = 2 * n := by
    by_contra h
    simp [evenBlockSequence, standardBasisSequence, h] at hkEven
  have hkOdd' : k = 2 * m + 1 := by
    by_contra h
    simp [oddBlockSequence, standardBasisSequence, h] at hkOdd
  omega

/-- The transported even-coordinate block embedding.
Support definition for blueprint label `lem:even-odd-blocks`. -/
def evenBlockEmbedding {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) : X →L[ℝ] X := by
  exact transportedBlockOperator hX evenBlockSequence evenOddBlockSequences.1

/-- The transported odd-coordinate block embedding.
Support definition for blueprint label `lem:even-odd-blocks`. -/
def oddBlockEmbedding {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) : X →L[ℝ] X := by
  exact transportedBlockOperator hX oddBlockSequence evenOddBlockSequences.2.1

/-- The graph operator `R₀ + R₁T` on a presented model.
Support definition for blueprint labels `lem:even-odd-blocks` and `prop:graph-fredholm`. -/
def graphBlockOperator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) :
    X →L[ℝ] X := by
  exact evenBlockEmbedding hX + oddBlockEmbedding hX * T

/-- The four even--odd adjoint relations and the two graph-operator identities.
Blueprint label: `lem:even-odd-blocks`; audit IDs `HID-EVEN-ODD-BLOCK-RELATIONS`,
`HID-LEFT-INVERSE-UPPER-SEMI`, and `HID-ADJOINT-EXPANSION`. -/
theorem evenOddBlocks {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) :
    let ω := transportedKaltonSwansonForm hX
    let R₀ := evenBlockEmbedding hX
    let R₁ := oddBlockEmbedding hX
    ω.adjoint R₀ * R₀ = 1 ∧
      ω.adjoint R₁ * R₁ = 1 ∧
      ω.adjoint R₀ * R₁ = 0 ∧
      ω.adjoint R₁ * R₀ = 0 ∧
      ∀ T : X →L[ℝ] X,
        let W := graphBlockOperator hX T
        ω.adjoint R₀ * W = 1 ∧
          ω.adjoint W * W = 1 + ω.adjoint T * T ∧ IsUpperSemiFredholm W := by
  dsimp only
  let ω := transportedKaltonSwansonForm hX
  let R₀ := evenBlockEmbedding hX
  let R₁ := oddBlockEmbedding hX
  have he := transportedNormalizedBlock hX evenBlockSequence evenOddBlockSequences.1
  have ho := transportedNormalizedBlock hX oddBlockSequence evenOddBlockSequences.2.1
  have h₀₀ : ω.adjoint R₀ * R₀ = 1 := by
    simpa [ω, R₀, evenBlockEmbedding] using he.2.2.2.2.1
  have h₁₁ : ω.adjoint R₁ * R₁ = 1 := by
    simpa [ω, R₁, oddBlockEmbedding] using ho.2.2.2.2.1
  have hcross : ω.adjoint R₀ * R₁ = 0 ∧ ω.adjoint R₁ * R₀ = 0 := by
    simpa [ω, R₀, R₁, evenBlockEmbedding, oddBlockEmbedding] using
      (he.2.2.2.2.2.2.2 oddBlockSequence evenOddBlockSequences.2.1
        evenOddBlockSequences.2.2)
  refine ⟨h₀₀, h₁₁, hcross.1, hcross.2, ?_⟩
  intro T
  let W := graphBlockOperator hX T
  have hleft : ω.adjoint R₀ * W = 1 := by
    rw [show W = R₀ + R₁ * T by rfl, mul_add, h₀₀]
    rw [← mul_assoc, hcross.1, zero_mul, add_zero]
  have hadj : ω.adjoint W * W = 1 + ω.adjoint T * T := by
    rw [show W = R₀ + R₁ * T by rfl]
    rw [Forms.adjoint_add, Forms.adjoint_mul]
    rw [mul_add, add_mul, add_mul]
    rw [h₀₀, ← mul_assoc, hcross.1, zero_mul]
    rw [mul_assoc (ω.adjoint T) (ω.adjoint R₁) R₀, hcross.2, mul_zero]
    rw [mul_assoc (ω.adjoint T) (ω.adjoint R₁) (R₁ * T)]
    rw [← mul_assoc (ω.adjoint R₁) R₁ T, h₁₁, one_mul]
    simp
  refine ⟨hleft, hadj, ?_⟩
  have hWleft : W.HasLeftInverse := by
    refine ⟨ω.adjoint R₀, ?_⟩
    intro x
    change (ω.adjoint R₀ * W) x = x
    rw [hleft]
    rfl
  have hkernelRange := Fredholm.leftInverseKernelRange W hWleft
  change IsUpperSemiFredholm W
  exact ⟨hkernelRange.2.1, hkernelRange.2.2⟩

/-- Every graph operator `I + T⁺T` on a complete presented real Kalton--Peck model is Fredholm.
Blueprint label: `prop:graph-fredholm`; audit ID `PROP-GRAPH-FREDHOLM`. -/
theorem graphFredholm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) :
    IsFredholm (1 + (transportedKaltonSwansonForm hX).adjoint T * T) := by
  let W := graphBlockOperator hX T
  have hblocks := evenOddBlocks hX
  have hW := hblocks.2.2.2.2 T
  have hfred := cgpTransport hX W hW.2.2
  rw [hW.2.1] at hfred
  exact hfred

/-- The weak alternating form `bₜ(x,y) = Ω(x,y) + t Ω(Tx,Ty)`.
Blueprint label: `lem:kp-alternating-path`; audit ID `HID-ALTERNATING-PATH`. -/
def kaltonPeckAlternatingPath {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) (t : ℝ) :
    ContinuousAlternatingForm X := by
  let omega := transportedKaltonSwansonForm hX
  refine
    { toDual := omega.toDual.toContinuousLinearMap +
        t • (transpose T).comp (omega.toDual.toContinuousLinearMap.comp T)
      alternating := ?_ }
  intro x
  change omega.toDual x x + t * omega.toDual (T x) (T x) = 0
  rw [omega.alternating, omega.alternating, mul_zero, add_zero]

/-- Evaluation, induced-operator formula, norm continuity, and Fredholmness of the path.
Blueprint label: `lem:kp-alternating-path`; audit IDs `HID-ALTERNATING-PATH`,
`HID-SQRT-SCALING`, and `HID-D-COMPOSITION`. -/
theorem kaltonPeckAlternatingPath_spec {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (hX : RealKaltonPeckPresentation X)
    (T : X →L[ℝ] X) :
    let ω := transportedKaltonSwansonForm hX
    (∀ t x y, (kaltonPeckAlternatingPath hX T t).toDual x y =
        ω.toDual x y + t * ω.toDual (T x) (T y)) ∧
      (∀ t, (kaltonPeckAlternatingPath hX T t).toDual =
        ω.toDual.toContinuousLinearMap.comp (1 + t • (ω.adjoint T * T))) ∧
      Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦
        (kaltonPeckAlternatingPath hX T t.1).toDual) ∧
      ∀ t : Set.Icc (0 : ℝ) 1, IsFredholm (kaltonPeckAlternatingPath hX T t.1).toDual := by
  dsimp only
  let ω := transportedKaltonSwansonForm hX
  have heval : ∀ t x y, (kaltonPeckAlternatingPath hX T t).toDual x y =
      ω.toDual x y + t * ω.toDual (T x) (T y) := by
    intro t x y
    rfl
  have hop : ∀ t, (kaltonPeckAlternatingPath hX T t).toDual =
      ω.toDual.toContinuousLinearMap.comp (1 + t • (ω.adjoint T * T)) := by
    intro t
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    rw [heval]
    change ω.toDual x y + t * ω.toDual (T x) (T y) =
      ω.toDual (x + t • ω.adjoint T (T x)) y
    rw [map_add, map_smul]
    simp only [add_apply, smul_apply]
    rw [Forms.adjoint_apply]
    rfl
  refine ⟨heval, hop, ?_, ?_⟩
  · change Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦
      ω.toDual.toContinuousLinearMap +
        t.1 • (transpose T).comp (ω.toDual.toContinuousLinearMap.comp T))
    let : NormedAddCommGroup (X →L[ℝ] StrongDual ℝ X) :=
      ContinuousLinearMap.toNormedAddCommGroup
    have hω : Continuous (fun _ : Set.Icc (0 : ℝ) 1 ↦
        ω.toDual.toContinuousLinearMap) := continuous_const
    have ht : Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦ t.1) := continuous_subtype_val
    have hQ : Continuous (fun _ : Set.Icc (0 : ℝ) 1 ↦
        (transpose T).comp (ω.toDual.toContinuousLinearMap.comp T)) := continuous_const
    exact hω.add (ht.smul hQ)
  · intro t
    let s := Real.sqrt t.1
    let S : X →L[ℝ] X := s • T
    let G : X →L[ℝ] X := 1 + t.1 • (ω.adjoint T * T)
    have ht : 0 ≤ t.1 := t.2.1
    have hs : s * s = t.1 := by
      exact Real.mul_self_sqrt ht
    have hS := graphFredholm hX S
    have hG : IsFredholm G := by
      have heq : G = 1 + ω.adjoint S * S := by
        ext x
        simp [G, S, Forms.adjoint_smul, smul_smul, hs]
      rw [heq]
      exact hS
    have hcomp := (Fredholm.isFredholm_equiv_comp G ω.toDual
      (ContinuousLinearEquiv.refl ℝ X)).1 hG
    rw [hop t.1]
    simpa [G] using hcomp

/-- The graph Fredholm operator has finite, even-dimensional kernel.
Blueprint label: `prop:even-kernel`; audit ID `PROP-EVEN-KERNEL`. -/
theorem evenGraphKernel {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : RealKaltonPeckPresentation X) (T : X →L[ℝ] X) :
    let G := 1 + (transportedKaltonSwansonForm hX).adjoint T * T
    IsFredholm G ∧ Even (nullity G) := by
  dsimp only
  let ω := transportedKaltonSwansonForm hX
  let G : X →L[ℝ] X := 1 + ω.adjoint T * T
  have hG : IsFredholm G := by
    exact graphFredholm hX T
  refine ⟨hG, ?_⟩
  let eta : Set.Icc (0 : ℝ) 1 → ContinuousAlternatingForm X :=
    fun t ↦ kaltonPeckAlternatingPath hX T t.1
  let t₀ : Set.Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
  let t₁ : Set.Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  have hspec := kaltonPeckAlternatingPath_spec hX T
  have hparity := PathParity.mod2Path eta hspec.2.2.1
    (Forms.strongSymplecticReflexive ω) hspec.2.2.2 t₀ t₁
  have hker₀ : (eta t₀).radical = ⊥ := by
    rw [ContinuousAlternatingForm.radical_eq_ker]
    have hop₀ : (eta t₀).toDual = ω.toDual.toContinuousLinearMap := by
      change (kaltonPeckAlternatingPath hX T 0).toDual = ω.toDual.toContinuousLinearMap
      rw [hspec.2.1 (0 : ℝ)]
      ext x
      simp [ω]
    rw [hop₀]
    exact LinearMap.ker_eq_bot.mpr ω.toDual.injective
  have hker₁ : (eta t₁).radical = G.toLinearMap.ker := by
    rw [ContinuousAlternatingForm.radical_eq_ker]
    have hop₁ : (eta t₁).toDual = ω.toDual.toContinuousLinearMap.comp G := by
      simpa [eta, t₁, G, ω] using hspec.2.1 (1 : ℝ)
    rw [hop₁]
    exact Fredholm.ker_comp_of_injective G ω.toDual.toContinuousLinearMap ω.toDual.injective
  have hfin₀ : Module.finrank ℝ (eta t₀).radical = 0 := by
    rw [hker₀]
    simp
  have hfin₁ : Module.finrank ℝ (eta t₁).radical = nullity G := by
    rw [hker₁]
    rfl
  have hmod : Nat.ModEq 2 0 (nullity G) := by
    rw [hfin₀, hfin₁] at hparity
    exact hparity
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp hmod.symm)

end


end KaltonPeck.Support.GraphFredholm

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
