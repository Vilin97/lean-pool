/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.FiniteLpGauge


/-!
# Rectangular Schatten norms

For a finite-dimensional rectangular map `A : E →ₗ[𝕜] F`, this file defines

`‖A‖_{S_p} = (∑ᵢ σᵢ(A)^p)^(1/p)`

for real `p ≥ 1`, using the singular-value vector of length
`min (finrank 𝕜 E) (finrank 𝕜 F)`.  This indexing convention is symmetric in
domain and codomain and discards only the automatic zero tail.

The triangle inequality is factored into the two canonical ingredients:

1. Ky Fan subadditivity gives
   `σ(A + B) ≺w σ(A) + σ(B)`;
2. finite `ℓᵖ` gauges are monotone under weak majorization and satisfy
   Minkowski's inequality.

The resulting object is a `UnitarilyInvariantSeminorm`, so it inherits
the existing two-sided unitary invariance, orbit-certificate bounds, Fan
dominance bridges, and operator-ideal inequalities.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SchattenNorm`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `a8d4ea3`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

universe uE uF

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
namespace UnitarilyInvariantSeminorm

/-- The canonical finite singular-value vector for a rectangular map. -/
noncomputable def singularValueVector (A : E →ₗ[𝕜] F) :
    Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → ℝ :=
  fun i => A.singularValues (i : ℕ)

/-- Singular values are nonnegative. -/
theorem singularValueVector_nonneg (A : E →ₗ[𝕜] F) (i) :
    0 ≤ singularValueVector A i :=
  A.singularValues_nonneg _

/-- Singular values are listed in decreasing order.  Stated for the `Fin`-indexed vector, where
the order is `Fin.le_def` rather than the underlying order on `ℕ`. -/
theorem singularValueVector_antitone (A : E →ₗ[𝕜] F) :
    Antitone (singularValueVector A) := by
  intro i j hij
  exact A.singularValues_antitone (Fin.le_def.mp hij)

/-- Rectangular Ky Fan sums stabilize once the prefix reaches the minimum of
the domain and codomain dimensions. -/
theorem kyFanSum_eq_minFinrank_of_minFinrank_le
    (A : E →ₗ[𝕜] F) {k : ℕ}
    (hk : min (finrank 𝕜 E) (finrank 𝕜 F) ≤ k) :
    kyFanSum k A =
      kyFanSum (min (finrank 𝕜 E) (finrank 𝕜 F)) A := by
  unfold kyFanSum
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hi hiMin
  rw [A.singularValues_eq_zero_iff_le_finrank_range.mpr]
  exact (finrank_range_le_min A).trans
    (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hiMin))

/-- Prefix sums of the canonical singular-value vector are exactly rectangular
Ky Fan sums. -/
theorem prefixSum_singularValueVector
    (k : ℕ) (A : E →ₗ[𝕜] F) :
    FiniteVector.prefixSum k (singularValueVector A) =
      kyFanSum k A := by
  let d := min (finrank 𝕜 E) (finrank 𝕜 F)
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change FiniteVector.prefixSum k
      (fun i : Fin d => A.singularValues (i : ℕ)) =
    kyFanSum k A
  rcases le_or_gt k d with hk | hk
  · unfold FiniteVector.prefixSum kyFanSum
    rw [sum_filter_lt_eq_sum_fin hk (fun j => A.singularValues j)]
  · have hdk : d ≤ k := Nat.le_of_lt hk
    rw [FiniteVector.prefixSum_eq_full_sum_of_le _ hdk]
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change kyFanSum d A = kyFanSum k A
    exact (kyFanSum_eq_minFinrank_of_minFinrank_le A hdk).symm

/-- Ky Fan prefix inequalities characterize weak majorization of two canonical
singular-value vectors. -/
theorem singularValueVector_weaklyMajorized_iff (A B : E →ₗ[𝕜] F) :
    FiniteVector.WeaklyMajorized (singularValueVector A)
      (singularValueVector B) ↔
      ∀ k, kyFanSum k A ≤ kyFanSum k B := by
  constructor
  · intro h k
    simpa only [prefixSum_singularValueVector] using h.prefix_le k
  · intro h
    exact ⟨singularValueVector_antitone A, singularValueVector_antitone B,
      singularValueVector_nonneg A, singularValueVector_nonneg B, fun k => by
        simpa only [prefixSum_singularValueVector] using h k⟩

/-- The singular-value vector of a sum is weakly majorized by the sum of the
singular-value vectors.  This is the correct simultaneous singular-value
subadditivity statement; no coordinatewise inequality is asserted. -/
theorem singularValueVector_add_weaklyMajorized (A B : E →ₗ[𝕜] F) :
    FiniteVector.WeaklyMajorized
      (singularValueVector (A + B))
      (singularValueVector A + singularValueVector B) := by
  refine ⟨singularValueVector_antitone (A + B), ?_,
    singularValueVector_nonneg (A + B), ?_, fun k => ?_⟩
  · intro i j hij
    exact add_le_add
      (singularValueVector_antitone A hij)
      (singularValueVector_antitone B hij)
  · intro i
    exact add_nonneg
      (singularValueVector_nonneg A i)
      (singularValueVector_nonneg B i)
  · rw [FiniteVector.prefixSum_add,
      prefixSum_singularValueVector,
      prefixSum_singularValueVector,
      prefixSum_singularValueVector]
    exact kyFanSum_add_le k A B

/-- Singular-value vectors scale by the norm of the scalar. -/
theorem singularValueVector_smul (a : 𝕜) (A : E →ₗ[𝕜] F) :
    singularValueVector (a • A) = ‖a‖ • singularValueVector A := by
  funext i
  exact singularValues_smul_apply a A (i : ℕ)

/-- Singular-value vectors are invariant under compatible unitary factors. -/
theorem singularValueVector_unitary_comp
    (U : F ≃ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] F) :
    singularValueVector (U.toLinearMap ∘ₗ A) = singularValueVector A := by
  funext i
  -- `singularValues` is bundled, so the equality has to be rewritten under the
  -- coercion rather than applied with `congrFun`
  simp only [singularValueVector, singularValues_unitary_comp U A]

/-- Precomposing with a unitary of the domain leaves the singular values unchanged; the
counterpart of `singularValueVector_unitary_comp` on the codomain side. -/
theorem singularValueVector_comp_unitary
    (A : E →ₗ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    singularValueVector (A ∘ₗ V.toLinearMap) = singularValueVector A := by
  funext i
  simp only [singularValueVector, singularValues_comp_unitary A V]

/-- Rectangular Schatten `p` norm for a real exponent `p ≥ 1`. -/
noncomputable def schattenNorm (p : ℝ) (hp : 1 ≤ p) :
    UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := Seminorm.of
    (fun A => FiniteVector.lpGauge p (singularValueVector A))
    (fun A B =>    calc
        FiniteVector.lpGauge p (singularValueVector (A + B))
            ≤ FiniteVector.lpGauge p
                (singularValueVector A + singularValueVector B) :=
          FiniteVector.lpGauge_mono_weaklyMajorized hp
            (singularValueVector_add_weaklyMajorized A B)
        _ ≤ FiniteVector.lpGauge p (singularValueVector A) +
            FiniteVector.lpGauge p (singularValueVector B) :=
          FiniteVector.lpGauge_add_le hp _ _)
    (fun a A => by
      rw [singularValueVector_smul,
        FiniteVector.lpGauge_smul (zero_lt_one.trans_le hp),
        abs_of_nonneg (norm_nonneg a)])
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry
      (f := fun A : E →ₗ[𝕜] F => FiniteVector.lpGauge p (singularValueVector A))
      (fun U V A => by
        rw [singularValueVector_unitary_comp, singularValueVector_comp_unitary])

/-- The Schatten `p` norm *is* the `ℓᵖ` gauge of the singular-value vector,
definitionally.  This is the lemma that turns Schatten statements into
finite-vector ones. -/
@[simp] theorem schattenNorm_apply (p : ℝ) (hp : 1 ≤ p) (A : E →ₗ[𝕜] F) :
    schattenNorm p hp A = FiniteVector.lpGauge p (singularValueVector A) :=
  (rfl)

/-- The Schatten `p` norm is nonnegative. -/
theorem schattenNorm_nonneg (p : ℝ) (hp : 1 ≤ p) (A : E →ₗ[𝕜] F) :
    0 ≤ schattenNorm p hp A :=
  (schattenNorm p hp).nonneg A

/-- The zero operator has zero Schatten norm at every exponent. -/
 theorem schattenNorm_zero (p : ℝ) (hp : 1 ≤ p) :
    schattenNorm (𝕜 := 𝕜) (E := E) (F := F) p hp 0 = 0 :=
  (schattenNorm p hp).apply_zero

/-- Triangle inequality for the Schatten `p` norm. -/
theorem schattenNorm_add_le (p : ℝ) (hp : 1 ≤ p) (A B : E →ₗ[𝕜] F) :
    schattenNorm p hp (A + B) ≤ schattenNorm p hp A + schattenNorm p hp B :=
  (schattenNorm p hp).add_le A B

/-- The Schatten `p` norm is absolutely homogeneous. -/
theorem schattenNorm_smul (p : ℝ) (hp : 1 ≤ p) (a : 𝕜)
    (A : E →ₗ[𝕜] F) :
    schattenNorm p hp (a • A) = ‖a‖ * schattenNorm p hp A :=
  (schattenNorm p hp).smul_eq a A

/-- The Schatten `p` norm is unchanged by unitaries on either side -- the defining property of a
rectangular unitarily invariant norm, restated for direct use. -/
theorem schattenNorm_invariant (p : ℝ) (hp : 1 ≤ p)
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F) :
    schattenNorm p hp (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) =
      schattenNorm p hp A :=
  (schattenNorm p hp).invariant U V A

/-- Definiteness of the rectangular Schatten norm. -/
theorem schattenNorm_eq_zero_iff (p : ℝ) (hp : 1 ≤ p) (A : E →ₗ[𝕜] F) :
    schattenNorm p hp A = 0 ↔ A = 0 := by
  rw [schattenNorm_apply,
    FiniteVector.lpGauge_eq_zero_iff (zero_lt_one.trans_le hp)]
  constructor
  · intro hσ
    by_contra hA
    have hrange : A.range ≠ ⊥ := by
      simpa [LinearMap.range_eq_bot] using hA
    have hrankpos : 0 < finrank 𝕜 A.range := by
      apply Nat.pos_of_ne_zero
      intro hrank
      exact hrange (Submodule.finrank_eq_zero.mp hrank)
    have hdpos : 0 < min (finrank 𝕜 E) (finrank 𝕜 F) :=
      hrankpos.trans_le (finrank_range_le_min A)
    let i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) := ⟨0, hdpos⟩
    have hzero : A.singularValues 0 = 0 := by
      have := congrFun hσ i
      simpa [singularValueVector, i] using this
    have hpos : 0 < A.singularValues 0 :=
      A.singularValues_pos_iff_lt_finrank_range.mpr hrankpos
    exact hpos.ne' hzero
  · rintro rfl
    funext i
    simp only [singularValueVector]
    refine (0 : E →ₗ[𝕜] F).singularValues_eq_zero_iff_le_finrank_range.mpr ?_
    rw [show LinearMap.range (0 : E →ₗ[𝕜] F) = ⊥ from LinearMap.range_zero,
      finrank_bot]
    exact Nat.zero_le _

/-- Adjoint invariance.  The minimum-dimension indexing makes this a direct
consequence of the zero-padded singular-value equality. -/
theorem schattenNorm_adjoint (p : ℝ) (hp : 1 ≤ p) (A : E →ₗ[𝕜] F) :
    schattenNorm (𝕜 := 𝕜) (E := F) (F := E) p hp A.adjoint =
      schattenNorm (𝕜 := 𝕜) (E := E) (F := F) p hp A := by
  simp only [schattenNorm_apply, FiniteVector.lpGauge, singularValueVector]
  rw [min_comm]
  simp_rw [A.singularValues_adjoint_apply]

/-- Left ideal inequality for Schatten norms. -/
theorem schattenNorm_comp_le_opNorm_mul (p : ℝ) (hp : 1 ≤ p)
    (C : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] F) :
    schattenNorm p hp (C ∘ₗ A) ≤
      ‖C.toContinuousLinearMap‖ * schattenNorm p hp A :=
  (schattenNorm p hp).comp_le_opNorm_mul C A

/-- Right ideal inequality for Schatten norms. -/
theorem schattenNorm_comp_le_mul_opNorm (p : ℝ) (hp : 1 ≤ p)
    (A : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E) :
    schattenNorm p hp (A ∘ₗ C) ≤
      schattenNorm p hp A * ‖C.toContinuousLinearMap‖ :=
  (schattenNorm p hp).comp_le_mul_opNorm A C

/-- Two-sided ideal inequality for endomorphism factors on the source and
 target spaces. -/
theorem schattenNorm_comp_comp_le (p : ℝ) (hp : 1 ≤ p)
    (B : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E) :
    schattenNorm p hp (B ∘ₗ A ∘ₗ C) ≤
      ‖B.toContinuousLinearMap‖ * schattenNorm p hp A *
        ‖C.toContinuousLinearMap‖ := by
  calc
    schattenNorm p hp (B ∘ₗ A ∘ₗ C)
        ≤ schattenNorm p hp (B ∘ₗ A) * ‖C.toContinuousLinearMap‖ :=
      schattenNorm_comp_le_mul_opNorm p hp (B ∘ₗ A) C
    _ ≤ (‖B.toContinuousLinearMap‖ * schattenNorm p hp A) *
            ‖C.toContinuousLinearMap‖ :=
      mul_le_mul_of_nonneg_right
        (schattenNorm_comp_le_opNorm_mul p hp B A)
        (norm_nonneg _)

/-- Powers of singular values may be summed over the minimum dimension or
over the whole domain dimension: the omitted tail is zero. -/
theorem sum_pow_singularValueVector_eq_sum_domain
    (A : E →ₗ[𝕜] F) (q : ℕ) (hq : q ≠ 0) :
    (∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)),
        singularValueVector A i ^ q) =
      ∑ i : Fin (finrank 𝕜 E), A.singularValues (i : ℕ) ^ q := by
  simp only [singularValueVector]
  -- the summand is not syntactically of the form `?f ↑i`, so `f` is supplied
  rw [Fin.sum_univ_eq_sum_range (fun j => A.singularValues j ^ q),
    Fin.sum_univ_eq_sum_range (fun j => A.singularValues j ^ q)]
  apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
  intro i hiDomain hiMin
  have hi : finrank 𝕜 A.range ≤ i :=
    (finrank_range_le_min A).trans
      (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hiMin))
  rw [A.singularValues_eq_zero_iff_le_finrank_range.mpr hi, zero_pow hq]

/-- Squares of the canonical singular-value vector recover the complete
domain-indexed singular-value energy. -/
theorem sum_sq_singularValueVector_eq_sum_domain (A : E →ₗ[𝕜] F) :
    (∑ i, singularValueVector A i ^ 2) =
      ∑ i : Fin (finrank 𝕜 E), A.singularValues (i : ℕ) ^ 2 :=
  sum_pow_singularValueVector_eq_sum_domain A 2 (by norm_num)

/-- The `S₁` norm is the nuclear norm. -/

theorem schattenNorm_one_apply (A : E →ₗ[𝕜] F) :
    schattenNorm (𝕜 := 𝕜) (E := E) (F := F) 1 le_rfl A = nuclear A := by
  rw [schattenNorm_apply]
  simp only [FiniteVector.lpGauge, one_div, inv_one, Real.rpow_one]
  simp_rw [abs_of_nonneg (singularValueVector_nonneg A _)]
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change kyFanSum (min (finrank 𝕜 E) (finrank 𝕜 F)) A =
    kyFanSum (finrank 𝕜 E) A
  exact (kyFanSum_eq_minFinrank_of_minFinrank_le A
    (min_le_left _ _)).symm

/-- The `S₂` norm is the existing rectangular Frobenius norm. -/

theorem schattenNorm_two_apply (A : E →ₗ[𝕜] F) :
    schattenNorm (𝕜 := 𝕜) (E := E) (F := F) 2 (by norm_num) A =
      frobenius A := by
  rw [schattenNorm_apply, frobenius_eq_sqrt_sum_sq_singularValues]
  simp only [FiniteVector.lpGauge]
  simp_rw [abs_of_nonneg (singularValueVector_nonneg A _), Real.rpow_two]
  rw [sum_sq_singularValueVector_eq_sum_domain, ← Real.sqrt_eq_rpow]

/-- The finite Hilbert--Schmidt energy is the square of the Frobenius seminorm.

The energy is valued in the extended nonnegative reals and indexed by a Hilbert basis;
Frobenius is the finite real-valued seminorm. The equality uses the standard orthonormal
basis, and `hilbertSchmidtEnergy_indep` transports the energy to any Hilbert basis.

Completeness is explicit because `FiniteDimensional.complete` is not a global instance. -/
theorem hilbertSchmidtEnergy_eq_ofReal_frobenius_sq [CompleteSpace E] (A : E →L[𝕜] F) :
    A.hilbertSchmidtEnergy (stdOrthonormalBasis 𝕜 E).toHilbertBasis
      = ENNReal.ofReal (frobenius A.toLinearMap ^ 2) := by
  have hsq : frobenius A.toLinearMap ^ 2
      = ∑ i, ‖A.toLinearMap (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 := by
    rw [frobenius_apply_basis A.toLinearMap rfl (stdOrthonormalBasis 𝕜 E)]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_def, tsum_fintype, hsq,
    ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.coe_toHilbertBasis, ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]
  rfl

/-- Schatten infinity norm is the existing rectangular operator norm. -/
noncomputable def schattenNormInf : UnitarilyInvariantSeminorm 𝕜 E F :=
  opNorm

/-- The `S∞` norm evaluates to the ordinary operator norm, definitionally —
`schattenNormInf` is `opNorm` under a name that places it at the end of the
Schatten scale. -/
@[simp] theorem schattenNormInf_apply (A : E →ₗ[𝕜] F) :
    schattenNormInf A = ‖A.toContinuousLinearMap‖ :=
  (rfl)

end UnitarilyInvariantSeminorm
end TauCeti
