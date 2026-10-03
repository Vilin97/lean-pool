/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidt
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-! # Hilbert Schmidt Basis -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Basis and tensor models of the paper square norm

The source square norm is defined in the main development by the complete
approximation-number sequence.  The spectral proof of the second generalized
sine theorem needs the equivalent Hilbert-space model.  This file proves the
coordinate bridge:

* the column-square sum is independent of the Hilbert basis;
* it equals the sum of squared approximation singular values;
The tensor model itself — the identification with `E tensor Conj F` and the
equality of the tensor norm with the paper square norm — lives in
`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtTensor.lean`, because it is the only
part that needs `vendor/Spectra`.

The key comparison uses finite basis projections.  For every finite set of
basis vectors, finite-dimensional Eckart--Young and the Frobenius identity
identify the two cutoff energies.  Strong convergence of the projections and
monotone convergence then identify their suprema.  No compactness assumption
is made; compactness follows afterwards from finite square energy.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal
open scoped Topology
open Filter

noncomputable section

universe vE vF

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type vE} {F : Type vF}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Extended column-square energy in a chosen Hilbert basis of the domain. -/
def hilbertSchmidtBasisEnergy {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) : ENNReal :=
  ∑' i, (‖A (b i)‖₊ : ENNReal) ^ 2

omit [CompleteSpace E] [CompleteSpace F] in
/-- The paper column energy is the staged `ContinuousLinearMap.hilbertSchmidtEnergy`. -/
theorem hilbertSchmidtBasisEnergy_eq_hilbertSchmidtEnergy {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    hilbertSchmidtBasisEnergy b A = A.hilbertSchmidtEnergy b := rfl

/-- Adjoint cross-swap for rectangular operators. -/
theorem hilbertSchmidtBasisEnergy_adjoint_swap
    {ι κ : Type*} (bF : HilbertBasis ι 𝕜 F)
    (bE : HilbertBasis κ 𝕜 E) (A : F →L[𝕜] E) :
    hilbertSchmidtBasisEnergy bF A =
      hilbertSchmidtBasisEnergy bE A.adjoint :=
  A.hilbertSchmidtEnergy_adjoint bF bE

/-- The rectangular column-square energy does not depend on the domain basis. -/
theorem hilbertSchmidtBasisEnergy_indep
    {ι κ : Type*} (b c : HilbertBasis ι 𝕜 F)
    (d : HilbertBasis κ 𝕜 E) (A : F →L[𝕜] E) :
    hilbertSchmidtBasisEnergy b A =
      hilbertSchmidtBasisEnergy c A := by
  rw [hilbertSchmidtBasisEnergy_adjoint_swap b d A,
    ← hilbertSchmidtBasisEnergy_adjoint_swap c d A]

/-- The span of finitely many basis vectors is finite dimensional. -/
instance basisSpan_finiteDimensional {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (s : Finset ι) :
    FiniteDimensional 𝕜 (Submodule.span 𝕜 (b '' (s : Set ι))) :=
  FiniteDimensional.span_of_finite 𝕜 (s.finite_toSet.image b)

/-- Projection onto the span of a finite set of Hilbert-basis vectors. -/
noncomputable def basisProjection {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (s : Finset ι) : F →L[𝕜] F :=
  (Submodule.span 𝕜 (b '' (s : Set ι))).starProjection

omit [CompleteSpace F] in
/-- The finite basis projection is an orthogonal projection. -/
theorem basisProjection_isOrthogonalProjection {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (s : Finset ι) :
    IsOrthogonalProjectionMap (basisProjection b s) :=
  ⟨Submodule.isIdempotentElem_starProjection _,
    fun x y => Submodule.starProjection_isSymmetric _ x y⟩

omit [CompleteSpace F] in
/-- The finite cutoff has rank at most the number of selected basis vectors. -/
theorem rank_basisProjection_le {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (s : Finset ι) :
    (basisProjection b s).rank ≤ (s.card : Cardinal) := by
  classical
  have hle : LinearMap.range (basisProjection b s).toLinearMap ≤
      Submodule.span 𝕜 ((s.image b : Finset F) : Set F) := by
    rw [Finset.coe_image]
    exact (Submodule.range_starProjection _).le
  calc
    (basisProjection b s).rank
        ≤ Module.rank 𝕜 (Submodule.span 𝕜 ((s.image b : Finset F) : Set F)) :=
          Submodule.rank_mono hle
    _ ≤ ((s.image b).card : Cardinal) := rank_span_finset_le _
    _ ≤ (s.card : Cardinal) := by
          exact_mod_cast Finset.card_image_le (s := s) (f := b)

omit [CompleteSpace F] in
/-- The finite basis projection is the finite Fourier partial sum. -/
theorem basisProjection_apply {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (s : Finset ι) (x : F) :
    basisProjection b s x = ∑ i ∈ s, ⟪b i, x⟫_𝕜 • b i := by
  classical
  have hb := orthonormal_iff_ite.mp b.orthonormal
  have hmem : ∀ i ∈ s, b i ∈ Submodule.span 𝕜 (b '' (s : Set ι)) := fun i hi =>
    Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩
  change (Submodule.span 𝕜 (b '' (s : Set ι))).starProjection x = _
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hmem i hi)
  · intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨j, hj, rfl⟩ := hw
        have hjs : j ∈ s := Finset.mem_coe.mp hj
        rw [inner_sub_left, sum_inner]
        have hkey : ∀ i ∈ s, ⟪(⟪b i, x⟫_𝕜) • b i, b j⟫_𝕜 =
            if i = j then (starRingEnd 𝕜) ⟪b j, x⟫_𝕜 else 0 := by
          intro i _
          rw [inner_smul_left, hb i j]
          by_cases hij : i = j <;> simp [hij]
        rw [Finset.sum_congr rfl hkey, Finset.sum_ite_eq' s j, ite_eq_left hjs,
          inner_conj_symm, sub_self]
    | zero => simp
    | add u v _ _ hu hv => rw [inner_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [inner_smul_right, hu, mul_zero]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The cutoff operator is the finite column expansion. -/
theorem comp_basisProjection_apply {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (s : Finset ι)
    (A : F →L[𝕜] E) (x : F) :
    (A ∘L basisProjection b s) x =
      ∑ i ∈ s, ⟪b i, x⟫_𝕜 • A (b i) := by
  rw [ContinuousLinearMap.comp_apply, basisProjection_apply, map_sum]
  simp only [map_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Finite-dimensional cutoff Frobenius identity: the approximation-number
energy of the compression of `A` to a finite-dimensional subspace `K` of the
domain is the sum of the squared column norms over any orthonormal basis
of `K`. -/
theorem approximationNumberEnergy_comp_starProjection
    (A : F →L[𝕜] E) (K : Submodule 𝕜 F) [FiniteDimensional 𝕜 K]
    {n : ℕ} (c : OrthonormalBasis (Fin n) 𝕜 K) :
    approximationNumberEnergy (A ∘L K.starProjection) =
      ∑ k : Fin n, ENNReal.ofReal (‖A ((c k : F))‖ ^ 2) := by
  classical
  have hn : Module.finrank 𝕜 K = n := by
    rw [Module.finrank_eq_card_basis c.toBasis, Fintype.card_fin]
  -- the compression of `A` to `K`, together with its finite-dimensional range
  let T₀ : K →L[𝕜] E := A ∘L K.subtypeL
  let L : Submodule 𝕜 E := LinearMap.range T₀.toLinearMap
  have hLfd : FiniteDimensional 𝕜 L := inferInstance
  let T : K →L[𝕜] L :=
    T₀.codRestrict L fun x => LinearMap.mem_range_self T₀.toLinearMap x
  -- the three factorisations relating the cutoff and the compression
  have hfac1 : A ∘L K.starProjection = T₀ ∘L K.orthogonalProjectionOnto :=
    ContinuousLinearMap.ext fun x => rfl
  have hfac2 : L.subtypeL ∘L T = T₀ := ContinuousLinearMap.ext fun x => rfl
  have hfac3 : T = L.orthogonalProjectionOnto ∘L T₀ :=
    ContinuousLinearMap.ext fun x => Subtype.ext
      (Submodule.starProjection_eq_self_iff.mpr
        (LinearMap.mem_range_self T₀.toLinearMap x)).symm
  have hfac4 : T₀ = (A ∘L K.starProjection) ∘L K.subtypeL :=
    ContinuousLinearMap.ext fun x =>
      congrArg A (Submodule.starProjection_eq_self_iff.mpr x.2).symm
  -- all four structural maps are contractions
  have hsubL : ‖L.subtypeL‖ ≤ 1 := by
    have h : ‖L.subtypeL‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        simp
    exact_mod_cast h
  have hsubK : ‖K.subtypeL‖ ≤ 1 := by
    have h : ‖K.subtypeL‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        simp
    exact_mod_cast h
  have hprojK : ‖K.orthogonalProjectionOnto‖ ≤ 1 := by
    exact_mod_cast K.orthogonalProjectionOnto_norm_le
  have hprojL : ‖L.orthogonalProjectionOnto‖ ≤ 1 := by
    exact_mod_cast L.orthogonalProjectionOnto_norm_le
  -- hence the cutoff and the compression have the same singular sequence
  have hsame : SameApproximationSingularSequence (A ∘L K.starProjection) T := by
    intro m
    have h1 : (A ∘L K.starProjection).approximationNumber m ≤
        T.approximationNumber m := by
      calc (A ∘L K.starProjection).approximationNumber m
          = (T₀ ∘L K.orthogonalProjectionOnto).approximationNumber m := by
            rw [hfac1]
        _ ≤ T₀.approximationNumber m * ‖K.orthogonalProjectionOnto‖ :=
            T₀.approximationNumber_comp_le_mul_norm _ m
        _ ≤ T₀.approximationNumber m * 1 :=
            mul_le_mul_of_nonneg_left hprojK
              (ContinuousLinearMap.approximationNumber_nonneg _ _)
        _ = (L.subtypeL ∘L T).approximationNumber m := by rw [mul_one, hfac2]
        _ ≤ ‖L.subtypeL‖ * T.approximationNumber m :=
            ContinuousLinearMap.approximationNumber_comp_le_norm_mul _ _ m
        _ ≤ 1 * T.approximationNumber m :=
            mul_le_mul_of_nonneg_right hsubL
              (ContinuousLinearMap.approximationNumber_nonneg _ _)
        _ = T.approximationNumber m := one_mul _
    have h2 : T.approximationNumber m ≤
        (A ∘L K.starProjection).approximationNumber m := by
      calc T.approximationNumber m
          = (L.orthogonalProjectionOnto ∘L T₀).approximationNumber m := by
            rw [← hfac3]
        _ ≤ ‖L.orthogonalProjectionOnto‖ * T₀.approximationNumber m :=
            ContinuousLinearMap.approximationNumber_comp_le_norm_mul _ _ m
        _ ≤ 1 * T₀.approximationNumber m :=
            mul_le_mul_of_nonneg_right hprojL
              (ContinuousLinearMap.approximationNumber_nonneg _ _)
        _ = ((A ∘L K.starProjection) ∘L K.subtypeL).approximationNumber m := by
            rw [one_mul, ← hfac4]
        _ ≤ (A ∘L K.starProjection).approximationNumber m * ‖K.subtypeL‖ :=
            ContinuousLinearMap.approximationNumber_comp_le_mul_norm _ _ m
        _ ≤ (A ∘L K.starProjection).approximationNumber m * 1 :=
            mul_le_mul_of_nonneg_left hsubK
              (ContinuousLinearMap.approximationNumber_nonneg _ _)
        _ = (A ∘L K.starProjection).approximationNumber m := mul_one _
    change approximationSingularValue m _ = approximationSingularValue m _
    unfold approximationSingularValue
    exact_mod_cast le_antisymm h1 h2
  -- the compression has rank at most `n`
  -- The rank of `T` lives in the codomain universe and `Module.rank 𝕜 K` in the
  -- domain universe, so compare them through `Cardinal.lift`.
  have hTrank : T.rank ≤ (n : Cardinal) := by
    have hK : Module.rank 𝕜 K = (n : Cardinal) := by
      rw [← Module.finrank_eq_rank' 𝕜 K, hn]
    refine Cardinal.lift_le_natCast.mp
      ((lift_rank_range_le T.toLinearMap).trans ?_)
    calc
      Cardinal.lift.{vE} (Module.rank 𝕜 K)
          = Cardinal.lift.{vE} ((n : Cardinal)) := by rw [hK]
      _ = (n : Cardinal) := Cardinal.lift_natCast n
      _ ≤ (n : Cardinal) := le_rfl
  -- singular values of the compression, and the finite Frobenius identity
  have hsv : ∀ m : ℕ,
      approximationSingularValue m T = T.toLinearMap.singularValues m := by
    intro m
    exact ContinuousLinearMap.approximationNumber_eq_singularValues T m
  have hfrob : ∑ k : Fin n, T.toLinearMap.singularValues (k : ℕ) ^ 2
      = ∑ k : Fin n, ‖T (c k)‖ ^ 2 :=
    TauCeti.sum_sq_singularValues T.toLinearMap hn c
  rw [hsame.approximationNumberEnergy_eq,
    approximationNumberEnergy_eq_sum_range_of_rank_le hTrank,
    ← Fin.sum_univ_eq_sum_range
      (fun m => ENNReal.ofReal ((approximationSingularValue m T) ^ 2)) n,
    ← ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _,
    ← ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
  congr 1
  calc ∑ k : Fin n, (approximationSingularValue (k : ℕ) T) ^ 2
      = ∑ k : Fin n, T.toLinearMap.singularValues (k : ℕ) ^ 2 :=
        Finset.sum_congr rfl fun k _ => by rw [hsv (k : ℕ)]
    _ = ∑ k : Fin n, ‖T (c k)‖ ^ 2 := hfrob
    _ = ∑ k : Fin n, ‖A ((c k : F))‖ ^ 2 := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Finite-cutoff Frobenius identity in approximation-number form. -/
theorem approximationNumberEnergy_comp_basisProjection
    {ι : Type*} (b : HilbertBasis ι 𝕜 F) (s : Finset ι)
    (A : F →L[𝕜] E) :
    approximationNumberEnergy (A ∘L basisProjection b s) =
      ∑ i ∈ s, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
  classical
  -- enumerate the selected basis vectors
  have hinj : Function.Injective
      (fun k : Fin s.card => ((s.equivFin.symm k : ι))) := fun k l hkl =>
    s.equivFin.symm.injective (Subtype.ext hkl)
  have hw : Orthonormal 𝕜 (fun k : Fin s.card => b ((s.equivFin.symm k : ι))) :=
    b.orthonormal.comp _ hinj
  have hrange : Set.range (fun k : Fin s.card => b ((s.equivFin.symm k : ι)))
      = b '' (s : Set ι) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, Finset.mem_coe.mpr (s.equivFin.symm k).2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨s.equivFin ⟨i, Finset.mem_coe.mp hi⟩, by simp⟩
  -- the selected vectors, viewed inside the cutoff subspace
  have hmem : ∀ k : Fin s.card,
      b ((s.equivFin.symm k : ι)) ∈ Submodule.span 𝕜 (b '' (s : Set ι)) := by
    intro k
    exact Submodule.subset_span
      ⟨_, Finset.mem_coe.mpr (s.equivFin.symm k).2, rfl⟩
  have hon : Orthonormal 𝕜 (fun k : Fin s.card =>
      (⟨b ((s.equivFin.symm k : ι)), hmem k⟩ :
        Submodule.span 𝕜 (b '' (s : Set ι)))) := hw
  have hsp : (⊤ : Submodule 𝕜 (Submodule.span 𝕜 (b '' (s : Set ι)))) ≤
      Submodule.span 𝕜 (Set.range (fun k : Fin s.card =>
        (⟨b ((s.equivFin.symm k : ι)), hmem k⟩ :
          Submodule.span 𝕜 (b '' (s : Set ι))))) := by
    have himg : (Submodule.span 𝕜 (b '' (s : Set ι))).subtype ''
        Set.range (fun k : Fin s.card =>
          (⟨b ((s.equivFin.symm k : ι)), hmem k⟩ :
            Submodule.span 𝕜 (b '' (s : Set ι))))
        = b '' (s : Set ι) := by
      rw [← Set.range_comp]
      exact hrange
    refine le_of_eq (Submodule.map_injective_of_injective
      (Submodule.span 𝕜 (b '' (s : Set ι))).injective_subtype ?_).symm
    rw [Submodule.map_span, Submodule.map_subtype_top, himg]
  let c : OrthonormalBasis (Fin s.card) 𝕜
      (Submodule.span 𝕜 (b '' (s : Set ι))) := OrthonormalBasis.mk hon hsp
  have hc : ∀ k, ((c k : F)) = b ((s.equivFin.symm k : ι)) := by
    intro k
    rw [show ⇑c = _ from OrthonormalBasis.coe_mk hon hsp]
  have hP : basisProjection b s
      = (Submodule.span 𝕜 (b '' (s : Set ι))).starProjection := rfl
  rw [hP, approximationNumberEnergy_comp_starProjection A _ c]
  calc ∑ k : Fin s.card, ENNReal.ofReal (‖A ((c k : F))‖ ^ 2)
      = ∑ k : Fin s.card,
          ENNReal.ofReal (‖A (b ((s.equivFin.symm k : ι)))‖ ^ 2) :=
        Finset.sum_congr rfl fun k _ => by rw [hc k]
    _ = ∑ j : (s : Finset ι), ENNReal.ofReal (‖A (b (j : ι))‖ ^ 2) :=
        Equiv.sum_comp s.equivFin.symm
          (fun j : (s : Finset ι) => ENNReal.ofReal (‖A (b (j : ι))‖ ^ 2))
    _ = ∑ i ∈ s, ENNReal.ofReal (‖A (b i)‖ ^ 2) :=
        Finset.sum_coe_sort s (fun i => ENNReal.ofReal (‖A (b i)‖ ^ 2))

omit [CompleteSpace F] in
/-- Finite basis projections converge strongly to the identity. -/
theorem basisProjection_stronglyTendsto {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) :
    StronglyTendsto (fun s : Finset ι => basisProjection b s)
      atTop (ContinuousLinearMap.id 𝕜 F) := by
  intro x
  have hsum := b.hasSum_repr x
  simp only [HilbertBasis.repr_apply_apply] at hsum
  have hpartial : Tendsto
      (fun s : Finset ι => ∑ i ∈ s, ⟪b i, x⟫_𝕜 • b i)
      atTop (𝓝 x) := hsum
  exact Tendsto.congr (fun s => (basisProjection_apply b s x).symm) hpartial

/-- Approximation singular values of finite basis cutoffs converge pointwise.

The min--max lower bound is the one scalar-specific ingredient in the whole
coordinate bridge, and it is the only reason the bridge was ever stated over
`ℂ` alone.  Taken as a hypothesis it is discharged at `ℂ` and at `ℝ` by
`hasMinMaxLowerBound_complex` and `hasMinMaxLowerBound_real`, and everything
downstream becomes scalar-generic. -/
theorem approximationSingularValue_cutoff_tendsto {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) (n : ℕ) :
    Tendsto
      (fun s : Finset ι => approximationSingularValue n
        (A ∘L basisProjection b s))
      atTop (𝓝 (approximationSingularValue n A)) :=
  approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    (ContinuousLinearMap.hasMinMaxLowerBound_rclike 𝕜)
    (fun s => basisProjection_isOrthogonalProjection b s)
    (basisProjection_stronglyTendsto b) n A

/-- The approximation-number energy is the supremum of finite-basis cutoff
energies. -/
theorem approximationNumberEnergy_eq_iSup_cutoff {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    approximationNumberEnergy A =
      ⨆ s : Finset ι,
        approximationNumberEnergy (A ∘L basisProjection b s) := by
  have hle : ∀ (s : Finset ι) (n : ℕ),
      approximationSingularValue n (A ∘L basisProjection b s) ≤
        approximationSingularValue n A := by
    intro s n
    have hnormNN : ‖basisProjection b s‖ ≤ (1 : NNReal) := by
      exact_mod_cast (basisProjection_isOrthogonalProjection b s).norm_le_one
    have hNN : (A ∘L basisProjection b s).approximationNumber n ≤
        A.approximationNumber n := by
      calc
        (A ∘L basisProjection b s).approximationNumber n
            ≤ A.approximationNumber n * ‖basisProjection b s‖ :=
          A.approximationNumber_comp_le_mul_norm (basisProjection b s) n
        _ ≤ A.approximationNumber n * 1 :=
          mul_le_mul_of_nonneg_left hnormNN
              (ContinuousLinearMap.approximationNumber_nonneg _ _)
        _ = A.approximationNumber n := by rw [mul_one]
    exact_mod_cast hNN
  apply le_antisymm
  · unfold approximationNumberEnergy
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun t => ?_
    have hten : Tendsto
        (fun s : Finset ι => ∑ n ∈ t, ENNReal.ofReal
          ((approximationSingularValue n (A ∘L basisProjection b s)) ^ 2))
        atTop (𝓝 (∑ n ∈ t, ENNReal.ofReal
          ((approximationSingularValue n A) ^ 2))) := by
      refine tendsto_finsetSum _ fun n _ => ?_
      exact ENNReal.tendsto_ofReal
        ((approximationSingularValue_cutoff_tendsto b A n).pow 2)
    refine le_of_tendsto hten (Filter.Eventually.of_forall fun s => ?_)
    calc
      ∑ n ∈ t, ENNReal.ofReal
          ((approximationSingularValue n (A ∘L basisProjection b s)) ^ 2)
          ≤ approximationNumberEnergy (A ∘L basisProjection b s) :=
            ENNReal.sum_le_tsum t
      _ ≤ ⨆ t : Finset ι,
            approximationNumberEnergy
              (A ∘L basisProjection b t) :=
            le_iSup (fun t : Finset ι =>
              approximationNumberEnergy (A ∘L basisProjection b t)) s
  · refine iSup_le fun s => ?_
    unfold approximationNumberEnergy
    refine ENNReal.tsum_le_tsum fun n => ?_
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (approximationSingularValue_nonneg n _) (hle s n) 2)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A nonnegative series is the supremum of its finite partial subsums. -/
theorem hilbertSchmidtBasisEnergy_eq_iSup_finset {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    hilbertSchmidtBasisEnergy b A =
      ⨆ s : Finset ι, ∑ i ∈ s, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
  unfold hilbertSchmidtBasisEnergy
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_congr fun s => Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

/-- The approximation-number and basis definitions of rectangular
Hilbert--Schmidt energy agree exactly. -/
theorem approximationNumberEnergy_eq_basisEnergy {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    approximationNumberEnergy A = hilbertSchmidtBasisEnergy b A := by
  rw [approximationNumberEnergy_eq_iSup_cutoff b A,
    hilbertSchmidtBasisEnergy_eq_iSup_finset b A]
  exact iSup_congr fun s =>
    approximationNumberEnergy_comp_basisProjection b s A

/-- The paper square energy is the canonical extended norm, squared: the two
energy interfaces agree without any finiteness hypothesis at all. -/
theorem approximationNumberEnergy_eq_hilbertSchmidtENorm_sq
    (A : F →L[𝕜] E) :
    approximationNumberEnergy A = A.hilbertSchmidtENorm ^ (2 : ℝ) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 F
  rw [A.hilbertSchmidtENorm_rpow_two b, approximationNumberEnergy_eq_basisEnergy b A,
    hilbertSchmidtBasisEnergy_eq_hilbertSchmidtEnergy]

/-- **The canonical real norm is the paper's square-root-of-energy formula**, with no
finiteness hypothesis: off the ideal both sides are `0`, because `ENNReal.toReal` sends
`∞` to `0` and `Real.sqrt 0 = 0`.

This is what lets every estimate the paper proves about `√(Σ aₙ²)` be *stated* about the
one canonical norm, rather than about a second norm that happens to be equal to it. -/
theorem hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy
    (A : F →L[𝕜] E) :
    A.hilbertSchmidtNorm = Real.sqrt (approximationNumberEnergy A).toReal := by
  rw [ContinuousLinearMap.hilbertSchmidtNorm_eq_toReal,
    approximationNumberEnergy_eq_hilbertSchmidtENorm_sq A]
  rcases eq_or_ne A.hilbertSchmidtENorm ⊤ with h | h
  · rw [h]
    rw [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
    simp
  · rw [← ENNReal.toReal_rpow, Real.rpow_two, Real.sqrt_sq ENNReal.toReal_nonneg]

/-- Paper square membership is equivalent to square-summable columns in any
Hilbert basis. -/
theorem approximationNumberEnergy_ne_top_iff_summable_basis {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    approximationNumberEnergy A ≠ ⊤ ↔ Summable (fun i => ‖A (b i)‖ ^ 2) := by
  have hE : hilbertSchmidtBasisEnergy b A
      = ∑' i, ((‖A (b i)‖₊ ^ 2 : NNReal) : ENNReal) := by
    simp only [hilbertSchmidtBasisEnergy, ENNReal.coe_pow]
  rw [approximationNumberEnergy_eq_basisEnergy b A, hE,
    ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp only [NNReal.coe_pow, coe_nnnorm]

/-- The paper square norm is the ordinary basis Hilbert--Schmidt norm. -/
theorem hilbertSchmidtNorm_eq_sqrt_tsum_basis {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E)
    (hA : approximationNumberEnergy A ≠ ⊤) :
    ContinuousLinearMap.hilbertSchmidtNorm A = Real.sqrt (∑' i, ‖A (b i)‖ ^ 2) := by
  have hsummable := (approximationNumberEnergy_ne_top_iff_summable_basis b A).1 hA
  have hnn : Summable (fun i => ‖A (b i)‖₊ ^ 2) := by
    rw [← NNReal.summable_coe]
    simpa only [NNReal.coe_pow, coe_nnnorm] using hsummable
  have hE : hilbertSchmidtBasisEnergy b A
      = ((∑' i, (‖A (b i)‖₊ ^ 2 : NNReal) : NNReal) : ENNReal) := by
    simp only [hilbertSchmidtBasisEnergy]
    exact (ENNReal.coe_tsum hnn).symm
  rw [hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy,
    approximationNumberEnergy_eq_basisEnergy b A, hE, ENNReal.coe_toReal]
  congr 1
  rw [NNReal.coe_tsum]
  simp only [NNReal.coe_pow, coe_nnnorm]

/-! ## Reconciliation with the staged Hilbert--Schmidt ideal

`ForTauCeti/Analysis/OperatorIdeal/Family/HilbertSchmidt.lean` builds the Hilbert--Schmidt
ideal from orthonormal expansions alone, deliberately never mentioning approximation
numbers, so that it needs no spectral theory.  The identity that reconciles the two
definitions is exactly `approximationNumberEnergy_eq_basisEnergy` above, and the four
statements below record what it buys: the staged ideal, its membership predicate and its
gauge agree with the paper ones, so the paper development may be reread through the staged
API without reproving anything. -/

/-- **The singular-value energy is the column energy.**  This is the obligation recorded
against Milestone B3 of `TauCetiRoadmap/OperatorTheory/OperatorIdeals/README.md`. -/
theorem approximationNumberEnergy_eq_hilbertSchmidtEnergy {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    ∑' n : ℕ, ENNReal.ofReal (approximationSingularValue n A ^ 2) =
      A.hilbertSchmidtEnergy b :=
  approximationNumberEnergy_eq_basisEnergy b A

/-- The staged Hilbert--Schmidt predicate is the paper one. -/
theorem isHilbertSchmidt_iff_approximationNumberEnergy_ne_top
    (A : F →L[𝕜] E) :
    A.IsHilbertSchmidt ↔ approximationNumberEnergy A ≠ ⊤ := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 F
  rw [A.isHilbertSchmidt_iff_energy_ne_top b,
    approximationNumberEnergy_eq_basisEnergy b A]
  rfl

/-- The staged Hilbert--Schmidt norm is the paper square norm. -/
theorem hilbertSchmidtENorm_eq_ofReal_hilbertSchmidtNorm
    (A : F →L[𝕜] E)
    (hA : approximationNumberEnergy A ≠ ⊤) :
    A.hilbertSchmidtENorm = ENNReal.ofReal (ContinuousLinearMap.hilbertSchmidtNorm A) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 F
  have henergy : A.hilbertSchmidtEnergy b = approximationNumberEnergy A :=
    (approximationNumberEnergy_eq_basisEnergy b A).symm
  have hne : approximationNumberEnergy A ≠ ⊤ := hA
  rw [hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy, A.hilbertSchmidtENorm_eq b,
    henergy, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal hne, one_div]

/-- Consequently the gauge of the staged symmetric ideal family, read on the paper ideal,
is the paper square norm.

`TauCeti.SymmetricOperatorIdealFamily` is the diagonal layer, so it constrains the source
and target to one universe; the rectangular statements above are the general ones. -/
theorem hilbertSchmidtIdealFamily_gauge_eq_hilbertSchmidtNorm {G K : Type vE}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : G →L[𝕜] K) (hA : approximationNumberEnergy A ≠ ⊤) :
    (TauCeti.hilbertSchmidtIdealFamily 𝕜).toOperatorIdealFamily.gauge A =
      ENNReal.ofReal (ContinuousLinearMap.hilbertSchmidtNorm A) :=
  hilbertSchmidtENorm_eq_ofReal_hilbertSchmidtNorm A hA

/-! ### The bridge at the two scalar fields

Min--max is the only hypothesis above, so it is discharged once here and the
paper and staged Hilbert--Schmidt theories are one theory over `ℂ` and over
`ℝ` alike.  Before this, the identification existed over `ℂ` only, and the
`ℝ`-valued paper norm had no connection at all to the staged ideal gauge over
a real Hilbert space. -/





/-! ### The `ℝ` and `ℝ≥0∞` interfaces are the same number

The ideal gauge is `ℝ≥0∞`-valued because a gauge must be defined off the ideal; the
paper's square norm is a real number because every estimate it appears in is an
inequality between reals.  These say the two readings agree on the ideal, so a paper
estimate and an ideal-gauge estimate are interchangeable rather than merely analogous. -/



end

end ExactSinTheta
end DavisKahan
end TauCeti
