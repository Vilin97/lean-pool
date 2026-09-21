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
import LeanPool.KaltonPeck.KaltonPeck.Support.CgpCompactRestriction
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularAdd

/-!
# Strictly singular lifting on the canonical Kalton--Peck space

This file uses biorthogonal interpolation to lift strict singularity from the canonical Hilbert
kernel and quotient to operators on the full canonical Kalton--Peck space.
-/


namespace KaltonPeck.Support.GraphFredholm

noncomputable
section

open Coordinates Symplectic StrictlySingular
open Function Set Filter Topology
open scoped ENNReal NNReal Topology lp BigOperators

private def interpolationTerm
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (φ : ℕ → StrongDual ℝ X) (e : ℕ → Y)
    (n : ℕ) : X →L[ℝ] Y :=
  (φ n).smulRight (e n)

private theorem interpolationTerm_norm_le
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (φ : ℕ → StrongDual ℝ X) (e : ℕ → Y)
    (n : ℕ) :
    ‖interpolationTerm φ e n‖ ≤ ‖φ n‖ * ‖e n‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖φ n (x : X) • e n‖ ≤
    (‖φ n‖ * ‖e n‖) * ‖x‖
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |φ n (x : X)| * ‖e n‖ =
        ‖φ n (x : X)‖ * ‖e n‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ (‖φ n‖ * ‖(x : X)‖) * ‖e n‖ :=
      mul_le_mul_of_nonneg_right ((φ n).le_opNorm (x : X))
        (norm_nonneg _)
    _ = (‖φ n‖ * ‖e n‖) * ‖x‖ := by
      ring

private theorem interpolationTerm_summable
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (φ : ℕ → StrongDual ℝ X) (e : ℕ → Y)
    (hsum : Summable (fun n => ‖φ n‖ * ‖e n‖)) :
    Summable (interpolationTerm φ e) := by
  apply Summable.of_norm (E := X →L[ℝ] Y)
  exact hsum.of_nonneg_of_le
    (fun n => norm_nonneg (interpolationTerm φ e n))
    (interpolationTerm_norm_le φ e)

private def interpolationOperator
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (φ : ℕ → StrongDual ℝ X) (e : ℕ → Y) :
    X →L[ℝ] Y :=
  ∑' n, interpolationTerm φ e n

private theorem interpolationOperator_apply
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (v : ℕ → X)
    (φ : ℕ → StrongDual ℝ X)
    (hbio : ∀ i j, φ i (v j) = if i = j then 1 else 0)
    (e : ℕ → Y)
    (hsum : Summable (fun n => ‖φ n‖ * ‖e n‖))
    (j : ℕ) :
    interpolationOperator φ e (v j) = e j := by
  have hTerms := interpolationTerm_summable φ e hsum
  have hApply :
      HasSum (fun n => interpolationTerm φ e n (v j))
        (interpolationOperator φ e (v j)) :=
    hTerms.hasSum.map (ContinuousLinearMap.apply ℝ Y (v j))
      (ContinuousLinearMap.apply ℝ Y (v j)).continuous
  have hterm :
      (fun n => interpolationTerm φ e n (v j)) =
        (fun n => if n = j then e j else 0) := by
    funext n
    by_cases hnj : n = j
    · subst n
      simp [interpolationTerm, hbio]
    · simp [interpolationTerm, hbio, hnj]
  rw [hterm] at hApply
  exact hApply.unique (hasSum_ite_eq j (e j))

private theorem interpolationOperator_apply_norm_le
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (φ : ℕ → StrongDual ℝ X) (e : ℕ → Y)
    (hsum : Summable (fun n => ‖φ n‖ * ‖e n‖))
    (x : X) :
    ‖interpolationOperator φ e x‖ ≤
      (∑' n, ‖φ n‖ * ‖e n‖) * ‖x‖ := by
  have hTerms := interpolationTerm_summable φ e hsum
  have hApply :
      HasSum (fun n => interpolationTerm φ e n x)
        (interpolationOperator φ e x) :=
    hTerms.hasSum.map (ContinuousLinearMap.apply ℝ Y x)
      (ContinuousLinearMap.apply ℝ Y x).continuous
  have hpoint (n : ℕ) :
      ‖interpolationTerm φ e n x‖ ≤
        (‖φ n‖ * ‖e n‖) * ‖x‖ := by
    exact (interpolationTerm φ e n).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right
        (interpolationTerm_norm_le φ e n) (norm_nonneg x))
  have hboundSummable :
      Summable (fun n => (‖φ n‖ * ‖e n‖) * ‖x‖) :=
    hsum.mul_right ‖x‖
  have hnormSummable :
      Summable (fun n => ‖interpolationTerm φ e n x‖) :=
    hboundSummable.of_nonneg_of_le
      (fun n => norm_nonneg (interpolationTerm φ e n x)) hpoint
  rw [← hApply.tsum_eq]
  exact (norm_tsum_le_tsum_norm hnormSummable).trans
    ((Summable.tsum_le_tsum hpoint hnormSummable hboundSummable).trans_eq
      (hsum.tsum_mul_right ‖x‖))

private theorem exists_antilipschitz_sub_of_apply_norm_le
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (S P : X →L[ℝ] Y) (K : NNReal) (d : ℝ)
    (hS : AntilipschitzWith K S)
    (_hd : 0 ≤ d)
    (hP : ∀ x, ‖P x‖ ≤ d * ‖x‖)
    (hsmall : (K : ℝ) * d < 1) :
    ∃ K' : NNReal, AntilipschitzWith K' (S - P) := by
  have hden : 0 < 1 - (K : ℝ) * d := sub_pos.mpr hsmall
  let K' : NNReal :=
    ⟨(K : ℝ) / (1 - (K : ℝ) * d),
      div_nonneg (NNReal.coe_nonneg K) hden.le⟩
  refine ⟨K', AntilipschitzWith.of_le_mul_dist ?_⟩
  intro x y
  have hPdist : dist (P x) (P y) ≤ d * dist x y := by
    simpa only [dist_eq_norm, map_sub] using hP (x - y)
  have hSdist :
      dist (S x) (S y) ≤
        dist ((S - P) x) ((S - P) y) + dist (P x) (P y) := by
    have heq :
        S (x - y) =
          (S - P) (x - y) + P (x - y) := by
      simp only [sub_apply]
      module
    have hnorm :=
      norm_add_le ((S - P) (x - y)) (P (x - y))
    rw [← heq] at hnorm
    simpa only [dist_eq_norm, map_sub] using hnorm
  have hlower := hS.le_mul_dist x y
  have hcore :
      dist x y * (1 - (K : ℝ) * d) ≤
        (K : ℝ) * dist ((S - P) x) ((S - P) y) := by
    calc
      dist x y * (1 - (K : ℝ) * d) =
          dist x y - (K : ℝ) * (d * dist x y) := by ring
      _ ≤ (K : ℝ) * dist (S x) (S y) -
          (K : ℝ) * (d * dist x y) := by
        linarith
      _ ≤ (K : ℝ) *
          (dist ((S - P) x) ((S - P) y) + dist (P x) (P y)) -
          (K : ℝ) * (d * dist x y) := by
        gcongr
      _ ≤ (K : ℝ) * dist ((S - P) x) ((S - P) y) := by
        have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
        nlinarith
  change dist x y ≤
    ((K : ℝ) / (1 - (K : ℝ) * d)) *
      dist ((S - P) x) ((S - P) y)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hden).2 hcore

/-- A sufficiently small perturbation into the kernel contradicts strict singularity there. -/
private theorem false_of_small_kernel_perturbation
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (M : Submodule ℝ Z) [CompleteSpace M] (hM : ¬ FiniteDimensional ℝ M)
    (T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hTi : IsStrictlySingular.{0, 0, 0, 0} (T.comp canonicalL2Inclusion))
    (S P : Z →L[ℝ] CanonicalRealKaltonPeck) (KS KT : ℝ≥0)
    (hKS : AntilipschitzWith KS S) (hKT : AntilipschitzWith KT (T.comp S))
    (d : ℝ) (hd : 0 ≤ d) (hPbound : ∀ x, ‖P x‖ ≤ d * ‖x‖)
    (hKSsmall : (KS : ℝ) * d < 1) (hKTsmall : (KT : ℝ) * (‖T‖ * d) < 1)
    (hkernel : ∀ x : M, canonicalL2Quotient ((S - P) (x : Z)) = 0) : False := by
  let SM : M →L[ℝ] CanonicalRealKaltonPeck :=
    S.comp M.subtypeL
  let PM : M →L[ℝ] CanonicalRealKaltonPeck :=
    P.comp M.subtypeL
  let J : M →L[ℝ] CanonicalRealKaltonPeck := SM - PM
  have hJ_eq (x : M) : J x = (S - P) (x : Z) := by
    rfl
  have hqJ (x : M) :
      canonicalL2Quotient (J x) = 0 := by
    exact hkernel x
  have hSManti : AntilipschitzWith KS SM := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x y ≤
      (KS : ℝ) * dist (S (x : Z)) (S (y : Z))
    rw [Subtype.dist_eq]
    exact hKS.le_mul_dist (x : Z) (y : Z)
  have hPMbound (x : M) : ‖PM x‖ ≤ d * ‖x‖ := by
    change ‖P (x : Z)‖ ≤ d * ‖x‖
    simpa only [Submodule.norm_coe] using hPbound (x : Z)
  obtain ⟨KJ, hJanti'⟩ :=
    exists_antilipschitz_sub_of_apply_norm_le
      SM PM KS d hSManti hd hPMbound hKSsmall
  have hJanti : AntilipschitzWith KJ J := hJanti'
  let TSM : M →L[ℝ] CanonicalRealKaltonPeck :=
    (T.comp S).comp M.subtypeL
  let TPM : M →L[ℝ] CanonicalRealKaltonPeck :=
    T.comp PM
  have hTSManti : AntilipschitzWith KT TSM := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x y ≤
      (KT : ℝ) * dist (T (S (x : Z))) (T (S (y : Z)))
    rw [Subtype.dist_eq]
    exact hKT.le_mul_dist (x : Z) (y : Z)
  have hTPMbound (x : M) :
      ‖TPM x‖ ≤ (‖T‖ * d) * ‖x‖ := by
    calc
      ‖TPM x‖ ≤ ‖T‖ * ‖PM x‖ := T.le_opNorm (PM x)
      _ ≤ ‖T‖ * (d * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hPMbound x) (norm_nonneg T)
      _ = (‖T‖ * d) * ‖x‖ := by ring
  obtain ⟨KTJ, hTJanti'⟩ :=
    exists_antilipschitz_sub_of_apply_norm_le
      TSM TPM KT (‖T‖ * d) hTSManti
        (mul_nonneg (norm_nonneg T) hd) hTPMbound hKTsmall
  have hTJ_identity :
      TSM - TPM = T.comp J := by
    ext x
    dsimp only [TSM, TPM, J, SM, PM]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  rw [hTJ_identity] at hTJanti'
  have hTJanti : AntilipschitzWith KTJ (T.comp J) := hTJanti'
  have hi_closed :
      IsClosed (canonicalL2Inclusion.range :
        Set CanonicalRealKaltonPeck) := by
    rw [canonicalL2Inclusion_range]
    exact canonicalL2Quotient.isClosed_ker
  let : CompleteSpace canonicalL2Inclusion.range :=
    hi_closed.completeSpace_coe
  let ir : CanonicalL2 →L[ℝ] canonicalL2Inclusion.range :=
    canonicalL2Inclusion.codRestrict canonicalL2Inclusion.range
      (fun x => ⟨x, rfl⟩)
  have hir_inj : Function.Injective ir := by
    intro x y hxy
    exact canonicalL2Inclusion_injective (congrArg Subtype.val hxy)
  have hir_surj : Function.Surjective ir := by
    rintro ⟨z, x, rfl⟩
    exact ⟨x, rfl⟩
  let ie :
      CanonicalL2 ≃L[ℝ] canonicalL2Inclusion.range :=
    ContinuousLinearEquiv.ofBijective ir
      (LinearMap.ker_eq_bot.mpr hir_inj)
      (LinearMap.range_eq_top.mpr hir_surj)
  let Jrange : M →L[ℝ] canonicalL2Inclusion.range :=
    J.codRestrict canonicalL2Inclusion.range (fun x => by
      rw [canonicalL2Inclusion_range]
      exact hqJ x)
  let L : M →L[ℝ] CanonicalL2 :=
    ie.symm.toContinuousLinearMap.comp Jrange
  have hiL : canonicalL2Inclusion.comp L = J := by
    ext x
    change canonicalL2Inclusion (ie.symm (Jrange x)) = J x
    have hir_apply :
        ir (ie.symm (Jrange x)) = Jrange x :=
      ie.apply_symm_apply (Jrange x)
    exact congrArg Subtype.val hir_apply
  have hLanti : ∃ KL, AntilipschitzWith KL L := by
    refine ⟨KJ * ‖canonicalL2Inclusion‖₊,
      AntilipschitzWith.of_le_mul_dist ?_⟩
    intro x y
    have hiLx : canonicalL2Inclusion (L x) = J x := by
      exact DFunLike.congr_fun hiL x
    have hiLy : canonicalL2Inclusion (L y) = J y := by
      exact DFunLike.congr_fun hiL y
    calc
      dist x y ≤ (KJ : ℝ) * dist (J x) (J y) :=
        hJanti.le_mul_dist x y
      _ = (KJ : ℝ) *
          dist (canonicalL2Inclusion (L x))
            (canonicalL2Inclusion (L y)) := by rw [hiLx, hiLy]
      _ ≤ (KJ : ℝ) *
          ((‖canonicalL2Inclusion‖₊ : ℝ) * dist (L x) (L y)) :=
        mul_le_mul_of_nonneg_left
          (canonicalL2Inclusion.lipschitzWith.dist_le_mul _ _)
          (NNReal.coe_nonneg KJ)
      _ = ((KJ * ‖canonicalL2Inclusion‖₊ : NNReal) : ℝ) *
          dist (L x) (L y) := by
        rw [NNReal.coe_mul]
        ring
  apply hTi M hM L hLanti
  refine ⟨KTJ, ?_⟩
  have hcomp :
      (T.comp canonicalL2Inclusion).comp L =
        T.comp J := by
    rw [ContinuousLinearMap.comp_assoc, hiL]
  rw [hcomp]
  exact hTJanti


-- The biorthogonal interpolation argument needs more elaboration time than the default limit.
/-- Canonical Proposition 5.3(b): strict singularity on the canonical kernel forces
strict singularity on all of `Z₂`. -/
theorem canonical_isStrictlySingular_of_inclusion_of_quotient
    (hq :
      IsStrictlySingular.{0, 0, 0, 0} canonicalL2Quotient)
    (T : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hTi : IsStrictlySingular.{0, 0, 0, 0}
      (T.comp canonicalL2Inclusion)) :
    IsStrictlySingular.{0, 0, 0, 0} T := by
  intro Z _ _ _ hZ S hS hTS
  obtain ⟨KS, hKS⟩ := hS
  obtain ⟨KT, hKT⟩ := hTS
  let U : Z →L[ℝ] CanonicalL2 :=
    canonicalL2Quotient.comp S
  have hU : IsStrictlySingular.{0, 0, 0, 0} U := by
    exact hq.precomp S
  obtain ⟨v, φ, hvnorm, hbio, hUsum, hprodsum⟩ :=
    IsStrictlySingular.exists_biorthogonal_sequence_summable hZ hU
  obtain ⟨C, hC, hkernel⟩ :=
    canonicalL2Quotient_kernel_approximation
  let A : ℝ := (KS : ℝ) + (KT : ℝ) * ‖T‖ + 1
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  let p : ℕ → ℝ := fun n => ‖φ n‖ * ‖U (v n)‖
  let ε : ℝ := 1 / (2 * A * C)
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  have hptend :
      Tendsto (fun N => ∑' n, p (n + N)) atTop (𝓝 0) :=
    _root_.tendsto_sum_nat_add p
  have hpevent : ∀ᶠ N in atTop, (∑' n, p (n + N)) < ε :=
    hptend.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpevent
  have htail : (∑' n, p (n + N)) < ε := hN N le_rfl
  let vt : ℕ → Z := fun n => v (n + N)
  let φt : ℕ → StrongDual ℝ Z := fun n => φ (n + N)
  have hbiot (i j : ℕ) :
      φt i (vt j) = if i = j then 1 else 0 := by
    simpa [φt, vt] using hbio (i + N) (j + N)
  have hprodtail :
      Summable (fun n => ‖φt n‖ * ‖U (vt n)‖) := by
    have hpcomp : Summable (fun n => p (n + N)) :=
      hprodsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    simpa [p, φt, vt] using hpcomp
  let M : Submodule ℝ Z :=
    (Submodule.span ℝ (Set.range vt)).topologicalClosure
  have hMclosed : IsClosed (M : Set Z) :=
    Submodule.isClosed_topologicalClosure _
  let : CompleteSpace M := hMclosed.completeSpace_coe
  have hM : ¬ FiniteDimensional ℝ M :=
    not_finiteDimensional_topologicalClosure_span_of_biorthogonal hbiot
  let k : ℕ → canonicalL2Quotient.ker :=
    fun n => Classical.choose (hkernel (S (vt n)))
  have hk_close (n : ℕ) :
      ‖S (vt n) - (k n : CanonicalRealKaltonPeck)‖ ≤
        C * ‖U (vt n)‖ := by
    have hk := Classical.choose_spec (hkernel (S (vt n)))
    simpa only [U, ContinuousLinearMap.comp_apply] using hk
  have hk_range (n : ℕ) :
      (k n : CanonicalRealKaltonPeck) ∈ canonicalL2Inclusion.range := by
    rw [canonicalL2Inclusion_range]
    exact (k n).property
  let a : ℕ → CanonicalL2 :=
    fun n => Classical.choose (hk_range n)
  have hia (n : ℕ) :
      canonicalL2Inclusion (a n) =
        (k n : CanonicalRealKaltonPeck) :=
    Classical.choose_spec (hk_range n)
  let e : ℕ → CanonicalRealKaltonPeck :=
    fun n => S (vt n) - canonicalL2Inclusion (a n)
  have he_bound (n : ℕ) :
      ‖e n‖ ≤ C * ‖U (vt n)‖ := by
    simpa only [e, hia] using hk_close n
  have he_weight (n : ℕ) :
      ‖φt n‖ * ‖e n‖ ≤
        C * (‖φt n‖ * ‖U (vt n)‖) := by
    calc
      ‖φt n‖ * ‖e n‖ ≤
          ‖φt n‖ * (C * ‖U (vt n)‖) :=
        mul_le_mul_of_nonneg_left (he_bound n) (norm_nonneg _)
      _ = C * (‖φt n‖ * ‖U (vt n)‖) := by ring
  have he_summable :
      Summable (fun n => ‖φt n‖ * ‖e n‖) :=
    (hprodtail.mul_left C).of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      he_weight
  let d : ℝ := ∑' n, ‖φt n‖ * ‖e n‖
  have hd : 0 ≤ d := by
    dsimp only [d]
    exact tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hd_bound :
      d ≤ C * ∑' n, p (n + N) := by
    calc
      d ≤ ∑' n, C * (‖φt n‖ * ‖U (vt n)‖) := by
        exact Summable.tsum_le_tsum he_weight he_summable
          (hprodtail.mul_left C)
      _ = C * ∑' n, ‖φt n‖ * ‖U (vt n)‖ :=
        (hprodtail.tsum_mul_left C)
      _ = C * ∑' n, p (n + N) := by
        rfl
  have hden : 0 < 2 * A * C := by positivity
  have htailMul :
      (∑' n, p (n + N)) * (2 * A * C) < 1 := by
    exact (lt_div_iff₀ hden).1 (by simpa [ε] using htail)
  have hAd : A * d < 1 := by
    have hnonnegA : 0 ≤ A := hA.le
    have hboundMul :
        A * d ≤ A * (C * ∑' n, p (n + N)) :=
      mul_le_mul_of_nonneg_left hd_bound hnonnegA
    nlinarith
  have hKSsmall : (KS : ℝ) * d < 1 := by
    have hKSA : (KS : ℝ) ≤ A := by
      dsimp only [A]
      nlinarith [mul_nonneg (NNReal.coe_nonneg KT) (norm_nonneg T)]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hKSA hd) hAd
  have hKTsmall : (KT : ℝ) * (‖T‖ * d) < 1 := by
    have hKTA : (KT : ℝ) * ‖T‖ ≤ A := by
      dsimp only [A]
      nlinarith [NNReal.coe_nonneg KS]
    have : ((KT : ℝ) * ‖T‖) * d < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hKTA hd) hAd
    nlinarith
  let P : Z →L[ℝ] CanonicalRealKaltonPeck :=
    interpolationOperator φt e
  have hPv (n : ℕ) : P (vt n) = e n :=
    interpolationOperator_apply vt φt hbiot e he_summable n
  have hPbound (x : Z) : ‖P x‖ ≤ d * ‖x‖ := by
    exact interpolationOperator_apply_norm_le φt e he_summable x
  let J₀ : Z →L[ℝ] CanonicalRealKaltonPeck := S - P
  have hJv (n : ℕ) :
      J₀ (vt n) = canonicalL2Inclusion (a n) := by
    dsimp only [J₀]
    rw [sub_apply, hPv]
    dsimp only [e]
    abel
  let F : Z →L[ℝ] CanonicalL2 :=
    canonicalL2Quotient.comp J₀
  have hFv (n : ℕ) : F (vt n) = 0 := by
    dsimp only [F]
    rw [ContinuousLinearMap.comp_apply, hJv]
    apply Subtype.ext
    funext j
    rw [canonicalL2Quotient_apply, canonicalL2Inclusion_coordinates]
    rfl
  have hspan : Submodule.span ℝ (Set.range vt) ≤ F.ker := by
    apply Submodule.span_le.2
    rintro _ ⟨n, rfl⟩
    exact hFv n
  have hMker : M ≤ F.ker := by
    change (Submodule.span ℝ (Set.range vt)).topologicalClosure ≤ F.ker
    exact Submodule.topologicalClosure_minimal _ hspan F.isClosed_ker
  exact false_of_small_kernel_perturbation M hM T hTi S P KS KT hKS hKT d hd
    hPbound hKSsmall hKTsmall (fun x => hMker x.property)

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
