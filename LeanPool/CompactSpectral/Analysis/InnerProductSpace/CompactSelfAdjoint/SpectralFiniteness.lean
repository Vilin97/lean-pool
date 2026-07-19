/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.LinearAlgebra.Eigenspace.Basic
import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactOperatorOrthonormal

/-!
# Compact self-adjoint operators: spectral finiteness toolkit

This file collects “spectral finiteness” facts for compact self-adjoint operators on Hilbert spaces:
finite-dimensionality of nonzero eigenspaces, finiteness away from `0`, countability of the nonzero
point spectrum, isolation of nonzero eigenvalues, and a packaged `‖μ n‖ → 0` statement for injective
eigenvalue sequences.

These are standard ingredients for spectral-iteration proofs and compact-resolvent applications.

## Main results

- `CompactSelfAdjoint.finiteDimensional_eigenspace_of_isCompactOperator`
- `CompactSelfAdjoint.finite_set_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint`
- `CompactSelfAdjoint.countable_set_hasEigenvalue_ne_zero_of_isCompactOperator_of_isSelfAdjoint`
- `CompactSelfAdjoint.exists_ball_hasEigenvalue_eq_of_isCompactOperator_of_isSelfAdjoint`
- `CompactSelfAdjoint.finiteDimensional_iSup_eigenspace_norm_ge`

- `CompactSelfAdjoint.tendsto_norm_of_injective_hasEigenvalue_of_isCompactOperator_of_isSelfAdjoint`
-/

namespace CompactSelfAdjoint

open Filter Topology Metric
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-! ### Finite-dimensionality of nonzero eigenspaces -/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- If `T` is compact, then the eigenspace for a nonzero eigenvalue is finite-dimensional. -/
theorem finiteDimensional_eigenspace_of_isCompactOperator (T : E →L[𝕜] E)
    (hTc : IsCompactOperator (T : E → E)) {μ : 𝕜} (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace (T : E →ₗ[𝕜] E) μ) := by
  classical
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  change FiniteDimensional 𝕜 (t.eigenspace μ)
  by_contra hfd
  obtain ⟨R, f, _hR, hfR, hpair⟩ :=
    exists_seq_norm_le_one_le_norm_sub (𝕜 := 𝕜) (E := t.eigenspace μ) hfd
  let x : ℕ → E := fun n => (f n : E)
  have hx_ball : ∀ n, x n ∈ Metric.closedBall (0 : E) R := by
    intro n
    have hx_norm : ‖x n‖ ≤ R := by
      simpa [x] using hfR n
    simp_all
  have hK : IsCompact (closure ((T : E →ₛₗ[RingHom.id 𝕜] E) '' Metric.closedBall (0 : E) R)) := by
    simpa using
      (IsCompactOperator.isCompact_closure_image_closedBall
        (𝕜₁ := 𝕜) (𝕜₂ := 𝕜) (σ₁₂ := RingHom.id 𝕜)
        (M₁ := E) (M₂ := E) (f := (T : E →ₛₗ[RingHom.id 𝕜] E)) hTc R)
  let y : ℕ → E := fun n => T (x n)
  have hy_mem : ∀ n,
      y n ∈ closure ((T : E →ₛₗ[RingHom.id 𝕜] E) '' Metric.closedBall (0 : E) R) := by
    intro n
    apply subset_closure
    exact ⟨x n, hx_ball n, rfl⟩
  obtain ⟨_a, _haK, φ, hφmono, hlim⟩ := hK.tendsto_subseq hy_mem
  have hμnorm : 0 < ‖μ‖ := (norm_pos_iff).2 hμ
  have hε : 0 < (‖μ‖ / 2 : ℝ) := by
    simpa [div_eq_mul_inv] using (half_pos hμnorm)
  have hsep : Pairwise fun m n => ‖μ‖ ≤ ‖y m - y n‖ := by
    intro m n hmn
    have hpair_mn : 1 ≤ ‖f m - f n‖ := hpair hmn
    have hm : t (x m) = μ • x m := by
      have : x m ∈ t.eigenspace μ := (f m).property
      simpa [x] using (Module.End.mem_eigenspace_iff (f := t) (μ := μ) (x := x m)).1 this
    have hn : t (x n) = μ • x n := by
      have : x n ∈ t.eigenspace μ := (f n).property
      simpa [x] using (Module.End.mem_eigenspace_iff (f := t) (μ := μ) (x := x n)).1 this
    have hym : y m = μ • x m := by
      simpa [y, t] using hm
    have hyn : y n = μ • x n := by
      simpa [y, t] using hn
    calc
      (‖μ‖ : ℝ) = ‖μ‖ * 1 := by simp
      _ ≤ ‖μ‖ * ‖f m - f n‖ := by gcongr
      _ = ‖μ‖ * ‖x m - x n‖ := by simp [x]
      _ = ‖μ • (x m - x n)‖ := by simp [norm_smul]
      _ = ‖μ • x m - μ • x n‖ := by simp [smul_sub]
      _ = ‖y m - y n‖ := by simp [hym, hyn]
  have hC : CauchySeq (y ∘ φ) := hlim.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.1 hC) (‖μ‖ / 2) hε
  have hlt : dist ((y ∘ φ) (N + 1)) ((y ∘ φ) N) < ‖μ‖ / 2 := hN (N + 1) (Nat.le_succ N)
  have hne : φ (N + 1) ≠ φ N := ne_of_gt (hφmono (Nat.lt_succ_self N))
  have hge : ‖μ‖ ≤ dist ((y ∘ φ) (N + 1)) ((y ∘ φ) N) := by
    have h := hsep hne
    simpa [Function.comp_apply, dist_eq_norm] using h
  have : ¬ (‖μ‖ ≤ ‖μ‖ / 2) := by
    simp_all
  exact this (le_trans hge (le_of_lt hlt))
end
/-! ### Finiteness of large eigenvalues (self-adjoint case) -/
/-- For a compact self-adjoint operator, there is no infinite sequence of distinct eigenvalues whose
norm is bounded below by `ε > 0`.
This is a standard compact spectral theorem ingredient: since distinct eigenspaces are orthogonal,
such a sequence would give an orthonormal family `e n` with `‖T (e n)‖ = ‖μ n‖ ≥ ε`, contradicting
that compact operators send orthonormal sequences to norm-null sequences. -/
lemma not_exists_injective_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ μ : ℕ → 𝕜, Function.Injective μ ∧ (∀ n, ε ≤ ‖μ n‖) ∧
        (∀ n, Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) (μ n)) := by
  classical
  intro h
  rcases h with ⟨μ, hμinj, hμge, hμeig⟩
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  have hSymm : t.IsSymmetric := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := T)).1 hT
  choose v hv using fun n =>
    (Module.End.HasEigenvalue.exists_hasEigenvector (f := t) (μ := μ n) (hμ := hμeig n))
  have hv_mem : ∀ n, v n ∈ t.eigenspace (μ n) := fun n =>
    (Module.End.hasEigenvector_iff.mp (hv n)).1
  have hv_ne0 : ∀ n, v n ≠ 0 := fun n =>
    (Module.End.hasEigenvector_iff.mp (hv n)).2
  let c : ℕ → 𝕜 := fun n => (((‖v n‖)⁻¹ : ℝ) : 𝕜)
  let e : ℕ → E := fun n => c n • v n
  have he_mem : ∀ n, e n ∈ t.eigenspace (μ n) := by
    intro n
    exact (t.eigenspace (μ n)).smul_mem (c n) (hv_mem n)
  have he_norm : ∀ n, ‖e n‖ = (1 : ℝ) := by
    intro n
    simp [e, c, hv_ne0 n, norm_smul]
  have he : Orthonormal 𝕜 e := by
    classical
    refine (orthonormal_iff_ite).2 ?_
    intro i j
    by_cases hij : i = j
    · simp_all
    · have hijμ : μ i ≠ μ j := by
        intro hEq
        exact hij (hμinj hEq)
      have hOrtho : (t.eigenspace (μ i)) ⟂ (t.eigenspace (μ j)) :=
        (hSymm.orthogonalFamily_eigenspaces).isOrtho hijμ
      have hji : inner 𝕜 (e j) (e i) = 0 := hOrtho (he_mem i) (e j) (he_mem j)
      have hij' : inner 𝕜 (e i) (e j) = 0 := (inner_eq_zero_symm).2 hji
      simpa [hij] using hij'
  have hTe : ∀ n, T (e n) = μ n • e n := by
    intro n
    have hv_eq : T (v n) = μ n • v n := by
      simpa [t] using (Module.End.mem_eigenspace_iff (f := t) (μ := μ n) (x := v n)).1 (hv_mem n)
    calc
      T (e n) = T (c n • v n) := rfl
      _ = c n • T (v n) := by simp
      _ = c n • (μ n • v n) := by simp [hv_eq]
      _ = μ n • (c n • v n) := by
            simp [smul_smul, mul_comm]
      _ = μ n • e n := rfl
  have hnorm_e : ∀ n, ‖T (e n)‖ = ‖μ n‖ := by
    intro n
    simp [hTe n, norm_smul, he_norm n]
  have hTnorm : Tendsto (fun n => ‖T (e n)‖) atTop (𝓝 (0 : ℝ)) :=
    CompactSpectral.tendsto_norm_apply_of_isCompactOperator_of_orthonormal
      (𝕜 := 𝕜) (E := E) T hTc he
  have hμlt : ∀ᶠ n in atTop, ‖μ n‖ < ε := by
    have hε' : (0 : ℝ) < ε := hε
    have hTlt : ∀ᶠ n in atTop, ‖T (e n)‖ < ε :=
      Filter.Tendsto.eventually_lt_const (u := ε) (v := (0 : ℝ)) hε' hTnorm
    simp_all
  rcases (Filter.Eventually.exists hμlt) with ⟨n, hn⟩
  exact (not_lt_of_ge (hμge n)) hn
/-- For a compact self-adjoint operator, the set of eigenvalues with norm bounded below by
`ε > 0` is finite. -/
theorem finite_set_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | ε ≤ ‖μ‖ ∧ Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ}.Finite := by
  classical
  by_contra hfin
  let s : Set 𝕜 :=
    {μ : 𝕜 | ε ≤ ‖μ‖ ∧ Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ}
  have hsInf : s.Infinite := by
    by_contra hs
    exact hfin ((Set.not_infinite (s := s)).1 hs)
  let emb : Function.Embedding ℕ s.Elem := Set.Infinite.natEmbedding s hsInf
  let μ : ℕ → 𝕜 := fun n => (emb n : s.Elem).1
  have hμinj : Function.Injective μ := by
    intro m n hmn
    apply emb.injective
    ext
    exact hmn
  have hμmem : ∀ n, μ n ∈ s := by
    intro n
    exact (emb n : s.Elem).property
  have hμge : ∀ n, ε ≤ ‖μ n‖ := fun n => (hμmem n).1
  have hμeig :
      ∀ n, Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) (μ n) := fun n => (hμmem n).2
  exact
    (not_exists_injective_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
        (𝕜 := 𝕜) (E := E) T hT hTc hε) ⟨μ, hμinj, hμge, hμeig⟩
/-- For a compact self-adjoint operator, the set of nonzero eigenvalues is countable (indeed, only
`0` can be an accumulation point). -/
theorem countable_set_hasEigenvalue_ne_zero_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E)) :
    {μ : 𝕜 | μ ≠ 0 ∧ Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ}.Countable := by
  classical
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  let s : Set 𝕜 := {μ : 𝕜 | μ ≠ 0 ∧ t.HasEigenvalue μ}
  let u : ℕ → Set 𝕜 :=
    fun n => {μ : 𝕜 | (1 : ℝ) / ((n : ℝ) + 1) ≤ ‖μ‖ ∧ t.HasEigenvalue μ}
  have hsub : s ⊆ ⋃ n : ℕ, u n := by
    intro μ hμ
    have hpos : 0 < ‖μ‖ := (norm_pos_iff).2 hμ.1
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    have hn' : (1 : ℝ) / ((n : ℝ) + 1) ≤ ‖μ‖ := le_of_lt hn
    exact ⟨hn', hμ.2⟩
  have hcountU : (⋃ n : ℕ, u n).Countable := by
    refine Set.countable_iUnion ?_
    intro n
    have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      simpa using (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
    exact
      (finite_set_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
          (𝕜 := 𝕜) (E := E) T hT hTc (ε := (1 : ℝ) / ((n : ℝ) + 1)) hε).countable
  exact hcountU.mono hsub
/-- For a compact self-adjoint operator, any injective eigenvalue sequence must have eigenvalues
converging to `0` in norm. -/
theorem tendsto_norm_of_injective_hasEigenvalue_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {μ : ℕ → 𝕜} (hμinj : Function.Injective μ)
    (hμeig : ∀ n, Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) (μ n)) :
    Tendsto (fun n => ‖μ n‖) atTop (𝓝 (0 : ℝ)) := by
  classical
  refine (NormedAddCommGroup.tendsto_atTop (f := fun n => (‖μ n‖ : ℝ)) (b := (0 : ℝ))).2 ?_
  intro ε hε
  have hev : ∀ᶠ n in atTop, ‖μ n‖ < ε := by
    by_contra hnot
    have hfreq : Filter.Frequently (fun n => ε ≤ ‖μ n‖) atTop := by
      simpa [Filter.Frequently, not_le] using hnot
    have hInf : (setOf fun n => ε ≤ ‖μ n‖).Infinite :=
      (Nat.frequently_atTop_iff_infinite).1 hfreq
    let emb : Function.Embedding ℕ ((setOf fun n => ε ≤ ‖μ n‖).Elem) :=
      Set.Infinite.natEmbedding _ hInf
    let idx : ℕ → ℕ := fun n => (emb n : (setOf fun n => ε ≤ ‖μ n‖).Elem).1
    have hidx_inj : Function.Injective idx := fun m n hmn => by
      apply emb.injective
      ext
      exact hmn
    have hidx_ge : ∀ n, ε ≤ ‖μ (idx n)‖ := fun n =>
      (emb n : (setOf fun n => ε ≤ ‖μ n‖).Elem).property
    have hμ' :
        ¬ ∃ μ' : ℕ → 𝕜, Function.Injective μ' ∧ (∀ n, ε ≤ ‖μ' n‖) ∧
            (∀ n, Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) (μ' n)) :=
      not_exists_injective_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
        (𝕜 := 𝕜) (E := E) T hT hTc hε
    have hcontra :
        ∃ μ' : ℕ → 𝕜, Function.Injective μ' ∧ (∀ n, ε ≤ ‖μ' n‖) ∧
            (∀ n, Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) (μ' n)) := by
      refine ⟨fun n => μ (idx n), ?_, ?_, ?_⟩
      · exact hμinj.comp hidx_inj
      · simp_all
      · simp_all
    exact hμ' hcontra
  simp_all
/-! ### Isolation of nonzero eigenvalues -/
/-- For a compact self-adjoint operator, any nonzero eigenvalue is isolated among eigenvalues. -/
lemma exists_ball_hasEigenvalue_eq_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {μ : 𝕜} (hμ0 : μ ≠ 0)
    (hμeig : Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ) :
    ∃ r > 0,
      ∀ {ν : 𝕜},
        Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) ν →
          dist ν μ < r → ν = μ := by
  classical
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  let ε0 : ℝ := ‖μ‖ / 2
  have hε0 : 0 < ε0 := by
    simpa [ε0, div_eq_mul_inv] using (half_pos ((norm_pos_iff).2 hμ0))
  let s : Set 𝕜 := {ν : 𝕜 | ε0 ≤ ‖ν‖ ∧ t.HasEigenvalue ν}
  have hsFin : s.Finite :=
    finite_set_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := 𝕜) (E := E) (T := T) hT hTc (ε := ε0) hε0
  let F : Finset 𝕜 := hsFin.toFinset
  have hμF : μ ∈ F := by
    have hμs : μ ∈ s := by
      refine ⟨?_, hμeig⟩
      have : (ε0 : ℝ) ≤ ‖μ‖ := by
        simp [ε0]
      exact this
    exact (hsFin.mem_toFinset (a := μ)).2 hμs
  have hnorm_ge_of_ball {ν : 𝕜} (hν : dist ν μ < ε0) : ε0 ≤ ‖ν‖ := by
    -- From `‖μ‖ ≤ ‖μ - ν‖ + ‖ν‖` and `‖μ - ν‖ ≤ ε0 = ‖μ‖/2`, conclude `ε0 ≤ ‖ν‖`.
    have htri : ‖μ‖ ≤ ‖μ - ν‖ + ‖ν‖ := by
      -- `μ = (μ - ν) + ν`
      simpa [sub_eq_add_neg, add_assoc] using (norm_add_le (μ - ν) ν)
    have hsub : ‖μ‖ - ‖μ - ν‖ ≤ ‖ν‖ := by
      refine (sub_le_iff_le_add).2 ?_
      simpa [add_comm, add_left_comm, add_assoc] using htri
    have hnorm_sub : ‖μ - ν‖ ≤ ε0 := by
      have : ‖ν - μ‖ ≤ ε0 := le_of_lt (by simpa [ε0, dist_eq_norm] using hν)
      simpa [norm_sub_rev] using this
    have hmid : (ε0 : ℝ) ≤ ‖μ‖ - ‖μ - ν‖ := by
      have := sub_le_sub_left hnorm_sub ‖μ‖
      -- `‖μ‖ - ε0 = ε0`
      simpa [ε0, sub_half] using this
    exact le_trans hmid hsub
  by_cases hNonempty : (F.erase μ).Nonempty
  · -- There are other eigenvalues in the finite set `s`; use the minimum distance to them.
    let D : Finset ℝ := (F.erase μ).image fun ν => dist ν μ
    have hDne : D.Nonempty := by
      rcases hNonempty with ⟨ν, hν⟩
      refine ⟨dist ν μ, ?_⟩
      exact Finset.mem_image.2 ⟨ν, hν, rfl⟩
    let d : ℝ := D.min' hDne
    have hd_mem : d ∈ D := Finset.min'_mem D hDne
    rcases Finset.mem_image.1 hd_mem with ⟨ν0, hν0, hd⟩
    have hν0ne : ν0 ≠ μ := (Finset.mem_erase.1 hν0).1
    have hdpos : 0 < d := by
      have : 0 < dist ν0 μ := (dist_pos).2 hν0ne
      simpa [d, hd] using this
    let r : ℝ := min ε0 (d / 2)
    have hrpos : 0 < r := by
      refine lt_min hε0 (half_pos hdpos)
    refine ⟨r, hrpos, ?_⟩
    intro ν hνeig hdist
    have hdistε : dist ν μ < ε0 := lt_of_lt_of_le hdist (min_le_left _ _)
    have hνs : ν ∈ s := ⟨hnorm_ge_of_ball (ν := ν) hdistε, hνeig⟩
    have hνF : ν ∈ F := (hsFin.mem_toFinset (a := ν)).2 hνs
    by_contra hne
    have hνerase : ν ∈ F.erase μ := by
      exact Finset.mem_erase.2 ⟨hne, hνF⟩
    have hd_le : d ≤ dist ν μ := by
      have hmem : dist ν μ ∈ D := by
        exact Finset.mem_image.2 ⟨ν, hνerase, rfl⟩
      have : D.min' hDne ≤ dist ν μ := Finset.min'_le D (dist ν μ) hmem
      simpa [d] using this
    have hlt : dist ν μ < d / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
    have : ¬ d ≤ d / 2 := by
      simp_all
    exact this (le_trans hd_le (le_of_lt hlt))
  · -- No other eigenvalues in the finite set `s`; use the radius `ε0 = ‖μ‖/2`.
    have hErase : F.erase μ = ∅ := Finset.not_nonempty_iff_eq_empty.1 hNonempty
    refine ⟨ε0, hε0, ?_⟩
    intro ν hνeig hdist
    have hνs : ν ∈ s := ⟨hnorm_ge_of_ball (ν := ν) hdist, hνeig⟩
    have hνF : ν ∈ F := (hsFin.mem_toFinset (a := ν)).2 hνs
    have hνμ : ν = μ := by
      by_contra hne
      have : ν ∈ F.erase μ := Finset.mem_erase.2 ⟨hne, hνF⟩
      -- Reduce noise: `erase` is empty, so membership is impossible.
      simp [hErase] at this
    exact hνμ
/-! ### Finite-dimensionality of large spectral subspaces -/
/-- For a compact self-adjoint operator, the sum (iSup) of eigenspaces corresponding to eigenvalues
with `‖μ‖ ≥ ε` is finite-dimensional. -/
lemma finiteDimensional_iSup_eigenspace_norm_ge
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E))
    {ε : ℝ} (hε : 0 < ε) :
    let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
    FiniteDimensional 𝕜
      ((⨆ i : {μ : 𝕜 // ε ≤ ‖μ‖ ∧ t.HasEigenvalue μ}, t.eigenspace i.1) : Submodule 𝕜 E) := by
  classical
  intro t
  let s : Set 𝕜 := {μ : 𝕜 | ε ≤ ‖μ‖ ∧ t.HasEigenvalue μ}
  have hsFin : s.Finite :=
    finite_set_hasEigenvalue_norm_ge_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := 𝕜) (E := E) (T := T) hT hTc (ε := ε) hε
  -- Use the finite index type `s.Elem` and `Submodule.finiteDimensional_iSup`.
  have hfd_each : ∀ i : s.Elem, FiniteDimensional 𝕜 (t.eigenspace i.1) := by
    intro i
    have hi : i.1 ∈ s := i.2
    have hne : (i.1 : 𝕜) ≠ 0 := by
      have : (0 : ℝ) < ‖(i.1 : 𝕜)‖ := lt_of_lt_of_le hε hi.1
      exact (norm_pos_iff).1 this
    exact
      finiteDimensional_eigenspace_of_isCompactOperator (𝕜 := 𝕜) (E := E) (T := T) hTc (μ := i.1)
        hne
  letI : Fintype s.Elem := hsFin.fintype
  haveI : ∀ i : s.Elem, FiniteDimensional 𝕜 (t.eigenspace i.1) := hfd_each
  -- Rewrite the target `iSup` index type to `s.Elem` using definitional equality of `s`.
  exact (inferInstance : FiniteDimensional 𝕜 ((⨆ i : s.Elem, t.eigenspace i.1) : Submodule 𝕜 E))
end CompactSelfAdjoint
