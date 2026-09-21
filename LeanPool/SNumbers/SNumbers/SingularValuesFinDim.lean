/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Uniqueness
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Singular numbers coincide with all `s`-numbers (finite dimension)

For operators between **finite-dimensional** Hilbert spaces, Mathlib's
singular numbers `LinearMap.singularValues` agree with **every** `s`-number
sequence:

```
s S n = σₙ(S)    for every s-number sequence s.
```

## Strategy and why

The statement factors through the approximation numbers:

```
s S n  =  aₙ(S)            (Pietsch uniqueness on Hilbert spaces)
       =  σₙ^{proj}(S)     (Eckart–Young, 'singular values' from the SVD)
       =  σₙ(S)            (Mathlib's eigenvalue-defined singular values)
```

* **Uniqueness** (`allSNumbers_eq_on_HilbertSpace`) gives the first step for
  *every* `s` at once — this is why it suffices to treat `aₙ`.
* **Eckart–Young** (`SVD.svd_sigma_eq_approx`) gives the second step. It
  depends on the SVD `IsCompactOperator.SVD` which works in finite dimension.
* The third step `σ^{proj} = σ` (the **project's singular values equal
  Mathlib's**, which are `√` of the eigenvalues of `S* ∘ S`) is
  `project_singularValues_eq`. It is proved by diagonalising `S* ∘ S` (the `uₖ`
  are eigenvectors with eigenvalues `σₖ²`) and matching eigenvalue
  multiplicities with Mathlib's `card_filter_eigenvalues_eq`.

## Main result

* `sn_eq_singularValues_of_finiteDimensional` — `sₙ = σₙ` for every `s`-number
  sequence. This is general: specialising `s` to the approximation numbers
  gives `aₙ = σₙ`, so no separate statement is needed.
-/

universe u

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
variable [Nontrivial H₁] [Nontrivial H₂]

/-! ### Eigenvectors of `S* ∘ S` from the SVD

The SVD expansion `S = ∑ σₖ ⟪uₖ, ·⟫ vₖ` gives, after collapsing the sum at a
basis vector, `S uₖ = σₖ vₖ` (`SVD.svd_apply_left`) and dually `S* vₖ = σₖ uₖ`
(`svd_adjoint_apply` below). Composing, `S*∘S uₖ = σₖ² uₖ`: the `uₖ` are
eigenvectors of the Gram operator `S* ∘ S` with eigenvalues `σₖ²`. This is the
analytic heart of the coincidence with Mathlib's eigenvalue-defined singular
values. -/

omit [Nontrivial H₁] [Nontrivial H₂] in
/-- **Dual SVD relation `S* vₖ = σₖ uₖ`.** Testing against an arbitrary `x`,
`⟪vₖ, S x⟫` collapses (orthonormality of the `vⱼ` and the nonzero-`σ` tie) to
`σₖ ⟪uₖ, x⟫`, which is `⟪σₖ uₖ, x⟫`. -/
private lemma svd_adjoint_apply {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₂}
    (hv : SVD.OrthonormalOrZero 𝕜 v) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) (k : ℕ) :
    LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) (v k) = (σ k : 𝕜) • u k := by
  classical
  refine ext_inner_right 𝕜 fun x => ?_
  have hval : (inner 𝕜 (v k) (S x) : 𝕜)
      = (σ k : 𝕜) * inner 𝕜 (u k) x * (‖v k‖ : 𝕜) ^ 2 := by
    have h := (hsum x).mapL (innerSL 𝕜 (v k))
    simp only [innerSL_apply_apply, inner_smul_right] at h
    have hfun : (fun j => ((σ j : 𝕜) * inner 𝕜 (u j) x) * inner 𝕜 (v k) (v j))
        = fun j => if j = k then (σ k : 𝕜) * inner 𝕜 (u k) x * (‖v k‖ : 𝕜) ^ 2 else 0 := by
      funext j
      rw [hv.inner_eq k j]
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [if_neg (fun e => hjk e.symm), mul_zero, if_neg hjk]
    rw [hfun] at h
    exact h.unique (hasSum_ite_eq k _)
  rw [LinearMap.adjoint_inner_left, ContinuousLinearMap.coe_coe, hval, inner_smul_left,
    RCLike.conj_ofReal]
  rcases hv.1 k with h1 | h0
  · rw [h1]; push_cast; ring
  · have hσ : σ k = 0 := by by_contra h; exact hvt k h h0
    rw [hσ]; simp

omit [Nontrivial H₁] [Nontrivial H₂] in
/-- **`uₖ` is an eigenvector of `S* ∘ S` with eigenvalue `σₖ²`.** Immediate from
`S uₖ = σₖ vₖ` and `S* vₖ = σₖ uₖ`. -/
private lemma svd_adjoint_comp_self_apply {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₂}
    (hu : SVD.OrthonormalOrZero 𝕜 u) (hv : SVD.OrthonormalOrZero 𝕜 v)
    (hut : ∀ k, σ k ≠ 0 → u k ≠ 0) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) (k : ℕ) :
    (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂)) (u k)
      = ((σ k : ℝ) ^ 2 : 𝕜) • u k := by
  have hSu : (S : H₁ →ₗ[𝕜] H₂) (u k) = (σ k : 𝕜) • v k := by
    rw [ContinuousLinearMap.coe_coe]; exact SVD.svd_apply_left hu hut hsum k
  rw [LinearMap.comp_apply, hSu, map_smul, svd_adjoint_apply hv hvt hsum k, smul_smul]
  congr 1
  ring

omit [Nontrivial H₁] in
/-- **At most `finrank H₁` singular values are nonzero.** If `σ k ≠ 0` with
`k ≥ finrank H₁`, then `σ 0, …, σ k` are all `> 0` (antitone), so `u 0, …, u k`
is an orthonormal family of `k + 1 > finrank H₁` vectors — impossible. -/
private lemma svd_sigma_eq_zero_of_finrank_le {σ : ℕ → ℝ} {u : ℕ → H₁}
    (hσ0 : ∀ k, 0 ≤ σ k) (hσanti : _root_.Antitone σ) (hu : SVD.OrthonormalOrZero 𝕜 u)
    (hut : ∀ k, σ k ≠ 0 → u k ≠ 0) {k : ℕ} (hk : Module.finrank 𝕜 H₁ ≤ k) : σ k = 0 := by
  classical
  by_contra hσk
  have hpos : ∀ i : Fin (k + 1), 0 < σ ↑i := fun i =>
    lt_of_lt_of_le (lt_of_le_of_ne (hσ0 k) (Ne.symm hσk)) (hσanti (Nat.lt_succ_iff.mp i.2))
  have hni : ∀ i : Fin (k + 1), ‖u ↑i‖ = 1 := fun i => by
    rcases hu.1 ↑i with h1 | h0
    · exact h1
    · exact absurd h0 (hut ↑i (ne_of_gt (hpos i)))
  have horth : Orthonormal 𝕜 (fun i : Fin (k + 1) => u ↑i) :=
    hu.orthonormal_comp (fun _ _ e => Fin.ext e) hni
  have hcard := horth.linearIndependent.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

/-! ### Diagonalisation of the Gram operator and its eigenspaces -/

omit [Nontrivial H₁] [Nontrivial H₂] in
/-- **Diagonalisation of `S* ∘ S`.** Mapping the Schmidt `HasSum` through the
adjoint, `(S* ∘ S) x = ∑ₖ σₖ² ⟪uₖ, x⟫ uₖ`. -/
private lemma svd_gram_hasSum {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₂}
    (hv : SVD.OrthonormalOrZero 𝕜 v) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) (x : H₁) :
    HasSum (fun k => ((σ k : 𝕜) ^ 2 * inner 𝕜 (u k) x) • u k)
      ((LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂)) x) := by
  have h := (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂)).toContinuousLinearMap.hasSum (hsum x)
  have hfun : (fun k => (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂)).toContinuousLinearMap
        (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k))
      = fun k => ((σ k : 𝕜) ^ 2 * inner 𝕜 (u k) x) • u k := by
    funext k
    rw [map_smul, LinearMap.coe_toContinuousLinearMap', svd_adjoint_apply hv hvt hsum k, smul_smul]
    congr 1; ring
  have hval : (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂)).toContinuousLinearMap (S x)
      = (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂)) x := by
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap']
  rw [hfun, hval] at h
  exact h

/-- **An antitone tuple is determined by its multiplicities.** Two antitone
`f, g : Fin m → ℝ` with `#{i | f i = ν} = #{i | g i = ν}` for every `ν` are
equal: their `ofFn` lists are sorted (`≥`) and have equal counts, hence are
permutations, hence equal. -/
private lemma eq_of_antitone_card {m : ℕ} {f g : Fin m → ℝ}
    (hf : _root_.Antitone f) (hg : _root_.Antitone g)
    (hc : ∀ ν : ℝ, (Finset.univ.filter (fun i => f i = ν)).card
                 = (Finset.univ.filter (fun i => g i = ν)).card) : f = g := by
  classical
  rw [← List.ofFn_inj]
  refine List.Perm.eq_of_sortedGE ?_ ?_ ?_
  · rw [List.sortedGE_ofFn_iff]; exact hf
  · rw [List.sortedGE_ofFn_iff]; exact hg
  · rw [← Multiset.coe_eq_coe]
    refine Multiset.ext.mpr fun a => ?_
    have key : ∀ p : Fin m → ℝ, Multiset.count a (Finset.univ.val.map p)
        = (Finset.univ.filter fun i => p i = a).card := by
      intro p
      rw [Multiset.count_map, Multiset.filter_congr (fun i _ => eq_comm (a := a) (b := p i)),
        ← Finset.filter_val, ← Finset.card_def]
    rw [← Fin.univ_val_map f, ← Fin.univ_val_map g, key f, key g]
    exact hc a

open Module in
omit [Nontrivial H₁] [Nontrivial H₂] in
/-- **Lower bound on an eigenspace dimension (`ν > 0`).** The `uₖ` with `σₖ² = ν`
are orthonormal eigenvectors of `S* ∘ S` for the eigenvalue `ν`, so their span
(of dimension `#{k | σₖ² = ν}`) sits inside the eigenspace. -/
private lemma card_le_finrank_eigenspace_pos {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁}
    {v : ℕ → H₂} (hu : SVD.OrthonormalOrZero 𝕜 u) (hv : SVD.OrthonormalOrZero 𝕜 v)
    (hut : ∀ k, σ k ≠ 0 → u k ≠ 0) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x))
    {ν : ℝ} (hν : 0 < ν) :
    (Finset.univ.filter (fun i : Fin (finrank 𝕜 H₁) => (σ ↑i) ^ 2 = ν)).card
      ≤ finrank 𝕜 (Module.End.eigenspace
          (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂)) (ν : 𝕜)) := by
  classical
  set m := finrank 𝕜 H₁ with hm
  set T := LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂) with hTdef
  set K := Finset.univ.filter (fun i : Fin m => (σ ↑i) ^ 2 = ν) with hKdef
  -- The `σ` at a matching index is nonzero (else `σ² = 0 ≠ ν`), so `uₖ` is a unit.
  have hnorm : ∀ i : Fin m, i ∈ K → ‖u ↑i‖ = 1 := by
    intro i hi
    rw [hKdef, Finset.mem_filter] at hi
    have hσ : σ ↑i ≠ 0 := by intro h; apply hν.ne'; rw [← hi.2, h]; ring
    rcases hu.1 ↑i with h1 | h0
    · exact h1
    · exact absurd h0 (hut ↑i hσ)
  -- `b`: the matching family, orthonormal.
  set b : {i // i ∈ K} → H₁ := fun i => u ↑(i : Fin m) with hbdef
  have hborth : Orthonormal 𝕜 b :=
    hu.orthonormal_comp (fun i j e => Subtype.ext (Fin.ext e)) fun i => hnorm i i.2
  -- Each `b i` is an eigenvector for the eigenvalue `ν`.
  have hmem : Submodule.span 𝕜 (Set.range b) ≤ Module.End.eigenspace T (ν : 𝕜) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    rintro ⟨i, hi⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
    show T (u ↑i) = (ν : 𝕜) • u ↑i
    rw [hTdef, svd_adjoint_comp_self_apply hu hv hut hvt hsum ↑i]
    rw [hKdef, Finset.mem_filter] at hi
    congr 1
    exact_mod_cast hi.2
  calc K.card = Fintype.card {i // i ∈ K} := (Fintype.card_coe K).symm
    _ = finrank 𝕜 (Submodule.span 𝕜 (Set.range b)) := (finrank_span_eq_card hborth.linearIndependent).symm
    _ ≤ finrank 𝕜 (Module.End.eigenspace T (ν : 𝕜)) := Submodule.finrank_mono hmem

open Module in
omit [Nontrivial H₁] [Nontrivial H₂] in
/-- **Lower bound on the kernel dimension (`ν = 0`).** `eigenspace (S*∘S) 0 = ker(S*∘S) ⊇ ker S`,
and `dim ker S = m − rank S ≥ m − #{k | σₖ ≠ 0} = #{i | σᵢ² = 0}` because
`range S ⊆ span {vₖ | σₖ ≠ 0}`. -/
private lemma card_le_finrank_eigenspace_zero {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁}
    {v : ℕ → H₂} (hσ0 : ∀ k, 0 ≤ σ k) (hσanti : _root_.Antitone σ)
    (hu : SVD.OrthonormalOrZero 𝕜 u) (hut : ∀ k, σ k ≠ 0 → u k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) :
    (Finset.univ.filter (fun i : Fin (finrank 𝕜 H₁) => (σ ↑i) ^ 2 = 0)).card
      ≤ finrank 𝕜 (Module.End.eigenspace
          (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂)) (0 : 𝕜)) := by
  classical
  set m := finrank 𝕜 H₁ with hm
  set T := LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂) with hTdef
  set Knz := Finset.univ.filter (fun i : Fin m => σ ↑i ≠ 0) with hKnz
  set V := Finset.image (fun i : Fin m => v ↑i) Knz with hVdef
  -- `range S ⊆ span {vₖ | σₖ ≠ 0}`.
  have hrange : LinearMap.range (S : H₁ →ₗ[𝕜] H₂) ≤ Submodule.span 𝕜 (↑V : Set H₂) := by
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [ContinuousLinearMap.coe_coe]
    have hsupp : ∀ k ∉ Finset.range m, ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k = 0 := by
      intro k hk
      have hmk : m ≤ k := by rw [Finset.mem_range, not_lt] at hk; exact hk
      rw [svd_sigma_eq_zero_of_finrank_le hσ0 hσanti hu hut hmk]; simp
    rw [(hsum x).unique (hasSum_sum_of_ne_finset_zero hsupp)]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    by_cases hσk : σ k = 0
    · rw [hσk]; simp
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [Finset.mem_coe, hVdef, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_range.mp hk⟩,
        by rw [hKnz, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hσk⟩, rfl⟩
  have hfr : finrank 𝕜 (LinearMap.range (S : H₁ →ₗ[𝕜] H₂)) ≤ Knz.card :=
    calc finrank 𝕜 (LinearMap.range (S : H₁ →ₗ[𝕜] H₂))
        ≤ finrank 𝕜 (Submodule.span 𝕜 (↑V : Set H₂)) := Submodule.finrank_mono hrange
      _ ≤ V.card := finrank_span_finset_le_card V
      _ ≤ Knz.card := Finset.card_image_le
  -- `ker S ⊆ eigenspace 0`, and rank–nullity.
  have hker : LinearMap.ker (S : H₁ →ₗ[𝕜] H₂) ≤ Module.End.eigenspace T (0 : 𝕜) := by
    rw [Module.End.eigenspace_zero]
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hTdef, LinearMap.comp_apply, hx, map_zero]
  have hkerge := Submodule.finrank_mono hker
  have hrn := LinearMap.finrank_range_add_finrank_ker (S : H₁ →ₗ[𝕜] H₂)
  -- `#{i | σᵢ² = 0} = #{i | σᵢ = 0}`, and the `=0 / ≠0` split of `Fin m`.
  have hcard0 : (Finset.univ.filter (fun i : Fin m => (σ ↑i) ^ 2 = 0)).card
      = (Finset.univ.filter (fun i : Fin m => σ ↑i = 0)).card := by
    congr 1
    exact Finset.filter_congr (fun i _ => pow_eq_zero_iff (by norm_num))
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun i => σ ↑i = 0)
  have huniv : (Finset.univ : Finset (Fin m)).card = m := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hPeq : (Finset.univ.filter (fun a : Fin m => ¬ σ ↑a = 0)) = Knz := rfl
  rw [hPeq, huniv] at hsplit
  rw [hcard0]
  omega

open Module in
omit [Nontrivial H₁] [Nontrivial H₂] in
/-- **The eigenvalues of `S* ∘ S` are `i ↦ σᵢ²`.** Both sides are antitone
`Fin m → ℝ`, so it suffices to match multiplicities. By
`card_filter_eigenvalues_eq` the eigenvalue-multiplicity `#{i | eigenvalues i = w}`
is `finrank (eigenspace (S*∘S) w)`; the `σ²`-multiplicity `#{i | σᵢ² = w}` is a
lower bound for that dimension (`card_le_finrank_eigenspace_{pos,zero}`). Two
families of nonnegative multiplicities with the same total `m` and a termwise
`≤` must agree termwise (`Finset.sum_eq_sum_iff_of_le`), giving equal
multiplicities, hence equal tuples. -/
private lemma svd_eigenvalues_eq_sq {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₂}
    (hσ0 : ∀ k, 0 ≤ σ k) (hσanti : _root_.Antitone σ)
    (hu : SVD.OrthonormalOrZero 𝕜 u) (hv : SVD.OrthonormalOrZero 𝕜 v)
    (hut : ∀ k, σ k ≠ 0 → u k ≠ 0) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) :
    (S : H₁ →ₗ[𝕜] H₂).isSymmetric_adjoint_comp_self.eigenvalues rfl
      = fun i : Fin (finrank 𝕜 H₁) => (σ ↑i) ^ 2 := by
  classical
  set m := finrank 𝕜 H₁ with hm
  set f : Fin m → ℝ := (S : H₁ →ₗ[𝕜] H₂).isSymmetric_adjoint_comp_self.eigenvalues rfl with hf_def
  set g : Fin m → ℝ := fun i => (σ ↑i) ^ 2 with hg_def
  -- `#{i | σᵢ² = w}` is a lower bound for the eigenspace dimension at `w`.
  have hB : ∀ w : ℝ, (Finset.univ.filter (fun i => g i = w)).card
      ≤ finrank 𝕜 (Module.End.eigenspace
          (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂)) (↑w : 𝕜)) := by
    intro w
    rcases lt_trichotomy w 0 with hw | hw | hw
    · have he : (Finset.univ.filter (fun i : Fin m => g i = w)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i _ hc
        rw [hg_def] at hc
        nlinarith [sq_nonneg (σ ↑i)]
      rw [he, Finset.card_empty]; exact Nat.zero_le _
    · subst hw
      rw [show ((0 : ℝ) : 𝕜) = 0 from by norm_num]
      simpa [hg_def] using card_le_finrank_eigenspace_zero hσ0 hσanti hu hut hsum
    · simpa [hg_def] using card_le_finrank_eigenspace_pos hu hv hut hvt hsum hw
  -- `#{i | eigenvalues i = w}` equals the eigenspace dimension at `w`.
  have hfeq : ∀ w : ℝ, (Finset.univ.filter (fun i => f i = w)).card
      = finrank 𝕜 (Module.End.eigenspace
          (LinearMap.adjoint (S : H₁ →ₗ[𝕜] H₂) ∘ₗ (S : H₁ →ₗ[𝕜] H₂)) (↑w : 𝕜)) := by
    intro w
    rw [← (S : H₁ →ₗ[𝕜] H₂).isSymmetric_adjoint_comp_self.card_filter_eigenvalues_eq rfl (↑w : 𝕜)]
    congr 1
    apply Finset.filter_congr
    intro i _
    rw [hf_def]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  have hle : ∀ w : ℝ, (Finset.univ.filter (fun i => g i = w)).card
      ≤ (Finset.univ.filter (fun i => f i = w)).card := fun w => by rw [hfeq w]; exact hB w
  -- Saturate over a finite set of values containing both images.
  set Sset := Finset.image f Finset.univ ∪ Finset.image g Finset.univ with hSset
  have hsumf : ∑ w ∈ Sset, (Finset.univ.filter (fun i => f i = w)).card
      = (Finset.univ : Finset (Fin m)).card :=
    (Finset.card_eq_sum_card_fiberwise (f := f) (t := Sset)
      (fun i _ => Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_univ i)))).symm
  have hsumg : ∑ w ∈ Sset, (Finset.univ.filter (fun i => g i = w)).card
      = (Finset.univ : Finset (Fin m)).card :=
    (Finset.card_eq_sum_card_fiberwise (f := g) (t := Sset)
      (fun i _ => Finset.mem_union_right _ (Finset.mem_image_of_mem g (Finset.mem_univ i)))).symm
  have hSeq := (Finset.sum_eq_sum_iff_of_le (fun w (_ : w ∈ Sset) => hle w)).mp
    (hsumg.trans hsumf.symm)
  refine eq_of_antitone_card (LinearMap.IsSymmetric.eigenvalues_antitone _ rfl) ?_ (fun w => ?_)
  · intro i j hij
    exact pow_le_pow_left₀ (hσ0 _) (hσanti hij) 2
  · by_cases hwS : w ∈ Sset
    · exact (hSeq w hwS).symm
    · have hf0 : (Finset.univ.filter (fun i => f i = w)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun i _ hc => hwS (hc ▸ Finset.mem_union_left _
          (Finset.mem_image_of_mem f (Finset.mem_univ i)))
      have hg0 : (Finset.univ.filter (fun i => g i = w)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun i _ hc => hwS (hc ▸ Finset.mem_union_right _
          (Finset.mem_image_of_mem g (Finset.mem_univ i)))
      rw [hf0, hg0]

omit [Nontrivial H₁] [Nontrivial H₂] in
/-- **`aₙ(S) = σₙ(S)`: the SVD's singular values are Mathlib's.** `S` is compact
(finite-dimensional domain), so the SVD applies and `svd_sigma_eq_approx`
reduces the goal to `singularValues S n = σ n`. Mathlib defines
`singularValues` as `√` of the antitone `eigenvalues` of `S* ∘ S`, and
`svd_eigenvalues_eq_sq` shows those eigenvalues are exactly `i ↦ σᵢ²`; for
`n < finrank` this gives `singularValues n = √(σₙ²) = σₙ`, and for
`n ≥ finrank` both sides vanish (`svd_sigma_eq_zero_of_finrank_le`). -/
theorem project_singularValues_eq (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    (S : H₁ →ₗ[𝕜] H₂).singularValues n = approximationNumber S n := by
  have : ProperSpace H₁ := FiniteDimensional.proper 𝕜 (E := H₁)
  have : CompleteSpace H₁ := FiniteDimensional.complete 𝕜 H₁
  have : CompleteSpace H₂ := FiniteDimensional.complete 𝕜 H₂
  have hScompact : IsCompactOperator S := isCompactOperator_of_locallyCompactSpace_rng S
  obtain ⟨σ, u, v, hσ0, hσanti, hu, hv, hut, hvt, _hσlim, hsum⟩ :=
    SVD.IsCompactOperator.SVD hScompact
  -- `svd_sigma_eq_approx` gives `aₙ = σ n`; it remains to identify `σ n` with
  -- Mathlib's eigenvalue-`σₙ`.
  rw [← SVD.svd_sigma_eq_approx hσ0 hσanti hu hv hut hvt hsum n]
  -- **The crux**: the eigenvalues of `S* ∘ S` are exactly `i ↦ σᵢ²`. Everything
  -- else (`√(σₙ²) = σₙ`, and `σₙ = 0` past `finrank`) is bookkeeping.
  have hmatch : ∀ i : Fin (Module.finrank 𝕜 H₁),
      (S : H₁ →ₗ[𝕜] H₂).isSymmetric_adjoint_comp_self.eigenvalues rfl i = (σ ↑i) ^ 2 :=
    fun i => congrFun (svd_eigenvalues_eq_sq hσ0 hσanti hu hv hut hvt hsum) i
  rcases lt_or_ge n (Module.finrank 𝕜 H₁) with hn | hn
  · -- `n < finrank`: `σₙ² = eigenvalues n`, and both sides are `≥ 0`.
    have h2 : (S : H₁ →ₗ[𝕜] H₂).singularValues n ^ 2 = (σ n) ^ 2 := by
      rw [(S : H₁ →ₗ[𝕜] H₂).sq_singularValues_of_lt rfl hn, hmatch ⟨n, hn⟩]
    exact (sq_eq_sq₀ ((S : H₁ →ₗ[𝕜] H₂).singularValues_nonneg n) (hσ0 n)).mp h2
  · -- `n ≥ finrank`: both sides vanish.
    rw [(S : H₁ →ₗ[𝕜] H₂).singularValues_of_finrank_le hn]
    exact (svd_sigma_eq_zero_of_finrank_le hσ0 hσanti hu hut hn).symm

omit [Nontrivial H₁] [Nontrivial H₂] in
/-- **Singular numbers coincide with all `s`-numbers (finite dimension).** For
every `s`-number sequence `s` and operator `S` between finite-dimensional
Hilbert spaces, `sₙ(S) = σₙ(S)`.

Uniqueness reduces `sₙ` to `aₙ` (for *every* `s` at once), and
`project_singularValues_eq` identifies `aₙ` with Mathlib's `σₙ`. Specialising
`s` to the approximation numbers recovers `aₙ(S) = σₙ(S)`, so no separate
statement is needed. -/
theorem sn_eq_singularValues_of_finiteDimensional {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    s S n = (S : H₁ →ₗ[𝕜] H₂).singularValues n := by
  have : CompleteSpace H₁ := FiniteDimensional.complete 𝕜 H₁
  have : CompleteSpace H₂ := FiniteDimensional.complete 𝕜 H₂
  rw [allSNumbers_eq_on_HilbertSpace hs S n, ← project_singularValues_eq S n]

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
