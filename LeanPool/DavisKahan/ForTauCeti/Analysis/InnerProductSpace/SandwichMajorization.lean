/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti.  Mathlib is not the destination (`ForTauCeti/README.md`);
on the closed Mathlib track this material would have been an addition to
`Mathlib/Analysis/InnerProductSpace/` (new file `SandwichMajorization.lean`).

Formalized by Claude Opus 5 (claude-opus-5).
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Convex.Majorization
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional

/-! # Weak majorization for the positive sandwich `D⋆ M D`

For a positive operator `M` and an arbitrary operator `D` on a finite-dimensional
inner product space,

  `σ(D⋆ M D)  ≺w  (i ↦ σᵢ(M) · σᵢ(D)²)`.

Both sides are decreasing nonnegative sequences of the same finite length, and
`≺w` is `TauCeti.FiniteVector.WeaklyMajorized`: **every** prefix sum of the left
side is dominated by the corresponding prefix sum of the right side.  By
`FiniteSymmetricGauge.mono_weaklyMajorized` this gives the same inequality for
every symmetric gauge, hence for every unitarily invariant norm.

This is the generalized von Neumann / rearrangement content of the sandwich
estimate.  It is genuinely stronger than the operator-norm relaxation
`σᵢ(D⋆ M D) ≤ ‖D‖² σᵢ(M)`: the whole singular-value sequence of `D` is retained,
weight by weight, rather than collapsed to its largest entry.

## Main results

* `TauCeti.singularValues_of_isPositive` -- for a positive operator the singular
  values are the sorted eigenvalues;
* `TauCeti.sum_range_singularValues_adjoint_sandwich_le` -- the Ky Fan prefix
  form, `∑_{i<k} σᵢ(D⋆ M D) ≤ ∑_{i<k} σᵢ(M) σᵢ(D)²`, for every `k`;
* `TauCeti.singularValues_adjoint_sandwich_weaklyMajorized` -- the packaged weak
  majorization;
* `TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized` -- the same
  statement for `ContinuousLinearMap.approximationNumber`, which is the form
  perturbation arguments consume.

## Proof

Everything reduces to the prefix inequality at a fixed `k`.  Because `D⋆ M D` is
positive, its top-`k` singular-value sum is the top-`k` eigenvalue sum, attained
at an orthonormal family `w` of its own eigenvectors:

  `∑_{i<k} σᵢ(D⋆ M D) = ∑_i re ⟪M (D wᵢ), D wᵢ⟫`.

Diagonalizing `M` in its eigenbasis `p` turns the right-hand side into a weighted
sum `∑_j μⱼ cⱼ` with `μ = σ(M)` decreasing and

  `cⱼ = ∑_{i<k} |⟪pⱼ, D wᵢ⟫|²`.

Two applications of the Ky Fan trace inequality bound the prefix sums of `c`:
Bessel's inequality against `w` gives `∑_{j<m} cⱼ ≤ ∑_{j<m} ‖D⋆ pⱼ‖²`, which the
trace inequality for `D D⋆` bounds by `∑_{j<m} σⱼ(D)²`; and Parseval against `p`
gives the total mass `∑_j cⱼ = ∑_{i<k} ‖D wᵢ‖²`, which the trace inequality for
`D⋆ D` bounds by `∑_{i<k} σᵢ(D)²`.  Together these say `c` has smaller prefix
sums than the truncated sequence `j ↦ if j < k then σⱼ(D)² else 0`, and Abel
summation against the decreasing weights `μ` finishes the estimate.

No von Neumann trace inequality and no alignment unitary are needed: the Ky Fan
maximum principle in the form `sum_re_inner_le_sum_eigenvalues_top` already
carries the rearrangement content.

## References

* R. Bhatia, *Matrix Analysis*, Chapters II and IV.
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation III*,
  SIAM J. Numer. Anal. 7 (1970), Theorem 8.1(iii).
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open _root_.LinearMap
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-! ### Abel summation against decreasing weights -/

/-- **Abel summation.**  If the weights `mu` are nonnegative and decreasing on
`[0, n)`, then domination of every prefix sum passes to the weighted sums.

The induction removes the last weight by replacing `mu` with `mu - mu n`, which
is still nonnegative and decreasing on `[0, n)`; the discarded amount is `mu n`
times the full prefix sum, which is dominated by hypothesis. -/
theorem sum_range_mul_le_of_sum_range_le :
    ∀ (n : ℕ) (mu c d : ℕ → ℝ),
      (∀ i j, i ≤ j → j < n → mu j ≤ mu i) →
      (∀ j, j < n → 0 ≤ mu j) →
      (∀ m, m ≤ n → ∑ j ∈ Finset.range m, c j ≤ ∑ j ∈ Finset.range m, d j) →
      ∑ j ∈ Finset.range n, mu j * c j ≤ ∑ j ∈ Finset.range n, mu j * d j := by
  intro n
  induction n with
  | zero => intro mu c d _ _ _; simp
  | succ n ih =>
    intro mu c d hmu hmu0 hpre
    have hsplit : ∀ f : ℕ → ℝ, ∑ j ∈ Finset.range (n + 1), mu j * f j
        = ∑ j ∈ Finset.range n, (mu j - mu n) * f j
          + mu n * ∑ j ∈ Finset.range (n + 1), f j := by
      intro f
      rw [Finset.sum_range_succ (f := fun j => mu j * f j), Finset.sum_range_succ (f := f)]
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_add]
      ring
    have hIH := ih (fun j => mu j - mu n) c d
      (fun i j hij hjn => by
        have h := hmu i j hij (hjn.trans (Nat.lt_succ_self n))
        simpa using sub_le_sub_right h (mu n))
      (fun j hj => sub_nonneg.mpr (hmu j n hj.le (Nat.lt_succ_self n)))
      (fun m hm => hpre m (hm.trans (Nat.le_succ n)))
    have hlast : mu n * ∑ j ∈ Finset.range (n + 1), c j
        ≤ mu n * ∑ j ∈ Finset.range (n + 1), d j :=
      mul_le_mul_of_nonneg_left (hpre (n + 1) le_rfl) (hmu0 n (Nat.lt_succ_self n))
    rw [hsplit c, hsplit d]
    exact add_le_add hIH hlast

/-! ### Singular values of a positive operator -/

/-- For a positive operator the singular values are exactly the sorted
eigenvalues: the Gram operator is the square, so its eigenvalues are the squares
and the square root undoes them. -/
theorem singularValues_of_isPositive {A : E →ₗ[𝕜] E} (hA : A.IsPositive)
    (j : Fin (finrank 𝕜 E)) :
    A.singularValues (j : ℕ) = hA.isSymmetric.eigenvalues rfl j := by
  have hgram : A.isSymmetric_adjoint_comp_self.eigenvalues rfl =
      fun i => (hA.isSymmetric.eigenvalues rfl i) ^ 2 :=
    LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis A.isSymmetric_adjoint_comp_self rfl
      (hA.isSymmetric.eigenvectorBasis rfl)
      (fun a b hab => pow_le_pow_left₀ (hA.nonneg_eigenvalues rfl b)
        (hA.isSymmetric.eigenvalues_antitone rfl hab) 2)
      (fun i => by
        rw [LinearMap.comp_apply, hA.isSymmetric.apply_eigenvectorBasis,
          map_smul, hA.isSymmetric.adjoint_eq,
          hA.isSymmetric.apply_eigenvectorBasis, smul_smul,
          ← RCLike.ofReal_mul, ← sq])
  rw [A.singularValues_of_lt rfl j.isLt, hgram]
  simpa using Real.sqrt_sq (hA.nonneg_eigenvalues rfl j)

/-! ### The Ky Fan bound on an orthonormal family -/

/-- The energy of an operator on an orthonormal `m`-family is at most the sum of
its `m` largest squared singular values.

This is the Ky Fan maximum principle applied to the Gram operator `D⋆ D`, whose
sorted eigenvalues are the squared singular values of `D`. -/
theorem sum_sq_norm_apply_le_sum_range_sq_singularValues
    (D : E →ₗ[𝕜] E) {m : ℕ} (hm : m ≤ finrank 𝕜 E) {v : Fin m → E}
    (hv : Orthonormal 𝕜 v) :
    ∑ i, ‖D (v i)‖ ^ 2 ≤ ∑ j ∈ Finset.range m, D.singularValues j ^ 2 := by
  have hform : ∀ i : Fin m, ‖D (v i)‖ ^ 2
      = RCLike.re ⟪(D.adjoint ∘ₗ D) (v i), v i⟫_𝕜 := by
    intro i
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
  have hkf := sum_re_inner_le_sum_eigenvalues_top
    D.isSymmetric_adjoint_comp_self (n := finrank 𝕜 E) rfl hm hv
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hform i]
  refine hkf.trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun j (_ : j ∈ _) => (D.sq_singularValues_fin rfl j).symm,
    sum_filter_lt_eq_sum_fin hm (fun j => D.singularValues j ^ 2)]
  exact Fin.sum_univ_eq_sum_range (fun j => D.singularValues j ^ 2) m

/-! ### The prefix inequality -/

/-- **The core estimate.**  For positive `M`, arbitrary `D`, and any orthonormal
`k`-family `w`, the energy of `M` on the image family `D w` is bounded by the `k`
leading products `σⱼ(M) σⱼ(D)²`. -/
theorem sum_re_inner_apply_comp_le_sum_range_mul_sq
    {M : E →ₗ[𝕜] E} (hM : M.IsPositive) (D : E →ₗ[𝕜] E)
    {k : ℕ} (hk : k ≤ finrank 𝕜 E) {w : Fin k → E} (hw : Orthonormal 𝕜 w) :
    ∑ i, RCLike.re ⟪M (D (w i)), D (w i)⟫_𝕜
      ≤ ∑ j ∈ Finset.range k, M.singularValues j * D.singularValues j ^ 2 := by
  classical
  set p := hM.isSymmetric.eigenvectorBasis (n := finrank 𝕜 E) rfl with hp
  -- The `j`-th eigenvector of `M`, extended by zero past the dimension.
  set pv : ℕ → E := fun j => if h : j < finrank 𝕜 E then p ⟨j, h⟩ else 0 with hpv
  set c : ℕ → ℝ := fun j => ∑ i : Fin k, ‖⟪w i, D.adjoint (pv j)⟫_𝕜‖ ^ 2 with hc
  set d : ℕ → ℝ := fun j => if j < k then D.singularValues j ^ 2 else 0 with hd
  have hpvfin : ∀ j : Fin (finrank 𝕜 E), pv (j : ℕ) = p j := by
    intro j
    simp only [hpv, dite_eq_left j.isLt, Fin.eta]
  -- Rewriting a `p`-coordinate of `D wᵢ` into the shape Bessel's inequality wants.
  have hcoord : ∀ (i : Fin k) (j : Fin (finrank 𝕜 E)),
      ‖p.repr (D (w i)) j‖ ^ 2 = ‖⟪w i, D.adjoint (pv (j : ℕ))⟫_𝕜‖ ^ 2 := by
    intro i j
    rw [hpvfin j, OrthonormalBasis.repr_apply_apply,
      ← LinearMap.adjoint_inner_left D (w i) (p j), ← norm_inner_symm]
  -- Step 1: diagonalize `M`, turning the energy into a weighted sum of `c`.
  have hstep1 : ∑ i, RCLike.re ⟪M (D (w i)), D (w i)⟫_𝕜
      = ∑ j ∈ Finset.range (finrank 𝕜 E), M.singularValues j * c j := by
    have hdiag : ∀ i : Fin k, RCLike.re ⟪M (D (w i)), D (w i)⟫_𝕜
        = ∑ j : Fin (finrank 𝕜 E),
            M.singularValues (j : ℕ) * ‖⟪w i, D.adjoint (pv (j : ℕ))⟫_𝕜‖ ^ 2 := by
      intro i
      rw [LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq
        hM.isSymmetric rfl (D (w i))]
      exact Finset.sum_congr rfl fun j _ => by
        rw [singularValues_of_isPositive hM j, ← hp, hcoord i j]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hdiag i, Finset.sum_comm,
      ← Fin.sum_univ_eq_sum_range (fun j => M.singularValues j * c j) (finrank 𝕜 E)]
    exact Finset.sum_congr rfl fun j _ => by simp only [hc, Finset.mul_sum]
  -- Step 2: the prefix sums of `c` are dominated by those of `d`.
  have hpre : ∀ m, m ≤ finrank 𝕜 E →
      ∑ j ∈ Finset.range m, c j ≤ ∑ j ∈ Finset.range m, d j := by
    intro m hm
    rcases le_or_gt m k with hmk | hmk
    · -- Below the cut: Bessel against `w`, then Ky Fan for `D D⋆`.
      have hbessel : ∀ j : ℕ, c j ≤ ‖D.adjoint (pv j)‖ ^ 2 := fun j =>
        hw.sum_inner_products_le (D.adjoint (pv j))
      have hpon : Orthonormal 𝕜 (fun j : Fin m => p (Fin.castLE hm j)) :=
        p.orthonormal.comp _ (Fin.castLE_injective hm)
      have hkyfan := sum_sq_norm_apply_le_sum_range_sq_singularValues D.adjoint hm hpon
      calc ∑ j ∈ Finset.range m, c j
          = ∑ j : Fin m, c (j : ℕ) := (Fin.sum_univ_eq_sum_range (fun j => c j) m).symm
        _ ≤ ∑ j : Fin m, ‖D.adjoint (p (Fin.castLE hm j))‖ ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h := hbessel (j : ℕ)
            have he : pv (j : ℕ) = p (Fin.castLE hm j) := hpvfin (Fin.castLE hm j)
            rwa [he] at h
        _ ≤ ∑ j ∈ Finset.range m, D.adjoint.singularValues j ^ 2 := hkyfan
        _ = ∑ j ∈ Finset.range m, d j := by
            refine Finset.sum_congr rfl fun j hj => ?_
            simp only [hd, ite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hj) hmk),
              LinearMap.singularValues_adjoint_apply]
    · -- Above the cut: Parseval, then Ky Fan for `D⋆ D` on `w` itself.
      have htot : ∑ j ∈ Finset.range (finrank 𝕜 E), c j = ∑ i : Fin k, ‖D (w i)‖ ^ 2 := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => c j) (finrank 𝕜 E)]
        have hcj : ∀ j : Fin (finrank 𝕜 E),
            c (j : ℕ) = ∑ i : Fin k, ‖p.repr (D (w i)) j‖ ^ 2 := by
          intro j
          simp only [hc]
          exact Finset.sum_congr rfl fun i _ => (hcoord i j).symm
        rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hcj j, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [OrthonormalBasis.repr_apply_apply]
        exact p.sum_sq_norm_inner_right (D (w i))
      have hsubm : Finset.range m ⊆ Finset.range (finrank 𝕜 E) := fun x hx =>
        Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le hm)
      have hmono : ∑ j ∈ Finset.range m, c j ≤ ∑ j ∈ Finset.range (finrank 𝕜 E), c j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubm ?_
        intro j _ _
        simp only [hc]
        exact Finset.sum_nonneg fun i _ => sq_nonneg _
      have hkyfan := sum_sq_norm_apply_le_sum_range_sq_singularValues D hk hw
      have hdk : ∑ j ∈ Finset.range m, d j
          = ∑ j ∈ Finset.range k, D.singularValues j ^ 2 := by
        have hsubk : Finset.range k ⊆ Finset.range m := fun x hx =>
          Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans hmk)
        rw [← Finset.sum_subset hsubk (fun j _ hj => by
          have hjk : ¬ j < k := by simpa using hj
          simp only [hd, ite_eq_right hjk])]
        exact Finset.sum_congr rfl fun j hj => by
          simp only [hd, ite_eq_left (Finset.mem_range.mp hj)]
      rw [hdk]
      exact (hmono.trans (le_of_eq htot)).trans hkyfan
  -- Step 3: Abel summation against the decreasing weights `σ(M)`.
  have habel := sum_range_mul_le_of_sum_range_le (finrank 𝕜 E) (fun j => M.singularValues j) c d
    (fun i j hij _ => M.singularValues_antitone hij)
    (fun j _ => M.singularValues_nonneg j) hpre
  refine hstep1.trans_le (habel.trans (le_of_eq ?_))
  -- The right-hand weighted sum collapses to the first `k` terms.
  have hsubk : Finset.range k ⊆ Finset.range (finrank 𝕜 E) := fun x hx =>
    Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le hk)
  rw [← Finset.sum_subset hsubk (fun j _ hj => by
    have hjk : ¬ j < k := by simpa using hj
    simp only [hd, ite_eq_right hjk, mul_zero])]
  exact Finset.sum_congr rfl fun j hj => by
    simp only [hd, ite_eq_left (Finset.mem_range.mp hj)]

/-- The prefix estimate at an index below the dimension. -/
private theorem sum_range_singularValues_adjoint_sandwich_le_aux
    {M : E →ₗ[𝕜] E} (hM : M.IsPositive) (D : E →ₗ[𝕜] E) {k : ℕ} (hk : k ≤ finrank 𝕜 E) :
    ∑ i ∈ Finset.range k, (D.adjoint ∘ₗ M ∘ₗ D).singularValues i
      ≤ ∑ i ∈ Finset.range k, M.singularValues i * D.singularValues i ^ 2 := by
  have hTpos : (D.adjoint ∘ₗ M ∘ₗ D).IsPositive := hM.adjoint_conj D
  set q := hTpos.isSymmetric.eigenvectorBasis (n := finrank 𝕜 E) rfl with hq
  have hqon : Orthonormal 𝕜 (fun i : Fin k => q (Fin.castLE hk i)) :=
    q.orthonormal.comp _ (Fin.castLE_injective hk)
  -- The top-`k` singular values of the positive sandwich are its top-`k`
  -- eigenvalues, and each is the energy of `M` at the image of an eigenvector.
  have hval : ∀ i : Fin k, (D.adjoint ∘ₗ M ∘ₗ D).singularValues (i : ℕ)
      = RCLike.re ⟪M (D (q (Fin.castLE hk i))), D (q (Fin.castLE hk i))⟫_𝕜 := by
    intro i
    have hself : ⟪(D.adjoint ∘ₗ M ∘ₗ D) (q (Fin.castLE hk i)), q (Fin.castLE hk i)⟫_𝕜
        = ⟪M (D (q (Fin.castLE hk i))), D (q (Fin.castLE hk i))⟫_𝕜 := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.comp_apply]
    have heig : (D.adjoint ∘ₗ M ∘ₗ D) (q (Fin.castLE hk i))
        = ((hTpos.isSymmetric.eigenvalues rfl (Fin.castLE hk i) : ℝ) : 𝕜) •
          q (Fin.castLE hk i) := by
      rw [hq]; exact hTpos.isSymmetric.apply_eigenvectorBasis rfl (Fin.castLE hk i)
    have hone : ⟪q (Fin.castLE hk i), q (Fin.castLE hk i)⟫_𝕜 = (1 : 𝕜) := by
      rw [inner_self_eq_norm_sq_to_K, q.orthonormal.norm_eq_one (Fin.castLE hk i)]
      norm_num
    have hsv : (D.adjoint ∘ₗ M ∘ₗ D).singularValues (i : ℕ)
        = hTpos.isSymmetric.eigenvalues rfl (Fin.castLE hk i) :=
      singularValues_of_isPositive hTpos (Fin.castLE hk i)
    rw [hsv, ← hself, heig,
      inner_smul_left, RCLike.conj_ofReal, hone, mul_one, RCLike.ofReal_re]
  calc ∑ i ∈ Finset.range k, (D.adjoint ∘ₗ M ∘ₗ D).singularValues i
      = ∑ i : Fin k, (D.adjoint ∘ₗ M ∘ₗ D).singularValues (i : ℕ) :=
        (Fin.sum_univ_eq_sum_range _ k).symm
    _ = ∑ i : Fin k, RCLike.re ⟪M (D (q (Fin.castLE hk i))), D (q (Fin.castLE hk i))⟫_𝕜 :=
        Finset.sum_congr rfl fun i _ => hval i
    _ ≤ ∑ i ∈ Finset.range k, M.singularValues i * D.singularValues i ^ 2 :=
        sum_re_inner_apply_comp_le_sum_range_mul_sq hM D hk hqon

/-- **The Ky Fan prefix form of the sandwich estimate.**  For positive `M` and
arbitrary `D`, every prefix sum of the singular values of `D⋆ M D` is dominated
by the corresponding prefix sum of the weighted sequence `σᵢ(M) σᵢ(D)²`. -/
theorem sum_range_singularValues_adjoint_sandwich_le
    {M : E →ₗ[𝕜] E} (hM : M.IsPositive) (D : E →ₗ[𝕜] E) (k : ℕ) :
    ∑ i ∈ Finset.range k, (D.adjoint ∘ₗ M ∘ₗ D).singularValues i
      ≤ ∑ i ∈ Finset.range k, M.singularValues i * D.singularValues i ^ 2 := by
  rcases le_or_gt k (finrank 𝕜 E) with hk | hk
  · exact sum_range_singularValues_adjoint_sandwich_le_aux hM D hk
  · -- Past the dimension both sides only gain zeros.
    have hsub : Finset.range (finrank 𝕜 E) ⊆ Finset.range k := fun x hx =>
      Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans hk)
    have hleft : ∑ i ∈ Finset.range k, (D.adjoint ∘ₗ M ∘ₗ D).singularValues i
        = ∑ i ∈ Finset.range (finrank 𝕜 E), (D.adjoint ∘ₗ M ∘ₗ D).singularValues i :=
      (Finset.sum_subset hsub fun i _ hi =>
        (D.adjoint ∘ₗ M ∘ₗ D).singularValues_of_finrank_le (by simpa using hi)).symm
    have hright : ∑ i ∈ Finset.range k, M.singularValues i * D.singularValues i ^ 2
        = ∑ i ∈ Finset.range (finrank 𝕜 E),
            M.singularValues i * D.singularValues i ^ 2 :=
      (Finset.sum_subset hsub fun i _ hi => by
        rw [M.singularValues_of_finrank_le (by simpa using hi), zero_mul]).symm
    rw [hleft, hright]
    exact sum_range_singularValues_adjoint_sandwich_le_aux hM D le_rfl

/-! ### The weak-majorization package -/

/-- Prefix sums of a finite vector cut out of an `ℕ`-indexed sequence are the
corresponding truncated range sums. -/
theorem prefixSum_comp_val {N : ℕ} (g : ℕ → ℝ) (k : ℕ) :
    FiniteVector.prefixSum k (fun i : Fin N => g (i : ℕ))
      = ∑ j ∈ Finset.range (min k N), g j := by
  unfold FiniteVector.prefixSum
  rw [Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun m => if m < k then g m else 0) N, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **Weak majorization for the positive sandwich.**  For positive `M` and
arbitrary `D` on a finite-dimensional space,

  `σ(D⋆ M D) ≺w (i ↦ σᵢ(M) σᵢ(D)²)`.

The right-hand side keeps the entire singular-value sequence of `D`; it is not
the operator-norm relaxation `‖D‖² σᵢ(M)`. -/
theorem singularValues_adjoint_sandwich_weaklyMajorized
    {M : E →ₗ[𝕜] E} (hM : M.IsPositive) (D : E →ₗ[𝕜] E) :
    FiniteVector.WeaklyMajorized
      (fun i : Fin (finrank 𝕜 E) => (D.adjoint ∘ₗ M ∘ₗ D).singularValues (i : ℕ))
      (fun i : Fin (finrank 𝕜 E) =>
        M.singularValues (i : ℕ) * D.singularValues (i : ℕ) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hij => (D.adjoint ∘ₗ M ∘ₗ D).singularValues_antitone (Fin.le_def.mp hij)
  · intro i j hij
    exact mul_le_mul (M.singularValues_antitone (Fin.le_def.mp hij))
      (pow_le_pow_left₀ (D.singularValues_nonneg _)
        (D.singularValues_antitone (Fin.le_def.mp hij)) 2)
      (by positivity) (M.singularValues_nonneg _)
  · exact fun i => (D.adjoint ∘ₗ M ∘ₗ D).singularValues_nonneg _
  · exact fun i => mul_nonneg (M.singularValues_nonneg _) (sq_nonneg _)
  · intro k
    rw [prefixSum_comp_val (fun j => (D.adjoint ∘ₗ M ∘ₗ D).singularValues j) k,
      prefixSum_comp_val (fun j => M.singularValues j * D.singularValues j ^ 2) k]
    exact sum_range_singularValues_adjoint_sandwich_le hM D _

/-- **Weak majorization for the positive sandwich, approximation-number form.**

`ContinuousLinearMap.approximationNumber` agrees with the singular values in
finite dimensions, so this is the previous theorem in the vocabulary that
perturbation arguments use. -/
theorem approximationNumber_adjoint_sandwich_weaklyMajorized [CompleteSpace E]
    {M : E →L[𝕜] E} (hM : (0 : E →L[𝕜] E) ≤ M) (D : E →L[𝕜] E) :
    FiniteVector.WeaklyMajorized
      (fun i : Fin (finrank 𝕜 E) =>
        (ContinuousLinearMap.adjoint D ∘L M ∘L D).approximationNumber (i : ℕ))
      (fun i : Fin (finrank 𝕜 E) =>
        M.approximationNumber (i : ℕ) * D.approximationNumber (i : ℕ) ^ 2) := by
  have hMpos : (M : E →ₗ[𝕜] E).IsPositive :=
    ((ContinuousLinearMap.nonneg_iff_isPositive M).mp hM).toLinearMap
  have hcoe : ((ContinuousLinearMap.adjoint D ∘L M ∘L D : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = (D : E →ₗ[𝕜] E).adjoint ∘ₗ (M : E →ₗ[𝕜] E) ∘ₗ (D : E →ₗ[𝕜] E) := rfl
  have hmain := singularValues_adjoint_sandwich_weaklyMajorized hMpos (D : E →ₗ[𝕜] E)
  rw [← hcoe] at hmain
  simpa only [ContinuousLinearMap.approximationNumber_eq_singularValues,
    ContinuousLinearMap.toLinearMap_singularValues] using hmain

end TauCeti
