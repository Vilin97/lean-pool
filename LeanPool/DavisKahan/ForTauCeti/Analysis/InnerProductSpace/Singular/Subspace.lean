/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/

/-
Staged for Tau Ceti, roadmap topic T05.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SingularSubspace.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

Groundwork for the Yu–Wang–Samworth singular-vector extension: perturbing the
Gram operator `A⋆A` by `Â⋆Â − A⋆A`, controlled by `Â − A`.  Includes the operator
adjoint norm bound `‖A⋆‖ = ‖A‖` in elementwise form.

Plan step W0.1(d) added by Claude Opus 4.8 (claude-opus-4-8[1m]): the
singular-value symmetry `σ(A⋆) = σ(A)` for a square operator, proved through the
eigenvalue invariance of a symmetric operator under unitary conjugation
(`eigenvalues_conj_unitary`, a Courant–Fischer consequence) applied to the polar
identity `A A⋆ = U (A⋆A) U⁻¹` with `U = choosePolarUnitary A`.
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SchurHorn
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition


/-! # Gram-operator perturbation

For `A, Â : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
singular subspaces are the spectral subspaces of the Gram operators `A⋆A` and
`Â⋆Â`.  The Yu–Wang–Samworth singular-vector bound applies the symmetric result
to these Gram operators, so it needs the Gram perturbation `Â⋆Â − A⋆A` bounded in
terms of `Â − A`.

## Main results

* `TauCeti.norm_adjoint_apply_le`: the adjoint of a `c`-bounded operator is
  `c`-bounded (`‖A⋆‖ ≤ ‖A‖` in elementwise form).
* `TauCeti.norm_gram_sub_gram_apply_le`: `‖(Â⋆Â − A⋆A) x‖ ≤ (a + â) ε ‖x‖`
  when `A, Â, Â − A` are `a`-, `â`-, `ε`-bounded, via
  `Â⋆Â − A⋆A = Â⋆(Â − A) + (Â − A)⋆A`.
* `TauCeti.abs_sq_singularValues_sub_le`: Weyl for squared singular values,
  `|σₖ(Â)² − σₖ(A)²| ≤ (a + â) ε` — the singular-value stability underlying the
  singular-subspace bound.
* `TauCeti.sum_sq_singularValues`: the squared Frobenius norm equals the sum
  of squared singular values, `∑ᵢ σᵢ(A)² = ∑ₖ ‖A bₖ‖²`.
* `TauCeti.eigenvalues_conj_unitary`: the sorted eigenvalues of a symmetric
  operator are invariant under unitary conjugation `S ↦ U S U⁻¹`.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), §"singular-vector extension".
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open LinearMap
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

omit [FiniteDimensional 𝕜 E] in
/-- **The quadratic form of a real dilation at a unit vector is the dilation factor**:
`re ⟪(c : 𝕜) • v, v⟫ = c` when `‖v‖ = 1`.

Stated because four proofs in this file each spelled it out as the same seven-lemma
rewrite -- `inner_smul_left`, `RCLike.conj_ofReal`, `RCLike.re_ofReal_mul`,
`inner_self_eq_norm_sq`, the unit-norm fact, `one_pow`, `mul_one`. Every use of it here
follows an eigenvector step that produces exactly this shape, so naming it removes the
repetition rather than hiding it. -/
private theorem re_inner_real_smul_self_of_norm_one {c : ℝ} {v : E} (hv : ‖v‖ = 1) :
    RCLike.re ⟪(c : 𝕜) • v, v⟫_𝕜 = c := by
  rw [inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq, hv]
  simp

/-- **The adjoint preserves an operator-norm bound.** If `‖A x‖ ≤ c ‖x‖` for all
`x`, then `‖A⋆ y‖ ≤ c ‖y‖` for all `y` — the elementwise form of `‖A⋆‖ = ‖A‖`.
Proof: `‖A⋆ y‖² = re⟪y, A (A⋆ y)⟫ ≤ ‖y‖ ‖A (A⋆ y)‖ ≤ c ‖y‖ ‖A⋆ y‖`. -/
theorem norm_adjoint_apply_le {A : E →ₗ[𝕜] F} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖A x‖ ≤ c * ‖x‖) (y : F) : ‖A.adjoint y‖ ≤ c * ‖y‖ := by
  have key : ‖A.adjoint y‖ ^ 2 ≤ c * ‖y‖ * ‖A.adjoint y‖ :=
    calc ‖A.adjoint y‖ ^ 2
        = RCLike.re ⟪A.adjoint y, A.adjoint y⟫_𝕜 := (inner_self_eq_norm_sq _).symm
      _ = RCLike.re ⟪y, A (A.adjoint y)⟫_𝕜 := by rw [LinearMap.adjoint_inner_left]
      _ ≤ ‖⟪y, A (A.adjoint y)⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖y‖ * ‖A (A.adjoint y)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (c * ‖A.adjoint y‖) := by gcongr; exact h _
      _ = c * ‖y‖ * ‖A.adjoint y‖ := by ring
  rcases eq_or_ne ‖A.adjoint y‖ 0 with h0 | h0
  · rw [h0]; positivity
  · have hpos : 0 < ‖A.adjoint y‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
    nlinarith [key, hpos]

/-- **Gram-operator perturbation bound.** With `A, Â, Â − A` bounded by `a, â, ε`
respectively, `‖(Â⋆Â − A⋆A) x‖ ≤ (a + â) ε ‖x‖`.  From the splitting
`Â⋆Â − A⋆A = Â⋆(Â − A) + (Â − A)⋆A`, the two pieces are bounded by `â ε` and
`ε a` (using `norm_adjoint_apply_le`). -/
theorem norm_gram_sub_gram_apply_le {A Â : E →ₗ[𝕜] F} {a â ε : ℝ}
    (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖) (x : E) :
    ‖(Â.adjoint ∘ₗ Â - A.adjoint ∘ₗ A) x‖ ≤ (a + â) * ε * ‖x‖ := by
  have hadj : (Â - A).adjoint = Â.adjoint - A.adjoint := map_sub _ _ _
  have hsplit : (Â.adjoint ∘ₗ Â - A.adjoint ∘ₗ A) x
      = Â.adjoint ((Â - A) x) + (Â - A).adjoint (A x) := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hadj]
    abel
  rw [hsplit]
  calc ‖Â.adjoint ((Â - A) x) + (Â - A).adjoint (A x)‖
      ≤ ‖Â.adjoint ((Â - A) x)‖ + ‖(Â - A).adjoint (A x)‖ := norm_add_le _ _
    _ ≤ â * ‖(Â - A) x‖ + ε * ‖A x‖ := by
        gcongr
        · exact norm_adjoint_apply_le hâ hÂ _
        · exact norm_adjoint_apply_le hε hE _
    _ ≤ â * (ε * ‖x‖) + ε * (a * ‖x‖) := by
        gcongr
        · exact hE x
        · exact hA x
    _ = (a + â) * ε * ‖x‖ := by ring

/-- **Trace of the modulus = sum of singular values.** For an endomorphism
`A : E →ₗ[𝕜] E`, `∑ₖ re⟪|A| bₖ, bₖ⟫ = ∑ᵢ σᵢ(A)` in any orthonormal basis `b`.
The modulus `|A| = √(A⋆A)` is diagonal in the `A⋆A`-eigenbasis with entries
`√λᵢ(A⋆A) = σᵢ(A)`, and the trace is basis-independent. -/
theorem sum_re_inner_abs_self_eq_sum_singularValues (A : E →ₗ[𝕜] E)
    {n : ℕ} (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, RCLike.re ⟪operatorAbs A (b k), b k⟫_𝕜 = ∑ i : Fin n, A.singularValues (i : ℕ) := by
  subst hn
  have hP := LinearMap.isPositive_adjoint_comp_self A
  have hsym : (operatorAbs A).IsSymmetric := (isPositive_operatorAbs A).isSymmetric
  -- Basis independence: the trace of `|A|` is the same in any basis.
  have key : ∀ b' : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      ∑ k, RCLike.re ⟪operatorAbs A (b' k), b' k⟫_𝕜
        = ∑ i : Fin (finrank 𝕜 E), hsym.eigenvalues rfl i :=
    fun b' => sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues hsym rfl b'
  rw [key b, ← key (hP.isSymmetric.eigenvectorBasis rfl)]
  refine Finset.sum_congr rfl fun k _ => ?_
  set w := hP.isSymmetric.eigenvectorBasis rfl with hw
  rw [show operatorAbs A (w k)
        = (Real.sqrt (hP.isSymmetric.eigenvalues rfl k) : 𝕜) • w k from
      hP.sqrt_apply_eigenvectorBasis k,
    re_inner_real_smul_self_of_norm_one (w.orthonormal.norm_eq_one k)]
  exact (A.singularValues_fin rfl k).symm

/-- **The Gram quadratic form at an eigenvector of the Gram operator is its
eigenvalue.**

The `A.adjoint ∘ₗ A` eigenbasis diagonalises the Gram form by construction, so
this is bookkeeping — but it is the bookkeeping three proofs in this file were
doing inline, as chains of eight to ten named rewrites through `inner_smul_left`,
`RCLike.conj_ofReal`, `RCLike.re_ofReal_mul` and orthonormality.  One statement
is both shorter at each site and no longer dependent on the order those rewrites
fire in. -/
private theorem re_inner_gram_eigenvectorBasis_self
    {n : ℕ} (A : E →ₗ[𝕜] F)
    (hsym : (A.adjoint ∘ₗ A).IsSymmetric) (hn : Module.finrank 𝕜 E = n) (k : Fin n) :
    RCLike.re ⟪(A.adjoint ∘ₗ A) (hsym.eigenvectorBasis hn k),
        hsym.eigenvectorBasis hn k⟫_𝕜 = hsym.eigenvalues hn k := by
  rw [hsym.apply_eigenvectorBasis hn k,
    re_inner_real_smul_self_of_norm_one
      ((hsym.eigenvectorBasis hn).orthonormal.norm_eq_one k)]

/-- **Contraction ⇒ singular values ≤ 1.** If `A` is a contraction
(`‖A x‖ ≤ ‖x‖`), then every singular value satisfies `σᵢ(A) ≤ 1`.  Each eigenvalue
`λᵢ(A⋆A) = re⟪A wᵢ, A wᵢ⟫ = ‖A wᵢ‖² ≤ 1` (`wᵢ` the unit eigenvector), and
`σᵢ = √λᵢ`. -/
theorem singularValues_le_one_of_contraction {A : E →ₗ[𝕜] F}
    (h : ∀ x, ‖A x‖ ≤ ‖x‖) {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    A.singularValues (i : ℕ) ≤ 1 := by
  have hSsym := A.isSymmetric_adjoint_comp_self
  have hunit : ‖hSsym.eigenvectorBasis hn i‖ = 1 :=
    (hSsym.eigenvectorBasis hn).orthonormal.norm_eq_one i
  have hquad : RCLike.re ⟪(A.adjoint ∘ₗ A) (hSsym.eigenvectorBasis hn i),
      hSsym.eigenvectorBasis hn i⟫_𝕜 = ‖A (hSsym.eigenvectorBasis hn i)‖ ^ 2 := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
  have heig : RCLike.re ⟪(A.adjoint ∘ₗ A) (hSsym.eigenvectorBasis hn i),
      hSsym.eigenvectorBasis hn i⟫_𝕜 = hSsym.eigenvalues hn i := by
    exact re_inner_gram_eigenvectorBasis_self A hSsym hn i
  have heval : hSsym.eigenvalues hn i ≤ 1 := by
    rw [← heig, hquad]
    have := h (hSsym.eigenvectorBasis hn i)
    rw [hunit] at this
    nlinarith [norm_nonneg (A (hSsym.eigenvectorBasis hn i))]
  rw [A.singularValues_fin hn]
  calc √(hSsym.eigenvalues hn i) ≤ √1 := Real.sqrt_le_sqrt heval
    _ = 1 := Real.sqrt_one

/-- **Squared Frobenius norm = sum of squared singular values.** For any
orthonormal basis `b` of `E`, `∑ᵢ σᵢ(A)² = ∑ₖ ‖A bₖ‖²`.  Via the dictionary
`σᵢ² = λᵢ(A⋆A)`, basis independence of the trace, and
`re⟪bₖ, A⋆A bₖ⟫ = ‖A bₖ‖²`. -/
theorem sum_sq_singularValues (A : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ i : Fin n, A.singularValues (i : ℕ) ^ 2 = ∑ k, ‖A (b k)‖ ^ 2 := by
  have h1 : ∑ i : Fin n, A.singularValues (i : ℕ) ^ 2
      = ∑ i, A.isSymmetric_adjoint_comp_self.eigenvalues hn i :=
    Finset.sum_congr rfl fun i _ => A.sq_singularValues_fin hn i
  rw [h1, ← sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues
    A.isSymmetric_adjoint_comp_self hn b]
  exact Finset.sum_congr rfl fun k _ => by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]

/-- **Frobenius² ≤ trace of the modulus, for a contraction.** If `A : E →ₗ[𝕜] E`
is a contraction, then `∑ₖ ‖A bₖ‖² ≤ ∑ₖ re⟪|A| bₖ, bₖ⟫`, i.e. `∑ σᵢ² ≤ ∑ σᵢ`
(each `σᵢ ∈ [0, 1]`).  This is the core inequality of the aligned-basis
(orthogonal-Procrustes) argument: `∑‖wⱼ − uⱼ‖² = 2d − 2∑σ ≤ 2d − 2∑σ² = 2·sinΘ²`. -/
theorem sum_sq_norm_le_sum_re_inner_abs_of_contraction {A : E →ₗ[𝕜] E}
    (h : ∀ x, ‖A x‖ ≤ ‖x‖) {n : ℕ} (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, ‖A (b k)‖ ^ 2 ≤ ∑ k, RCLike.re ⟪operatorAbs A (b k), b k⟫_𝕜 := by
  rw [← sum_sq_singularValues A hn b, sum_re_inner_abs_self_eq_sum_singularValues A hn b]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := singularValues_le_one_of_contraction h hn i
  have h0 := A.singularValues_nonneg (i : ℕ)
  nlinarith

/-- **Unitary invariance of the Frobenius sum.** Pre-composing with a unitary `U`
does not change `∑ₖ ‖A (b k)‖²`: `∑ₖ ‖A (U bₖ)‖² = ∑ₖ ‖A bₖ‖²`.  Both equal the
sum of squared singular values (`sum_sq_singularValues`), since `k ↦ U bₖ` is
another orthonormal basis. -/
theorem sum_sq_norm_apply_unitary_comp (A : E →ₗ[𝕜] F) (U : E ≃ₗᵢ[𝕜] E)
    {n : ℕ} (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, ‖A (U (b k))‖ ^ 2 = ∑ k, ‖A (b k)‖ ^ 2 := by
  have h1 := sum_sq_singularValues A hn (b.map U)
  have h2 := sum_sq_singularValues A hn b
  simp only [OrthonormalBasis.map_apply] at h1
  rw [← h2, ← h1]

/-- **Gram-transported Weyl bound for squared singular values.** The `k`-th
squared singular values of `A` and `Â` differ by at most the Gram perturbation
bound: `|σₖ(Â)² − σₖ(A)²| ≤ (a + â) ε`.  Via the dictionary `σₖ² = λₖ(·⋆·)`
(`sq_singularValues_fin`) and Weyl's inequality on the Gram operators, fed by the
perturbation bound `norm_gram_sub_gram_apply_le`.

**This is weaker than Weyl's inequality for singular values, in three ways**, and
the name is deliberately not "Weyl's inequality" on that account: it bounds the
*squares*, its constant carries the extra factor `a + â` so the bound degrades
with the size of the operators, and it needs the auxiliary hypotheses `hA`, `hÂ`
that the genuine theorem does not.  The sharp form is
`ContinuousLinearMap.abs_singularValues_sub_singularValues_le`
(`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteDimensional.lean`),
`|σₙ(T) − σₙ(S)| ≤ ‖T − S‖`, which implies this one but not conversely — dividing
back out by `σₖ(A) + σₖ(Â)` recovers nothing when the singular values are small.
This version survives because it is the shape the Gram-side arguments produce. -/
theorem abs_sq_singularValues_sub_le {A Â : E →ₗ[𝕜] F} {a â ε : ℝ}
    (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖)
    {n : ℕ} (hn : finrank 𝕜 E = n) (k : Fin n) :
    |Â.singularValues k ^ 2 - A.singularValues k ^ 2| ≤ (a + â) * ε := by
  rw [Â.sq_singularValues_fin hn, A.sq_singularValues_fin hn]
  exact abs_eigenvalue_sub_eigenvalue_le Â.isSymmetric_adjoint_comp_self
    A.isSymmetric_adjoint_comp_self hn
    (fun x => norm_gram_sub_gram_apply_le hâ hε hA hÂ hE x) k

/-! ### Extreme singular values: variational characterization

The largest singular value is the operator norm and the smallest is the
minimum gain, both attained.  These are the quantitative
inputs for the operator-norm principal-angle identification. -/

section Extreme

variable {n : ℕ}

/-- `‖A x‖² = re ⟪(A⋆A) x, x⟫`, the seed of every variational bound here. -/
private theorem sq_norm_apply_eq_re_inner_gram (A : E →ₗ[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = RCLike.re ⟪(A.adjoint ∘ₗ A) x, x⟫_𝕜 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]

/-- The squared gain at a Gram eigenvector is the corresponding eigenvalue. -/
private theorem sq_norm_apply_eigenvectorBasis
    {n : ℕ} (A : E →ₗ[𝕜] F)
    (hsym : (A.adjoint ∘ₗ A).IsSymmetric) (hn : Module.finrank 𝕜 E = n) (k : Fin n) :
    ‖A (hsym.eigenvectorBasis hn k)‖ ^ 2 = hsym.eigenvalues hn k := by
  rw [sq_norm_apply_eq_re_inner_gram, re_inner_gram_eigenvectorBasis_self A hsym hn k]

/-- **The smallest singular value is a lower bound for the gain:**
`σ_{n-1}(A) * ‖x‖ ≤ ‖A x‖`. -/
theorem singularValues_last_mul_norm_le (A : E →ₗ[𝕜] F) (hn : finrank 𝕜 E = n)
    (hn0 : 0 < n) (x : E) : A.singularValues (n - 1) * ‖x‖ ≤ ‖A x‖ := by
  have hlast : n - 1 < n := by omega
  set k : Fin n := ⟨n - 1, hlast⟩
  have hsym := A.isSymmetric_adjoint_comp_self
  have hsq : (A.singularValues (n - 1) * ‖x‖) ^ 2 ≤ ‖A x‖ ^ 2 := by
    rw [sq_norm_apply_eq_re_inner_gram,
      LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hsym hn x, mul_pow,
      A.sq_singularValues_of_lt hn hlast]
    have hpars : ∑ i : Fin n, ‖(hsym.eigenvectorBasis hn).repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
      simp_rw [(hsym.eigenvectorBasis hn).repr_apply_apply]
      exact (hsym.eigenvectorBasis hn).sum_sq_norm_inner_right x
    calc hsym.eigenvalues hn k * ‖x‖ ^ 2
        = ∑ i : Fin n, hsym.eigenvalues hn k * ‖(hsym.eigenvectorBasis hn).repr x i‖ ^ 2 := by
          rw [← Finset.mul_sum, hpars]
      _ ≤ ∑ i : Fin n, hsym.eigenvalues hn i * ‖(hsym.eigenvectorBasis hn).repr x i‖ ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right
              (hsym.eigenvalues_antitone hn (Fin.le_def.mpr (by omega : (i : ℕ) ≤ n - 1)))
              (sq_nonneg _)
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- **The smallest singular value is attained.** -/
theorem exists_norm_apply_eq_singularValues_last (A : E →ₗ[𝕜] F) (hn : finrank 𝕜 E = n)
    (hn0 : 0 < n) : ∃ x, ‖x‖ = 1 ∧ ‖A x‖ = A.singularValues (n - 1) := by
  have hlast : n - 1 < n := by omega
  set k : Fin n := ⟨n - 1, hlast⟩
  have hsym := A.isSymmetric_adjoint_comp_self
  refine ⟨hsym.eigenvectorBasis hn k, (hsym.eigenvectorBasis hn).orthonormal.norm_eq_one k, ?_⟩
  have hsq : ‖A (hsym.eigenvectorBasis hn k)‖ ^ 2 = A.singularValues (n - 1) ^ 2 := by
    rw [sq_norm_apply_eigenvectorBasis A hsym hn k, A.sq_singularValues_of_lt hn hlast]
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (A.singularValues_nonneg _)] at this

/-- **The largest singular value bounds the gain:** `‖A x‖ ≤ σ₀(A) * ‖x‖`
(the elementwise form of `σ₀ = ‖A‖`). -/
theorem norm_apply_le_singularValues_zero_mul (A : E →ₗ[𝕜] F) (hn : finrank 𝕜 E = n)
    (hn0 : 0 < n) (x : E) : ‖A x‖ ≤ A.singularValues 0 * ‖x‖ := by
  have hsym := A.isSymmetric_adjoint_comp_self
  have hsq : ‖A x‖ ^ 2 ≤ (A.singularValues 0 * ‖x‖) ^ 2 := by
    rw [sq_norm_apply_eq_re_inner_gram,
      LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hsym hn x, mul_pow,
      A.sq_singularValues_of_lt hn hn0]
    have hpars : ∑ i : Fin n, ‖(hsym.eigenvectorBasis hn).repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
      simp_rw [(hsym.eigenvectorBasis hn).repr_apply_apply]
      exact (hsym.eigenvectorBasis hn).sum_sq_norm_inner_right x
    calc ∑ i : Fin n, hsym.eigenvalues hn i * ‖(hsym.eigenvectorBasis hn).repr x i‖ ^ 2
        ≤ ∑ i : Fin n, hsym.eigenvalues hn ⟨0, hn0⟩
            * ‖(hsym.eigenvectorBasis hn).repr x i‖ ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right
              (hsym.eigenvalues_antitone hn (Fin.le_def.mpr (Nat.zero_le _)))
              (sq_nonneg _)
      _ = hsym.eigenvalues hn ⟨0, hn0⟩ * ‖x‖ ^ 2 := by rw [← Finset.mul_sum, hpars]
  exact le_of_sq_le_sq hsq (mul_nonneg (A.singularValues_nonneg 0) (norm_nonneg x))

/-- **The largest singular value is attained.** -/
theorem exists_norm_apply_eq_singularValues_zero (A : E →ₗ[𝕜] F) (hn : finrank 𝕜 E = n)
    (hn0 : 0 < n) : ∃ x, ‖x‖ = 1 ∧ ‖A x‖ = A.singularValues 0 := by
  have hsym := A.isSymmetric_adjoint_comp_self
  refine ⟨hsym.eigenvectorBasis hn ⟨0, hn0⟩,
    (hsym.eigenvectorBasis hn).orthonormal.norm_eq_one _, ?_⟩
  have hsq : ‖A (hsym.eigenvectorBasis hn ⟨0, hn0⟩)‖ ^ 2 = A.singularValues 0 ^ 2 := by
    rw [sq_norm_apply_eigenvectorBasis A hsym hn _, A.sq_singularValues_of_lt hn hn0]
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (A.singularValues_nonneg _)] at this

end Extreme

/-! ### Singular values of the adjoint (square case)

`σ(A⋆) = σ(A)` for a square operator `A : E →ₗ[𝕜] E`.  The Gram operators
`A⋆A` and `A A⋆` are unitarily conjugate (`A A⋆ = U (A⋆A) U⁻¹` with
`U = choosePolarUnitary A`), so they have equal sorted eigenvalues, hence `A` and
`A⋆` have equal singular values.  This is the symmetry `cosPrincipalAngles`
needs (plan step W0.1(d)).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SingularSubspace`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `29506b0`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

section Adjoint

variable {n : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- The conjugate `U S U⁻¹` of a symmetric operator by a unitary is symmetric. -/
theorem isSymmetric_conj_unitary {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (U : E ≃ₗᵢ[𝕜] E) :
    (U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap).IsSymmetric := by
  intro x y
  simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
  calc ⟪U (S (U.symm x)), y⟫_𝕜
      = ⟪U (S (U.symm x)), U (U.symm y)⟫_𝕜 := by rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪S (U.symm x), U.symm y⟫_𝕜 := U.inner_map_map _ _
    _ = ⟪U.symm x, S (U.symm y)⟫_𝕜 := hS _ _
    _ = ⟪U (U.symm x), U (S (U.symm y))⟫_𝕜 := (U.inner_map_map _ _).symm
    _ = ⟪x, U (S (U.symm y))⟫_𝕜 := by rw [LinearIsometryEquiv.apply_symm_apply]

/-- One direction of unitary-conjugation eigenvalue invariance:
`λₖ(S) ≤ λₖ(U S U⁻¹)`.  Courant–Fischer — a witness `(k+1)`-subspace for `S`
maps under `U` to one for the conjugate, on which the same Rayleigh values
recur. -/
private theorem eigenvalues_conj_unitary_le {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (U : E ≃ₗᵢ[𝕜] E) (k : Fin n) :
    hS.eigenvalues hn k ≤ (isSymmetric_conj_unitary hS U).eigenvalues hn k := by
  obtain ⟨V, hVdim, hVlow⟩ :=
    LinearMap.IsSymmetric.exists_submodule_forall_unit_eigenvalue_le_re_inner hS hn k
  have hmapfin : finrank 𝕜 (V.map U.toLinearMap) = (k : ℕ) + 1 := by
    rw [show (U.toLinearMap : E →ₗ[𝕜] E) = (U.toLinearEquiv : E →ₗ[𝕜] E) from rfl,
      LinearEquiv.finrank_map_eq, hVdim]
  obtain ⟨y, hyV', hny, hup⟩ := LinearMap.IsSymmetric.exists_unit_vector_re_inner_le_eigenvalue
    (isSymmetric_conj_unitary hS U) hn k (V.map U.toLinearMap) hmapfin
  obtain ⟨x, hxV, hUxy⟩ := Submodule.mem_map.mp hyV'
  simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at hUxy
  have hnx : ‖x‖ = 1 := by rw [← hny, ← hUxy, U.norm_map]
  have hyx : U.symm y = x := by rw [← hUxy, U.symm_apply_apply]
  have hray : RCLike.re ⟪(U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap) y, y⟫_𝕜
      = RCLike.re ⟪S x, x⟫_𝕜 := by
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
    rw [hyx, ← hUxy, U.inner_map_map]
  calc hS.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
    _ = RCLike.re ⟪(U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap) y, y⟫_𝕜 := hray.symm
    _ ≤ (isSymmetric_conj_unitary hS U).eigenvalues hn k := hup

/-- **Unitary conjugation preserves sorted eigenvalues.** For a symmetric
operator `S` and a unitary `U`, `S` and `U S U⁻¹` have the same sorted
eigenvalues.  (Courant–Fischer: the Rayleigh minimax is invariant under the
subspace bijection `V ↦ U V`.) -/
theorem eigenvalues_conj_unitary {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (U : E ≃ₗᵢ[𝕜] E) :
    (isSymmetric_conj_unitary hS U).eigenvalues hn = hS.eigenvalues hn := by
  funext k
  refine le_antisymm ?_ (eigenvalues_conj_unitary_le hS hn U k)
  -- Reverse direction: `S` is the conjugate of `U S U⁻¹` by `U⁻¹`.
  have hback : U.symm.toLinearMap ∘ₗ (U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap)
      ∘ₗ U.symm.symm.toLinearMap = S := by
    ext v
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]
  have hcong := eigenvalues_congr hback
    (isSymmetric_conj_unitary (isSymmetric_conj_unitary hS U) U.symm) hS hn
  have := eigenvalues_conj_unitary_le (isSymmetric_conj_unitary hS U) hn U.symm k
  rwa [hcong] at this

/-- The Gram operators `A A⋆` and `A⋆A` are unitarily conjugate:
`A A⋆ = U (A⋆A) U⁻¹` with `U = choosePolarUnitary A`.  From `A = U |A|`,
`A⋆ = |A| U⁻¹`, so `A A⋆ = U |A|² U⁻¹ = U (A⋆A) U⁻¹`. -/
theorem comp_adjoint_eq_conj_adjoint_comp (A : E →ₗ[𝕜] E) :
    A ∘ₗ A.adjoint = (choosePolarUnitary A).toLinearMap ∘ₗ (A.adjoint ∘ₗ A)
      ∘ₗ (choosePolarUnitary A).symm.toLinearMap := by
  set U := choosePolarUnitary A with hU
  have hpolar : A = U.toLinearMap ∘ₗ operatorAbs A := polar_decomposition_choosePolarUnitary A
  have hadj : A.adjoint = operatorAbs A ∘ₗ U.symm.toLinearMap := by
    conv_lhs => rw [hpolar]
    rw [LinearMap.adjoint_comp, (isPositive_operatorAbs A).adjoint_eq,
      U.adjoint_toLinearMap_eq_symm]
  calc A ∘ₗ A.adjoint
      = (U.toLinearMap ∘ₗ operatorAbs A) ∘ₗ (operatorAbs A ∘ₗ U.symm.toLinearMap) := by
        rw [← hpolar, ← hadj]
    _ = U.toLinearMap ∘ₗ (operatorAbs A ∘ₗ operatorAbs A) ∘ₗ U.symm.toLinearMap := by
        ext v; simp only [LinearMap.comp_apply]
    _ = U.toLinearMap ∘ₗ (A.adjoint ∘ₗ A) ∘ₗ U.symm.toLinearMap := by rw [operatorAbs_mul_self A]

/-- The Gram operators of `A` and `A⋆` have equal sorted eigenvalues. -/
theorem eigenvalues_gram_adjoint (A : E →ₗ[𝕜] E) (hn : finrank 𝕜 E = n) :
    A.adjoint.isSymmetric_adjoint_comp_self.eigenvalues hn
      = A.isSymmetric_adjoint_comp_self.eigenvalues hn := by
  have hAA : A.adjoint.adjoint ∘ₗ A.adjoint = (choosePolarUnitary A).toLinearMap
      ∘ₗ (A.adjoint ∘ₗ A) ∘ₗ (choosePolarUnitary A).symm.toLinearMap := by
    rw [LinearMap.adjoint_adjoint]; exact comp_adjoint_eq_conj_adjoint_comp A
  have hcong := eigenvalues_congr hAA A.adjoint.isSymmetric_adjoint_comp_self
    (isSymmetric_conj_unitary A.isSymmetric_adjoint_comp_self (choosePolarUnitary A)) hn
  rw [hcong, eigenvalues_conj_unitary A.isSymmetric_adjoint_comp_self hn (choosePolarUnitary A)]

end Adjoint

end TauCeti
