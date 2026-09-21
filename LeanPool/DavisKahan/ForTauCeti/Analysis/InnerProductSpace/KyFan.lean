/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T05.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`KyFan.lean`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).

Ky Fan partial sums of singular values: the trace inequality
`∑ᵢ re⟪S wᵢ, wᵢ⟫ ≤ ∑_{top k} λᵢ(S)` for an orthonormal `k`-family (via a
fractional-knapsack lemma), the Ky Fan variational principle
`∑_{i<k} σᵢ(A) = max re ∑ᵢ ⟪uᵢ, A vᵢ⟫` (via the polar decomposition and the
positive square root), and its consequence, the simultaneous triangle
inequality for all Ky Fan norms — weak majorization
`σ(A + B) ≺_w σ(A) + σ(B)`.
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectrum
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ZeroExtension
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix


/-! # Ky Fan sums of singular values

For operators on finite-dimensional inner product spaces over `𝕜 = ℝ, ℂ`:

* `kyFanSum k A = ∑_{i<k} σᵢ(A)`, the Ky Fan `k`-sums;
* the **Ky Fan trace inequality**: for a symmetric `S` and an orthonormal
  family `w : Fin k → E`, `∑ᵢ re⟪S wᵢ, wᵢ⟫ ≤ ∑_{i<k} λᵢ(S)`;
* the **Ky Fan variational principle**: `kyFanSum k A` is the maximum of
  `re ∑ᵢ ⟪uᵢ, A vᵢ⟫` over orthonormal `k`-families `u, v`;
* **weak majorization** `kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B` —
  the triangle inequality for every Ky Fan norm simultaneously, the engine of
  the Fan dominance principle (`UnitarilyInvariantSeminorm.lean`);
* unitary invariance, adjoint invariance, and nonnegative-real scaling of
  singular values and Ky Fan sums, plus the bounded-factor domination
  `σᵢ(C ∘ A) ≤ c σᵢ(A)` (Loewner monotonicity of the Gram eigenvalues).

## References

* R. Bhatia, *Matrix Analysis*, Chapter IV (Ky Fan norms, dominance).
* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear
  transformations I*, Proc. Nat. Acad. Sci. USA 35 (1949), 652–655.
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open _root_.LinearMap
open Module (finrank)

variable {𝕜 E F F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']

/-! ### Singular values under unitaries, scaling, and bounded factors (F0) -/

/-- Post-composing with a unitary does not change the singular values. -/
theorem singularValues_unitary_comp (U : F ≃ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] F) :
    (U.toLinearMap ∘ₗ A).singularValues = A.singularValues := by
  refine singularValues_eq_of_gram_eq ?_
  rw [LinearMap.adjoint_comp, U.adjoint_toLinearMap_eq_symm]
  ext x
  simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
    LinearIsometryEquiv.symm_apply_apply]

/-- Pre-composing with a unitary does not change the singular values. -/
theorem singularValues_comp_unitary (A : E →ₗ[𝕜] F) (U : E ≃ₗᵢ[𝕜] E) :
    (A ∘ₗ U.toLinearMap).singularValues = A.singularValues := by
  have hgram : (A ∘ₗ U.toLinearMap).adjoint ∘ₗ (A ∘ₗ U.toLinearMap)
      = U.symm.toLinearMap ∘ₗ (A.adjoint ∘ₗ A) ∘ₗ U.symm.symm.toLinearMap := by
    rw [LinearMap.adjoint_comp, U.adjoint_toLinearMap_eq_symm, LinearIsometryEquiv.symm_symm]
    ext x
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
  ext i
  rcases lt_or_ge i (finrank 𝕜 E) with hi | hi
  · rw [(A ∘ₗ U.toLinearMap).singularValues_of_lt rfl hi, A.singularValues_of_lt rfl hi]
    congr 1
    calc (A ∘ₗ U.toLinearMap).isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, hi⟩
        = (isSymmetric_conj_unitary A.isSymmetric_adjoint_comp_self
            U.symm).eigenvalues rfl ⟨i, hi⟩ :=
          congrFun (eigenvalues_congr hgram _ _ rfl) _
      _ = A.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, hi⟩ :=
          congrFun (eigenvalues_conj_unitary A.isSymmetric_adjoint_comp_self rfl U.symm) _
  · rw [(A ∘ₗ U.toLinearMap).singularValues_of_finrank_le hi,
      A.singularValues_of_finrank_le hi]

omit [FiniteDimensional 𝕜 E] in
/-- Real-smul of a symmetric operator is symmetric. -/
theorem isSymmetric_real_smul {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (r : ℝ) :
    (((r : 𝕜)) • S).IsSymmetric := fun x y => by
  simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
  rw [hS x y]

/-- Sorted eigenvalues scale under a nonnegative real scaling. -/
theorem eigenvalues_real_smul {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric) {n : ℕ}
    (hn : finrank 𝕜 E = n) {r : ℝ} (hr : 0 ≤ r) :
    (isSymmetric_real_smul hS r).eigenvalues hn = fun i => r * hS.eigenvalues hn i := by
  refine LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis _ hn (hS.eigenvectorBasis hn)
    (fun i j hij => mul_le_mul_of_nonneg_left (hS.eigenvalues_antitone hn hij) hr)
    fun i => ?_
  rw [LinearMap.smul_apply, hS.apply_eigenvectorBasis hn i, smul_smul, ← RCLike.ofReal_mul]

/-- The adjoint of a real scaling. -/
private theorem adjoint_real_smul (A : E →ₗ[𝕜] F) (r : ℝ) :
    (((r : 𝕜)) • A).adjoint = ((r : 𝕜)) • A.adjoint := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    LinearMap.adjoint_inner_left]

/-- Singular values scale by `r` under a nonnegative real scaling. -/
theorem singularValues_real_smul (A : E →ₗ[𝕜] F) {r : ℝ} (hr : 0 ≤ r) (i : ℕ) :
    (((r : 𝕜)) • A).singularValues i = r * A.singularValues i := by
  rcases lt_or_ge i (finrank 𝕜 E) with hi | hi
  · have hgram : (((r : 𝕜)) • A).adjoint ∘ₗ (((r : 𝕜)) • A)
        = ((r ^ 2 : ℝ) : 𝕜) • (A.adjoint ∘ₗ A) := by
      rw [adjoint_real_smul]
      ext x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul,
        ← RCLike.ofReal_mul, sq]
    -- Not shortened: every step here is a congruence term applied to explicit arguments
    -- (`congrFun (eigenvalues_congr ..) ⟨i, hi⟩`), not a name `simp` could pick up, and the
    -- order is forced -- the two `eigenvalues_*` rewrites must fire before `Real.sqrt_mul`
    -- has a product to split.
    rw [(((r : 𝕜)) • A).singularValues_of_lt rfl hi, A.singularValues_of_lt rfl hi,
      congrFun (eigenvalues_congr hgram (((r : 𝕜)) • A).isSymmetric_adjoint_comp_self
        (isSymmetric_real_smul A.isSymmetric_adjoint_comp_self (r ^ 2)) rfl) ⟨i, hi⟩,
      congrFun (eigenvalues_real_smul A.isSymmetric_adjoint_comp_self rfl
        (by positivity : (0:ℝ) ≤ r ^ 2)) ⟨i, hi⟩,
      Real.sqrt_mul (by positivity) _, Real.sqrt_sq hr]
  · rw [(((r : 𝕜)) • A).singularValues_of_finrank_le hi, A.singularValues_of_finrank_le hi,
      mul_zero]

/-- **Domination by a bounded left factor:** `σᵢ(C ∘ A) ≤ c σᵢ(A)` when
`‖C y‖ ≤ c ‖y‖`.  Via Loewner monotonicity of the Gram eigenvalues. -/
theorem singularValues_comp_le {C : F →ₗ[𝕜] F'} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) (A : E →ₗ[𝕜] F) (i : ℕ) :
    (C ∘ₗ A).singularValues i ≤ c * A.singularValues i := by
  rcases lt_or_ge i (finrank 𝕜 E) with hi | hi
  · have hsm := isSymmetric_real_smul A.isSymmetric_adjoint_comp_self (c ^ 2)
    have hforms : ∀ x, RCLike.re ⟪((C ∘ₗ A).adjoint ∘ₗ (C ∘ₗ A)) x, x⟫_𝕜
        ≤ RCLike.re ⟪(((c ^ 2 : ℝ) : 𝕜) • (A.adjoint ∘ₗ A)) x, x⟫_𝕜 := by
      intro x
      have h1 : RCLike.re ⟪((C ∘ₗ A).adjoint ∘ₗ (C ∘ₗ A)) x, x⟫_𝕜 = ‖(C ∘ₗ A) x‖ ^ 2 := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
      have h2 : RCLike.re ⟪(((c ^ 2 : ℝ) : 𝕜) • (A.adjoint ∘ₗ A)) x, x⟫_𝕜
          = c ^ 2 * ‖A x‖ ^ 2 := by
        simp [inner_smul_left, LinearMap.adjoint_inner_left]
      rw [h1, h2]
      have h3 : ‖(C ∘ₗ A) x‖ ≤ c * ‖A x‖ := hC (A x)
      nlinarith [norm_nonneg ((C ∘ₗ A) x), norm_nonneg (A x),
        mul_nonneg hc (norm_nonneg (A x))]
    have hloew := LinearMap.IsSymmetric.eigenvalue_mono
      (C ∘ₗ A).isSymmetric_adjoint_comp_self hsm rfl hforms ⟨i, hi⟩
    rw [congrFun (eigenvalues_real_smul A.isSymmetric_adjoint_comp_self rfl
      (by positivity : (0:ℝ) ≤ c ^ 2)) ⟨i, hi⟩] at hloew
    rw [(C ∘ₗ A).singularValues_of_lt rfl hi, A.singularValues_of_lt rfl hi]
    calc √((C ∘ₗ A).isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, hi⟩)
        ≤ √(c ^ 2 * A.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, hi⟩) :=
          Real.sqrt_le_sqrt hloew
      _ = c * √(A.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, hi⟩) := by
          rw [Real.sqrt_mul (by positivity) _, Real.sqrt_sq hc]
  · rw [(C ∘ₗ A).singularValues_of_finrank_le hi, A.singularValues_of_finrank_le hi, mul_zero]

/-- **Domination by a bounded right factor:**
`σᵢ(X ∘ C) ≤ c σᵢ(X)`.  Via `singularValues_adjoint`. -/
theorem singularValues_comp_le' {X : E →ₗ[𝕜] F} {C : E →ₗ[𝕜] E} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) (i : ℕ) :
    (X ∘ₗ C).singularValues i ≤ c * X.singularValues i := by
  rw [← LinearMap.singularValues_adjoint (X ∘ₗ C), LinearMap.adjoint_comp,
    ← LinearMap.singularValues_adjoint X]
  exact singularValues_comp_le hc (fun y => norm_adjoint_apply_le hc hC y) X.adjoint i

/-- The sorted eigenvalues of the modulus `|A|` are the singular values. -/
theorem eigenvalues_operatorAbs (A : E →ₗ[𝕜] E) :
    (isPositive_operatorAbs A).isSymmetric.eigenvalues rfl
      = fun i : Fin (finrank 𝕜 E) => A.singularValues (i : ℕ) := by
  refine LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis _ rfl
    (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
    (fun i j hij => A.singularValues_antitone (by exact_mod_cast hij))
    fun i => ?_
  rw [show operatorAbs A = (LinearMap.isPositive_adjoint_comp_self A).sqrt from rfl,
    (LinearMap.isPositive_adjoint_comp_self A).sqrt_apply_eigenvectorBasis i,
    A.singularValues_fin rfl i]

/-! ### The Ky Fan trace inequality (F1.a–b) -/

/-- **Fractional knapsack**: an antitone list, integrated against weights in
`[0, 1]` of total mass exactly `k`, is at most its top-`k` sum. -/
private theorem sum_mul_le_sum_top {n k : ℕ} (hk : k ≤ n) {lam c : Fin n → ℝ}
    (hlam : Antitone lam) (h0 : ∀ j, 0 ≤ c j) (h1 : ∀ j, c j ≤ 1)
    (hsum : ∑ j, c j = k) :
    ∑ j, lam j * c j
      ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), lam j := by
  rcases lt_or_eq_of_le hk with hkn | rfl
  · set t := lam ⟨k, hkn⟩ with ht
    have hhead : ∀ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
        lam j * c j ≤ lam j + t * (c j - 1) := by
      intro j hj
      have hjk : (j : ℕ) < k := (Finset.mem_filter.mp hj).2
      have hle : t ≤ lam j := hlam (Fin.le_def.mpr hjk.le)
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr (h1 j))]
    have htail : ∀ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k),
        lam j * c j ≤ t * c j := by
      intro j hj
      have hjk : ¬ (j : ℕ) < k := (Finset.mem_filter.mp hj).2
      have hle : lam j ≤ t := hlam (Fin.le_def.mpr (Nat.le_of_not_lt hjk))
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (h0 j)]
    have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin n => (j : ℕ) < k) (fun j => lam j * c j)).symm
    have hhead_eq : ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
        (lam j + t * (c j - 1))
        = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), lam j
          + t * (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), c j) - t * k := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_filter_lt hk, nsmul_eq_mul, mul_one]
      ring
    have htail_eq : ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), t * c j
        = t * ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), c j :=
      (Finset.mul_sum _ _ _).symm
    have hcsplit : ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), c j
        + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), c j = k := by
      rw [Finset.sum_filter_add_sum_filter_not]; exact hsum
    have hmul := congrArg (fun z => t * z) hcsplit
    simp only [mul_add] at hmul
    calc ∑ j, lam j * c j
        = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), lam j * c j
          + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), lam j * c j := hsplit
      _ ≤ (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
            (lam j + t * (c j - 1)))
          + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), t * c j :=
          add_le_add (Finset.sum_le_sum hhead) (Finset.sum_le_sum htail)
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), lam j := by
          rw [hhead_eq, htail_eq]
          linarith [hmul]
  · have hall : ∀ j, c j = 1 := by
      intro j
      by_contra hne
      have hlt : c j < 1 := lt_of_le_of_ne (h1 j) hne
      have hstrict : ∑ j', c j' < k := by
        calc ∑ j', c j' < ∑ _j' : Fin k, (1 : ℝ) :=
              Finset.sum_lt_sum (fun j' _ => h1 j') ⟨j, Finset.mem_univ j, hlt⟩
          _ = k := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [hsum] at hstrict
      exact lt_irrefl _ hstrict
    have hfilter : (Finset.univ.filter (fun j : Fin k => (j : ℕ) < k)) = Finset.univ := by
      ext j; simp
    rw [hfilter]
    exact le_of_eq (Finset.sum_congr rfl fun j _ => by rw [hall j, mul_one])

/-- **The Ky Fan trace inequality.**  For a symmetric operator `S` and an
orthonormal family `w : Fin k → E`,
`∑ᵢ re ⟪S (w i), w i⟫ ≤ ∑_{j < k} λⱼ(S)` — the trace of `S` compressed to any
`k`-dimensional subspace is at most the sum of the `k` largest eigenvalues.
(Ky Fan's maximum principle; implies the Schur–Horn partial-sum
inequalities.) -/
theorem sum_re_inner_le_sum_eigenvalues_top {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k ≤ n) {w : Fin k → E}
    (hw : Orthonormal 𝕜 w) :
    ∑ i, RCLike.re ⟪S (w i), w i⟫_𝕜
      ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), hS.eigenvalues hn j := by
  set b := hS.eigenvectorBasis hn with hb
  set c : Fin n → ℝ := fun j => ∑ i : Fin k, ‖b.repr (w i) j‖ ^ 2 with hc
  have hswap : ∑ i, RCLike.re ⟪S (w i), w i⟫_𝕜 = ∑ j, hS.eigenvalues hn j * c j := by
    have hdiag : ∀ i, RCLike.re ⟪S (w i), w i⟫_𝕜
        = ∑ j : Fin n, hS.eigenvalues hn j * ‖b.repr (w i) j‖ ^ 2 := fun i =>
      LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hS hn (w i)
    simp_rw [hdiag, hc, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  refine sum_mul_le_sum_top hk (hS.eigenvalues_antitone hn)
    (fun j => Finset.sum_nonneg fun i _ => sq_nonneg _) (fun j => ?_) ?_
  · -- Bessel: the `j`-th column mass is at most `‖b j‖² = 1`.
    have hbess := Orthonormal.norm_sq_starProjection_span_image hw Finset.univ (b j)
    have hcontr : ‖(Submodule.span 𝕜 (w '' ↑(Finset.univ : Finset (Fin k)))).starProjection
        (b j)‖ ^ 2 ≤ 1 := by
      have h1 := Submodule.norm_starProjection_apply_le
        (Submodule.span 𝕜 (w '' ↑(Finset.univ : Finset (Fin k)))) (b j)
      have h2 : ‖b j‖ = 1 := b.orthonormal.norm_eq_one j
      nlinarith [norm_nonneg ((Submodule.span 𝕜
        (w '' ↑(Finset.univ : Finset (Fin k)))).starProjection (b j))]
    rw [hbess] at hcontr
    calc c j = ∑ i : Fin k, ‖⟪w i, b j⟫_𝕜‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [b.repr_apply_apply, ← norm_inner_symm]
      _ ≤ 1 := hcontr
  · -- Parseval: the total mass is `k`.
    have hcomm : ∑ j, c j = ∑ i : Fin k, ∑ j : Fin n, ‖b.repr (w i) j‖ ^ 2 := by
      rw [hc]; exact Finset.sum_comm
    have hone : ∀ i : Fin k, ∑ j : Fin n, ‖b.repr (w i) j‖ ^ 2 = 1 := by
      intro i
      simp_rw [b.repr_apply_apply]
      rw [b.sum_sq_norm_inner_right (w i), hw.1 i, one_pow]
    rw [hcomm, Finset.sum_congr rfl fun i _ => hone i]
    simp

/-! ### The Ky Fan variational principle (F1.c) -/

/-- Index plumbing: a top-`k` filtered sum over `Fin n` is a sum over `Fin k`.
(Not `private`: `UnitarilyInvariantSeminorm.lean` consumes it to convert `kyFanSum`
domination into the prefix-sum hypothesis of the T-transform descent.) -/
theorem sum_filter_lt_eq_sum_fin {n k : ℕ} (hk : k ≤ n) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), f (j : ℕ)
      = ∑ i : Fin k, f (i : ℕ) := by
  rw [show (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), f (j : ℕ))
      = ∑ j : Fin n, if (j : ℕ) < k then f (j : ℕ) else 0 from Finset.sum_filter _ _,
    Fin.sum_univ_eq_sum_range (fun m => if m < k then f m else 0) n,
    Fin.sum_univ_eq_sum_range (fun m => f m) k, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **Ky Fan variational principle, upper bound:** for orthonormal families
`u, v : Fin k → E` and any `A : E →ₗ[𝕜] E`,
`re ∑ᵢ ⟪uᵢ, A vᵢ⟫ ≤ ∑_{i<k} σᵢ(A)`. -/
private theorem re_sum_inner_map_le_sum_singularValues_square {A : E →ₗ[𝕜] E} {k : ℕ}
    (hk : k ≤ finrank 𝕜 E) {u v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := by
  set W := choosePolarUnitary A with hW
  set R := (isPositive_operatorAbs A).sqrt with hR
  have hRsymm : R.IsSymmetric := (isPositive_operatorAbs A).sqrt_isPositive.isSymmetric
  have hRR : R ∘ₗ R = operatorAbs A := (isPositive_operatorAbs A).sqrt_mul_self
  -- Pull the polar unitary across and split `|A|` symmetrically.
  have hterm : ∀ i, ⟪u i, A (v i)⟫_𝕜 = ⟪R (W.symm (u i)), R (v i)⟫_𝕜 := by
    intro i
    have h1 : A (v i) = W (operatorAbs A (v i)) := by
      have h := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary A) (v i)
      rw [LinearMap.comp_apply] at h
      exact h.trans rfl
    calc ⟪u i, A (v i)⟫_𝕜 = ⟪W (W.symm (u i)), W (operatorAbs A (v i))⟫_𝕜 := by
          rw [W.apply_symm_apply, ← h1]
      _ = ⟪W.symm (u i), operatorAbs A (v i)⟫_𝕜 := W.inner_map_map _ _
      _ = ⟪W.symm (u i), R (R (v i))⟫_𝕜 := by
          rw [← hRR]; rfl
      _ = ⟪R (W.symm (u i)), R (v i)⟫_𝕜 := (hRsymm (W.symm (u i)) (R (v i))).symm
  have hquad : ∀ x : E, ‖R x‖ ^ 2 = RCLike.re ⟪operatorAbs A x, x⟫_𝕜 := fun x =>
    (isPositive_operatorAbs A).sq_norm_sqrt_apply x
  have hterm_le : ∀ i, RCLike.re ⟪u i, A (v i)⟫_𝕜
      ≤ RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜 / 2
        + RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜 / 2 := by
    intro i
    rw [hterm i, ← hquad, ← hquad]
    have h1 : RCLike.re ⟪R (W.symm (u i)), R (v i)⟫_𝕜 ≤ ‖R (W.symm (u i))‖ * ‖R (v i)‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    nlinarith [sq_nonneg (‖R (W.symm (u i))‖ - ‖R (v i)‖)]
  have hu' : Orthonormal 𝕜 (fun i => W.symm (u i)) := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    rw [W.symm.inner_map_map]
    exact hu i j
  have htr1 := sum_re_inner_le_sum_eigenvalues_top (isPositive_operatorAbs A).isSymmetric rfl hk hu'
  have htr2 := sum_re_inner_le_sum_eigenvalues_top (isPositive_operatorAbs A).isSymmetric rfl hk hv
  rw [eigenvalues_operatorAbs A] at htr1 htr2
  rw [sum_filter_lt_eq_sum_fin hk (fun j => A.singularValues j)] at htr1 htr2
  calc RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜)
      = ∑ i, RCLike.re ⟪u i, A (v i)⟫_𝕜 := map_sum _ _ _
    _ ≤ ∑ i, (RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜 / 2
          + RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜 / 2) :=
        Finset.sum_le_sum fun i _ => hterm_le i
    _ = (∑ i, RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜) / 2
        + (∑ i, RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜) / 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
    _ ≤ (∑ i : Fin k, A.singularValues (i : ℕ)) / 2
        + (∑ i : Fin k, A.singularValues (i : ℕ)) / 2 := by
        have h1 : ∑ i, RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜
            ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := htr1
        have h2 : ∑ i, RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜
            ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := htr2
        linarith
    _ = ∑ i : Fin k, A.singularValues (i : ℕ) := by ring

/-- **Ky Fan variational principle, achievability:** the top-`k` singular-value
sum is attained at the singular pairs. -/
private theorem exists_orthonormal_re_sum_inner_map_eq_square (A : E →ₗ[𝕜] E) {k : ℕ}
    (hk : k ≤ finrank 𝕜 E) :
    ∃ u v : Fin k → E, Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) = ∑ i : Fin k, A.singularValues (i : ℕ) := by
  set b := A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hb
  set v : Fin k → E := fun i => b (Fin.castLE hk i) with hv
  have hvon : Orthonormal 𝕜 v := b.orthonormal.comp _ (Fin.castLE_injective hk)
  set u : Fin k → E := fun i => choosePolarUnitary A (v i) with hu
  have huon : Orthonormal 𝕜 u := by
    rw [orthonormal_iff_ite] at hvon ⊢
    intro i j
    rw [hu]
    simp only
    rw [(choosePolarUnitary A).inner_map_map]
    exact hvon i j
  refine ⟨u, v, huon, hvon, ?_⟩
  have hterm : ∀ i, ⟪u i, A (v i)⟫_𝕜 = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) := by
    intro i
    have h1 : A (v i) = choosePolarUnitary A (operatorAbs A (v i)) := by
      have h := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary A) (v i)
      rw [LinearMap.comp_apply] at h
      exact h.trans rfl
    have h2 : operatorAbs A (v i) = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) • v i := by
      rw [hv]
      simp only
      rw [show operatorAbs A = (LinearMap.isPositive_adjoint_comp_self A).sqrt from rfl,
        (LinearMap.isPositive_adjoint_comp_self A).sqrt_apply_eigenvectorBasis (Fin.castLE hk i),
        ← A.singularValues_fin rfl (Fin.castLE hk i)]
      rfl
    rw [hu]
    simp only
    rw [h1, (choosePolarUnitary A).inner_map_map, h2, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hvon.1 i]
    simp
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [show (∑ i : Fin k, ((A.singularValues (i : ℕ) : ℝ) : 𝕜))
      = ((∑ i : Fin k, A.singularValues (i : ℕ) : ℝ) : 𝕜) by push_cast; rfl,
    RCLike.ofReal_re]

/-! ### Ky Fan sums and weak majorization (F2)

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.KyFan`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `199390a`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

/-- **The Ky Fan `k`-sum** of an operator: the sum of its `k` largest singular
values.  `kyFanSum 1 A = ‖A‖`, `kyFanSum (finrank 𝕜 E) A` is the trace norm.

`@[expose]`: the defining sum is the working form throughout the Ky Fan and
unitarily-invariant-norm development, so the body must stay visible to the
kernel for the `rfl`-level rewrites below. -/
@[expose]
noncomputable def kyFanSum (k : ℕ) (A : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin k, A.singularValues (i : ℕ)

/-- The Ky Fan sum as a finite singular-value vector sum. -/
theorem kyFanSum_eq_sum_fin (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = ∑ i : Fin k, A.singularValues (i : ℕ) :=
  rfl

/-- The Ky Fan sum as the sum over the natural-number prefix `[0, k)`. -/
theorem kyFanSum_eq_sum_range (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = ∑ i ∈ Finset.range k, A.singularValues i :=
  Fin.sum_univ_eq_sum_range (fun i => A.singularValues i) k

/-- Ky Fan sums are nonnegative, being sums of singular values. -/
theorem kyFanSum_nonneg (k : ℕ) (A : E →ₗ[𝕜] F) : 0 ≤ kyFanSum k A :=
  Finset.sum_nonneg fun i _ => A.singularValues_nonneg i

/-- Ky Fan sums saturate at `k = finrank`: larger `k` adds only zeros. -/
theorem kyFanSum_eq_of_finrank_le {k : ℕ} (hk : finrank 𝕜 E ≤ k) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = kyFanSum (finrank 𝕜 E) A := by
  rw [kyFanSum_eq_sum_range, kyFanSum_eq_sum_range]
  refine (Finset.sum_subset (fun i hi => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)) fun i _ hi => ?_).symm
  exact A.singularValues_of_finrank_le (by simpa using hi)

/-- **Weak majorization / the simultaneous Ky Fan triangle inequality:**
`kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B` for every `k` — i.e.
`σ(A + B) ≺_w σ(A) + σ(B)`.  From the variational principle: the maximizing
pair for `A + B` tests both `A` and `B`. -/
private theorem kyFanSum_add_le_aux {k : ℕ} (hk : k ≤ finrank 𝕜 E) (A B : E →ₗ[𝕜] E) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := by
  obtain ⟨u, v, hu, hv, heq⟩ := exists_orthonormal_re_sum_inner_map_eq_square (A + B) hk
  have hsplit : RCLike.re (∑ i, ⟪u i, (A + B) (v i)⟫_𝕜)
      = RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) + RCLike.re (∑ i, ⟪u i, B (v i)⟫_𝕜) := by
    rw [← map_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.add_apply, inner_add_right]
  rw [kyFanSum_eq_sum_fin, ← heq, hsplit, kyFanSum_eq_sum_fin, kyFanSum_eq_sum_fin]
  exact add_le_add (re_sum_inner_map_le_sum_singularValues_square hk hu hv)
    (re_sum_inner_map_le_sum_singularValues_square hk hu hv)

/-- Square variational proof, used internally for the rectangular theorem. -/
private theorem kyFanSum_add_le_square (k : ℕ) (A B : E →ₗ[𝕜] E) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := by
  rcases le_or_gt k (finrank 𝕜 E) with hk | hk
  · exact kyFanSum_add_le_aux hk A B
  · rw [kyFanSum_eq_of_finrank_le hk.le, kyFanSum_eq_of_finrank_le hk.le A,
      kyFanSum_eq_of_finrank_le hk.le B]
    exact kyFanSum_add_le_aux le_rfl A B


/-- The Ky Fan triangle inequality for arbitrary rectangular maps and every prefix length. -/
theorem kyFanSum_add_le (k : ℕ) (A B : E →ₗ[𝕜] F) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := by
  have h := kyFanSum_add_le_square k (zeroExtension A) (zeroExtension B)
  simpa only [← zeroExtension_add, kyFanSum, singularValues_zeroExtension] using h


/-- Pointwise singular-value domination gives Ky Fan domination. -/
theorem kyFanSum_le_of_singularValues_le {A B : E →ₗ[𝕜] F}
    (h : ∀ i, A.singularValues i ≤ B.singularValues i) (k : ℕ) :
    kyFanSum k A ≤ kyFanSum k B :=
  Finset.sum_le_sum fun i _ => h i

/-- Ky Fan sums are adjoint-invariant, since the singular values are. -/
theorem kyFanSum_adjoint (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFanSum k A.adjoint = kyFanSum k A := by
  unfold kyFanSum
  rw [LinearMap.singularValues_adjoint]

/-- Ky Fan sums are unchanged by a unitary on the codomain. -/
theorem kyFanSum_unitary_comp (k : ℕ) (U : F ≃ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] F) :
    kyFanSum k (U.toLinearMap ∘ₗ A) = kyFanSum k A := by
  unfold kyFanSum
  rw [singularValues_unitary_comp]

/-- Ky Fan sums are unchanged by a unitary on the domain.  With `kyFanSum_unitary_comp` this is
the two-sided unitary invariance that makes each Ky Fan sum a unitarily invariant norm. -/
theorem kyFanSum_comp_unitary (k : ℕ) (A : E →ₗ[𝕜] F) (U : E ≃ₗᵢ[𝕜] E) :
    kyFanSum k (A ∘ₗ U.toLinearMap) = kyFanSum k A := by
  unfold kyFanSum
  rw [singularValues_comp_unitary]

/-- Ky Fan sums are absolutely homogeneous under real scaling. -/
theorem kyFanSum_real_smul (k : ℕ) (A : E →ₗ[𝕜] F) {r : ℝ} (hr : 0 ≤ r) :
    kyFanSum k (((r : 𝕜)) • A) = r * kyFanSum k A := by
  unfold kyFanSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => singularValues_real_smul A hr i

/-- Singular values scale by the norm of an arbitrary scalar. -/
theorem singularValues_smul_apply (a : 𝕜) (A : E →ₗ[𝕜] F) (i : ℕ) :
    (a • A).singularValues i = ‖a‖ * A.singularValues i := by
  have hgram : (a • A).adjoint ∘ₗ (a • A) =
      (((‖a‖ : ℝ) : 𝕜) • A).adjoint ∘ₗ (((‖a‖ : ℝ) : 𝕜) • A) := by
    ext x
    apply ext_inner_right 𝕜
    intro y
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal]
    rw [← mul_assoc, RCLike.mul_conj]
    ring
  calc
    (a • A).singularValues i =
        (((‖a‖ : ℝ) : 𝕜) • A).singularValues i :=
      congrArg (fun s : ℕ →₀ ℝ => s i)
        (singularValues_eq_of_gram_eq hgram)
    _ = ‖a‖ * A.singularValues i :=
      singularValues_real_smul A (norm_nonneg a) i


/-- Bundled singular-value sequence of a scalar multiple.  This is the
Finsupp-level companion to `singularValues_smul_apply`; it is convenient when
a unitarily invariant norm is compared through its complete gauge sequence. -/
theorem singularValues_smul (a : 𝕜) (A : E →ₗ[𝕜] F) :
    (a • A).singularValues = ‖a‖ • A.singularValues := by
  ext i
  simp [singularValues_smul_apply]

/-- **Rectangular Ky Fan variational principle, upper bound.**

For orthonormal domain and codomain families, the real part of the paired
matrix coefficient sum is bounded by the corresponding singular-value prefix.
The proof embeds both families in the two coordinates of the `L²` product and
applies the square Ky Fan variational principle to `zeroExtension A`. -/
theorem re_sum_inner_map_le_kyFanSum
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ kyFanSum k A := by
  let u' : Fin k → WithLp 2 (E × F) :=
    fun i => WithLp.toLp 2 (0, u i)
  let v' : Fin k → WithLp 2 (E × F) :=
    fun i => WithLp.toLp 2 (v i, 0)
  have hu' : Orthonormal 𝕜 u' := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    simpa [u', WithLp.prod_inner_apply] using hu i j
  have hv' : Orthonormal 𝕜 v' := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    simpa [v', WithLp.prod_inner_apply] using hv i j
  have hfin : finrank 𝕜 (WithLp 2 (E × F)) =
      finrank 𝕜 E + finrank 𝕜 F := by
    calc
      finrank 𝕜 (WithLp 2 (E × F)) = finrank 𝕜 (E × F) :=
        (WithLp.linearEquiv 2 𝕜 (E × F)).finrank_eq
      _ = finrank 𝕜 E + finrank 𝕜 F := by
        simp [Module.finrank_prod]
  have hk' : k ≤ finrank 𝕜 (WithLp 2 (E × F)) := by
    rw [hfin]
    omega
  have h := re_sum_inner_map_le_sum_singularValues_square
    (A := zeroExtension A) hk' hu' hv'
  simpa [u', v', zeroExtension_apply, WithLp.prod_inner_apply,
    kyFanSum, singularValues_zeroExtension] using h

/-- A convenient witness form of the rectangular Ky Fan upper bound. -/
theorem sum_le_kyFanSum_of_orthonormal
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜) :
    ∑ i, t i ≤ kyFanSum k A := by
  calc
    ∑ i, t i ≤ ∑ i, RCLike.re ⟪u i, A (v i)⟫_𝕜 :=
      Finset.sum_le_sum fun i _ => ht i
    _ = RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) := by
      rw [map_sum]
    _ ≤ kyFanSum k A :=
      re_sum_inner_map_le_kyFanSum hk hu hv

omit [FiniteDimensional 𝕜 F] in
/-- Rescaling an orthonormal family by unimodular scalars leaves it
orthonormal. -/
theorem orthonormal_unimodular_smul {ι : Type*} {u : ι → F}
    (hu : Orthonormal 𝕜 u) {c : ι → 𝕜} (hc : ∀ i, ‖c i‖ = 1) :
    Orthonormal 𝕜 fun i => c i • u i := by
  classical
  rw [orthonormal_iff_ite] at hu ⊢
  intro i j
  rw [inner_smul_left, inner_smul_right, hu i j]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, mul_one, RCLike.conj_mul, hc i]
    norm_num
  · rw [ite_eq_right h, mul_zero, mul_zero]

/-- **Absolute-value witness form of the rectangular Ky Fan upper bound.**
Because the two orthonormal families may be rephased independently, the Ky Fan
prefix dominates the sum of the *magnitudes* of the matched coefficients, not
merely their signed real parts.  This is the form needed whenever the sign of
each matched coefficient is dictated by the geometry rather than chosen. -/
theorem sum_abs_le_kyFanSum_of_orthonormal
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ |RCLike.re ⟪u i, A (v i)⟫_𝕜|) :
    ∑ i, t i ≤ kyFanSum k A := by
  classical
  set ε : Fin k → 𝕜 := fun i =>
    if 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜 then 1 else -1 with hε
  have hεnorm : ∀ i, ‖ε i‖ = 1 := by
    intro i
    rw [hε]
    by_cases h : 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜 <;> simp [h]
  refine sum_le_kyFanSum_of_orthonormal hk
    (orthonormal_unimodular_smul hu hεnorm) hv (t := t) fun i => ?_
  have hval : RCLike.re ⟪ε i • u i, A (v i)⟫_𝕜 =
      |RCLike.re ⟪u i, A (v i)⟫_𝕜| := by
    rw [inner_smul_left, hε]
    by_cases h : 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.mp h)]
  rw [hval]
  exact ht i

/-- **Rectangular Ky Fan variational principle, achievability.**

For `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces and any `k` no larger
than either dimension, the upper bound `re_sum_inner_map_le_kyFanSum` is attained:
there are orthonormal `k`-families `v` in the domain and `u` in the codomain with
`re ∑ᵢ ⟪uᵢ, A vᵢ⟫ = ∑_{i<k} σᵢ(A)`.

Both dimension hypotheses are needed, and neither is an artefact of the proof: the statement
asserts the existence of orthonormal `k`-tuples in `E` and in `F`, so it is false as soon as
`k` exceeds either dimension.

The domain family is read off the eigenbasis of `A⋆A`, exactly as in the square case
`exists_orthonormal_re_sum_inner_map_eq_square`.  The codomain family cannot be obtained from a
unitary the way the square case obtains it from the polar factor, because `A` need not have
one; instead the normalized images `σᵢ⁻¹ • A vᵢ` of the directions with `σᵢ ≠ 0` are an
orthonormal family in `F`, and `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
completes it.  The directions with `σᵢ = 0` contribute nothing to either side, since
`‖A vᵢ‖ = σᵢ`. -/
theorem exists_orthonormal_re_sum_inner_map_eq_kyFanSum
    (A : E →ₗ[𝕜] F) {k : ℕ} (hkE : k ≤ finrank 𝕜 E) (hkF : k ≤ finrank 𝕜 F) :
    ∃ (u : Fin k → F) (v : Fin k → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) = kyFanSum k A := by
  classical
  set hS := A.isSymmetric_adjoint_comp_self with hSdef
  set b := hS.eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) with hbdef
  set v : Fin k → E := fun i => b (Fin.castLE hkE i) with hvdef
  have hv : Orthonormal 𝕜 v := b.orthonormal.comp _ (Fin.castLE_injective hkE)
  -- the Gram relation of the singular directions
  have hgram : ∀ i j : Fin k, ⟪A (v i), A (v j)⟫_𝕜
      = ((A.singularValues (i : ℕ) ^ 2 : ℝ) : 𝕜) * (if i = j then (1 : 𝕜) else 0) := by
    intro i j
    have h1 : ⟪A (v i), A (v j)⟫_𝕜 = ⟪(A.adjoint ∘ₗ A) (v i), v j⟫_𝕜 := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    have h2 : (A.adjoint ∘ₗ A) (v i)
        = ((hS.eigenvalues rfl (Fin.castLE hkE i) : ℝ) : 𝕜) • v i :=
      hS.apply_eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) (Fin.castLE hkE i)
    have h3 : (A.singularValues (i : ℕ) ^ 2 : ℝ)
        = hS.eigenvalues rfl (Fin.castLE hkE i) :=
      A.sq_singularValues_fin (rfl : finrank 𝕜 E = finrank 𝕜 E) (Fin.castLE hkE i)
    rw [h1, h2, inner_smul_left, RCLike.conj_ofReal, h3]
    rw [orthonormal_iff_ite.mp hv i j]
  -- norms of the images
  have hnorm : ∀ i : Fin k, ‖A (v i)‖ = A.singularValues (i : ℕ) := by
    intro i
    have h := hgram i i
    rw [ite_eq_left rfl, mul_one] at h
    have h2 : ‖A (v i)‖ ^ 2 = A.singularValues (i : ℕ) ^ 2 := by
      have := congrArg (RCLike.re (K := 𝕜)) h
      rw [inner_self_eq_norm_sq_to_K] at this
      simpa using this
    have := A.singularValues_nonneg (i : ℕ)
    nlinarith [norm_nonneg (A (v i))]
  -- the codomain family, defined on the indices with a nonzero singular value
  set w : Fin (finrank 𝕜 F) → F := fun j =>
    if h : (j : ℕ) < k then ((A.singularValues (j : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j, h⟩) else 0
    with hwdef
  set s : Set (Fin (finrank 𝕜 F)) :=
    {j | (j : ℕ) < k ∧ A.singularValues (j : ℕ) ≠ 0} with hsdef
  have hws : Orthonormal 𝕜 (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨j', hj'⟩
    obtain ⟨hjk, hjne⟩ := hj
    obtain ⟨hj'k, hj'ne⟩ := hj'
    have hwj : w j = ((A.singularValues (j : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j, hjk⟩) := by
      simp [hwdef, hjk]
    have hwj' : w j' = ((A.singularValues (j' : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j', hj'k⟩) := by
      simp [hwdef, hj'k]
    change ⟪w j, w j'⟫_𝕜 = _
    rw [hwj, hwj', inner_smul_left, inner_smul_right, hgram ⟨j, hjk⟩ ⟨j', hj'k⟩]
    have hj0 : ((A.singularValues (j : ℕ) : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hjne
    rcases eq_or_ne j j' with hjj | hjj
    · subst hjj
      simp only [map_inv₀, RCLike.conj_ofReal]
      push_cast
      field_simp
    · have h1 : (⟨(j : ℕ), hjk⟩ : Fin k) ≠ ⟨(j' : ℕ), hj'k⟩ := by
        simp only [ne_eq, Fin.mk.injEq]
        exact fun hh => hjj (Fin.ext hh)
      simp [h1, hjj, Subtype.ext_iff]
  obtain ⟨c, hc⟩ := hws.exists_orthonormalBasis_extension_of_card_eq
    (Fintype.card_fin _).symm
  set u : Fin k → F := fun i => c (Fin.castLE hkF i) with hudef
  have hu : Orthonormal 𝕜 u := c.orthonormal.comp _ (Fin.castLE_injective hkF)
  refine ⟨u, v, hu, hv, ?_⟩
  have hterm : ∀ i : Fin k, ⟪u i, A (v i)⟫_𝕜 = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) := by
    intro i
    by_cases hz : A.singularValues (i : ℕ) = 0
    · have hA0 : A (v i) = 0 := by
        have h := hnorm i
        rw [hz] at h
        exact norm_eq_zero.mp h
      rw [hA0, inner_zero_right, hz, RCLike.ofReal_zero]
    · have hlt : ((Fin.castLE hkF i : Fin (finrank 𝕜 F)) : ℕ) < k := i.isLt
      have hmem : (Fin.castLE hkF i) ∈ s := ⟨hlt, hz⟩
      have hwv : w (Fin.castLE hkF i) = ((A.singularValues (i : ℕ) : ℝ) : 𝕜)⁻¹ • A (v i) := by
        simp only [hwdef, dite_eq_left hlt]
        rfl
      have h0 : ((A.singularValues (i : ℕ) : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hz
      change ⟪c (Fin.castLE hkF i), A (v i)⟫_𝕜 = _
      rw [hc _ hmem, hwv, inner_smul_left, hgram i i]
      simp only [map_inv₀, RCLike.conj_ofReal]
      push_cast
      field_simp
  rw [Finset.sum_congr rfl fun (i : Fin k) (_ : i ∈ Finset.univ) => hterm i]
  rw [show (∑ i : Fin k, ((A.singularValues (i : ℕ) : ℝ) : 𝕜))
      = ((∑ i : Fin k, A.singularValues (i : ℕ) : ℝ) : 𝕜) by push_cast; rfl,
    RCLike.ofReal_re]
  rfl


end TauCeti
