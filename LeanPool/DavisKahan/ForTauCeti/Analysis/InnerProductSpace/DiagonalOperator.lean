/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan

/-!
# Real diagonal operators and the operator singular-value decomposition

This module contains no norm structure. It supplies the diagonal operators used by
both rectangular orbit majorization and square symmetric-gauge representation.
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open _root_.LinearMap
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {n : ℕ}

/-! ### The diagonal operator of a real vector in an orthonormal basis -/

/-- The operator with (real) diagonal `x` in the orthonormal basis `b`:
`diagOp b x (b i) = x i • b i`. -/
noncomputable def diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    E →ₗ[𝕜] E :=
  ∑ i, ((x i : ℝ) : 𝕜) • (InnerProductSpace.rankOne 𝕜 (b i) (b i)).toLinearMap

omit [FiniteDimensional 𝕜 E] in
/-- The defining formula: `diagOp b x` expands `v` in the basis and scales the `i`-th coefficient
by `x i`. -/
@[simp]
theorem diagOp_apply (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) (v : E) :
    diagOp b x v = ∑ i, ((x i : ℝ) : 𝕜) • ⟪b i, v⟫_𝕜 • b i := by
  unfold diagOp
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    simp [InnerProductSpace.rankOne_apply]

omit [FiniteDimensional 𝕜 E] in
/-- A diagonal operator scales each basis vector by its own entry.  This is the form used to
compare two diagonal operators, since equality on a basis suffices. -/
theorem diagOp_apply_basis (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (j : Fin n) : diagOp b x (b j) = ((x j : ℝ) : 𝕜) • b j := by
  rw [diagOp_apply]
  have hterm : ∀ i ∈ Finset.univ, ((x i : ℝ) : 𝕜) • ⟪b i, b j⟫_𝕜 • b i
      = if i = j then ((x i : ℝ) : 𝕜) • b i else 0 := fun i _ => by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [orthonormal_iff_ite.mp b.orthonormal i j, hij]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' Finset.univ j fun i => ((x i : ℝ) : 𝕜) • b i]
  simp

omit [FiniteDimensional 𝕜 E] in
/-- `diagOp b` is additive in the diagonal. -/
theorem diagOp_add (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    diagOp b (x + y) = diagOp b x + diagOp b y := by
  unfold diagOp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, RCLike.ofReal_add, add_smul]

omit [FiniteDimensional 𝕜 E] in
/-- `diagOp b` is homogeneous in the diagonal, with the real scalar cast into `𝕜`. -/
theorem diagOp_real_smul (b : OrthonormalBasis (Fin n) 𝕜 E) (c : ℝ)
    (x : Fin n → ℝ) : diagOp b (c • x) = ((c : ℝ) : 𝕜) • diagOp b x := by
  unfold diagOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul, smul_smul]

omit [FiniteDimensional 𝕜 E] in
/-- A constant real diagonal is a scalar multiple of the identity.  This is
the bridge between the functional-calculus form `r • id` and the diagonal
form the singular-value lemmas are stated in. -/
theorem diagOp_const (b : OrthonormalBasis (Fin n) 𝕜 E) (r : ℝ) :
    diagOp b (fun _ => r) = (((r : ℝ) : 𝕜) • LinearMap.id) := by
  refine b.toBasis.ext fun j => ?_
  rw [OrthonormalBasis.coe_toBasis, diagOp_apply_basis]
  simp

omit [FiniteDimensional 𝕜 E] in
/-- The two-entry constant diagonal, in the `![r, r]` shape the planar
singular-value lemmas use. -/
theorem diagOp_const_pair (b : OrthonormalBasis (Fin 2) 𝕜 E) (r : ℝ) :
    diagOp b ![r, r] = (((r : ℝ) : 𝕜) • LinearMap.id) := by
  refine b.toBasis.ext fun j => ?_
  rw [OrthonormalBasis.coe_toBasis, diagOp_apply_basis]
  fin_cases j <;> simp

omit [FiniteDimensional 𝕜 E] in
/-- A real diagonal operator is symmetric. -/
theorem isSymmetric_diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    (diagOp b x).IsSymmetric := by
  intro u v
  rw [diagOp_apply, diagOp_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    inner_conj_symm]
  ring

/-- A real diagonal operator is self-adjoint.  This is why a unitarily invariant norm applied to
`diagOp` yields a *symmetric* gauge on vectors. -/
theorem adjoint_diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    (diagOp b x).adjoint = diagOp b x :=
  (isSymmetric_diagOp b x).adjoint_eq

omit [FiniteDimensional 𝕜 E] in
/-- Diagonal operators in the same basis multiply diagonally. -/
theorem diagOp_comp (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    diagOp b x ∘ₗ diagOp b y = diagOp b (x * y) := by
  refine b.toBasis.ext fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, diagOp_apply_basis,
    map_smul, smul_smul, Pi.mul_apply, RCLike.ofReal_mul, mul_comm]

/-- The singular values of a diagonal operator with *antitone nonnegative*
diagonal are the diagonal itself. -/
theorem singularValues_diagOp (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {x : Fin n → ℝ}
    (hx_anti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) (i : Fin n) :
    (diagOp b x).singularValues (i : ℕ) = x i := by
  have hgram : (diagOp b x).adjoint ∘ₗ diagOp b x = diagOp b (x * x) := by
    rw [adjoint_diagOp, diagOp_comp]
  have hsq_anti : Antitone fun i => x i ^ 2 := fun i j hij =>
    pow_le_pow_left₀ (hx0 j) (hx_anti hij) 2
  have heig : (diagOp b x).isSymmetric_adjoint_comp_self.eigenvalues hn
      = fun i => x i ^ 2 :=
    (eigenvalues_congr hgram (diagOp b x).isSymmetric_adjoint_comp_self
      (isSymmetric_diagOp b (x * x)) hn).trans
      (LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis _ hn b hsq_anti fun i => by
        rw [diagOp_apply_basis]
        congr 1
        rw [Pi.mul_apply]
        push_cast
        ring)
  rw [(diagOp b x).singularValues_fin hn i, congrFun heig i,
    Real.sqrt_sq (hx0 i)]

/-! ### The operator SVD factorization -/

/-- **Operator SVD**: relative to *any* fixed orthonormal basis `b`, every
square operator factors as `A = U ∘ diag(σ(A)) ∘ V` with `U, V` unitary. -/
theorem exists_unitary_diagOp_factorization (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (A : E →ₗ[𝕜] E) :
    ∃ U V : E ≃ₗᵢ[𝕜] E,
      A = U.toLinearMap ∘ₗ diagOp b (fun i => A.singularValues (i : ℕ))
        ∘ₗ V.toLinearMap := by
  subst hn
  set w := A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hw
  set K := b.equiv w (Equiv.refl _) with hK
  have hKb : ∀ i, K (b i) = w i := fun i => by
    rw [hK, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
  have hKsymm : ∀ i, K.symm (w i) = b i := fun i => by
    rw [← hKb i, LinearIsometryEquiv.symm_apply_apply]
  have habs_w : ∀ i, operatorAbs A (w i)
      = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) • w i := by
    intro i
    rw [show operatorAbs A = (LinearMap.isPositive_adjoint_comp_self A).sqrt from rfl,
      (LinearMap.isPositive_adjoint_comp_self A).sqrt_apply_eigenvectorBasis i,
      ← A.singularValues_fin rfl i]
  have habs : operatorAbs A
      = K.toLinearMap ∘ₗ diagOp b (fun i => A.singularValues (i : ℕ))
        ∘ₗ K.symm.toLinearMap := by
    refine w.toBasis.ext fun i => ?_
    change operatorAbs A (w i) =
      K (diagOp b (fun i => A.singularValues (i : ℕ)) (K.symm (w i)))
    simp only [habs_w i, hKsymm i, diagOp_apply_basis, map_smul, hKb i]
  refine ⟨K.trans (choosePolarUnitary A), K.symm, ?_⟩
  ext v
  have hpolar := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary A) v
  change A v = choosePolarUnitary A (operatorAbs A v) at hpolar
  have habsv := LinearMap.congr_fun habs v
  change operatorAbs A v =
    K (diagOp b (fun i => A.singularValues (i : ℕ)) (K.symm v)) at habsv
  change A v = (K.trans (choosePolarUnitary A))
    (diagOp b (fun i => A.singularValues (i : ℕ)) (K.symm v))
  rw [hpolar, habsv, LinearIsometryEquiv.trans_apply]


end TauCeti
