/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.SpectralPositivity.Matrix.MetzlerExp
import LeanPool.SpectralPositivity.Matrix.PerronFrobenius
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Group.Pi.Units

/-!
# M-matrix Inverse Positivity (strict + non-strict)

For a non-singular M-matrix `M` (positive definite Z-matrix; equivalently
PD with non-positive off-diagonal entries), the inverse `M⁻¹` is
entrywise non-negative; on a "connected" lattice it is in fact strictly
positive.

This file provides both forms:
* `Matrix.MMatrix.inverse_nonneg` — `M⁻¹ ≥ 0` entrywise, no
  irreducibility required. Discharge: Laplace transform identity
  (`laplace_transform_inverse_real`) + `metzler_exp_nonneg` applied to
  `-M` (since `M` Z-matrix ⇒ `-M` Metzler) + `setIntegral_nonneg`.
* `Matrix.MMatrix.inverse_pos` — `M⁻¹ > 0` strictly, requiring the
  Metzler shift `Q := α • 1 - M` to be `Matrix.IsIrreducible`
  (connectedness of the off-diagonal pattern).

## References

* Berman & Plemmons, *Nonnegative Matrices in the Mathematical
  Sciences*, SIAM, 1994, Ch. 6, Thm 4.16 (Z-matrix inverse positivity).
* Horn & Johnson, *Topics in Matrix Analysis*, Cambridge, 1991, §2.5.
* Seneta, *Non-negative Matrices and Markov Chains*, Springer, 2006.

## Downstream consumers

* `markov-semigroups/Matrix/LaplaceTransform.lean` re-exports
  `inverse_nonneg` under the historical name `m_matrix_inverse_nonneg`
  (formerly an axiom there; now backed by this file). Used in turn by
  pphi2N's QHJ thimble proofs (`Pphi2N/QuantumHJ/ThimbleLocalGeneric.lean`
  etc.) for the diamagnetic / Combes-Thomas resolvent bound on the path
  to the 2D mass gap.
* `graphops-qft` consumes the strict version for resolvent positivity.
-/

noncomputable section

namespace SpectralPositivity

open Matrix BigOperators Finset MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Strict positivity of `exp(t·Q)` for irreducible non-negative `Q`.**

For an irreducible non-negative matrix `Q` (in this library's
`Matrix.IsIrreducible` sense: nonneg + per-pair `exists_pos_power`
+ positive self-loop) and `t > 0`, every entry of the matrix
exponential `exp(t·Q)` is strictly positive.

**Proof**: from `Q.IsIrreducible.exists_pos_power`, ∃ a single `k₀ > 0`
with `(Q^k₀)_{xy} > 0` for ALL pairs `(x, y)`. The matrix-exp series
`exp(t·Q) = ∑' k, (k!⁻¹) • (t·Q)^k` has the `k₀`-th term strictly
positive at every entry (since `(t • Q)^k₀ = t^k₀ • Q^k₀` via
`smul_pow`) and all other terms non-negative (`Q^k` nonneg by
`Matrix.Nonneg.pow`). Entry projection follows the
`Pi.evalAddMonoidHom` + `HasSum.map` pattern from
`MetzlerExp.nonneg_matrix_exp_nonneg`; conclusion via
`Summable.tsum_pos`. -/
theorem nonneg_irreducible_matrix_exp_pos
    [Nonempty n] {Q : Matrix n n ℝ} (hQ_irr : Matrix.IsIrreducible Q)
    {t : ℝ} (ht : 0 < t) (x y : n) :
    0 < (NormedSpace.exp (t • Q) : Matrix n n ℝ) x y := by
  obtain ⟨k₀, _hk₀_pos, hk₀_all⟩ := hQ_irr.exists_pos_power
  have hQ_nn : Q.Nonneg := hQ_irr.1
  -- Matrix-exp series HasSum.
  have hexp : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℚ) • (t • Q) ^ k)
      (NormedSpace.exp (t • Q) : Matrix n n ℝ) :=
    NormedSpace.exp_series_hasSum_exp' (t • Q)
  -- Project to entry (x, y) via two HasSum.map applications
  -- (mirrors the pattern in MetzlerExp.nonneg_matrix_exp_nonneg).
  have heval_x : Continuous (Pi.evalAddMonoidHom (fun _ : n => n → ℝ) x) :=
    continuous_apply x
  have heval_y : Continuous (Pi.evalAddMonoidHom (fun _ : n => ℝ) y) :=
    continuous_apply y
  have hxy_hasSum : HasSum
      (fun k => ((k.factorial⁻¹ : ℚ) • (t • Q) ^ k) x y)
      ((NormedSpace.exp (t • Q) : Matrix n n ℝ) x y) := by
    have h1 := hexp.map (Pi.evalAddMonoidHom (fun _ : n => n → ℝ) x) heval_x
    exact h1.map (Pi.evalAddMonoidHom (fun _ : n => ℝ) y) heval_y
  -- Each term is ≥ 0 at entry (x, y).
  have hterm_nn : ∀ k : ℕ, 0 ≤ ((k.factorial⁻¹ : ℚ) • (t • Q) ^ k) x y := by
    intro k
    rw [inv_natCast_smul_eq ℚ ℝ k.factorial ((t • Q) ^ k),
        Matrix.smul_apply, smul_eq_mul, smul_pow, Matrix.smul_apply, smul_eq_mul]
    refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
    exact mul_nonneg (pow_nonneg ht.le k) ((hQ_nn.pow k) x y)
  -- The k₀-th term is strictly positive at entry (x, y).
  have hterm_k0 : 0 < ((k₀.factorial⁻¹ : ℚ) • (t • Q) ^ k₀) x y := by
    rw [inv_natCast_smul_eq ℚ ℝ k₀.factorial ((t • Q) ^ k₀),
        Matrix.smul_apply, smul_eq_mul, smul_pow, Matrix.smul_apply, smul_eq_mul]
    refine mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _))) ?_
    exact mul_pos (pow_pos ht k₀) (hk₀_all x y)
  -- Conclude: tsum > 0 since one term is strictly positive and all are ≥ 0.
  rw [← hxy_hasSum.tsum_eq]
  exact hxy_hasSum.summable.tsum_pos hterm_nn k₀ hterm_k0

/-- **Strict positivity of `exp(-tM)` for an M-matrix with irreducible
Metzler shift.**

For `M : Matrix n n ℝ` and `α : ℝ`, if the Metzler shift
`Q := α • 1 - M` is irreducible, then for `t > 0` every entry of
`exp(-tM)` is strictly positive.

**Proof**: split `(-t) • M = -t·α • 1 + t • Q` (commutes since
scalar matrices commute with everything). By
`Matrix.exp_add_of_commute`,
`exp(-tM) = exp(-t·α • 1) * exp(t • Q) = Real.exp(-tα) • exp(t • Q)`.
Both factors are strictly positive: `Real.exp_pos` for the scalar,
`nonneg_irreducible_matrix_exp_pos` for the matrix. Mirrors the
structure of `MetzlerExp.metzler_exp_nonneg` (non-strict version). -/
theorem mmatrix_exp_neg_pos
    [Nonempty n] {M : Matrix n n ℝ} {α : ℝ}
    (hQ_irr : Matrix.IsIrreducible (α • (1 : Matrix n n ℝ) - M))
    {t : ℝ} (ht : 0 < t) (x y : n) :
    0 < (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y := by
  -- Step 1: (-t) • M = -(t * α) • 1 + t • Q where Q = α • 1 - M.
  set Q := α • (1 : Matrix n n ℝ) - M
  have hM_eq : (-t) • M = -(t * α) • (1 : Matrix n n ℝ) + t • Q := by
    change (-t) • M = -(t * α) • (1 : Matrix n n ℝ) + t • (α • (1 : Matrix n n ℝ) - M)
    ext i j
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul]
    split <;> ring
  rw [hM_eq]
  -- Step 2: -(t * α) • 1 commutes with t • Q.
  have hcomm : Commute (-(t * α) • (1 : Matrix n n ℝ)) (t • Q) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Algebra.commute_algebraMap_left (-(t * α)) (t • Q)
  -- Step 3: exp(-(tα) • 1 + t • Q) = exp(-(tα) • 1) * exp(t • Q).
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  -- Step 4: exp(-(tα) • 1) = Real.exp(-(tα)) • 1.
  have hscalar : NormedSpace.exp (-(t * α) • (1 : Matrix n n ℝ)) =
      NormedSpace.exp (-(t * α)) • (1 : Matrix n n ℝ) := by
    rw [← Algebra.algebraMap_eq_smul_one (-(t * α)),
        ← Algebra.algebraMap_eq_smul_one (NormedSpace.exp (-(t * α)))]
    exact (NormedSpace.algebraMap_exp_comm (-(t * α))).symm
  rw [hscalar]
  -- Step 5: (Real.exp(-(tα)) • 1) * exp(t • Q) = Real.exp(-(tα)) • exp(t • Q).
  rw [Algebra.smul_mul_assoc, one_mul]
  -- Step 6: positivity. Both factors strictly positive.
  have hexp_scalar_pos : 0 < (NormedSpace.exp (-(t * α)) : ℝ) := by
    rw [← Real.exp_eq_exp_ℝ]
    exact Real.exp_pos _
  have hexp_Q_pos : 0 < (NormedSpace.exp (t • Q) : Matrix n n ℝ) x y :=
    nonneg_irreducible_matrix_exp_pos hQ_irr ht x y
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_pos hexp_scalar_pos hexp_Q_pos

/-! ## Step 5: Laplace transform identity for `M⁻¹`. -/

private lemma mul_diagonal_star_entry_lt (A B : Matrix n n ℝ) (d : n → ℝ) (x y : n) :
    (A * Matrix.diagonal d * star B) x y = ∑ k, A x k * d k * B y k := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
        Finset.sum_ite_eq', Finset.mem_univ, star_trivial]

private lemma integral_exp_neg_pos_lt (lam : ℝ) (hlam : 0 < lam) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) = lam⁻¹ := by
  have h1 := integral_exp_mul_Ioi (show -lam < 0 from by linarith) 0
  simp only [mul_zero, Real.exp_zero] at h1
  rw [h1]; field_simp

/-- **Laplace transform identity for the inverse of a PD matrix.**

For a positive-definite real matrix `M`,
`M⁻¹ x y = ∫_(0,∞) (exp(-tM))_xy dt` for every entry `(x, y)`.

Proof via spectral decomposition `M = U · diag(λ) · Uᵀ`: both sides
reduce to `∑ k, U(x,k) · (1/λ_k) · U(y,k)` using
`∫_(0,∞) exp(-λt) dt = 1/λ` for `λ > 0`. (Horn-Johnson §6.2;
Higham, *Functions of Matrices*, Thm 10.2.) -/
theorem laplace_transform_inverse_real
    (M : Matrix n n ℝ) (hM : M.PosDef) (x y : n) :
    M⁻¹ x y = ∫ t in Set.Ioi (0 : ℝ), (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y := by
  set hH := hM.isHermitian
  set U := hH.eigenvectorUnitary.val
  set ev := hH.eigenvalues
  have hev_pos : ∀ i, 0 < ev i := hM.eigenvalues_pos
  have hspec : M = U * Matrix.diagonal ev * star U := by
    have := hH.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id] at this
    exact this
  have hU_unit : IsUnit U :=
    ⟨⟨U, star U, hH.eigenvectorUnitary.prop.2, hH.eigenvectorUnitary.prop.1⟩, rfl⟩
  have hU_inv : U⁻¹ = star U := inv_eq_left_inv hH.eigenvectorUnitary.prop.1
  have hstarU_inv : (star U)⁻¹ = U := inv_eq_left_inv hH.eigenvectorUnitary.prop.2
  set f : n → ℝ → ℝ := fun k t => U x k * Real.exp (-t * ev k) * U y k
  have exp_sum : ∀ t : ℝ, (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y = ∑ k, f k t := by
    intro t; rw [hspec]
    conv_lhs => rw [show (-t) • (U * Matrix.diagonal ev * star U) =
      U * ((-t) • Matrix.diagonal ev) * star U from by simp]
    rw [show U * ((-t) • Matrix.diagonal ev) * star U =
      U * ((-t) • Matrix.diagonal ev) * U⁻¹ from by rw [hU_inv]]
    rw [Matrix.exp_conj U _ hU_unit, hU_inv, ← Matrix.diagonal_smul, Matrix.exp_diagonal,
        mul_diagonal_star_entry_lt]
    congr 1; ext k; congr 1; congr 1
    rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]; simp [Pi.smul_apply, smul_eq_mul]
  have hint : ∀ k ∈ Finset.univ,
      Integrable (f k) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro k _
    change MeasureTheory.IntegrableOn (f k) (Set.Ioi 0)
    have : f k = fun t => (U x k * U y k) * Real.exp (-(ev k) * t) := by
      ext t; simp [f]; ring_nf
    rw [this]
    exact (integrableOn_exp_mul_Ioi (by linarith [hev_pos k]) 0).const_mul _
  have hint_eval : ∀ k, ∫ t in Set.Ioi (0 : ℝ), f k t =
      U x k * (ev k)⁻¹ * U y k := by
    intro k
    have h : ∀ t, f k t = (U x k * U y k) * Real.exp (-(ev k) * t) := by
      intro t; simp [f]; ring_nf
    simp_rw [h]
    rw [integral_const_mul, integral_exp_neg_pos_lt (ev k) (hev_pos k)]; ring
  have rhs_eq : (∫ t in Set.Ioi (0 : ℝ), (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y) =
      ∑ k, U x k * (ev k)⁻¹ * U y k := by
    simp_rw [exp_sum]
    rw [integral_finsetSum Finset.univ hint]
    congr 1; ext k; exact hint_eval k
  have lhs_eq : M⁻¹ x y = ∑ k, U x k * (ev k)⁻¹ * U y k := by
    rw [hspec, mul_inv_rev (U * Matrix.diagonal ev) (star U), mul_inv_rev U (Matrix.diagonal ev)]
    rw [hU_inv, hstarU_inv, ← mul_assoc, Matrix.inv_diagonal,
        mul_diagonal_star_entry_lt]
    congr 1; ext k; congr 1; congr 1
    have hunit : IsUnit ev :=
      Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (ne_of_gt (hev_pos i)))
    conv_lhs => rw [← IsUnit.unit_spec hunit]
    rw [Ring.inverse_unit, Units.val_inv_eq_inv_val, Pi.inv_apply, IsUnit.unit_spec]
  rw [lhs_eq, rhs_eq]

/-- Integrability of the heat-kernel entry on `Set.Ioi 0` for a PD
matrix. Each entry is a finite sum of integrable scalar exponentials
(spectral decomposition). -/
private theorem heat_kernel_entry_integrableOn (M : Matrix n n ℝ)
    (hM : M.PosDef) (x y : n) :
    IntegrableOn
      (fun t : ℝ => (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y)
      (Set.Ioi (0 : ℝ)) := by
  set hH := hM.isHermitian
  set U := hH.eigenvectorUnitary.val
  set ev := hH.eigenvalues
  have hev_pos : ∀ i, 0 < ev i := hM.eigenvalues_pos
  have hspec : M = U * Matrix.diagonal ev * star U := by
    have := hH.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id] at this
    exact this
  have hU_unit : IsUnit U :=
    ⟨⟨U, star U, hH.eigenvectorUnitary.prop.2, hH.eigenvectorUnitary.prop.1⟩, rfl⟩
  have hU_inv : U⁻¹ = star U := inv_eq_left_inv hH.eigenvectorUnitary.prop.1
  set f : n → ℝ → ℝ := fun k t => U x k * Real.exp (-t * ev k) * U y k
  have exp_sum : ∀ t : ℝ, (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y = ∑ k, f k t := by
    intro t; rw [hspec]
    conv_lhs => rw [show (-t) • (U * Matrix.diagonal ev * star U) =
      U * ((-t) • Matrix.diagonal ev) * star U from by simp]
    rw [show U * ((-t) • Matrix.diagonal ev) * star U =
      U * ((-t) • Matrix.diagonal ev) * U⁻¹ from by rw [hU_inv]]
    rw [Matrix.exp_conj U _ hU_unit, hU_inv, ← Matrix.diagonal_smul, Matrix.exp_diagonal,
        mul_diagonal_star_entry_lt]
    congr 1; ext k; congr 1; congr 1
    rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]; simp [Pi.smul_apply, smul_eq_mul]
  -- Each f k is integrable.
  have hf_int : ∀ k, IntegrableOn (f k) (Set.Ioi (0 : ℝ)) := by
    intro k
    have : f k = fun t => (U x k * U y k) * Real.exp (-(ev k) * t) := by
      ext t; simp [f]; ring_nf
    rw [this]
    exact (integrableOn_exp_mul_Ioi (by linarith [hev_pos k]) 0).const_mul _
  -- The sum-form is integrable as a finite sum of integrables.
  have hsum_int : IntegrableOn (fun t => ∑ k, f k t) (Set.Ioi (0 : ℝ)) :=
    integrable_finsetSum _ (fun k _ => hf_int k)
  -- Transport via exp_sum.
  have heq : (fun t : ℝ => (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y) =
      fun t => ∑ k, f k t := funext exp_sum
  rw [heq]; exact hsum_int

/-- **Strict entrywise positivity of an M-matrix inverse**
(Berman-Plemmons Thm 4.16; Horn-Johnson §2.5).

The full discharge using:
* `laplace_transform_inverse_real` (Step 5: spectral decomposition)
* `mmatrix_exp_neg_pos` (Step 4: heat-kernel strict positivity)
* `setIntegral_pos_iff_support_of_nonneg_ae` (Mathlib: integral
  positivity from positive integrand on positive-measure support).

Only the `α : ℝ` parameter and `hα` are vestigial in this final form
(carried for API stability with the original axiom shape). -/
theorem Matrix.MMatrix.inverse_pos
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (M : Matrix n n ℝ) (hM_pd : M.PosDef)
    (_hM_off : ∀ i j, i ≠ j → M i j ≤ 0)
    {α : ℝ} (_hα : ∀ i, M i i ≤ α)
    (hQ_irr : Matrix.IsIrreducible (α • (1 : Matrix n n ℝ) - M))
    (x y : n) :
    0 < M⁻¹ x y := by
  -- Step A: convert to the integral via the Laplace transform.
  rw [laplace_transform_inverse_real M hM_pd x y]
  set f : ℝ → ℝ := fun t => (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y
  -- Step B: integrand is strictly positive on Set.Ioi 0.
  have hf_pos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t := fun t ht =>
    mmatrix_exp_neg_pos hQ_irr ht x y
  -- Step C: integrand is nonneg ae on Set.Ioi 0.
  have hf_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Filter.Eventually.of_forall fun t ht => le_of_lt (hf_pos t ht)
  -- Step D: integrand is integrable on Set.Ioi 0.
  have hf_int : IntegrableOn f (Set.Ioi (0 : ℝ)) :=
    heat_kernel_entry_integrableOn M hM_pd x y
  -- Step E: support of f intersected with Ioi 0 has positive measure.
  -- Since f t > 0 for all t ∈ Ioi 0, support f ⊇ Ioi 0, so the intersection is Ioi 0,
  -- which has infinite (hence positive) Lebesgue measure.
  have hsupp_pos : 0 < volume (Function.support f ∩ Set.Ioi (0 : ℝ)) := by
    have h_sub : Set.Ioi (0 : ℝ) ⊆ Function.support f ∩ Set.Ioi 0 := by
      intro t ht
      refine ⟨?_, ht⟩
      exact ne_of_gt (hf_pos t ht)
    have h1 : volume (Set.Ioi (0 : ℝ)) ≤ volume (Function.support f ∩ Set.Ioi 0) :=
      measure_mono h_sub
    have h2 : volume (Set.Ioi (0 : ℝ)) = ⊤ := by simp
    rw [h2] at h1
    exact lt_of_lt_of_le ENNReal.zero_lt_top h1
  -- Step F: combine.
  exact (setIntegral_pos_iff_support_of_nonneg_ae hf_nn hf_int).mpr hsupp_pos

/-- **Heat-kernel entrywise nonnegativity for a Z-matrix.**

For `M` with non-positive off-diagonal entries and `t ≥ 0`,
`exp((-t) • M) ≥ 0` entrywise. No irreducibility, no positive
definiteness — just the sign condition on the off-diagonal.

**Proof**: `(-t) • M = t • (-M)`, and `-M` has nonneg off-diagonal,
so `metzler_exp_nonneg` (in `MetzlerExp.lean`) applies. -/
private theorem mmatrix_exp_neg_nonneg
    {M : Matrix n n ℝ} (hM_off : ∀ i j, i ≠ j → M i j ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) (x y : n) :
    0 ≤ (NormedSpace.exp ((-t) • M) : Matrix n n ℝ) x y := by
  have h_eq : (-t) • M = t • (-M) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, neg_mul, mul_neg]
  rw [h_eq]
  have hL : (-M).NonnegOffDiag := fun i j hij => by
    show 0 ≤ (-M) i j
    rw [Matrix.neg_apply]
    linarith [hM_off i j hij]
  exact metzler_exp_nonneg hL ht x y

/-- **Entrywise non-negativity of an M-matrix inverse**
(Berman-Plemmons Thm 4.16; Horn-Johnson §2.5).

For a real PD matrix `M` whose off-diagonal entries are non-positive
(equivalently, a non-singular M-matrix), the inverse `M⁻¹` is
entrywise non-negative.

This is the non-strict version of `Matrix.MMatrix.inverse_pos`; it
drops the irreducibility hypothesis. The proof uses
`laplace_transform_inverse_real` (`M⁻¹ = ∫_(0,∞) exp(-tM) dt`) plus
the heat-kernel entrywise non-negativity `mmatrix_exp_neg_nonneg`,
combined with `setIntegral_nonneg`.

Used by markov-semigroups for the diamagnetic-inequality chain (the
`m_matrix_inverse_nonneg` axiom there is replaced by this theorem). -/
theorem Matrix.MMatrix.inverse_nonneg
    (M : Matrix n n ℝ) (hM_pd : M.PosDef)
    (hM_off : ∀ i j, i ≠ j → M i j ≤ 0)
    (x y : n) :
    0 ≤ M⁻¹ x y := by
  rw [laplace_transform_inverse_real M hM_pd x y]
  refine setIntegral_nonneg measurableSet_Ioi ?_
  intro t ht
  exact mmatrix_exp_neg_nonneg hM_off (le_of_lt ht) x y

end SpectralPositivity

end
