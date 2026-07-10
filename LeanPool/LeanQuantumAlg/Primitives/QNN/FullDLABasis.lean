/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Primitives.QNN.VarianceFormula
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The full algebra `gl(2ⁿ)` as a dynamical Lie algebra: an exponential barren plateau

This module constructs the explicit **Hermitian Hilbert–Schmidt orthonormal basis** of
the full matrix algebra `gl(N, ℂ)` (the Hermitized matrix units: diagonal `Eₖₖ`,
symmetric `(Eᵢⱼ+Eⱼᵢ)/√2`, antisymmetric `i(Eᵢⱼ−Eⱼᵢ)/√2`). For `N = 2ⁿ`
this is a `DLAHermBasis` of the fully controllable circuit (dynamical Lie
algebra `= gl(2ⁿ)`, dimension `4ⁿ`), which — fed into `ragone_hasBarrenPlateau`
— exhibits a concrete
family with an **exponentially vanishing** loss variance: a genuine barren plateau,
witnessing that the capstone is not vacuous on the canonical physical case.
-/

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QuantumAlg

open Matrix

variable {N : ℕ}

/-- The real constant `1/√2`, as a complex scalar (the off-diagonal normalization). -/
noncomputable def rt2inv : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem rt2inv_mul_self : rt2inv * rt2inv = 1 / 2 := by
  rw [rt2inv, ← Complex.ofReal_mul]
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem rt2inv_conj : star rt2inv = rt2inv := by
  rw [rt2inv]; exact Complex.conj_ofReal _

/-- The **Hermitized matrix units**: a complete Hermitian basis of `gl(N, ℂ)`, indexed
by `Fin N × Fin N` (diagonal / symmetric-off-diagonal / antisymmetric-off-diagonal). -/
noncomputable def hermUnit (p : Fin N × Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  if p.1 = p.2 then single p.1 p.1 1
  else if p.1 < p.2 then rt2inv • (single p.1 p.2 1 + single p.2 p.1 1)
  else rt2inv • (Complex.I • (single p.1 p.2 1 - single p.2 p.1 1))

/-- Every Hermitized matrix unit is Hermitian. -/
theorem hermUnit_isHermitian (p : Fin N × Fin N) : (hermUnit p)ᴴ = hermUnit p := by
  unfold hermUnit
  split_ifs with h1 h2
  · simp [conjTranspose_single]
  · simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_single, star_one, rt2inv_conj]
    rw [add_comm]
  · have hI : star Complex.I = -Complex.I := by rw [← starRingEnd_apply]; exact Complex.conj_I
    simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_single, star_one, rt2inv_conj,
      hI, smul_sub, neg_smul, smul_neg]
    abel

theorem hermUnit_diag (i : Fin N) : hermUnit ((i, i) : Fin N × Fin N) = single i i 1 := by
  simp [hermUnit]

theorem hermUnit_lt {i j : Fin N} (h : i < j) :
    hermUnit ((i, j) : Fin N × Fin N) = rt2inv • (single i j 1 + single j i 1) := by
  simp [hermUnit, h.ne, h]

theorem hermUnit_gt {i j : Fin N} (h : j < i) :
    hermUnit ((i, j) : Fin N × Fin N)
      = rt2inv • (Complex.I • (single i j 1 - single j i 1)) := by
  simp [hermUnit, h.ne', not_lt.mpr h.le]

theorem rt2inv_sq : rt2inv ^ 2 = 1 / 2 := by rw [sq, rt2inv_mul_self]

theorem star_I_eq : star Complex.I = -Complex.I := by
  rw [← starRingEnd_apply]
  exact Complex.conj_I

/-- Shared finisher for the orthonormality Gram-matrix computation: expand the
Hilbert–Schmidt inner product, then resolve the index `if`s (impossible ones by `omega`)
and the `√2`/`i` arithmetic. -/
local macro "hsFinish" : tactic =>
  `(tactic|
      (simp only [hsInner_smul_left, hsInner_smul_right, hsInner_add_left, hsInner_add_right,
          hsInner_sub_left, hsInner_sub_right, hsInner_single, starRingEnd_apply, rt2inv_conj,
          star_I_eq]
       all_goals
         (split_ifs <;> (try (exfalso; omega)) <;> (try ring) <;>
           (try (rw [rt2inv_sq]; norm_num)) <;>
           (try (rw [rt2inv_sq, Complex.I_sq]; norm_num)))))

/-- The Hermitized matrix units form a Hilbert–Schmidt orthonormal family. -/
theorem hermUnit_orthonormal (p q : Fin N × Fin N) :
    hsInner (hermUnit p) (hermUnit q) = if p = q then 1 else 0 := by
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [Prod.mk.injEq]
  rcases lt_trichotomy i j with hij | hij | hij
  · rcases lt_trichotomy k l with hkl | hkl | hkl
    · rw [hermUnit_lt hij, hermUnit_lt hkl]; hsFinish
    · subst hkl; rw [hermUnit_lt hij, hermUnit_diag]; hsFinish
    · rw [hermUnit_lt hij, hermUnit_gt hkl]; hsFinish
  · rcases lt_trichotomy k l with hkl | hkl | hkl
    · subst hij; rw [hermUnit_diag, hermUnit_lt hkl]; hsFinish
    · subst hij; subst hkl; rw [hermUnit_diag, hermUnit_diag]; hsFinish
    · subst hij; rw [hermUnit_diag, hermUnit_gt hkl]; hsFinish
  · rcases lt_trichotomy k l with hkl | hkl | hkl
    · rw [hermUnit_gt hij, hermUnit_lt hkl]; hsFinish
    · subst hkl; rw [hermUnit_gt hij, hermUnit_diag]; hsFinish
    · rw [hermUnit_gt hij, hermUnit_gt hkl]; hsFinish

/-- The Hermitized matrix units are linearly independent. -/
theorem hermUnit_linearIndependent :
    LinearIndependent ℂ (hermUnit : Fin N × Fin N → Matrix (Fin N) (Fin N) ℂ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have h1 : hsInner (hermUnit p) (∑ q, c q • hermUnit q) = c p := by
    rw [hsInner_sum_right]
    have hterm : ∀ q, hsInner (hermUnit p) (c q • hermUnit q) = if p = q then c q else 0 := by
      intro q; rw [hsInner_smul_right, hermUnit_orthonormal]; split <;> simp
    rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_ite_eq]
    simp
  rw [hc] at h1
  simpa [hsInner] using h1.symm

/-- The Hermitized matrix units span all of `gl(N, ℂ)`. -/
theorem hermUnit_span_top :
    Submodule.span ℂ
      (Set.range (hermUnit : Fin N × Fin N → Matrix (Fin N) (Fin N) ℂ)) = ⊤ := by
  apply hermUnit_linearIndependent.span_eq_top_of_card_eq_finrank'
  rw [Fintype.card_prod, Fintype.card_fin, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self]
  ring

/-- **The full algebra `gl(N, ℂ)` as a `DLAHermBasis`** — the dynamical Lie algebra of a
fully controllable circuit (generators span everything), with the Hermitized matrix
units as its Hermitian orthonormal basis. Its dimension is `N²`. -/
noncomputable def fullHermBasis (N : ℕ) :
    DLAHermBasis (Set.univ : Set (Matrix (Fin N) (Fin N) ℂ)) where
  dim := N * N
  B := fun a => hermUnit (finProdFinEquiv.symm a)
  herm := fun a => hermUnit_isHermitian _
  ortho := fun a b => by
    simp only [hermUnit_orthonormal, EmbeddingLike.apply_eq_iff_eq]
  span_eq := by
    rw [show (Set.range fun a => hermUnit (finProdFinEquiv.symm a))
          = Set.range (hermUnit : Fin N × Fin N → _) from
        finProdFinEquiv.symm.surjective.range_comp hermUnit, hermUnit_span_top,
      dynamicalLieAlgebra_eq_top_of_span_top (by rw [Submodule.span_univ]),
      LieSubalgebra.top_toSubmodule]

/-- The Ragone second-moment bundle for the fully controllable `n`-qubit family, with
observable and state both equal to the first (Hermitian, normalized) basis element. -/
noncomputable def fullCtrlSM (n : ℕ) :
    RagoneSecondMoment (fullHermBasis (2 ^ n))
      ((fullHermBasis (2 ^ n)).B ⟨0, by change 0 < 2 ^ n * 2 ^ n; positivity⟩)
      ((fullHermBasis (2 ^ n)).B ⟨0, by change 0 < 2 ^ n * 2 ^ n; positivity⟩) :=
  RagoneSecondMoment.ofHermitian ((fullHermBasis (2 ^ n)).herm _)
    ((fullHermBasis (2 ^ n)).herm _) (by change 0 < 2 ^ n * 2 ^ n; positivity)

/-- **Concrete exponential barren plateau (full controllability).** The qubit-indexed
family of fully controllable circuits — dynamical Lie algebra `gl(2ⁿ)`, dimension `4ⁿ` —
has an exponentially vanishing loss variance: a genuine barren plateau. This instantiates
`ragone_hasBarrenPlateau` on the canonical physical case, witnessing it is not vacuous. -/
theorem fullControllability_hasBarrenPlateau :
    HasBarrenPlateau (fun n => (fullCtrlSM n).variance) := by
  apply ragone_hasBarrenPlateau (M := fullCtrlSM)
    (hρ := fun n => (fullHermBasis (2 ^ n)).herm _)
    (hdimpos := fun n => by change 0 < 2 ^ n * 2 ^ n; positivity)
    (C := 1) (hC := zero_le_one) (base := 2) (hbase := one_lt_two)
  · intro n
    rw [DLAHermBasis.gPurity_basis_elem]; norm_num
  · intro n
    have hdimeq : ((fullHermBasis (2 ^ n)).dim : ℝ) = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
      change ((2 ^ n * 2 ^ n : ℕ) : ℝ) = _
      push_cast
      ring
    rw [hdimeq]
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n),
      pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n]

end QuantumAlg
