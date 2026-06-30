/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Gate
public import LeanPool.LeanQuantumAlg.Primitives.QNN.DynamicalLieAlgebra
public import LeanPool.LeanQuantumAlg.Primitives.QNN.Trainability
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.DirectSum.Module

/-!
# Lie-algebraic barren plateaus from the *real* dynamical Lie algebra

The standard logic of a Lie-algebraic barren-plateau analysis is:

> circuit generators  ⟹  dynamical Lie algebra `g`  ⟹  decomposition into
> components `g = ⊕ₖ gₖ`  ⟹  the dimension `dim g`  ⟹  (with the variance law
> `Var ∼ 1 / dim g`)  the *scaling* of the variance: exponential or polynomial in
> the number of qubits.

The earlier `LieAlgebraicVariance` model (in `LeanPool.LeanQuantumAlg.Primitives.Trainability`)
bundled `dim g` as an opaque `ℕ → ℝ`. This module replaces it by the **genuine**
dimension `Module.finrank ℂ g` of the *formalized* `dynamicalLieAlgebra`, and proves:

* **`dlaDim`** — the real dimension of the dynamical Lie algebra.
* **`hasBarrenPlateau_of_exp_dlaDim`** — if the real `dim g` grows exponentially in
  the qubit count then the (Ragone) variance law forces a barren plateau. The
  variance *value* `numer / dim g` (which needs Haar / Weingarten averaging) is the
  only assumed input; the dimension is real.
* **`finrank_eq_sum_of_isInternal` / `dlaDim_eq_sum_of_isInternal`** — the
  *decomposition* step: if `g` is an internal direct sum of subspaces `gₖ` then
  `dim g = ∑ₖ dim gₖ`.
* Two end-to-end **worked examples** computing the real `dim g` and deriving the
  scaling:
  - `dlaDim_univ` + `barrenPlateau_of_full_dla` — the maximal (fully controllable)
    algebra `g = gl(2ⁿ)` has `dim g = 4ⁿ` (exponential) ⟹ barren plateau;
  - `dlaDim_singleton` + `not_barrenPlateau_of_dlaDim_const` — a single-generator
    (commuting) circuit has `dim g = 1` (constant) ⟹ *no* barren plateau (trainable).

The first-principles derivation of the variance law itself (Ragone et al. 2023,
Eq. (10), via Weingarten calculus / `t`-designs) remains a Mathlib gap and is left as
an assumed hypothesis throughout; see `LeanPool.LeanQuantumAlg.Primitives.Trainability`.

Source: Ragone, Bakalov, Sauvage, Kemper, Ortiz Marrero, Larocca, Cerezo (2023),
*A Lie algebraic theory of barren plateaus* (arXiv:2309.09342).
-/

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QuantumAlg

open Filter Module
open scoped DirectSum

noncomputable section

variable {N : ℕ}

/-! ### The real dimension of the dynamical Lie algebra -/

/-- The **dimension of the dynamical Lie algebra** of a generator set: the `ℂ`-finrank
of the formalized `dynamicalLieAlgebra` (a subspace of `gl(N, ℂ)`). This is the genuine
`dim g` of the Lie-algebraic variance law, not an opaque parameter. -/
def dlaDim (gens : Set (Matrix (Fin N) (Fin N) ℂ)) : ℕ :=
  Module.finrank ℂ (dynamicalLieAlgebra gens).toSubmodule

/-! ### Tier 1 — barren plateau from exponential growth of the *real* dimension -/

/-- **Lie-algebraic barren plateau (real dimension).** Given the Ragone variance law
`variance n = numer / dim g_n` (the numerator, requiring Haar/Weingarten averaging, is
the assumed input), if the **real** dynamical-Lie-algebra dimension grows at least like
`bⁿ` for some `b > 1`, then the loss has a barren plateau. -/
theorem hasBarrenPlateau_of_exp_dlaDim
    {sz : ℕ → ℕ} {gens : (n : ℕ) → Set (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)}
    {variance : ℕ → ℝ} {numer : ℝ} (hnum : 0 ≤ numer)
    (hvar : ∀ n, variance n = numer / (dlaDim (gens n) : ℝ))
    {b : ℝ} (hb : 1 < b) (hdim : ∀ n, b ^ n ≤ (dlaDim (gens n) : ℝ)) :
    HasBarrenPlateau variance := by
  refine ⟨b, hb, numer, hnum, fun n => ?_⟩
  have hbn : 0 < b ^ n := pow_pos (one_pos.trans hb) n
  have hpos : 0 < (dlaDim (gens n) : ℝ) := lt_of_lt_of_le hbn (hdim n)
  rw [hvar n, sub_zero, abs_of_nonneg (div_nonneg hnum hpos.le)]
  exact div_le_div_of_nonneg_left hnum hbn (hdim n)

/-! ### Tier 2 — the decomposition step: dimension is additive over a direct sum -/

/-- If a finite-dimensional space is the internal direct sum of subspaces `A i`, its
dimension is the sum of theirs. (Linear-algebra core of the Lie-algebra decomposition
`dim g = ∑ₖ dim gₖ`.) -/
theorem finrank_eq_sum_of_isInternal {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*}
    [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    {A : ι → Submodule ℂ M} (h : DirectSum.IsInternal A) :
    Module.finrank ℂ M = ∑ i, Module.finrank ℂ (A i) := by
  have e : (⨁ i, A i) ≃ₗ[ℂ] M := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h
  rw [← LinearEquiv.finrank_eq e, Module.finrank_directSum]

/-- **Decomposition of the dynamical Lie algebra dimension.** If the dynamical Lie
algebra decomposes as an internal direct sum of subspaces `A k` (its irreducible /
ideal components), then `dim g = ∑ₖ dim (A k)`. -/
theorem dlaDim_eq_sum_of_isInternal {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Submodule ℂ (dynamicalLieAlgebra gens).toSubmodule}
    (h : DirectSum.IsInternal A) :
    dlaDim gens = ∑ i, Module.finrank ℂ (A i) :=
  finrank_eq_sum_of_isInternal h

/-! ### Tier 3a — worked example: full algebra `gl(2ⁿ)`, exponential ⟹ barren plateau -/

/-- A generating set that spans all of `gl(N, ℂ)` generates the whole algebra: its
dynamical Lie algebra is `⊤`. -/
theorem dynamicalLieAlgebra_eq_top_of_span_top
    {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    (hspan : Submodule.span ℂ gens = ⊤) :
    dynamicalLieAlgebra gens = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x ∈ Submodule.span ℂ gens := by rw [hspan]; trivial
  exact LieSubalgebra.submodule_span_le_lieSpan hx

/-- The dynamical Lie algebra of the *full* operator set is all of `gl(N, ℂ)`, of
dimension `N²` (maximal / fully controllable case). -/
theorem dlaDim_univ : dlaDim (Set.univ : Set (Matrix (Fin N) (Fin N) ℂ)) = N * N := by
  have htop : dynamicalLieAlgebra (Set.univ : Set (Matrix (Fin N) (Fin N) ℂ)) = ⊤ :=
    dynamicalLieAlgebra_eq_top_of_span_top (by rw [Submodule.span_univ])
  rw [dlaDim, htop, LieSubalgebra.top_toSubmodule, finrank_top, Module.finrank_matrix]
  simp

/-- **Worked example (exponential ⟹ barren plateau).** A fully controllable circuit
family on `n` qubits — whose generators span all of `gl(2ⁿ, ℂ)`, so `dim g = 4ⁿ` — has
a barren plateau under the Ragone variance law. -/
theorem barrenPlateau_of_full_dla
    {gens : (n : ℕ) → Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)}
    (hfull : ∀ n, Submodule.span ℂ (gens n) = ⊤)
    {variance : ℕ → ℝ} {numer : ℝ} (hnum : 0 ≤ numer)
    (hvar : ∀ n, variance n = numer / (dlaDim (gens n) : ℝ)) :
    HasBarrenPlateau variance := by
  refine hasBarrenPlateau_of_exp_dlaDim hnum hvar (b := 2) one_lt_two fun n => ?_
  have hdim : dlaDim (gens n) = 2 ^ n * 2 ^ n := by
    have htop : dynamicalLieAlgebra (gens n) = ⊤ :=
      dynamicalLieAlgebra_eq_top_of_span_top (hfull n)
    rw [dlaDim, htop, LieSubalgebra.top_toSubmodule, finrank_top, Module.finrank_matrix]
    simp
  rw [hdim]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  push_cast
  nlinarith [h1, pow_pos (show (0:ℝ) < 2 by norm_num) n]

/-! ### Tier 3b — worked example: single generator, constant ⟹ no barren plateau -/

/-- A single-generator circuit has a one-dimensional dynamical Lie algebra (the
generator commutes with itself, so the Lie closure is just its span). -/
theorem dlaDim_singleton {H : Matrix (Fin N) (Fin N) ℂ} (hH : H ≠ 0) :
    dlaDim ({H} : Set (Matrix (Fin N) (Fin N) ℂ)) = 1 := by
  have hcoe : (dynamicalLieAlgebra ({H} : Set (Matrix (Fin N) (Fin N) ℂ))).toSubmodule
      = Submodule.span ℂ {H} := by
    rw [dynamicalLieAlgebra]
    exact LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero
      (by rintro x rfl y rfl; exact lie_self _)
  rw [dlaDim, hcoe, finrank_span_singleton hH]

/-! ### Tier 3c — worked example: commuting family, dimension grows linearly in `n` -/

/-- The `n` diagonal unit matrices `diag(eᵢ)` pairwise commute and are linearly
independent, so their dynamical Lie algebra is the `n`-dimensional diagonal subalgebra:
`dim g = n`. This is a worked example of a dynamical Lie algebra whose dimension grows
**polynomially (linearly)** in the size parameter `n` — the trainable regime, in
contrast to the exponential `gl(2ⁿ)` case. -/
theorem dlaDim_diagonalFamily (n : ℕ) :
    dlaDim (Set.range (fun i : Fin n => Matrix.diagonal (Pi.single i (1 : ℂ)))) = n := by
  set g : Fin n → Matrix (Fin n) (Fin n) ℂ := fun i => Matrix.diagonal (Pi.single i (1 : ℂ))
    with hg
  -- the generators pairwise commute, so the Lie closure is just their linear span
  have hcoe : (dynamicalLieAlgebra (Set.range g)).toSubmodule
      = Submodule.span ℂ (Set.range g) := by
    rw [dynamicalLieAlgebra]
    refine LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero ?_
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    rw [hg, Ring.lie_def, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      sub_eq_zero]
    congr 1
    funext x
    exact mul_comm _ _
  -- the generators are linearly independent (reflected by the `diag` linear map)
  have hbasis : LinearIndependent ℂ (fun i : Fin n => Pi.single i (1 : ℂ)) := by
    have h := (Pi.basisFun ℂ (Fin n)).linearIndependent
    have heqb : (fun i : Fin n => Pi.single i (1 : ℂ)) = ⇑(Pi.basisFun ℂ (Fin n)) := by
      funext i; rw [Pi.basisFun_apply]
    rw [heqb]; exact h
  let D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := Matrix.diag, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hLI : LinearIndependent ℂ g := by
    have hcomp : LinearIndependent ℂ (D ∘ g) := by
      have heq : (D ∘ g) = fun i : Fin n => Pi.single i (1 : ℂ) := by
        funext i; simp [D, hg, Matrix.diag_diagonal]
      rw [heq]; exact hbasis
    exact hcomp.of_comp D
  rw [dlaDim, hcoe, finrank_span_eq_card hLI, Fintype.card_fin]

/-- **Worked example (constant ⟹ no barren plateau).** A single-generator circuit
family — whose dynamical Lie algebra is one-dimensional for every `n` — is *trainable*:
under the variance law `variance = numer / dim g` with `numer > 0`, the variance is the
positive constant `numer`, which does not vanish, so there is no barren plateau. -/
theorem not_barrenPlateau_of_dlaDim_const
    {sz : ℕ → ℕ} {H : (n : ℕ) → Matrix (Fin (sz n)) (Fin (sz n)) ℂ}
    (hH : ∀ n, H n ≠ 0)
    {variance : ℕ → ℝ} {numer : ℝ} (hnum : 0 < numer)
    (hvar : ∀ n,
      variance n = numer / (dlaDim ({H n} :
        Set (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)) : ℝ)) :
    ¬ HasBarrenPlateau variance := by
  intro hbp
  have hconst : variance = fun _ => numer := by
    funext n; rw [hvar n, dlaDim_singleton (hH n)]; simp
  have h0 : Filter.Tendsto variance Filter.atTop (nhds 0) := hbp.variance_tendsto_zero
  rw [hconst] at h0
  exact hnum.ne (tendsto_nhds_unique h0 tendsto_const_nhds)

end

end QuantumAlg
