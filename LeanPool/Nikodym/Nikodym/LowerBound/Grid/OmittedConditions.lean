/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.Jets

/-!
# Omitting conditions leaves a nonzero restriction

This file implements blueprint node **G04** of the lower-bound side of the sharp finite-field
Nikodym exponent.

Let `F ⊆ K` be the finite grid field, `q = |F|`, `ι = liftPt : F^d → K^d`, `I` an ideal of
`P_d = MvPolynomial (Fin d) K`, `r : ℕ` and `U = q (r - 1) + d (q - 1)`. For a finite set
`B₀ ⊆ F^d` of omitted grid points we define

* `Nikodym.LowerBound.omittedJetsLinearMap I r B₀ T : V_I(T) →ₗ[K] ∏_{x ∉ B₀} Q_{I, ι x}(r)`,
  the restriction of `gridJetsLinearMap` to `V_I(T)` followed by the projection onto the
  coordinates outside `B₀`;

and prove

* `Nikodym.LowerBound.sum_jetDim_compl_add_sum_jetDim`: `∑_{x ∉ B₀} j + ∑_{b ∈ B₀} j = ∑_x j`;
* `Nikodym.LowerBound.exists_omitted_conditions`: if
  `H_I(U) < H_I(T) + ∑_{b ∈ B₀} j_{I, ι b}(r)`, then there is `g ∈ P_{d, ≤ T} \ I` with
  `g ∈ I + 𝔪_{ι x} ^ r` for every grid point `x ∉ B₀`.

The proof is the blueprint's: by G03, `∑_{x ∉ B₀} j_{I, ι x}(r) ≤ H_I(U) - ∑_{b ∈ B₀} j_{I, ι b}(r)
< H_I(T)` (kept in additive form), so the map `omittedJetsLinearMap` from `V_I(T)` to the product
of the remaining jet spaces has nonzero kernel by rank–nullity; a nonzero kernel element has a
representative `g ∈ P_{d, ≤ T} \ I` (F02), and its jets vanish outside `B₀`.

The blueprint also assumes `r ≥ 1` and `T ≤ U`; neither is needed for the statement, so both are
omitted.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial Finset

variable {K : Type*} [Field K] {d : ℕ}
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

section Omitted

variable (I : Ideal (MvPolynomial (Fin d) K)) (r : ℕ) (B₀ : Finset (Fin d → F)) (T : ℕ)

omit [Fintype F] in
/-- Blueprint G04: the `K`-linear map `V_I(T) → ∏_{x ∉ B₀} Q_{I, ι x}(r)` sending the class of a
polynomial of total degree at most `T` to its jets at the grid points outside `B₀`. -/
noncomputable def omittedJetsLinearMap :
    restrictionSpace I T →ₗ[K] ∀ x : {x : Fin d → F // x ∉ B₀}, JetSpace I (liftPt x.1) r :=
  (LinearMap.pi fun x : {x : Fin d → F // x ∉ B₀} ↦ LinearMap.proj x.1) ∘ₗ
    gridJetsLinearMap I r ∘ₗ (restrictionSpace I T).subtype

omit [Fintype F] in
/-- Blueprint G04: the components of `omittedJetsLinearMap`. -/
@[simp]
theorem omittedJetsLinearMap_apply (v : restrictionSpace I T) (x : {x : Fin d → F // x ∉ B₀}) :
    omittedJetsLinearMap I r B₀ T v x =
      gridJetsLinearMap I r (v : MvPolynomial (Fin d) K ⧸ I) x.1 :=
  rfl

variable [DecidableEq (Fin d → F)]

/-- Blueprint G04: the dimension of the product of the jet spaces at the grid points outside `B₀`
is the sum of the corresponding jet dimensions. -/
theorem finrank_pi_jetSpace_compl :
    Module.finrank K (∀ x : {x : Fin d → F // x ∉ B₀}, JetSpace I (liftPt x.1) r) =
      ∑ x ∈ B₀ᶜ, jetDim I (liftPt x) r := by
  rw [Module.finrank_pi_fintype K]
  exact (Finset.sum_subtype B₀ᶜ (fun x ↦ Finset.mem_compl) fun x ↦ jetDim I (liftPt x) r).symm

/-- Blueprint G04: splitting the sum of the grid jet dimensions along `B₀`. -/
theorem sum_jetDim_compl_add_sum_jetDim :
    ∑ x ∈ B₀ᶜ, jetDim I (liftPt x) r + ∑ b ∈ B₀, jetDim I (liftPt b) r =
      ∑ x : Fin d → F, jetDim I (liftPt x) r :=
  Finset.sum_compl_add_sum B₀ _

/-- Blueprint G04: the rank of `omittedJetsLinearMap` is at most the number of omitted-complement
jet conditions `∑_{x ∉ B₀} j_{I, ι x}(r)`. -/
theorem finrank_range_omittedJetsLinearMap_le :
    Module.finrank K (LinearMap.range (omittedJetsLinearMap I r B₀ T)) ≤
      ∑ x ∈ B₀ᶜ, jetDim I (liftPt x) r := by
  rw [← finrank_pi_jetSpace_compl]
  exact Submodule.finrank_le _

omit [DecidableEq (Fin d → F)]

/-- Blueprint G04: if `H_I(U) < H_I(T) + ∑_{b ∈ B₀} j_{I, ι b}(r)` with `U = q (r - 1) + d (q - 1)`,
then `omittedJetsLinearMap I r B₀ T` has a nonzero kernel. -/
theorem ker_omittedJetsLinearMap_ne_bot
    (hlt : hilbert I (Fintype.card F * (r - 1) + d * (Fintype.card F - 1)) <
      hilbert I T + ∑ b ∈ B₀, jetDim I (liftPt b) r) :
    LinearMap.ker (omittedJetsLinearMap I r B₀ T) ≠ ⊥ := by
  classical
  intro hker
  have h1 := LinearMap.finrank_range_add_finrank_ker (omittedJetsLinearMap I r B₀ T)
  have h2 := finrank_range_omittedJetsLinearMap_le I r B₀ T
  have h3 := sum_jetDim_compl_add_sum_jetDim I r B₀
  have h4 := sum_jetDim_le_hilbert I r (F := F)
  rw [hker, finrank_bot, add_zero] at h1
  change _ < Module.finrank K (restrictionSpace I T) + _ at hlt
  omega

/-- Blueprint G04: if `H_I(U) < H_I(T) + ∑_{b ∈ B₀} j_{I, ι b}(r)` with `U = q (r - 1) + d (q - 1)`,
then there is a polynomial `g ∈ P_{d, ≤ T} \ I` lying in `I + 𝔪_{ι x} ^ r` for every grid point
`x ∉ B₀`. -/
theorem exists_omitted_conditions
    (hlt : hilbert I (Fintype.card F * (r - 1) + d * (Fintype.card F - 1)) <
      hilbert I T + ∑ b ∈ B₀, jetDim I (liftPt b) r) :
    ∃ g ∈ restrictTotalDegree (Fin d) K T, g ∉ I ∧
      ∀ x : Fin d → F, x ∉ B₀ → g ∈ jetIdeal I (liftPt x) r := by
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (ker_omittedJetsLinearMap_ne_bot I r B₀ T hlt)
  have hv0' : (v : MvPolynomial (Fin d) K ⧸ I) ≠ 0 := fun h ↦ hv0 (Subtype.ext h)
  obtain ⟨g, hg, hgI, hgv⟩ := exists_notMem_of_ne_zero v.2 hv0'
  refine ⟨g, hg, hgI, fun x hx ↦ ?_⟩
  rw [LinearMap.mem_ker] at hv
  have := congr_fun hv ⟨x, hx⟩
  rw [omittedJetsLinearMap_apply, ← hgv, gridJetsLinearMap_mk] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end Omitted

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
