/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.Reduction
public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.CRT
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Defs
public import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Basic

/-!
# Joint grid jet interpolation on a quotient

This file implements blueprint node **G03** of the lower-bound side of the sharp finite-field
Nikodym exponent.

Let `F ⊆ K` be the finite grid field, `q = |F|`, and `ι = liftPt : F^d → K^d` the coordinate
lift. For an ideal `I` of `P_d = MvPolynomial (Fin d) K` and `r : ℕ` we define

* `Nikodym.LowerBound.gridJetsLinearMap I r : P_d ⧸ I →ₗ[K] ∏_{x ∈ F^d} Q_{I, ι x}(r)`, the
  `K`-linear map induced on the quotient by collecting all jets at the grid points;

and prove, with `U = q (r - 1) + d (q - 1)`,

* `Nikodym.LowerBound.gridJets_restriction_surjective`: every family of jets `w x ∈ Q_{I, ι x}(r)`
  is the image of an element of the restriction space `V_I(U)`;
* `Nikodym.LowerBound.map_restrictionSpace_gridJetsLinearMap_eq_top`: the same statement packaged
  as `(V_I(U)).map (gridJetsLinearMap I r) = ⊤`;
* `Nikodym.LowerBound.sum_jetDim_le_hilbert`: `∑_{x ∈ F^d} j_{I, ι x}(r) ≤ H_I(U)`.

The proof follows the blueprint: CRT (G02) provides a polynomial with the prescribed jets, the
bounded reduction (G01) modulo `J ^ r` (with `J` the grid ideal) replaces it by a polynomial of
total degree at most `U`, and `J ^ r ≤ 𝔪_{ι x} ^ r` (G02) shows that the jets are unchanged.

The blueprint assumes `r ≥ 1`; none of the statements here needs it (for `r = 0` all jet spaces are
zero), so the hypothesis is omitted.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial Finset

variable {K : Type*} [Field K] {d : ℕ}
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

section GridJets

variable (I : Ideal (MvPolynomial (Fin d) K)) (r : ℕ)

/-- Blueprint G03: the `K`-linear map `P_d ⧸ I → ∏_{x ∈ F^d} Q_{I, ι x}(r)` collecting all jets
at the grid points, induced on the quotient by `I ≤ I + 𝔪_{ι x} ^ r`. -/
noncomputable def gridJetsLinearMap :
    (MvPolynomial (Fin d) K ⧸ I) →ₗ[K] ∀ x : Fin d → F, JetSpace I (liftPt x) r :=
  LinearMap.pi fun x ↦
    (Ideal.quotientMapₐ (jetIdeal I (liftPt x) r) (AlgHom.id K (MvPolynomial (Fin d) K))
      fun _ hf ↦ le_jetIdeal_left I (liftPt x) r hf).toLinearMap

omit [Fintype F] in
/-- Blueprint G03: the `x`-component of `gridJetsLinearMap I r` on the class of `f` is the jet of
`f` at `ι x`. -/
@[simp]
theorem gridJetsLinearMap_mk (f : MvPolynomial (Fin d) K) (x : Fin d → F) :
    gridJetsLinearMap I r (Ideal.Quotient.mk I f) x =
      Ideal.Quotient.mk (jetIdeal I (liftPt x) r) f :=
  rfl

omit [Fintype F] in
/-- Blueprint G03 (bridge to G02): for any jets `w x ∈ Q_{I, ι x}(r)` at the grid points there is
a single polynomial `f` representing all of them. -/
theorem exists_grid_jets_eq_liftPt [Finite F] (w : ∀ x : Fin d → F, JetSpace I (liftPt x) r) :
    ∃ f : MvPolynomial (Fin d) K, ∀ x : Fin d → F,
      Ideal.Quotient.mk (jetIdeal I (liftPt x) r) f = w x :=
  exists_grid_jets_eq I r w

/-- Blueprint G03 (bridge to G02): `J ^ r ≤ I + 𝔪_{ι x} ^ r` for the grid ideal `J`. -/
theorem gridIdeal_pow_le_jetIdeal (x : Fin d → F) :
    gridIdeal (fun _ ↦ gridPoly F K) ^ r ≤ jetIdeal I (liftPt x) r :=
  (gridIdeal_pow_le_pointIdeal_pow x r).trans (pointIdeal_pow_le_jetIdeal I (liftPt x) r)

/-- Blueprint G03: every family of jets `w x ∈ Q_{I, ι x}(r)` at the grid points is the image of
an element of the restriction space `V_I(U)`, `U = q (r - 1) + d (q - 1)`. -/
theorem gridJets_restriction_surjective (w : ∀ x : Fin d → F, JetSpace I (liftPt x) r) :
    ∃ v ∈ restrictionSpace I (Fintype.card F * (r - 1) + d * (Fintype.card F - 1)),
      gridJetsLinearMap I r v = w := by
  obtain ⟨f, hf⟩ := exists_grid_jets_eq_liftPt I r w
  obtain ⟨f', hf', hmem⟩ := exists_bounded_rep (g := fun _ ↦ gridPoly F K)
    (fun _ ↦ gridPoly_monic F K) (fun _ ↦ natDegree_gridPoly F K) Fintype.card_pos r f
  refine ⟨Ideal.Quotient.mk I f', mk_mem_restrictionSpace hf', ?_⟩
  funext x
  rw [gridJetsLinearMap_mk, ← hf x]
  exact (Ideal.Quotient.eq.mpr (gridIdeal_pow_le_jetIdeal I r x hmem)).symm

variable (F) in
/-- Blueprint G03, packaged: the restriction map `V_I(U) → ∏_{x ∈ F^d} Q_{I, ι x}(r)` is
surjective, where `U = q (r - 1) + d (q - 1)`. -/
theorem map_restrictionSpace_gridJetsLinearMap_eq_top :
    (restrictionSpace I (Fintype.card F * (r - 1) + d * (Fintype.card F - 1))).map
      (gridJetsLinearMap (F := F) I r) = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  obtain ⟨v, hv, rfl⟩ := gridJets_restriction_surjective I r w
  exact Submodule.mem_map_of_mem hv

/-- Blueprint G03: the dimension of the product of the grid jet spaces is the sum of the jet
dimensions. -/
theorem finrank_pi_jetSpace :
    Module.finrank K (∀ x : Fin d → F, JetSpace I (liftPt x) r) =
      ∑ x : Fin d → F, jetDim I (liftPt x) r :=
  Module.finrank_pi_fintype K

/-- Blueprint G03: `∑_{x ∈ F^d} j_{I, ι x}(r) ≤ H_I(U)` with `U = q (r - 1) + d (q - 1)`. -/
theorem sum_jetDim_le_hilbert :
    ∑ x : Fin d → F, jetDim I (liftPt x) r ≤
      hilbert I (Fintype.card F * (r - 1) + d * (Fintype.card F - 1)) := by
  rw [← finrank_pi_jetSpace, hilbert, ← finrank_top K,
    ← map_restrictionSpace_gridJetsLinearMap_eq_top F I r]
  exact Submodule.finrank_map_le _ _

end GridJets

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
