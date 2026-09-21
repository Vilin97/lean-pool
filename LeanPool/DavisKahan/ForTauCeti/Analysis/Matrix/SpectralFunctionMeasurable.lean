/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T19.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
addition to `Mathlib/Analysis/Matrix/Spectrum.lean`
(measurability of a continuous spectral function of a measurable Hermitian-matrix
family).

Formalized by Claude Fable 5 (claude-fable-5[1m]); relocated/staged and
self-contained-ized by Claude Opus 4.8 (claude-opus-4-8[1m]); linter pass by
Claude Opus 4.8 (name the two `MeasurableSpace`/`BorelSpace` instances so the
auto-name carries no underscore; `opSym` `def` → `theorem` since it is
Prop-valued; `rwa` consolidation).
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Matrix.EntrywiseOpNorm
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex


/-! # Continuous spectral functions of Hermitian matrices

The matrix CFC is the canonical spectral transform over any `RCLike` field.
Its continuity on Hermitian matrices gives measurability in the entrywise Borel structure.
The proof uses a locally uniform spectral bound, not a measurable choice of eigenvectors.
The coordinate and eigenvalue lemmas below also serve the CMDS statistics consumers.
-/

public section

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix Topology
open MeasureTheory Filter Set

namespace TauCeti.Matrix

variable {n : ℕ}

/-- `Matrix` is a type-level def, so the pi `MeasurableSpace` instance does not
fire on it automatically; register the entrywise σ-algebra (matching the pi
topology used by the matrix functional calculus).

Stated for an arbitrary index pair and entry type rather than `Matrix (Fin n) (Fin n) ℝ`.
Nothing here uses finiteness of the index or the field structure of the entries -- the
σ-algebra is the pi one transported across a type-level `def` -- and the narrow version
would have to be widened before this could go to Mathlib.  (To be reconciled with
Mathlib's matrix measurable structure at PR time.) -/
instance instMeasurableSpaceMatrix {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))

/-- `Matrix` is a type-level def, so the pi metrizability instance does not fire on it
either; register it for the entrywise topology. -/
instance instPseudoMetrizableSpaceMatrix {m n α : Type*} [Finite m] [Finite n]
    [TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n α) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → α))

/-- Matrices carry the Borel σ-algebra of their entrywise topology, so spectral functions of a
matrix can be shown measurable entrywise.

The hypotheses are exactly `Pi.borelSpace`'s, applied twice: countability of each index and
second countability of the entry type are what make the product σ-algebra Borel. -/
instance instBorelSpaceMatrix {m n α : Type*} [Countable m] [Countable n]
    [TopologicalSpace α] [MeasurableSpace α] [SecondCountableTopology α] [BorelSpace α] :
    BorelSpace (Matrix m n α) :=
  inferInstanceAs (BorelSpace (m → n → α))

/-- The symmetric-operator structure of `toEuclideanLin B` for a Hermitian `B`. -/
theorem opSym {𝕜 : Type*} [RCLike 𝕜]
    {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.IsHermitian) :
    (Matrix.toEuclideanLin B).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr hB

/-- The sorted eigenvalues of a Hermitian matrix over `Fin n` are the sorted eigenvalues of
the operator it induces, read across `Fintype.card (Fin n) = n`.

`Matrix.IsHermitian.eigenvalues₀` is *defined* as the operator enumeration, but indexed by
`Fin (Fintype.card (Fin n))` rather than `Fin n`; the equality of those cardinals is a
theorem, not a definitional unfolding, so the transport is this lemma and not `rfl`. -/
theorem eigenvalues₀_eq_eigenvalues_toEuclideanLin {𝕜 : Type*} [RCLike 𝕜]
    {B : Matrix (Fin n) (Fin n) 𝕜}
    (hB : B.IsHermitian) (i : Fin (Fintype.card (Fin n))) :
    hB.eigenvalues₀ i
      = (opSym hB).eigenvalues finrank_euclideanSpace_fin (Fin.cast (Fintype.card_fin n) i) :=
  TauCeti.eigenvalues_cast _ _ _ _ _

/-- The operator enumeration read back as the matrix one. -/
theorem eigenvalues_toEuclideanLin_eq_eigenvalues₀ {𝕜 : Type*} [RCLike 𝕜]
    {B : Matrix (Fin n) (Fin n) 𝕜}
    (hB : B.IsHermitian) (i : Fin n) :
    (opSym hB).eigenvalues finrank_euclideanSpace_fin i
      = hB.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) := by
  rw [eigenvalues₀_eq_eigenvalues_toEuclideanLin]
  congr 1

/-! ### Coordinate and eigenvalue bounds -/

/-- A coordinate of a Euclidean vector is bounded by its norm. -/
theorem abs_coord_le_norm (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h := EuclideanSpace.norm_eq x
  have hsq : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 := by
    have hterm : ∀ j ∈ Finset.univ, (0:ℝ) ≤ (x j) ^ 2 := fun j _ => sq_nonneg _
    simpa using Finset.single_le_sum hterm (Finset.mem_univ i)
  calc |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (x j) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖x‖ := by
        rw [h]; congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Real.norm_eq_abs, sq_abs]

/-- Entrywise bound on a Hermitian matrix bounds all its eigenvalues. -/
theorem abs_eigenvalues₀_le_of_entry_le {𝕜 : Type*} [RCLike 𝕜]
    {B : Matrix (Fin n) (Fin n) 𝕜}
    (hB : B.IsHermitian) {β : ℝ} (hβ : ∀ i j, ‖B i j‖ ≤ β)
    (k : Fin (Fintype.card (Fin n))) :
    |hB.eigenvalues₀ k| ≤ (n : ℝ) * β := by
  set u := (opSym hB).eigenvectorBasis finrank_euclideanSpace with hu
  have hnorm1 : ‖u k‖ = 1 := u.orthonormal.1 k
  have happly : Matrix.toEuclideanLin B (u k) = (hB.eigenvalues₀ k : 𝕜) • u k := by
    rw [hu]
    exact (opSym hB).apply_eigenvectorBasis finrank_euclideanSpace k
  have hle : ‖Matrix.toEuclideanLin B (u k)‖ ≤ (n : ℝ) * β * ‖u k‖ :=
    TauCeti.norm_toEuclideanLin_le_of_entry_le hβ (u k)
  rwa [happly, norm_smul, RCLike.norm_ofReal, hnorm1, mul_one, mul_one] at hle

/-- One-sided form of the entrywise eigenvalue bound.  A consumer that only needs a
spectral ceiling states it against this rather than discharging the absolute value. -/
theorem eigenvalues₀_le_of_entry_le {𝕜 : Type*} [RCLike 𝕜]
    {B : Matrix (Fin n) (Fin n) 𝕜}
    (hB : B.IsHermitian) {β : ℝ} (hβ : ∀ i j, ‖B i j‖ ≤ β)
    (k : Fin (Fintype.card (Fin n))) :
    hB.eigenvalues₀ k ≤ (n : ℝ) * β :=
  le_trans (le_abs_self _) (abs_eigenvalues₀_le_of_entry_le hB hβ k)

/-! ### Canonical continuous functional calculus -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator

/-- Matrices over `𝕜` in the L2 operator norm are a normed algebra over `𝕜`, and Mathlib
registers the *real* restriction of that only for `𝕜 = ℂ`.  `ContinuousAt.cfc` needs it over
`ℝ`, the scalar field of the Hermitian calculus, so supply it here — built on the canonical
`Algebra ℝ (Matrix …)` so that the matrix (isometric) CFC instances still apply — and keep it
local, so no second real algebra structure on matrices escapes this section. -/
noncomputable local instance instRealNormedAlgebraMatrix :
    NormedAlgebra ℝ (Matrix (Fin n) (Fin n) 𝕜) :=
  { (inferInstance : Algebra ℝ (Matrix (Fin n) (Fin n) 𝕜)) with
    norm_smul_le := fun r x => by
      have hx : r • x = (r : 𝕜) • x := by
        ext i j
        simp [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
      rw [hx, norm_smul, RCLike.norm_ofReal, Real.norm_eq_abs] }

/-- A fixed continuous real spectral function is continuous on Hermitian matrices. -/
theorem continuous_cfc_on_hermitian (h : ℝ → ℝ) (hh : Continuous h) :
    Continuous fun A : {A : Matrix (Fin n) (Fin n) 𝕜 // A.IsHermitian} => cfc h A.1 := by
  rw [continuous_iff_continuousAt]
  intro A
  have hnorm : ∀ᶠ B : {B : Matrix (Fin n) (Fin n) 𝕜 // B.IsHermitian}
      in 𝓝 A, ‖B.1‖ < ‖A.1‖ + 1 :=
    (continuous_subtype_val.norm.continuousAt).eventually
      (gt_mem_nhds (lt_add_one _))
  refine ContinuousAt.cfc (𝕜 := ℝ) (p := IsSelfAdjoint)
    (a := fun B : {B : Matrix (Fin n) (Fin n) 𝕜 // B.IsHermitian} => B.1)
    (isCompact_closedBall (0 : ℝ)
      ((‖A.1‖ + 1) * ‖(1 : Matrix (Fin n) (Fin n) 𝕜)‖)) h
    continuous_subtype_val.continuousAt ?_ ?_ hh.continuousOn
  · -- `‖1‖ = 1` needs `NormOneClass`, which fails on the zero matrix algebra `n = 0`;
    -- the `‖a‖ * ‖1‖` bound holds unconditionally.
    filter_upwards [hnorm] with B hB
    refine (spectrum.subset_closedBall_norm_mul B.1).trans
      (Metric.closedBall_subset_closedBall ?_)
    exact mul_le_mul_of_nonneg_right hB.le (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun B => B.2.isSelfAdjoint

/-- A continuous real spectral function of a measurable Hermitian matrix is measurable. -/
theorem measurable_cfc_of_hermitian {Ω : Type*} [MeasurableSpace Ω]
    (h : ℝ → ℝ) (hh : Continuous h)
    {Bm : Ω → Matrix (Fin n) (Fin n) 𝕜} (hBmeas : Measurable Bm)
    (hherm : ∀ w, (Bm w).IsHermitian) :
    Measurable fun w => cfc h (Bm w) :=
  (continuous_cfc_on_hermitian h hh).measurable.comp (hBmeas.subtype_mk (h := hherm))

/-- At a fixed finite Hermitian matrix, convergence at its eigenvalues suffices for CFC
convergence. The scalar functions need not be continuous on the whole real line. -/
theorem tendsto_cfc_of_pointwise {ι : Type*} {l : Filter ι}
    {F : ι → ℝ → ℝ} {f : ℝ → ℝ}
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (hF : ∀ x ∈ spectrum ℝ A, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Tendsto (fun i => cfc (F i) A) l (𝓝 (cfc f A)) := by
  have hvalues : Tendsto (fun i j => F i (hA.eigenvalues j)) l
      (𝓝 (fun j => f (hA.eigenvalues j))) :=
    tendsto_pi_nhds.mpr fun j => hF _ (hA.eigenvalues_mem_spectrum_real j)
  have hdiag : Continuous (fun v : Fin n → ℝ =>
      Matrix.diagonal (fun j => (v j : 𝕜))) := by
    fun_prop
  have ht := hdiag.continuousAt.tendsto.comp hvalues
  simpa only [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def] using (tendsto_const_nhds.mul ht).mul tendsto_const_nhds

end RCLike

end TauCeti.Matrix
