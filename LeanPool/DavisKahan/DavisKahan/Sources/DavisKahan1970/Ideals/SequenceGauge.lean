/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.Majorization.WeakSubmajorization
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.NormCorrespondence
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormInstances
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization
import Mathlib.Topology.Compactness.Compact

/-!
# The sequence gauge of a coherent symmetric norm, and its Riesz splitting

This file extends a coherent unitarily invariant norm from finite vectors to
sequences, and proves the splitting theorem that extension exists to support.
The key finite result is a Riesz splitting for weak majorization: if
`x ≺w y + z`, then `x = u + v` with the symmetric gauge of `u` bounded by that
of `y` and the symmetric gauge of `v` bounded by that of `z`.

The order-continuous part of the gauge is what the minimal symmetrically normed
operator ideal is built from; that construction lives downstream, and this file
is the sequence-space half of it.

The proof is not an assumption and does not use a separation theorem.  It
applies the repository's constructive Hardy--Littlewood--Pólya descent to the
Minkowski sum of two symmetric-convex gauge balls.
-/

namespace TauCeti
namespace Majorization

open scoped BigOperators ENNReal
open DavisKahan.ExactSinTheta

noncomputable section

/-- The coherent finite gauge applied to the first `n` entries of a sequence. -/
def sequencePrefixGauge (N : SymmetricNormingFunction) (n : ℕ)
    (x : ℕ → ℝ) : ℝ :=
  N.finiteGauge n (sequencePrefixVector n x)

/-- The maximal extended sequence gauge associated with `N`. -/
def sequenceExtendedGauge (N : SymmetricNormingFunction)
    (x : ℕ → ℝ) : ENNReal :=
  ⨆ n : ℕ, ENNReal.ofReal (sequencePrefixGauge N n x)

/-- Membership in the maximal sequence space. -/
def SequenceMem (N : SymmetricNormingFunction) (x : ℕ → ℝ) : Prop :=
  sequenceExtendedGauge N x ≠ ⊤

/-- The real-valued sequence gauge on its maximal domain. -/
def sequenceGauge (N : SymmetricNormingFunction) (x : ℕ → ℝ) : ℝ :=
  (sequenceExtendedGauge N x).toReal

/-- The paper's finite gauge, packaged in the algebraic interface consumed by
finite majorization. -/
noncomputable def normingFiniteSymmetricGauge
    (N : SymmetricNormingFunction) (n : ℕ) : FiniteSymmetricGauge n :=
  (N.finiteNorm n).finiteSymmetricGauge
    (EuclideanSpace.basisFun (Fin n) ℂ)

/-- `normingFiniteSymmetricGauge` computes the paper's own finite gauge: the repackaging
into `FiniteSymmetricGauge` changes the interface, not the value. -/
@[simp] theorem normingFiniteSymmetricGauge_apply
    (N : SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) :
    normingFiniteSymmetricGauge N n x = N.finiteGauge n x :=
  rfl

/-- A Minkowski sum of two symmetric-gauge balls is symmetric-convex. -/
theorem isSymmetricConvex_gaugeBall_add_gaugeBall
    {n : ℕ} (Φ Ψ : FiniteSymmetricGauge n)
    (r s : ℝ) :
    FiniteVector.IsSymmetricConvex
      {x : Fin n → ℝ | ∃ u v,
        x = u + v ∧ Φ u ≤ r ∧ Ψ v ≤ s} := by
  let U : Set (Fin n → ℝ) := {u | Φ u ≤ r}
  let V : Set (Fin n → ℝ) := {v | Ψ v ≤ s}
  have hU : FiniteVector.IsSymmetricConvex U :=
    Φ.isSymmetricConvex_sublevel r
  have hV : FiniteVector.IsSymmetricConvex V :=
    Ψ.isSymmetricConvex_sublevel s
  refine
    { convex := ?_
      swap_mem := ?_
      neg_single_mem := ?_ }
  · rintro x ⟨ux, vx, rfl, hux, hvx⟩
      y ⟨uy, vy, rfl, huy, hvy⟩ a b ha hb hab
    refine ⟨a • ux + b • uy, a • vx + b • vy, ?_, ?_, ?_⟩
    · module
    · exact hU.convex hux huy ha hb hab
    · exact hV.convex hvx hvy ha hb hab
  · rintro x ⟨u, v, rfl, hu, hv⟩ j l
    refine ⟨u ∘ Equiv.swap j l, v ∘ Equiv.swap j l, ?_, ?_, ?_⟩
    · funext i
      simp [Function.comp_apply]
    · exact hU.swap_mem u hu j l
    · exact hV.swap_mem v hv j l
  · rintro x ⟨u, v, rfl, hu, hv⟩ j
    refine ⟨Function.update u j (-(u j)),
      Function.update v j (-(v j)), ?_, ?_, ?_⟩
    · funext i
      rcases eq_or_ne i j with rfl | hij
      · simp [add_comm]
      · simp [Function.update_of_ne hij]
    · exact hU.neg_single_mem u hu j
    · exact hV.neg_single_mem v hv j

/-- **Finite Riesz decomposition for weak majorization.**

If `x` is weakly majorized by `y + z`, then `x` splits as `u + v`, with
`u` no larger than `y` in one prescribed symmetric gauge and `v` no larger
than `z` in another. -/
theorem exists_gauge_decomposition_of_weaklyMajorized
    {n : ℕ} (Φ Ψ : FiniteSymmetricGauge n)
    {x y z : Fin n → ℝ}
    (h : FiniteVector.WeaklyMajorized x (y + z)) :
    ∃ u v : Fin n → ℝ,
      x = u + v ∧ Φ u ≤ Φ y ∧ Ψ v ≤ Ψ z := by
  let K : Set (Fin n → ℝ) :=
    {w | ∃ u v, w = u + v ∧ Φ u ≤ Φ y ∧ Ψ v ≤ Ψ z}
  have hK : FiniteVector.IsSymmetricConvex K :=
    isSymmetricConvex_gaugeBall_add_gaugeBall Φ Ψ (Φ y) (Ψ z)
  have hyz : y + z ∈ K := ⟨y, z, rfl, le_rfl, le_rfl⟩
  exact hK.mem_of_weaklyMajorized h hyz

/-- The finite Riesz decomposition specialized to the normalized ℓ¹ gauge and
one coherent paper gauge. -/
theorem exists_l1_normingGauge_decomposition_of_weaklyMajorized
    (N : SymmetricNormingFunction) {n : ℕ}
    {x y z : Fin n → ℝ}
    (h : FiniteVector.WeaklyMajorized x (y + z)) :
    ∃ u v : Fin n → ℝ,
      x = u + v ∧
      l1Gauge n u ≤ l1Gauge n y ∧
      N.finiteGauge n v ≤ N.finiteGauge n z := by
  obtain ⟨u, v, huv, hu, hv⟩ :=
    exists_gauge_decomposition_of_weaklyMajorized
      (normingFiniteSymmetricGauge nuclearNormingFunction n)
      (normingFiniteSymmetricGauge N n) h
  refine ⟨u, v, huv, ?_, ?_⟩
  · change nuclearNormingFunction.finiteGauge n u ≤
      nuclearNormingFunction.finiteGauge n y at hu
    simpa only [nuclearNormingFunction_finiteGauge] using hu
  · change N.finiteGauge n v ≤ N.finiteGauge n z at hv
    exact hv

end

end Majorization
end TauCeti
