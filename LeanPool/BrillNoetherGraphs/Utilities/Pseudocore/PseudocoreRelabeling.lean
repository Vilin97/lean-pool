/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.GenusFourPseudocore
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Vertex relabeling and the handshake identity for pseudocores

Three ingredients, all generic in the vertex count:

* `Pseudocore.relabel` — transport of a pseudocore along a vertex
  permutation, with well-formedness, connectedness, valence, and edge-count
  preservation;
* `Pseudocore.sum_valence_eq` — the handshake identity
  `Σ valence = 2 · edgeCount` for well-formed pseudocores, which pins an
  arbitrary valid pseudocore's valence vector to a partition-of-six degree
  sequence;
* `Pseudocore.exists_monotone_relabel` — every pseudocore admits a
  relabeling with monotone valences (`Tuple.sort`), which is what reduces
  the classifier to one generated tree per *sorted* degree sequence.
-/

@[expose] public section

namespace Utilities.Certificate.GenusFourPseudocore

namespace Pseudocore

variable {n : ℕ}

/-- Transport of a pseudocore along a vertex permutation: vertex `v` of the
relabeled pseudocore carries the data of vertex `σ v`. -/
def relabel (core : Pseudocore n) (σ : Equiv.Perm (Fin n)) : Pseudocore n where
  loops := fun v => core.loops (σ v)
  multiplicity := fun v w => core.multiplicity (σ v) (σ w)

@[simp] theorem relabel_loops (core : Pseudocore n) (σ : Equiv.Perm (Fin n))
    (v : Fin n) : (core.relabel σ).loops v = core.loops (σ v) := rfl

@[simp] theorem relabel_multiplicity (core : Pseudocore n)
    (σ : Equiv.Perm (Fin n)) (v w : Fin n) :
    (core.relabel σ).multiplicity v w
      = core.multiplicity (σ v) (σ w) := rfl

theorem valence_relabel (core : Pseudocore n) (σ : Equiv.Perm (Fin n))
    (v : Fin n) : (core.relabel σ).valence v = core.valence (σ v) := by
  unfold valence
  simp only [relabel_loops, relabel_multiplicity]
  congr 1
  exact Equiv.sum_comp σ fun w => core.multiplicity (σ v) w

theorem matrixWellFormed_relabel (core : Pseudocore n)
    (σ : Equiv.Perm (Fin n)) (hWellFormed : core.MatrixWellFormed) :
    (core.relabel σ).MatrixWellFormed := by
  obtain ⟨hDiag, hSymm⟩ := hWellFormed
  exact ⟨fun v => hDiag (σ v), fun v w => hSymm (σ v) (σ w)⟩

theorem connected_relabel (core : Pseudocore n) (σ : Equiv.Perm (Fin n))
    (hConnected : core.Connected) : (core.relabel σ).Connected := by
  intro S hWitness
  obtain ⟨v, w, hv, hw⟩ := hWitness
  have hImage : ∀ x : Fin n, σ x ∈ S.image σ ↔ x ∈ S := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hEq⟩ := Finset.mem_image.mp hx
      rwa [← σ.injective hEq]
    · intro hx
      exact Finset.mem_image_of_mem σ hx
  obtain ⟨inside, hInside, outside, hOutside, hPos⟩ :=
    hConnected (S.image σ)
      ⟨σ v, σ w, (hImage v).mpr hv, fun hAbsurd => hw ((hImage w).mp hAbsurd)⟩
  obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hInside
  refine ⟨a, ha, σ.symm outside, ?_, ?_⟩
  · intro hAbsurd
    exact hOutside (by
      have := (hImage (σ.symm outside)).mpr hAbsurd
      simpa using this)
  · simp only [relabel_multiplicity, hEq, Equiv.apply_symm_apply]
    exact hPos

/-- The doubling identity behind the handshake: the full matrix sum of a
well-formed pseudocore is twice its strict-upper-triangle sum. -/
theorem double_nonloopEdgeCount (core : Pseudocore n)
    (hWellFormed : core.MatrixWellFormed) :
    2 * core.nonloopEdgeCount
      = ∑ v : Fin n, ∑ w : Fin n, core.multiplicity v w := by
  obtain ⟨hDiag, hSymm⟩ := hWellFormed
  have hSplit : ∀ v w : Fin n, core.multiplicity v w
      = (if v < w then core.multiplicity v w else 0)
        + (if w < v then core.multiplicity v w else 0) := by
    intro v w
    rcases lt_trichotomy v w with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst h
      simp [hDiag v]
    · simp [h, not_lt_of_gt h]
  have hLower : (∑ v : Fin n, ∑ w : Fin n,
        if w < v then core.multiplicity v w else 0)
      = core.nonloopEdgeCount := by
    rw [Finset.sum_comm]
    unfold nonloopEdgeCount
    refine Finset.sum_congr rfl fun w _ => ?_
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : w < v
    · simp [h, hSymm v w]
    · simp [h]
  have hUpper : (∑ v : Fin n, ∑ w : Fin n,
      if v < w then core.multiplicity v w else 0)
      = core.nonloopEdgeCount := rfl
  have hAll : ∑ v : Fin n, ∑ w : Fin n, core.multiplicity v w
      = (∑ v : Fin n, ∑ w : Fin n,
          if v < w then core.multiplicity v w else 0)
        + (∑ v : Fin n, ∑ w : Fin n,
            if w < v then core.multiplicity v w else 0) := by
    calc ∑ v : Fin n, ∑ w : Fin n, core.multiplicity v w
        = ∑ v : Fin n,
            ((∑ w : Fin n, if v < w then core.multiplicity v w else 0)
              + ∑ w : Fin n, if w < v then core.multiplicity v w else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ => hSplit v w
      _ = _ := Finset.sum_add_distrib
  omega

/-- **The handshake identity.**  A well-formed pseudocore's total valence is
twice its edge count. -/
theorem sum_valence_eq (core : Pseudocore n)
    (hWellFormed : core.MatrixWellFormed) :
    ∑ v : Fin n, core.valence v = 2 * core.edgeCount := by
  unfold valence edgeCount loopCount
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← double_nonloopEdgeCount core hWellFormed]
  ring

theorem loopCount_relabel (core : Pseudocore n) (σ : Equiv.Perm (Fin n)) :
    (core.relabel σ).loopCount = core.loopCount := by
  unfold loopCount
  simp only [relabel_loops]
  exact Equiv.sum_comp σ core.loops

theorem nonloopEdgeCount_relabel (core : Pseudocore n)
    (σ : Equiv.Perm (Fin n)) (hWellFormed : core.MatrixWellFormed) :
    (core.relabel σ).nonloopEdgeCount = core.nonloopEdgeCount := by
  have hDouble : 2 * (core.relabel σ).nonloopEdgeCount
      = 2 * core.nonloopEdgeCount := by
    rw [double_nonloopEdgeCount _ (matrixWellFormed_relabel core σ
        hWellFormed),
      double_nonloopEdgeCount core hWellFormed]
    calc ∑ v : Fin n, ∑ w : Fin n, (core.relabel σ).multiplicity v w
        = ∑ v : Fin n, ∑ w : Fin n, core.multiplicity (σ v) w := by
          refine Finset.sum_congr rfl fun v _ => ?_
          exact Equiv.sum_comp σ fun w => core.multiplicity (σ v) w
      _ = ∑ v : Fin n, ∑ w : Fin n, core.multiplicity v w :=
          Equiv.sum_comp σ fun v => ∑ w : Fin n, core.multiplicity v w
  omega

theorem edgeCount_relabel (core : Pseudocore n) (σ : Equiv.Perm (Fin n))
    (hWellFormed : core.MatrixWellFormed) :
    (core.relabel σ).edgeCount = core.edgeCount := by
  unfold edgeCount
  rw [loopCount_relabel, nonloopEdgeCount_relabel core σ hWellFormed]

theorem stable_relabel (core : Pseudocore n) (σ : Equiv.Perm (Fin n))
    (hStable : core.Stable) : (core.relabel σ).Stable := by
  intro v
  rw [valence_relabel]
  exact hStable (σ v)

theorem validAt_relabel (core : Pseudocore n) (σ : Equiv.Perm (Fin n))
    {g : ℕ} (hValid : core.ValidAt g) : (core.relabel σ).ValidAt g := by
  obtain ⟨hWellFormed, hConnected, hStable, hEdges⟩ := hValid
  exact ⟨matrixWellFormed_relabel core σ hWellFormed,
    connected_relabel core σ hConnected, stable_relabel core σ hStable,
    by rw [edgeCount_relabel core σ hWellFormed]; exact hEdges⟩

/-- Every pseudocore admits a relabeling with monotone valences. -/
theorem exists_monotone_relabel (core : Pseudocore n) :
    ∃ σ : Equiv.Perm (Fin n), Monotone (core.relabel σ).valence := by
  refine ⟨Tuple.sort core.valence, fun a b hab => ?_⟩
  rw [valence_relabel, valence_relabel]
  exact Tuple.monotone_sort core.valence hab

end Pseudocore

end Utilities.Certificate.GenusFourPseudocore
