/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Homogeneous Markov chains as trajectory measures

This file packages the Ionescu--Tulcea trajectory construction for a
homogeneous Markov kernel and identifies every coordinate marginal with the
usual recursive iterate of the initial law.
-/

namespace FD1D.TrajectoryBridge

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- The state law obtained after recursively applying a homogeneous kernel. -/
def iterateLaw (κ : Kernel α α) (μ₀ : Measure α) : ℕ → Measure α
  | 0 => μ₀
  | n + 1 => κ ∘ₘ iterateLaw κ μ₀ n

@[simp]
theorem iterateLaw_zero (κ : Kernel α α) (μ₀ : Measure α) :
    iterateLaw κ μ₀ 0 = μ₀ :=
  rfl

@[simp]
theorem iterateLaw_succ (κ : Kernel α α) (μ₀ : Measure α) (n : ℕ) :
    iterateLaw κ μ₀ (n + 1) = κ ∘ₘ iterateLaw κ μ₀ n :=
  rfl

/-- A homogeneous kernel viewed as a history-dependent kernel. -/
def historyKernel (κ : Kernel α α) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → α) α :=
  κ.comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance historyKernel.instIsMarkovKernel (κ : Kernel α α)
    [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (historyKernel κ n) := by
  unfold historyKernel
  infer_instance

/-- The single path-space law generated from `μ₀` by repeatedly applying `κ`. -/
def trajectoryLaw (μ₀ : Measure α) (κ : Kernel α α) [IsMarkovKernel κ] :
    Measure (ℕ → α) :=
  Kernel.trajMeasure (X := fun _ => α) μ₀ (historyKernel κ)

theorem trajectoryLaw_marginal_zero
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (κ : Kernel α α) [IsMarkovKernel κ] :
    Measure.map (fun path : ℕ → α => path 0) (trajectoryLaw μ₀ κ) = μ₀ := by
  rw [trajectoryLaw, Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_pi_apply 0)]
  have hmap :
      (Kernel.traj (historyKernel κ) 0).map
          (fun path : ℕ → α => path 0) =
        Kernel.deterministic
          (fun h : (i : Finset.Iic 0) → α => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
          (by fun_prop) := by
    have heval :
        (fun path : ℕ → α => path 0) =
          (fun h : (i : Finset.Iic 0) → α =>
            h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
            Preorder.frestrictLe 0 := by
      rfl
    rw [heval, Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0)
        (measurable_pi_apply ⟨0, Finset.mem_Iic.mpr le_rfl⟩),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
      Kernel.id_map]
  rw [hmap, Measure.deterministic_comp_eq_map]
  rw [Measure.map_map
    (measurable_pi_apply ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm.measurable]
  have hcomp :
      (fun h : (i : Finset.Iic 0) → α =>
        h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm = id := by
    funext x
    rfl
  rw [hcomp, Measure.map_id]

theorem trajectoryLaw_marginal_succ
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    Measure.map (fun path : ℕ → α => path (n + 1)) (trajectoryLaw μ₀ κ) =
      κ ∘ₘ Measure.map (fun path : ℕ → α => path n) (trajectoryLaw μ₀ κ) := by
  let P := trajectoryLaw μ₀ κ
  let pref : (ℕ → α) → ((i : Finset.Iic n) → α) :=
    Preorder.frestrictLe n
  let hP : IsProbabilityMeasure P := by
    dsimp [P, trajectoryLaw]
    infer_instance
  have hjoint :
      P.map pref ⊗ₘ historyKernel κ n =
        P.map (fun path => (pref path, path (n + 1))) := by
    simpa only [P, pref, trajectoryLaw] using
      (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => α) (μ₀ := μ₀) (κ := historyKernel κ) (a := n))
  have hsnd := congrArg Measure.snd hjoint
  rw [Measure.snd_compProd,
    Measure.snd_map_prodMk (show Measurable pref by fun_prop)] at hsnd
  rw [← hsnd]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [historyKernel, Kernel.comap_apply']
  dsimp only [pref, P]
  rw [lintegral_map
      (μ := trajectoryLaw μ₀ κ)
      (f := fun h : (i : Finset.Iic n) → α =>
        κ (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) s)
      (g := Preorder.frestrictLe n)
      ((κ.measurable_coe hs).comp
        (measurable_pi_apply
          (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)))
      (Preorder.measurable_frestrictLe n),
    lintegral_map
      (μ := trajectoryLaw μ₀ κ)
      (f := fun x : α => κ x s)
      (g := fun path : ℕ → α => path n)
      (κ.measurable_coe hs) (measurable_pi_apply n)]
  rfl

theorem trajectoryLaw_marginal
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    Measure.map (fun path : ℕ → α => path n) (trajectoryLaw μ₀ κ) =
      iterateLaw κ μ₀ n := by
  induction n with
  | zero =>
      exact trajectoryLaw_marginal_zero μ₀ κ
  | succ n ih =>
      rw [iterateLaw_succ, ← ih]
      exact trajectoryLaw_marginal_succ μ₀ κ n

end

end FD1D.TrajectoryBridge
