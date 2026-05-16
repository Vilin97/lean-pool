/-
Copyright (c) 2026 Rémy Degenne, Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# `fst'` and `snd'` projections of kernels in the first / second domain coordinate

These are convenience definitions for evaluating a `Kernel (α × β) γ` at a fixed second (or
first) coordinate, returning a `Kernel α γ` (or `Kernel β γ`).
-/

open MeasureTheory

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}
variable {δ : Type*} {mδ : MeasurableSpace δ}

/-- Define a `Kernel α γ` from a `Kernel (α × β) γ` by taking the comap of `fun a ↦ (a, b)` for
a given `b : β`. -/
noncomputable def fst' (κ : Kernel (α × β) γ) (b : β) : Kernel α γ :=
  comap κ (fun a ↦ (a, b)) (measurable_id.prodMk measurable_const)

@[simp]
theorem fst'_apply (κ : Kernel (α × β) γ) (b : β) (a : α) : fst' κ b a = κ (a, b) := rfl

@[simp]
lemma fst'_zero (b : β) : fst' (0 : Kernel (α × β) γ) b = 0 := by simp [fst']

instance (κ : Kernel (α × β) γ) (b : β) [IsMarkovKernel κ] : IsMarkovKernel (fst' κ b) := by
  rw [fst']; infer_instance

instance (κ : Kernel (α × β) γ) (b : β) [IsFiniteKernel κ] : IsFiniteKernel (fst' κ b) := by
  rw [fst']; infer_instance

instance (κ : Kernel (α × β) γ) (b : β) [IsSFiniteKernel κ] : IsSFiniteKernel (fst' κ b) := by
  rw [fst']; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((fst' κ b) a) := by
  rw [fst'_apply]; infer_instance

instance (priority := 100) {κ : Kernel (α × β) γ} [∀ b, IsMarkovKernel (fst' κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ ↦ ⟨?_⟩⟩
  rw [← fst'_apply, measure_univ]

lemma comap_fst' (κ : Kernel (α × β) γ) (b : β) {f : δ → α} (hf : Measurable f) :
    comap (fst' κ b) f hf = comap κ (fun d ↦ (f d, b)) (hf.prodMk measurable_const) := by
  ext d s
  rw [comap_apply, fst'_apply, comap_apply]

@[simp]
lemma fst'_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) {b : β} :
    fst' (prodMkLeft α κ) b a = κ b := rfl

@[simp]
lemma fst'_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) :
    fst' (prodMkRight β κ) b = κ := rfl

/-- Define a `Kernel β γ` from a `Kernel (α × β) γ` by taking the comap of `fun b ↦ (a, b)` for
a given `a : α`. -/
noncomputable def snd' (κ : Kernel (α × β) γ) (a : α) : Kernel β γ :=
  comap κ (fun b ↦ (a, b)) (measurable_const.prodMk measurable_id)

@[simp]
theorem snd'_apply (κ : Kernel (α × β) γ) (b : β) (a : α) : snd' κ a b = κ (a, b) := rfl

@[simp]
lemma snd'_zero (a : α) : snd' (0 : Kernel (α × β) γ) a = 0 := by simp [snd']

instance (κ : Kernel (α × β) γ) (a : α) [IsMarkovKernel κ] : IsMarkovKernel (snd' κ a) := by
  rw [snd']; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) [IsFiniteKernel κ] : IsFiniteKernel (snd' κ a) := by
  rw [snd']; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) [IsSFiniteKernel κ] : IsSFiniteKernel (snd' κ a) := by
  rw [snd']; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((snd' κ a) b) := by
  rw [snd'_apply]; infer_instance

instance (priority := 100) {κ : Kernel (α × β) γ} [∀ b, IsMarkovKernel (snd' κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ ↦ ⟨?_⟩⟩
  rw [← snd'_apply, measure_univ]

lemma comap_snd' (κ : Kernel (α × β) γ) (a : α) {f : δ → β} (hf : Measurable f) :
    comap (snd' κ a) f hf = comap κ (fun d ↦ (a, f d)) (measurable_const.prodMk hf) := by
  ext d s
  rw [comap_apply, snd'_apply, comap_apply]

@[simp]
lemma snd'_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) :
    snd' (prodMkLeft α κ) a = κ := rfl

@[simp]
lemma snd'_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) {a : α} :
    snd' (prodMkRight β κ) a b = κ a := rfl

@[simp]
lemma fst'_swapRight (κ : Kernel (α × β) γ) : fst' (swapLeft κ) = snd' κ := rfl

@[simp]
lemma snd'_swapRight (κ : Kernel (α × β) γ) : snd' (swapLeft κ) = fst' κ := rfl

lemma compProd_apply_eq_compProd_snd' (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a = (κ a) ⊗ₘ (snd' η a) := by
  ext s hs
  simp_rw [compProd_apply hs, Measure.compProd_apply hs, snd'_apply]

end Kernel

end ProbabilityTheory
