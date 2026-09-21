/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Last-coordinate splitting of finite product spaces

This file records the measurable equivalence
`((i : Fin n) → α i.castSucc) × α (Fin.last n) ≃ᵐ (∀ i, α i)` given by `Fin.snoc`, together
with the fact that it preserves finite products of sigma-finite measures.

This is `Fin.snocEquiv` with the product factors swapped, so that the last coordinate is the
`Prod.snd` factor.

This is a temporary project home. Intended Mathlib placement:

* `MeasurableEquiv.piFinSnoc` and its `simp` lemmas
  → `Mathlib.MeasureTheory.MeasurableSpace.Embedding`, after `piFinSuccAbove`
* `measurePreserving_piFinSnoc`, `volume_preserving_piFinSnoc`
  → `Mathlib.MeasureTheory.Constructions.Pi`, after `volume_preserving_piFinSuccAbove`

TODO: if those lemmas land in Mathlib, delete this file and switch uses to the upstream names.
-/

open MeasureTheory MeasureTheory.Measure

@[expose] public section

namespace MeasurableEquiv

/-- Measurable equivalence
`((i : Fin n) → α i.castSucc) × α (Fin.last n) ≃ᵐ (∀ i, α i)` given by `Fin.snoc`.

Measurable version of `Fin.snocEquiv` with the product factors swapped. -/
def piFinSnoc {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)] :
    ((i : Fin n) → α i.castSucc) × α (Fin.last n) ≃ᵐ (∀ i, α i) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (Fin.init f, f (Fin.last n))
  left_inv p := by simp
  right_inv f := by simp [Fin.snoc_init_self]
  measurable_toFun := measurable_pi_iff.2 fun i ↦ i.lastCases
    (by simpa [Fin.snoc_last] using! measurable_snd)
    (fun j ↦ by
      simpa [Fin.snoc_castSucc] using! (measurable_pi_apply j).comp measurable_fst)
  measurable_invFun := Measurable.prodMk
    (measurable_pi_iff.2 fun j ↦ measurable_pi_apply j.castSucc)
    (measurable_pi_apply _)

@[simp]
theorem piFinSnoc_apply {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)]
    (p : ((i : Fin n) → α i.castSucc) × α (Fin.last n)) :
    piFinSnoc α p = Fin.snoc p.1 p.2 :=
  rfl

@[simp]
theorem piFinSnoc_symm_apply {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)]
    (f : ∀ i, α i) :
    (piFinSnoc α).symm f = (Fin.init f, f (Fin.last n)) :=
  rfl

end MeasurableEquiv

namespace MeasureTheory

/-- Last-coordinate splitting preserves a finite product of sigma-finite measures. -/
theorem measurePreserving_piFinSnoc {n : ℕ} {α : Fin (n + 1) → Type*}
    {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinSnoc α)
      ((Measure.pi fun j : Fin n ↦ μ j.castSucc).prod (μ (Fin.last n))) (Measure.pi μ) := by
  refine ⟨(MeasurableEquiv.piFinSnoc α).measurable, (pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply, Fin.prod_univ_castSucc, ← pi_pi, ← prod_prod]
  congr 1 with p
  simp [Set.mem_prod, Fin.forall_iff_castSucc, MeasurableEquiv.piFinSnoc_apply,
    Fin.snoc_last, Fin.snoc_castSucc]
  exact and_comm

/-- Last-coordinate splitting preserves product volume. -/
theorem volume_preserving_piFinSnoc {n : ℕ} (α : Fin (n + 1) → Type*)
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piFinSnoc α) :=
  measurePreserving_piFinSnoc fun i ↦ (volume : Measure (α i))

end MeasureTheory
