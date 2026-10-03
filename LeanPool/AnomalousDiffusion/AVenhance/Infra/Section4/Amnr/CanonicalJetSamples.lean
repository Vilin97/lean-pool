/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SmoothLocalization

/-! A finite, exhaustive index set for the bounded canonical jet budget. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- All ordered two-dimensional spatial words of an exact length. -/
def amnrSpatialWords : ℕ → Finset (List (Fin 2))
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion (fun i : Fin 2 => (amnrSpatialWords n).image (List.cons i))

@[simp] theorem amnrSpatialWords_mem (α : List (Fin 2)) (n : ℕ) :
    α ∈ amnrSpatialWords n ↔ α.length = n := by
  induction n generalizing α with
  | zero => simp [amnrSpatialWords]
  | succ n ih =>
    cases α with
    | nil => simp [amnrSpatialWords]
    | cons i α => simp [amnrSpatialWords, ih]

/-- The finite sample contains precisely the admissible canonical jets. -/
def amnrCanonicalSamples (N cut : ℕ) : Finset (List (Fin 2) × ℕ) :=
  ((Finset.range (N + 1)).biUnion (fun k =>
    (amnrSpatialWords k).product (Finset.range (cut + 1)))).filter
      (fun q => q.1.length + 2 * q.2 ≤ N)

@[simp] theorem amnrCanonicalSamples_mem (α : List (Fin 2)) (r N cut : ℕ) :
    (α, r) ∈ amnrCanonicalSamples N cut ↔ α.length + 2 * r ≤ N ∧ r ≤ cut := by
  classical
  simp only [amnrCanonicalSamples, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨k, hk, hp⟩, hbudget⟩
    have hp' := Finset.mem_product.mp hp
    have heq := (amnrSpatialWords_mem α k).mp hp'.1
    have hr := Finset.mem_range.mp hp'.2
    exact ⟨hbudget, by omega⟩
  · rintro ⟨hbudget, hr⟩
    refine ⟨⟨α.length, by omega, ?_⟩, hbudget⟩
    exact Finset.mem_product.mpr ⟨(amnrSpatialWords_mem α α.length).mpr rfl,
      Finset.mem_range.mpr (by omega)⟩

/-- Normalizing and summing the finite canonical jet family gives a pointwise
majorant without replacing an L2 estimate by a pointwise assumption. -/
def amnrCanonicalEnvelope (N cut : ℕ) (S H : ℝ) (b : AmnrSpace → Vec 2)
    (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ :=
  ∑ q ∈ amnrCanonicalSamples N cut,
    |amnrWord b (amnrMixedWord q.1 q.2) f z| / amnrWeight S H (amnrMixedWord q.1 q.2)

theorem amnrCanonicalEnvelope_nonneg {S H : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (N cut : ℕ) (b : AmnrSpace → Vec 2) (f : AmnrSpace → ℝ) (z : AmnrSpace) :
    0 ≤ amnrCanonicalEnvelope N cut S H b f z := by
  exact Finset.sum_nonneg (fun q _ => div_nonneg (abs_nonneg _)
    (amnrWeight_nonneg hS hH _))

theorem amnrCanonicalEnvelope_dominates {S H : ℝ} (hS : 0 < S) (hH : 0 < H)
    (N cut : ℕ) (b : AmnrSpace → Vec 2) (f : AmnrSpace → ℝ) (z : AmnrSpace)
    (α : List (Fin 2)) (r : ℕ) (hbudget : α.length + 2 * r ≤ N) (hcut : r ≤ cut) :
    |amnrWord b (amnrMixedWord α r) f z| ≤
      amnrCanonicalEnvelope N cut S H b f z * amnrWeight S H (amnrMixedWord α r) := by
  have hW : 0 < amnrWeight S H (amnrMixedWord α r) := by
    rw [amnrMixedWord_weight]
    positivity
  apply (div_le_iff₀ hW).mp
  unfold amnrCanonicalEnvelope
  exact Finset.single_le_sum (f := fun q : List (Fin 2) × ℕ =>
    |amnrWord b (amnrMixedWord q.1 q.2) f z| / amnrWeight S H (amnrMixedWord q.1 q.2)) (fun q _ =>
        div_nonneg (abs_nonneg _)
    (amnrWeight_nonneg hS.le hH.le _))
      ((amnrCanonicalSamples_mem α r N cut).mpr ⟨hbudget, hcut⟩)

end AVenhance.Infra.Section4
