/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Basis
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ODE
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real sine/cosine modes for symmetric Fourier cutoffs

The integer frequency box is split into the zero frequency and one representative from each pair
`{k, -k}`. Each nonzero representative contributes its real and imaginary character. This module
builds the concrete real-valued modes and their smooth periodic ambient representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance realModesMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance realModesMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance realModesProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The lexicographically positive half of the nonzero integer pairs. -/
def positiveFrequencyPair (p : ℤ × ℤ) : Prop :=
  0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)

/-- One representative from each pair `{p,-p}` in the symmetric frequency box. -/
noncomputable def positiveFrequencyRepresentatives (N : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact (symmetricFrequencyBox N).filter positiveFrequencyPair

/-- The unique ordered pair corresponding to a two-coordinate integer frequency. -/
def frequencyPair (k : Fin 2 → ℤ) : ℤ × ℤ := (k 0, k 1)

theorem pairFrequency_frequencyPair (k : Fin 2 → ℤ) :
    pairFrequency (frequencyPair k) = k := by
  funext i
  fin_cases i <;> simp [pairFrequency, frequencyPair]

/-- The complex partial sum applied to a complex-valued function. -/
def complexFourierPartialSumComplex (N : ℕ) (f : Torus → ℂ) (x : Torus) : ℂ :=
  ∑ p ∈ symmetricFrequencyBox N,
    UnitAddTorus.mFourierCoeff f (pairFrequency p) *
      UnitAddTorus.mFourier (pairFrequency p) x

theorem mem_positiveFrequencyRepresentatives {N : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ positiveFrequencyRepresentatives N) :
    p ∈ symmetricFrequencyBox N ∧ positiveFrequencyPair p := by
  simpa [positiveFrequencyRepresentatives] using hp

/-- A smaller symmetric frequency box is contained in every larger one. -/
theorem symmetricFrequencyBox_subset {M N : ℕ} (hMN : M ≤ N) :
    symmetricFrequencyBox M ⊆ symmetricFrequencyBox N := by
  intro p hp
  simp only [symmetricFrequencyBox, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  rcases hp with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  have hcast : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hMN
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Positive frequency representatives are preserved by enlarging the cutoff. -/
theorem positiveFrequencyRepresentatives_subset {M N : ℕ} (hMN : M ≤ N)
    {p : ℤ × ℤ} (hp : p ∈ positiveFrequencyRepresentatives M) :
    p ∈ positiveFrequencyRepresentatives N := by
  classical
  have hp' := mem_positiveFrequencyRepresentatives hp
  unfold positiveFrequencyRepresentatives
  exact Finset.mem_filter.mpr ⟨symmetricFrequencyBox_subset hMN hp'.1, hp'.2⟩

theorem positiveFrequencyPair_ne_zero {p : ℤ × ℤ} (hp : positiveFrequencyPair p) : p ≠ (0, 0) := by
  rcases hp with h | ⟨h₁, h₂⟩
  · intro he
    cases p with
    | mk a b =>
      simp only [Prod.mk.injEq] at he
      omega
  · intro he
    cases p with
    | mk a b =>
      simp only [Prod.mk.injEq] at he
      omega

theorem positiveFrequencyPair_neg_not {p : ℤ × ℤ} (hp : positiveFrequencyPair p) :
    ¬ positiveFrequencyPair (-p) := by
  rcases p with ⟨a, b⟩
  rcases hp with h | ⟨h₁, h₂⟩ <;>
    simp only [positiveFrequencyPair, Prod.fst_neg, Prod.snd_neg] <;> omega

theorem positiveFrequencyRepresentatives_neg_not {N : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ positiveFrequencyRepresentatives N) :
    -p ∉ positiveFrequencyRepresentatives N := by
  intro hneg
  exact (positiveFrequencyPair_neg_not (mem_positiveFrequencyRepresentatives hp).2)
    (mem_positiveFrequencyRepresentatives hneg).2

theorem frequencyBox_partition (N : ℕ) (p : ℤ × ℤ) :
    p ∈ symmetricFrequencyBox N ↔
      p = (0, 0) ∨ p ∈ positiveFrequencyRepresentatives N ∨
        -p ∈ positiveFrequencyRepresentatives N := by
  constructor
  · intro hp
    by_cases hp0 : p = (0, 0)
    · exact Or.inl hp0
    · by_cases hpos : positiveFrequencyPair p
      · exact Or.inr (Or.inl (by simp [positiveFrequencyRepresentatives, hp, hpos]))
      · have hneg : positiveFrequencyPair (-p) := by
          rcases p with ⟨a, b⟩
          simp only [positiveFrequencyPair, Prod.fst_neg, Prod.snd_neg] at hpos ⊢
          have hp0' : a ≠ 0 ∨ b ≠ 0 := by
            by_cases ha0 : a = 0
            · by_cases hb0 : b = 0
              · exact False.elim (hp0 (Prod.ext ha0 hb0))
              · exact Or.inr hb0
            · exact Or.inl ha0
          by_cases ha : 0 < a
          · exact False.elim (hpos (Or.inl ha))
          · by_cases ha0 : a = 0
            · by_cases hb : 0 < b
              · exact False.elim (hpos (Or.inr ⟨ha0, hb⟩))
              · have hbne : b ≠ 0 := by
                  rcases hp0' with ha | hbne
                  · exact False.elim (ha ha0)
                  · exact hbne
                exact Or.inr ⟨by omega, by omega⟩
            · exact Or.inl (by omega)
        have hnegmem : -p ∈ symmetricFrequencyBox N := by
          exact neg_mem_symmetricFrequencyBox hp
        exact Or.inr (Or.inr (by
          simp [positiveFrequencyRepresentatives, hnegmem, hneg]))
  · rintro (hp | hp | hp)
    · subst p
      simp [symmetricFrequencyBox]
    · exact (mem_positiveFrequencyRepresentatives hp).1
    · have h := neg_mem_symmetricFrequencyBox (mem_positiveFrequencyRepresentatives hp).1
      simpa using h

end AVenhance.Infra.Parabolic.FourierGalerkin

end
