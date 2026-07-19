/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

import LeanPool.ZhangYeungInequality.Theorem5

/-!
# LeanPool.ZhangYeungInequality.Test.Theorem5

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.Test.Theorem5`.
-/

namespace ZhangYeungTest

open MeasureTheory ProbabilityTheory
open ZhangYeung
open scoped ZhangYeungPFR

universe u

section Signatures

variable {Ω : Type*} [MeasurableSpace Ω]
  {n : ℕ}
  {S_U S_Z : Type u} {S : Fin n → Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [∀ i, MeasurableSpace (S i)]
  [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [∀ i, MeasurableSingletonClass (S i)]

example
    (hn : 2 ≤ n)
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Fin n) :
    n * I[U : Z; μ] - ∑ j, I[U : Z | X j; μ] - n * I[U : Z | X i; μ]
      ≤ I[X i : ⟨U, Z⟩; μ]
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] :=
  theorem5 hU hZ hX μ i hn

example
    (hn : 2 ≤ n)
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    n * I[U : Z; μ] - 2 * (∑ j, I[U : Z | X j; μ])
      ≤ (1 / n : ℝ) * (∑ i, I[X i : ⟨U, Z⟩; μ])
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] :=
  theorem5_averaged hn hU hZ hX μ

end Signatures

section BaseCaseCompatibility

variable {Ω : Type*} [MeasurableSpace Ω]
  {S_U S_Z S₁ S₂ : Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [Finite S_U] [Finite S_Z] [Finite S₁] [Finite S₂]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]

example
    {U : Ω → S_U} {Z : Ω → S_Z} {X₁ : Ω → S₁} {X₂ : Ω → S₂}
    (hU : Measurable U) (hZ : Measurable Z) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    2 * I[U : Z; μ] - 3 * I[U : Z | X₁; μ] - I[U : Z | X₂; μ]
      ≤ I[X₁ : ⟨U, Z⟩; μ] + I[X₁ : X₂; μ] := by
  let S : Fin 2 → Type u
    | 0 => S₁
    | 1 => S₂
  let X : ∀ i : Fin 2, Ω → S i
    | 0 => X₁
    | 1 => X₂
  letI : ∀ i, MeasurableSpace (S i)
    | 0 => inferInstance
    | 1 => inferInstance
  letI : ∀ i, Finite (S i)
    | 0 => inferInstance
    | 1 => inferInstance
  letI : ∀ i, MeasurableSingletonClass (S i)
    | 0 => inferInstance
    | 1 => inferInstance
  have hX : ∀ i : Fin 2, Measurable (X i)
    | 0 => hX₁
    | 1 => hX₂
  have hTupleEnt : H[(fun ω : Ω => fun j : Fin 2 => X j ω); μ] = H[⟨X₁, X₂⟩; μ] := by
    let Xtuple : Ω → ∀ j : Fin 2, S j := fun ω j => X j ω
    let πe := MeasurableEquiv.piFinTwo S
    let π : (∀ j : Fin 2, S j) → S 0 × S 1 := πe
    have hXtuple : Measurable Xtuple := measurable_pi_lambda _ hX
    change H[Xtuple; μ] = H[π ∘ Xtuple; μ]
    exact (entropy_comp_of_injective μ hXtuple π πe.injective).symm
  have hRaw :
      2 * I[U : Z; μ] - (I[U : Z | X₁; μ] + I[U : Z | X₂; μ]) - 2 * I[U : Z | X₁; μ]
        ≤ I[X₁ : ⟨U, Z⟩; μ] + H[X₁; μ] + H[X₂; μ]
          - H[(fun ω : Ω => fun j : Fin 2 => X j ω); μ] := by
    have h := theorem5 (n := 2) (S := S) hU hZ hX μ 0 (by decide)
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
    simpa [X, S, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hPair :
      2 * I[U : Z; μ] - 3 * I[U : Z | X₁; μ] - I[U : Z | X₂; μ]
        ≤ I[X₁ : ⟨U, Z⟩; μ] + H[X₁; μ] + H[X₂; μ]
          - H[(fun ω : Ω => fun j : Fin 2 => X j ω); μ] := by
    linarith
  have hMI :
      H[X₁; μ] + H[X₂; μ]
        - H[(fun ω : Ω => fun j : Fin 2 => X j ω); μ] = I[X₁ : X₂; μ] := by
    rw [mutualInfo_def, hTupleEnt]
  linarith [hPair, hMI]

end BaseCaseCompatibility

section AssumptionSpecialization

example {Ω : Type*} [MeasurableSpace Ω]
    {U Z : Ω → Fin 2} {X : Fin 3 → Ω → Fin 2}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h0 : I[U : Z|X 0;μ] = 0)
    (h1 : I[U : Z|X 1;μ] = 0)
    (h2 : I[U : Z|X 2;μ] = 0)
    (htail : ∑ j : Fin 3, H[X j; μ] - H[(fun ω : Ω => fun j : Fin 3 => X j ω); μ] = 0) :
    3 * I[U : Z; μ] ≤ I[X 0 : ⟨U, Z⟩; μ] := by
  have h := theorem5 (n := 3) (S := fun _ => Fin 2) hU hZ hX μ 0 (by decide)
  rw [Fin.sum_univ_three] at h
  rw [h0, h1, h2] at h
  have htail' :
      I[X 0 : ⟨U, Z⟩; μ] + ∑ j : Fin 3, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin 3 => X j ω); μ] = I[X 0 : ⟨U, Z⟩; μ] := by
    linarith
  rw [htail'] at h
  simpa using h

end AssumptionSpecialization

section AveragedFromPointForm

variable {Ω : Type*} [MeasurableSpace Ω]
  {S_U S_Z : Type u} {S : Fin 3 → Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [∀ i, MeasurableSpace (S i)]
  [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [∀ i, MeasurableSingletonClass (S i)]

example
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin 3, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    3 * I[U : Z; μ] - 2 * (∑ j, I[U : Z | X j; μ])
      ≤ (1 / 3 : ℝ) * (∑ i, I[X i : ⟨U, Z⟩; μ])
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin 3 => X j ω); μ] := by
  let lhs : ℝ := 3 * I[U : Z; μ] - 2 * (∑ j : Fin 3, I[U : Z | X j; μ])
  let tail : ℝ := ∑ j : Fin 3, H[X j; μ] - H[(fun ω : Ω => fun j : Fin 3 => X j ω); μ]
  let rhs : Fin 3 → ℝ := fun i => I[X i : ⟨U, Z⟩; μ]
  have hsum :
      ∑ i : Fin 3,
          (3 * I[U : Z; μ]
            - ∑ j : Fin 3, I[U : Z | X j; μ]
            - 3 * I[U : Z | X i; μ])
        ≤ ∑ i : Fin 3, (rhs i + tail) := by
    refine Finset.sum_le_sum ?_
    intro i _
    simpa [rhs, tail, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (theorem5 (n := 3) (S := S) hU hZ hX μ i (by decide))
  have hleft :
      ∑ i : Fin 3,
          (3 * I[U : Z; μ]
            - ∑ j : Fin 3, I[U : Z | X j; μ]
            - 3 * I[U : Z | X i; μ])
        = 3 * lhs := by
    have hsumCond :
        ∑ x : Fin 3, 3 * I[U : Z | X x; μ]
          = 3 * ∑ x : Fin 3, I[U : Z | X x; μ] := by
      rw [Finset.mul_sum]
    calc
      ∑ i : Fin 3,
          (3 * I[U : Z; μ]
            - ∑ j : Fin 3, I[U : Z | X j; μ]
            - 3 * I[U : Z | X i; μ])
          = 3 ^ 2 * I[U : Z; μ]
            - ∑ x : Fin 3, 3 * I[U : Z | X x; μ]
            - 3 * ∑ j : Fin 3, I[U : Z | X j; μ] := by
            simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            ring
      _ = 3 ^ 2 * I[U : Z; μ]
            - 3 * ∑ x : Fin 3, I[U : Z | X x; μ]
            - 3 * ∑ j : Fin 3, I[U : Z | X j; μ] := by
            rw [hsumCond]
      _ = 3 * lhs := by
            change 3 ^ 2 * I[U : Z; μ]
                - 3 * ∑ x : Fin 3, I[U : Z | X x; μ]
                - 3 * ∑ j : Fin 3, I[U : Z | X j; μ]
              = 3 * (3 * I[U : Z; μ]
                - 2 * ∑ j : Fin 3, I[U : Z | X j; μ])
            ring
  have hright : ∑ i : Fin 3, (rhs i + tail) = (∑ i : Fin 3, rhs i) + 3 * tail := by
    simp only [rhs, tail, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hscaled : 3 * lhs ≤ (∑ i : Fin 3, rhs i) + 3 * tail := by
    simpa [hleft, hright] using hsum
  have hfinal : lhs ≤ (1 / 3 : ℝ) * (∑ i : Fin 3, rhs i) + tail := by
    nlinarith [hscaled]
  simpa [lhs, rhs, tail, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_add, add_mul] using hfinal

end AveragedFromPointForm

end ZhangYeungTest
