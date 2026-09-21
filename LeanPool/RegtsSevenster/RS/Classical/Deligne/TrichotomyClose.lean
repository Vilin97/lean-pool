/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModSchur
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29State

/-!
# The trichotomy, closed over a descent

The case analysis of the dévissage trichotomy: over any state,
classically either all symmetric powers of the remainder survive,
or all alternating powers survive, or some power of each dies —
and then the Schur collapse and the power descent kill the
remainder.  The descent is a parameter, discharged by the
sandwich retract.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

/-- The antisymmetriser at arity one is the identity. -/
theorem antisymmetriser_one : antisymmetriser 1 = 1 := by
  rw [antisymmetriser]
  rw [show (Finset.univ : Finset (Equiv.Perm (Fin 1))) =
    {1} from Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_univ _, fun σ _ =>
        Subsingleton.elim σ 1⟩]
  simp [MonoidAlgebra.one_def]

/-- The antisymmetriser at arity zero is the identity. -/
theorem antisymmetriser_zero : antisymmetriser 0 = 1 := by
  rw [antisymmetriser]
  rw [show (Finset.univ : Finset (Equiv.Perm (Fin 0))) =
    {1} from Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_univ _, fun σ _ =>
        Subsingleton.elim σ 1⟩]
  simp [MonoidAlgebra.one_def]

variable {D : Type u}

/-- A dead arity-one symmetric power kills the module. -/
theorem isZero_of_isZero_symPowOne
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (h : IsZero (symPow A X 1)) : IsZero X := by
  have h0 : symPowIdem A X 1 = 0 :=
    (symPowIdem_eq_zero_iff A X 1).mpr h
  rw [show symPowIdem A X 1 =
      modPowAlg A X 1 (symmetriser 1) from rfl,
    symmetriser_one, map_one] at h0
  have hm : IsZero (modPow A X 1) := by
    rw [Limits.IsZero.iff_id_eq_zero]
    exact h0
  exact hm.of_iso (modPowOne A X).symm

/-- A dead arity-one alternating power kills the module. -/
theorem isZero_of_isZero_altPow_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (h : IsZero (altPow A X 1)) : IsZero X := by
  have h0 : altPowIdem A X 1 = 0 :=
    (altPowIdem_eq_zero_iff A X 1).mpr h
  rw [show altPowIdem A X 1 =
      modPowAlg A X 1 (antisymmetriser 1) from rfl,
    antisymmetriser_one, map_one] at h0
  have hm : IsZero (modPow A X 1) := by
    rw [Limits.IsZero.iff_id_eq_zero]
    exact h0
  exact hm.of_iso (modPowOne A X).symm

/-- A dead tensor unit kills every object. -/
theorem isZero_of_isZero_unit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (X : D)
    (h : IsZero (𝟙_ D)) :
    IsZero X :=
  (isZero_whiskerLeft X h).of_iso (ρ_ X).symm

/-- A dead arity-zero symmetric power kills the module. -/
theorem isZero_of_isZero_symPowZero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] (A : D) [MonObj A] (X : D) [ModObj A X]
    (h : IsZero (symPow A X 0)) : IsZero X :=
  isZero_of_isZero_unit X
    (h.of_iso (symPowZero A X).symm)

/-- A dead arity-zero alternating power kills the module. -/
theorem isZero_of_isZero_altPow_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] (A : D) [MonObj A] (X : D) [ModObj A X]
    (h : IsZero (altPow A X 0)) : IsZero X := by
  have h0 : altPowIdem A X 0 = 0 :=
    (altPowIdem_eq_zero_iff A X 0).mpr h
  rw [show altPowIdem A X 0 =
      modPowAlg A X 0 (antisymmetriser 0) from rfl,
    antisymmetriser_zero, map_one] at h0
  have hm : IsZero (modPow A X 0) := by
    rw [Limits.IsZero.iff_id_eq_zero]
    exact h0
  exact isZero_of_isZero_unit X
    (hm.of_iso (modPowZero A X).symm)

section Main

/-- **The trichotomy holds over a power descent**: classically,
either all symmetric powers of the remainder survive, or all
alternating powers survive, or the Schur collapse and the
descent kill the remainder. -/
theorem devissageTrichotomy_of_descent
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (P : SchurPackage.{v})
    (L : OddLine D) (X : D)
    (hdesc : ∀ (B : D) (_ : MonObj B) (_ : IsCommMonObj B)
      (R R' : Mod D B) (d : ModDualityDatum B R R')
      (_ : ModZigzagDatum B d) (k : ℕ),
      IsZero (modPow B R.X (k + 2)) → IsZero R.X) :
    DevissageTrichotomy D L X := by
  intro st
  letI := st.monObj
  letI := st.comm
  by_cases hS : ∀ n : ℕ,
    ¬ IsZero (symPow st.base st.rest.X n)
  · exact Or.inl hS
  right
  by_cases hA : ∀ n : ℕ,
    ¬ IsZero (altPow st.base st.rest.X n)
  · exact Or.inl hA
  right
  push Not at hS hA
  obtain ⟨n₀, hn₀⟩ := hS
  obtain ⟨m₀, hm₀⟩ := hA
  match n₀, hn₀ with
  | 0, hn =>
    exact isZero_of_isZero_symPowZero st.base st.rest.X hn
  | 1, hn =>
    exact isZero_of_isZero_symPowOne st.base st.rest.X hn
  | (n + 2), hn =>
    match m₀, hm₀ with
    | 0, hm =>
      exact isZero_of_isZero_altPow_zero st.base
        st.rest.X hm
    | 1, hm =>
      exact isZero_of_isZero_altPow_one st.base
        st.rest.X hm
    | (m + 2), hm =>
      have hp : IsZero (modPow st.base st.rest.X
          ((n + 1) * (m + 1) + 1)) :=
        isZero_modPow_of_isZero_sym_alt st.base st.rest.X
          P (n := n + 1) (m := m + 1) hn hm
      have hcast : ∀ {j k : ℕ}, j = k + 2 →
          IsZero (modPow st.base st.rest.X j) →
          IsZero (modPow st.base st.rest.X (k + 2)) := by
        rintro j k rfl h
        exact h
      exact hdesc st.base _ _ st.rest st.restDual st.datum
        st.zigzag (n * m + n + m)
        (hcast (by ring) hp)

end Main

end RS
