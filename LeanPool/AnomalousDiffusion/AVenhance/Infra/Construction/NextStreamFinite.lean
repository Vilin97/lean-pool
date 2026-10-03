/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.NextStream

/-! Infrastructure for the §2 construction. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

theorem Infra.Construction.nextStreamTerm_support_finite {β : ℝ} (I : Ingredients β) (m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (t : ℝ) (x : Vec 2) :
    (Function.support fun k : ℤ => I.nextStreamTerm m φ hφ t x k).Finite := by
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  refine (Set.finite_Icc (⌊t / tau β I.Λ m⌋ - 1) (⌈t / tau β I.Λ m⌉ + 1)).subset ?_
  intro k hk
  have hz : I.zetaMK m k t ≠ 0 := by
    intro h0
    apply hk
    simp [Ingredients.nextStreamTerm, h0]
  have hne : I.zeta ((t - k * tau β I.Λ m) / tau β I.Λ m) ≠ 0 := hz
  have hle := I.zeta_le_ind ((t - k * tau β I.Λ m) / tau β I.Λ m)
  have hpos : 0 < I.zeta ((t - k * tau β I.Λ m) / tau β I.Λ m) :=
    lt_of_le_of_ne (I.zeta_nonneg _) (Ne.symm hne)
  have hmem : (t - k * tau β I.Λ m) / tau β I.Λ m ∈ Set.Icc (-(2 / 3) : ℝ) (2 / 3) := by
    by_contra hnot
    have : indIcc (-(2 / 3)) (2 / 3) ((t - k * tau β I.Λ m) / tau β I.Λ m) = 0 := by
      simp [indIcc, hnot]
    linarith
  have hdiv : (t - k * tau β I.Λ m) / tau β I.Λ m = t / tau β I.Λ m - k := by
    field_simp
  rw [hdiv] at hmem
  obtain ⟨h1, h2⟩ := hmem
  constructor
  · have : (⌊t / tau β I.Λ m⌋ : ℝ) - 1 ≤ k := by
      have := Int.floor_le (t / tau β I.Λ m)
      linarith
    exact_mod_cast this
  · have : (k : ℝ) ≤ (⌈t / tau β I.Λ m⌉ : ℝ) + 1 := by
      have := Int.le_ceil (t / tau β I.Λ m)
      linarith
    exact_mod_cast this

end AVenhance
