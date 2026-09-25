/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HasseArf.LowerRamificationGroupAntitone
public import Mathlib.FieldTheory.Fixed
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Localization.FractionRing
/-!
# Eventual triviality of lower ramification groups

For a finite field extension and a Noetherian valuation subring, each
nonidentity automorphism moves an element of the valuation ring by a nonzero
amount. Krull's intersection theorem then excludes that automorphism from
some lower group. Finiteness gives a common bound for all automorphisms.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- All sufficiently high lower ramification groups are trivial. -/
theorem lowerRamificationGroup_eventually_bot
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (A : ValuationSubring L) [IsNoetherianRing A] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → lowerRamificationGroup K A n = ⊥ := by
  classical
  let G := A.decompositionSubgroup K
  let m : Ideal A := IsLocalRing.maximalIdeal A
  have hm : m ≠ ⊤ := Ideal.IsPrime.ne_top'
  have hseparated (σ : G)
      (hall : ∀ n : ℕ, σ ∈ lowerRamificationGroup K A n) : σ = 1 := by
    have hfix (x : A) : σ • x = x := by
      have hmem : σ • x - x ∈ ⨅ n : ℕ, m ^ n := by
        rw [Ideal.mem_iInf]
        intro n
        cases n with
        | zero =>
            simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
        | succ n =>
            simpa only [Nat.succ_eq_add_one] using hall n x
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing m hm] at hmem
      exact sub_eq_zero.mp ((Submodule.mem_bot A).mp hmem)
    have hring :
        (σ.1 : L ≃ₐ[K] L).toRingHom =
          (1 : L ≃ₐ[K] L).toRingHom := by
      apply IsFractionRing.ringHom_ext (A := A)
      intro x
      have hx := congrArg (fun y : A => (y : L)) (hfix x)
      change (σ.1 : L ≃ₐ[K] L) (x : L) = (x : L) at hx
      exact hx
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    exact RingHom.congr_fun hring x
  have hcutoff (σ : G) (hσ : σ ≠ 1) :
      ∃ n : ℕ, σ ∉ lowerRamificationGroup K A n := by
    by_contra hnone
    apply hσ
    apply hseparated σ
    intro n
    by_contra hn
    exact hnone ⟨n, hn⟩
  let cutoff (σ : G) : ℕ :=
    if hσ : σ = 1 then 0 else (hcutoff σ hσ).choose
  let N : ℕ := Finset.univ.sup cutoff
  have hbot : lowerRamificationGroup K A N = ⊥ := by
    apply le_antisymm _ bot_le
    intro σ hσ
    have hσone : σ = 1 := by
      by_contra hne
      have hcut : σ ∉ lowerRamificationGroup K A (cutoff σ) := by
        simpa only [cutoff, dite_eq_right hne] using (hcutoff σ hne).choose_spec
      have hle : cutoff σ ≤ N := Finset.le_sup (Finset.mem_univ σ)
      exact hcut (lowerRamificationGroup_antitone K A hle hσ)
    exact Subgroup.mem_bot.mpr hσone
  refine ⟨N, fun n hn => ?_⟩
  apply le_antisymm _ bot_le
  exact (lowerRamificationGroup_antitone K A hn).trans (le_of_eq hbot)

end ClassFieldTheory
