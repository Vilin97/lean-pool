/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold

/-!
# Splitting a multiset along a fixed-point-free involution

A multiset invariant under a fixed-point-free involution `τ` splits as `N + N.map τ`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- A multiset `M` invariant under an involution `τ` that is fixed-point-free on its support
splits as `N + N.map τ`. -/
theorem Multiset.exists_add_map_of_involutive {β : Type*} (τ : β → β) (M : Multiset β)
    (hτ : ∀ x ∈ M, τ (τ x) = x) (hinv : M.map τ = M) (hfix : ∀ x ∈ M, τ x ≠ x) :
    ∃ N : Multiset β, M = N + N.map τ := by
  classical
  revert hτ hinv hfix
  induction M using Multiset.strongInductionOn with
  | _ M ih =>
    intro hτ hinv hfix
    rcases eq_or_ne M 0 with hM | hM
    · exact ⟨0, by simp [hM]⟩
    · obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hM
      have hne : τ x ≠ x := hfix x hx
      set M0 := M.erase x with hM0
      set M' := M0.erase (τ x) with hM'
      have hτx : τ x ∈ M := by rw [← hinv]; exact Multiset.mem_map_of_mem τ hx
      have hMdecomp : M = x ::ₘ (τ x) ::ₘ M' := by
        rw [hM', Multiset.cons_erase (by
          rw [hM0]; exact (Multiset.mem_erase_of_ne hne).2 hτx), hM0, Multiset.cons_erase hx]
      have hinv' : M'.map τ = M' := by
        rw [hMdecomp] at hinv
        simp only [Multiset.map_cons, hτ x hx, Multiset.cons_swap] at hinv
        exact (Multiset.cons_inj_right (τ x)).mp <| (Multiset.cons_inj_right x).mp hinv
      have hmem' : ∀ y ∈ M', y ∈ M := fun y hy ↦ by rw [hMdecomp]; simp [hy]
      obtain ⟨N', hN'⟩ := ih M' (hMdecomp ▸ lt_trans (Multiset.lt_cons_self _ _)
        (Multiset.lt_cons_self _ _)) (fun y hy ↦ hτ y (hmem' y hy)) hinv'
        (fun y hy ↦ hfix y (hmem' y hy))
      exact ⟨x ::ₘ N', by
        rw [hMdecomp, hN']
        simp only [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons, Multiset.cons_swap]⟩
