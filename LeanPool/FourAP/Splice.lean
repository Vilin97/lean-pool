/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
module

public import LeanPool.FourAP.Binary
public import LeanPool.FourAP.Completion

/-!
# The contradiction at the heart of Lemma 2

The last half of the extension lemma needs only three facts about the new
completion: the old prefix remains fixed, each parity restriction is 4AP-free,
and the odd-before-even comparison in equation (2) holds. We isolate this
argument so that the subsequent recursive construction can be read separately
from its safety proof.
-/
@[expose] public section

namespace FourAP

/-- Lemma 2, from “Suppose, for a contradiction, that a 4AP ...” to the end.
`hparity` excludes progressions with even common difference. `hguard` is exactly
the displayed odd-before-even property labelled `eq:odd-even` in the paper. -/
theorem safe_of_parity_and_guard {P Q : List ℕ}
    (hP : Safe bits P) (hp : P.IsPrefix Q) (hq : Q.Nodup)
    (hparity : ∀ ⦃a b c d : ℕ⦄, IsAP4 a b c d → a % 2 = b % 2 →
      Completion bits Q a b → Completion bits Q b c → Completion bits Q c d → False)
    (hguard : ∀ ⦃x y : ℕ⦄, x ∉ P → y ∉ P → x % 2 = 0 → y % 2 = 1 →
      y ≤ 2 * x → Completion bits Q y x) :
    Safe bits Q := by
  refine ⟨hq, ?_⟩
  intro a b c d hap hab hbc hcd
  by_cases heven : a % 2 = b % 2
  · exact hparity hap heven hab hbc hcd
  have heq₁ := hap.2.1
  have heq₂ := hap.2.2
  -- If the third term was already placed, all three old comparisons survive.
  have hc : c ∉ P := by
    intro hc
    have hb := completion_prefix_mem_left hp hc hbc
    have ha := completion_prefix_mem_left hp hb hab
    exact hP.2 hap (completion_prefix_left hp ha hab)
      (completion_prefix_left hp hb hbc) (completion_prefix_left hp hc hcd)
  have hd : d ∉ P := fun hd => hc (completion_prefix_mem_left hp hd hcd)
  by_cases hcEven : c % 2 = 0
  · -- Paper: `d = 2c - b ≤ 2c`, so the guard puts `d` before `c`.
    have hdOdd : d % 2 = 1 := by omega
    have hdc := hguard hc hd hcEven hdOdd (by omega)
    exact completion_asymm (R := bits) (fun {_ _} h => bits_asymm h) hcd hdc
  · have hcOdd : c % 2 = 1 := by omega
    have hbEven : b % 2 = 0 := by omega
    have hdEven : d % 2 = 0 := by omega
    -- If `b` was old, the odd-even tail comparison already gives an AP in 𝒞(P).
    have hb : b ∉ P := by
      intro hb
      have ha := completion_prefix_mem_left hp hb hab
      have hcdOld : Completion bits P c d := by
        apply (completion_of_notMem hc hd).2
        rw [bits_iff_of_diff_parity (by omega : c % 2 ≠ d % 2)]
        omega
      exact hP.2 hap (completion_prefix_left hp ha hab)
        (completion_mem_notMem hb hc) hcdOld
    -- Paper: `c = 2b - a ≤ 2b`, giving the remaining contradiction.
    have hcb := hguard hb hc hbEven hcOdd (by omega)
    exact completion_asymm (R := bits) (fun {_ _} h => bits_asymm h) hbc hcb

end FourAP
