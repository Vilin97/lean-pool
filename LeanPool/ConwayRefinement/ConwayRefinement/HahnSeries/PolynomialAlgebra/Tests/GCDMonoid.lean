/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.GCDMonoid

/-!
# API checks for greatest common divisors in the series ring

Pre-Schreier refinement alone does not provide a greatest common divisor for each pair. The first
check extracts exactly that stronger conclusion from the public GCD-domain theorem. The second
specializes it to `(0, a)` and checks both the zero boundary and the orientation of the universal
property: the chosen gcd is associated to `a`.
-/

public noncomputable section

namespace Tests

open Berarducci

universe v

variable {K : Type v} [Field K] [CharZero K]

/-- Every pair of series has a greatest common divisor. -/
theorem series_pairwise_gcd_exists (a b : Series K) :
    ∃ d : Series K, ∀ e : Series K, e ∣ a ∧ e ∣ b ↔ e ∣ d := by
  obtain ⟨inst⟩ := Berarducci.nonemptyGCDMonoid (K := K)
  letI : GCDMonoid (Series K) := inst
  exact ⟨gcd a b, fun e ↦ (dvd_gcd_iff e a b).symm⟩

/-- A gcd of `(0, a)` is associated to `a` and has the expected universal property. -/
theorem series_gcd_zero_left (a : Series K) :
    ∃ d : Series K, (d ∣ a ∧ a ∣ d) ∧ ∀ e : Series K, e ∣ 0 ∧ e ∣ a ↔ e ∣ d := by
  obtain ⟨d, hd⟩ := series_pairwise_gcd_exists (0 : Series K) a
  refine ⟨d, ⟨?_, ?_⟩, hd⟩
  · exact ((hd d).mpr dvd_rfl).2
  · exact (hd a).mp ⟨dvd_zero _, dvd_rfl⟩

end Tests
