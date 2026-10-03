/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # The comparison measure of Appendix A and the constants of Section 6

`λ`, `α`, `C*` (6.3), `M₀` (6.2), Table 1 (the sixteen arcsine components of `ρ`), the partial
sums `S_j`, and the energy `I(ρ)` by formula (A.2).
-/

public section

open Finset

namespace Zeta5Irrational

/-- `λ = 37/40`. -/
noncomputable abbrev lam : ℝ :=
  37 / 40

/-- `α = 3/40`. -/
noncomputable abbrev alph : ℝ :=
  3 / 40

/-- The constant `C*` of (6.3). -/
@[expose] noncomputable def Cstar : ℝ :=
  -2 * lam + 12 * alph * lam * (1 - Real.log alph) + 3 * lam ^ 2 -
    2 * lam ^ 2 * Real.log (2 * lam)

/-- `M₀ = -1329/200` of (6.2). -/
noncomputable abbrev M0 : ℝ :=
  -1329 / 200

/-- Table 1: `10¹² a_j`, `10¹² b_j`, `10¹² c_j`. -/
@[expose] def table1 : List (ℕ × ℕ × ℕ) :=
  [(3906748086, 8992695531, 10515596180), (2312248264, 15340997855, 29471737793),
    (1402286665, 25730180724, 42934365099), (881725356, 41909578246, 58204231966),
    (578197906, 65851089563, 69037621310), (396324613, 99481037884, 78873099189),
    (283911191, 144325727458, 84856120711), (212206188, 201105762729, 88396082127),
    (165097686, 269345996903, 88303382125), (133347132, 347089554156, 85472321255),
    (111522114, 430806704415, 78899184238), (96349355, 515561896511, 70353471918),
    (85815639, 595448778546, 58838976615), (78667711, 664241383483, 44421321106),
    (74129565, 716160577112, 30462865791), (71741310, 746637295669, 5959622577)]

/-- `a_j`, `b_j`, `c_j` (1-indexed; `0` outside the table). -/
@[expose] noncomputable def aρ (j : ℕ) : ℝ :=
  ((table1.getD (j - 1) (0, 0, 0)).1 : ℝ) / 10 ^ 12

/-- Right endpoint of the `j`th arcsine component, read from the exact rational table. -/
@[expose] noncomputable def bρ (j : ℕ) : ℝ :=
  ((table1.getD (j - 1) (0, 0, 0)).2.1 : ℝ) / 10 ^ 12

/-- Mass of the `j`th arcsine component, read from the exact rational table. -/
@[expose] noncomputable def cρ (j : ℕ) : ℝ :=
  ((table1.getD (j - 1) (0, 0, 0)).2.2 : ℝ) / 10 ^ 12

/-- Partial sums `S_j = ∑_{i ≤ j} c_i`. -/
@[expose] noncomputable def Sρ (j : ℕ) : ℝ :=
  ∑ i ∈ Icc 1 j, cρ i

/-- The logarithmic energy `I(ρ)` of the measure `ρ`, formula (A.2). -/
@[expose] noncomputable def Irho : ℝ :=
  ∑ j ∈ Icc 1 16, (Sρ j ^ 2 - Sρ (j - 1) ^ 2) * Real.log ((bρ j - aρ j) / 4)

/-- The total mass of `ρ` is `λ` (Appendix A.1). -/
lemma Sρ_sixteen : Sρ 16 = lam := by
  simp [Sρ, cρ, table1, Finset.sum_Icc_succ_top]
  norm_num

end Zeta5Irrational
