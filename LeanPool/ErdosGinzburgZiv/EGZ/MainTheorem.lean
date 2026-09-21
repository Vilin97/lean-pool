/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Main.Assembly
import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.Existence
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.RelativeProof

namespace EGZ

/-- The unconditional upper bound, combining relative expansion and
balanced combinations with the proved Helly and flag-decomposition inputs. -/
theorem main_upper_bound (d : ℕ) (hd : 0 < d) : MainUpperBound d :=
  mainUpperBound_of_expansion_balanced Expansion.relative_expansion_theorem
    balanced_combination_lemma d hd

/-- Theorem 1.2 of D. Zakharov, *Convex geometry and the
Erdős--Ginzburg--Ziv problem*:

`𝔰(𝔽_p^d) = p * 𝔴(𝔽_p^d) + o(p)` as `p → ∞` through primes, for every fixed
positive dimension `d`.

The polynomial bound and elementary lower estimate are discharged in
`EGZ.Asymptotics`. Relative expansion, balanced combinations, Helly, and
flag decomposition supply the unconditional upper bound. -/
theorem theorem_1_2 (d : ℕ) (hd : 0 < d) : MainAsymptotic d :=
  mainAsymptotic_of_mainUpperBound d hd (main_upper_bound d hd)

/-- Theorem 1.2 with exactly the relative expansion theorem and the
balanced-combination lemma as explicit inputs. The entire deduction,
including flag decomposition and Helly, is kernel checked without `sorry`. -/
theorem theorem_1_2_of_expansion_balanced
    (hExpansion : Expansion.RelativeExpansionStatement)
    (hBalanced : BalancedCombinationLemma) (d : ℕ) (hd : 0 < d) :
    MainAsymptotic d :=
  mainAsymptotic_of_expansion_balanced hExpansion hBalanced d hd

/-- The reusable implication when relative expansion is supplied explicitly. -/
theorem theorem_1_2_of_expansion
    (hExpansion : Expansion.RelativeExpansionStatement) (d : ℕ) (hd : 0 < d) :
    MainAsymptotic d :=
  mainAsymptotic_of_expansion_balanced hExpansion balanced_combination_lemma d hd

end EGZ
