/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Algebra.FactorialTrace
import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockFactor
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SemisimpleEnd

/-!
# The factorial proof for strand endomorphisms

Block permutations and the existing block cycle-trace formula give
a `CycleTraceTower` at every strand arity. The connection-rank
bound then forces nilpotent traces to vanish. Nondegeneracy of the
connection pairing supplies semisimplicity by the trace criterion.
The Schur and trace-zeta proof remains in `BlockAssembly`.
-/

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The cycle-trace tower at an arbitrary strand arity. -/
noncomputable def blockCycleTraceTower (n : ℕ) :
    CycleTraceTower (fun k => skeinEnd f (n * k)) (skeinEnd f n) where
  traceA := HomSpace.traceMap f.val n
  trace k := HomSpace.traceMap f.val (n * k)
  rep k := (permToEnd f (n * k)).comp (blockPermHom n k)
  pow k g := blockPow f n g k
  cycleTrace k π g := by
    change skeinTrace f (n * k)
      (permClass f (n * k) (blockPerm n π) * blockPow f n g k) =
        (π.cycleType.map (fun c => skeinTrace f n (g ^ c))).prod *
          skeinTrace f n g ^ (k - π.cycleType.sum)
    simpa only [pow_one] using skeinTrace_blockPerm_mul_pow f n π g

/-- The factorial proof of nilpotent-trace vanishing at every
strand arity, without a Schur package. -/
theorem skeinTrace_eq_zero_of_isNilpotent_factorial (n : ℕ)
    {g : skeinEnd f n} (hg : IsNilpotent g) : skeinTrace f n g = 0 := by
  apply (blockCycleTraceTower f n).traceA_eq_zero_of_exponential_bound
    (((R : ℝ) ^ n) ^ 2) _ hg
  intro k
  have h := blockEnd_finrank_le f n k
  have hreal : (Module.finrank ℂ (skeinEnd f (n * k)) : ℝ) ≤
      ((R ^ n : ℕ) : ℝ) ^ (2 * k) := by exact_mod_cast h
  simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_assoc] using hreal

/-- Every strand endomorphism algebra is semisimple by the
factorial trace obstruction and the connection pairing. -/
theorem skeinEnd_isSemisimpleRing_factorial (n : ℕ) :
    IsSemisimpleRing (skeinEnd f n) := by
  refine isSemisimpleRing_of_trace (HomSpace.traceMap f.val n)
    (fun _ hg => skeinTrace_eq_zero_of_isNilpotent_factorial f n hg) ?_
  intro a ha
  exact HomSpace.eq_zero_of_traces_vanish f a
    (fun G => ha (HomSpace.ofFragment f.val G))

end RS
