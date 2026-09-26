/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Basic

/-!
# Constants
-/

@[expose] public section

namespace EGZ

/-- The Erdős--Ginzburg--Ziv constant `𝔰(𝔽_p^d)`: the least exact sequence
length with the EGZ property.  `exists_egzProperty` supplies the witness used by
`Nat.find`, so the definition does not depend on the default behavior of an
infimum of an empty set. -/
noncomputable def egzConstant (p d : ℕ) : ℕ :=
  @Nat.find (EGZProperty p d) (Classical.decPred _) (exists_egzProperty p d)

/-- The least EGZ length itself has the EGZ property. -/
theorem egzConstant_spec (p d : ℕ) : EGZProperty p d (egzConstant p d) := by
  classical
  exact Nat.find_spec (exists_egzProperty p d)

/-- Minimality of the EGZ constant. -/
theorem egzConstant_min {p d n : ℕ} (h : EGZProperty p d n) :
    egzConstant p d ≤ n := by
  classical
  exact Nat.find_min' (exists_egzProperty p d) h

/-- The crude pigeonhole construction gives an explicit finite upper bound. -/
theorem egzConstant_le_pigeonhole_bound (p d : ℕ) :
    egzConstant p d ≤ (p - 1) * p ^ d + 1 :=
  egzConstant_min (EGZProperty.pigeonhole_bound p d)

/-- Every exact length at least the EGZ constant has the EGZ property. -/
theorem egzProperty_of_egzConstant_le {p d n : ℕ} (h : egzConstant p d ≤ n) :
    EGZProperty p d n :=
  EGZProperty.mono h (egzConstant_spec p d)

/-- A failed exact length lies strictly below the EGZ constant. -/
theorem lt_egzConstant_of_not_egzProperty {p d n : ℕ}
    (h : ¬ EGZProperty p d n) : n < egzConstant p d := by
  exact Nat.lt_of_not_ge fun hn ↦ h (egzProperty_of_egzConstant_le hn)

/-- The extremal `p`-hollow number `𝔴(𝔽_p^d)`.

The paper only uses this at primes.  We search through the natural ambient
bound `p ^ d`; for prime `p`, injectivity of hollow families proves that this
cutoff loses nothing.  This bounded definition is total even at the degenerate
moduli `0` and `1`, where hollow lengths need not be bounded. -/
noncomputable def hollowConstant (p d : ℕ) : ℕ :=
  @Nat.findGreatest (AdmitsPHollowLength p d) (Classical.decPred _) (p ^ d)

/-- The bounded-search definition is always at most the ambient cutoff. -/
theorem hollowConstant_le_pow (p d : ℕ) : hollowConstant p d ≤ p ^ d := by
  classical
  exact Nat.findGreatest_le _

/-- At a prime, the extremal hollow length is attained. -/
theorem hollowConstant_spec {p d : ℕ} (hp : Nat.Prime p) :
    AdmitsPHollowLength p d (hollowConstant p d) := by
  classical
  unfold hollowConstant
  exact Nat.findGreatest_spec (P := AdmitsPHollowLength p d) (n := p ^ d)
    (Nat.zero_le _) (admitsPHollowLength_zero hp.pos)

/-- At a prime, every admitted hollow length is at most the hollow constant. -/
theorem hollowConstant_max {p d s : ℕ} (hp : Nat.Prime p)
    (h : AdmitsPHollowLength p d s) : s ≤ hollowConstant p d := by
  classical
  unfold hollowConstant
  exact Nat.le_findGreatest (P := AdmitsPHollowLength p d) (h.le_pow hp) h

/-- Any positive-modulus hollow family gives the elementary EGZ lower bound. -/
theorem hollowLength_mul_add_one_le_egzConstant {p d s : ℕ} (hp : 0 < p)
    (h : AdmitsPHollowLength p d s) :
    s * (p - 1) + 1 ≤ egzConstant p d := by
  have hlt : s * (p - 1) < egzConstant p d :=
    lt_egzConstant_of_not_egzProperty
      (not_egzProperty_of_admitsPHollowLength hp h)
  omega

/-- The standard lower comparison between the two constants. -/
theorem hollowConstant_mul_add_one_le_egzConstant {p d : ℕ} (hp : Nat.Prime p) :
    hollowConstant p d * (p - 1) + 1 ≤ egzConstant p d :=
  hollowLength_mul_add_one_le_egzConstant hp.pos (hollowConstant_spec hp)

end EGZ
