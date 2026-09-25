/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.NilpotentPowerTrace
import LeanPool.RegtsSevenster.RS.Common.TraceSeparation
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FactorialBeats

/-!
# The factorial obstruction to a nonzero nilpotent trace

Schrijver's argument (arXiv:1211.3561, Proposition 4) uses only
permutation representations and the cycle-trace identity. A last
nonzero power trace separates all permutations, forcing dimension
at least `n!` at every level. A single level of smaller dimension
therefore suffices for nilpotent-trace vanishing.

`CycleTraceTower` records precisely these inputs, without Schur
idempotents, branching, hook confinement or rationality. The object
and strand instances are supplied in `Novel/Envelope/FactorialTrace`
and `Novel/Envelope/BlockFactorialTrace`.
-/

namespace RS

/-- Permutation representations and tensor-power traces satisfying
the cycle formula, with fixed points recorded separately. -/
structure CycleTraceTower (E : ℕ → Type*) [∀ n, Ring (E n)]
    [∀ n, Algebra ℂ (E n)] (A : Type*) [Ring A] [Algebra ℂ A] where
  /-- The trace on the ambient algebra. -/
  traceA : A →ₗ[ℂ] ℂ
  /-- The trace at each tensor level. -/
  trace : ∀ n, E n →ₗ[ℂ] ℂ
  /-- The permutation representations. -/
  rep : ∀ n, Equiv.Perm (Fin n) →* E n
  /-- The tensor-power maps; their cycle traces are all that is used. -/
  pow : ∀ n, A → E n
  /-- The trace of a permutation against a tensor power is the
  product of the traces along its cycles. -/
  cycleTrace : ∀ n (π : Equiv.Perm (Fin n)) (g : A),
    trace n (rep n π * pow n g) =
      (π.cycleType.map (fun c => traceA (g ^ c))).prod *
        traceA g ^ (n - π.cycleType.sum)

namespace CycleTraceTower

variable {E : ℕ → Type*}

/-- For an isolated nonzero power trace, every nonidentity
permutation has zero trace against the tensor power. -/
theorem trace_perm_pow
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : Type*} [Ring A]
    [Algebra ℂ A]
    (T : CycleTraceTower E A) {y : A}
    (hy : SinglePowerTrace T.traceA y) (n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    T.trace n (T.rep n π * T.pow n y) =
      if π = 1 then T.traceA y ^ n else 0 := by
  classical
  rw [T.cycleTrace]
  by_cases hπ : π = 1
  · subst π
    simp
  · rw [ite_eq_right hπ]
    have hcycles : π.cycleType ≠ 0 :=
      mt Equiv.Perm.cycleType_eq_zero.mp hπ
    obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hcycles
    have hzero : (π.cycleType.map (fun c => T.traceA (y ^ c))).prod = 0 :=
      Multiset.prod_eq_zero (Multiset.mem_map.mpr
        ⟨c, hc, hy.higher_eq_zero c (Equiv.Perm.two_le_of_mem_cycleType hc)⟩)
    rw [hzero, zero_mul]

/-- An isolated nonzero power trace makes all permutation
operators linearly independent. -/
theorem linearIndependent_rep
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : Type*} [Ring A]
    [Algebra ℂ A]
    (T : CycleTraceTower E A) {y : A}
    (hy : SinglePowerTrace T.traceA y) (n : ℕ) :
    LinearIndependent ℂ (fun π => T.rep n π) := by
  let τ := (T.trace n).comp (LinearMap.mulRight ℂ (T.pow n y))
  exact linearIndependent_of_group_trace (T.rep n) τ
    (pow_ne_zero n hy.trace_ne_zero) (T.trace_perm_pow hy n)

/-- A nilpotent with nonzero trace forces factorial dimension at
every finite-dimensional level. -/
theorem factorial_le_finrank
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : Type*} [Ring A]
    [Algebra ℂ A]
    (T : CycleTraceTower E A) {g : A}
    (hg : IsNilpotent g) (hτ : T.traceA g ≠ 0) (n : ℕ)
    [Module.Finite ℂ (E n)] : n.factorial ≤ Module.finrank ℂ (E n) := by
  obtain ⟨r, _, hr⟩ := exists_singlePowerTrace_pow T.traceA hg hτ
  simpa only [Fintype.card_perm, Fintype.card_fin] using
    (T.linearIndependent_rep hr n).fintype_card_le_finrank

/-- One finite-dimensional level below factorial growth forces
the trace of every nilpotent to vanish. -/
theorem traceA_eq_zero_of_finrank_lt_factorial
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : Type*} [Ring A]
    [Algebra ℂ A]
    (T : CycleTraceTower E A)
    {n : ℕ} [Module.Finite ℂ (E n)]
    (hbound : Module.finrank ℂ (E n) < n.factorial)
    {g : A} (hg : IsNilpotent g) : T.traceA g = 0 := by
  by_contra hτ
  exact (T.factorial_le_finrank hg hτ n).not_gt hbound

/-- Exponential endomorphism growth is a sufficient instance of
the single-level factorial bound. -/
theorem traceA_eq_zero_of_exponential_bound
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : Type*} [Ring A]
    [Algebra ℂ A]
    (T : CycleTraceTower E A)
    [∀ n, Module.Finite ℂ (E n)] (B : ℝ)
    (hbound : ∀ n, (Module.finrank ℂ (E n) : ℝ) ≤ B ^ n)
    {g : A} (hg : IsNilpotent g) : T.traceA g = 0 := by
  obtain ⟨n, hn⟩ := exists_lt_sqrt_factorial 1 B
  have hfact : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast (show 1 ≤ n.factorial from Nat.factorial_pos n)
  have hsqrt : Real.sqrt (n.factorial : ℝ) ≤ n.factorial := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by nlinarith⟩
  have hexp : B ^ n < Real.sqrt (n.factorial : ℝ) := by
    simpa only [one_mul] using hn
  have hlt : (Module.finrank ℂ (E n) : ℝ) < n.factorial :=
    (hbound n).trans_lt (hexp.trans_le hsqrt)
  exact T.traceA_eq_zero_of_finrank_lt_factorial (by exact_mod_cast hlt) hg

end CycleTraceTower

end RS
