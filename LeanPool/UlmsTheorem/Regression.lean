/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import LeanPool.UlmsTheorem.Ulm.Theorem

/-!
DIFFERENTIAL TEST OF `ulm_theorem` AGAINST INDEPENDENTLY-KNOWN GROUND TRUTH.

`Z/4 + Z/4` and `Z/2 + Z/8` both have order 16 and are non-isomorphic — a fact
that needs no Ulm theory. Here that non-isomorphism is DERIVED FROM
`ulm_theorem`, by computing the two Ulm invariants at 0 and finding them
different. If the formalized invariant were degenerate, mis-indexed, or blind to
its group argument, it could not separate these two and this file would not
compile.

  Z/4 + Z/4 : socle = {0,2}^2 = 2G exactly, so P_0 = P_1 and f(0) = 0.
  Z/2 + Z/8 : (1,0) is in the socle but not in 2G, so P_0 != P_1 and f(0) != 0.

Why this pair rather than a cheaper one: both groups have order 16, two cyclic
summands, and socle dimension 2. Only the Ulm invariant separates them, so the
test cannot be passed by an invariant that has collapsed to the order, the
summand count, or the socle dimension. For a finite direct sum of cyclics,
`f(n)` is the number of summands of order `p^(n+1)` -- note the off-by-one --
so the full vectors are `0,2,0,...` and `1,0,1,...`. That formula is stated
verbatim in E. A. Walker, "Ulm's Theorem for Totally Projective Groups",
Proc. Amer. Math. Soc. 37 (1973), 387-392, at p. 387, which also gives the
filtration, the invariant, and the classical statement in quotable form.

Two checks that cannot live in a build, recorded here so they are not lost:

* **Countability is load-bearing.** The theorem is FALSE without it, so a
  formalization that did not require it would be proving a false statement.
  Fuchs, *Abelian Groups* (Pergamon 1960), has a section titled
  "Non-isomorphic groups with the same Ulm sequence" (Sec. 39, p. 134) giving
  a counterexample at cardinality aleph_1; Crawley, Pacific J. Math. 22 (1967)
  235-239, records the same failure. Stating `ulm_theorem`'s conclusion without
  `[Countable G] [Countable H]` and discharging it with `ulm_theorem` fails on
  `failed to synthesize Countable G`, and the proof consumes countability for
  real at `Lib/Ulm/Classification.lean:283` via `exists_surjective_nat`.
* **No external artifact exists to test against.** As of 2026-08-27 Ulm's
  theorem is not formalized in Mathlib, the Isabelle AFP, Coq, Mizar, Metamath,
  or any other Lean project, and Mathlib's finite-abelian structure theorem is
  existence-only -- it never proves the exponent multiset is an invariant, so it
  cannot serve as an independent isomorphism oracle. Ground truth has to come
  from hand-computed finite instances like this one.
-/

namespace UlmsTheorem

namespace UlmDifferentialRegression

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

section Witnesses

private lemma reduced_44 : IsReducedPGroup 2 (ZMod 4 × ZMod 4) where
  primary := fun x ↦ ⟨2, by revert x; decide⟩
  reduced := by
    refine ⟨((2 : ℕ) : Ordinal), ?_⟩
    rw [ulmSubgroup_nat]
    ext x
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_ofPred_eq, AddSubgroup.mem_bot,
      AddSubsemigroup.mem_mk, AddSubmonoid.mem_mk]
    constructor
    · rintro ⟨y, rfl⟩; revert y; decide
    · rintro rfl; exact ⟨0, by decide⟩

private lemma reduced_28 : IsReducedPGroup 2 (ZMod 2 × ZMod 8) where
  primary := fun x ↦ ⟨3, by revert x; decide⟩
  reduced := by
    refine ⟨((3 : ℕ) : Ordinal), ?_⟩
    rw [ulmSubgroup_nat]
    ext x
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_ofPred_eq, AddSubgroup.mem_bot,
      AddSubsemigroup.mem_mk, AddSubmonoid.mem_mk]
    constructor
    · rintro ⟨y, rfl⟩; revert y; decide
    · rintro rfl; exact ⟨0, by decide⟩

end Witnesses

/-- `f(0) = 0` for `Z/4 + Z/4`: its socle is exactly `2G`. -/
theorem ulm_44_zero : ulmInvariant 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4) = 0 := by
  have hsub : pSocleAt 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4)
      ≤ pSocleAt 2 (Order.succ (0 : Ordinal)) (G := ZMod 4 × ZMod 4) := by
    intro x hx
    rw [mem_pSocleAt] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have h1 : Order.succ (0 : Ordinal) = ((1 : ℕ) : Ordinal) := by simp
    rw [h1, ulmSubgroup_nat]
    obtain ⟨hp, -⟩ := hx
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_ofPred_eq, AddSubsemigroup.mem_mk,
      AddSubmonoid.mem_mk]
    revert hp
    revert x
    decide
  have htop : ulmDenSubmodule 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4) = ⊤ := by
    ext y
    simp only [Submodule.mem_top, iff_true]
    exact hsub y.2
  have hss : Subsingleton (ulmQuotient 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4)) := by
    rw [ulmQuotient, htop]
    infer_instance
  rw [ulmInvariant]
  exact rank_zero_iff.mpr hss

/-- `f(0) != 0` for `Z/2 + Z/8`: `(1,0)` is a socle element outside `2G`. -/
theorem ulm_28_ne_zero : ulmInvariant 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) ≠ 0 := by
  have hmem : ((1 : ZMod 2), (0 : ZMod 8)) ∈ pSocleAt 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := by
    rw [mem_pSocleAt]
    refine ⟨by decide, ?_⟩
    simp [ulmSubgroup_zero]
  set x : pSocleAt 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := ⟨_, hmem⟩ with hx
  have hnot : x ∉ ulmDenSubmodule 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) := by
    intro hcon
    have : ((1 : ZMod 2), (0 : ZMod 8))
        ∈ pSocleAt 2 (Order.succ (0 : Ordinal)) (G := ZMod 2 × ZMod 8) := hcon
    rw [mem_pSocleAt] at this
    obtain ⟨-, hin⟩ := this
    have h1 : Order.succ (0 : Ordinal) = ((1 : ℕ) : Ordinal) := by simp
    rw [h1, ulmSubgroup_nat] at hin
    simp only [pPow, AddSubgroup.mem_mk, Set.mem_ofPred_eq, AddSubsemigroup.mem_mk,
      AddSubmonoid.mem_mk] at hin
    revert hin
    decide
  let _ : Nontrivial (ulmQuotient 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8)) := by
    refine ⟨Submodule.Quotient.mk x, 0, ?_⟩
    simpa [Submodule.Quotient.mk_eq_zero] using hnot
  rw [ulmInvariant]
  exact ne_of_gt rank_pos

/-- **The differential test.** `ulm_theorem` says these two groups are isomorphic
iff their Ulm invariants agree everywhere. They disagree at 0, so the theorem
forbids an isomorphism — and independently, no isomorphism exists. -/
theorem no_iso_44_28 : ¬ Nonempty ((ZMod 4 × ZMod 4) ≃+ (ZMod 2 × ZMod 8)) := by
  intro hiso
  have hall := (ulm_theorem 2 reduced_44 reduced_28).1 hiso
  have h0 := hall 0
  rw [ulm_44_zero] at h0
  exact ulm_28_ne_zero h0.symm

end UlmDifferentialRegression

end UlmsTheorem
