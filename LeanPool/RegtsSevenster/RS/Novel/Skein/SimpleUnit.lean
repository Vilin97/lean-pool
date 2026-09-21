/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.Multiplicativity
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdeal

/-!
# The simple unit

Lemma 3.4 of the accompanying paper: the arity-zero Hom space of an
edge-rank-bounded parameter is spanned by the class of the empty
fragment, which is nonzero — `End(𝟙) = ℂ·[∅]`.  The rank bound at
arity zero caps the dimension at one, and the empty class is
nonzero because its closure row at the empty fragment is
`f(∅) = 1`.
-/

noncomputable section

namespace RS

/-- The class of the empty fragment in the arity-zero Hom
space. -/
noncomputable def emptyClass (f : ClosedFragment → ℂ) :
    HomSpace f 0 :=
  HomSpace.ofFragment f emptyClosedFragment

/-- The arity-zero connection pairing is the parameter of the
union. -/
theorem connectionPairing_zero {R : ℕ} (f : EdgeRankParameter R)
    (F G : ClosedFragment) :
    connectionPairing f.val 0 F G =
      f.val (ClosedFragment.union F G) :=
  f.iso_invariant _ _
    ((Fragment.composeCongr (relabelZeroEquiv F _)
      (relabelZeroEquiv G _)).trans (composeZeroEquiv F G))

/-- The empty class is nonzero. -/
theorem emptyClass_ne_zero {R : ℕ} (f : EdgeRankParameter R) :
    emptyClass f.val ≠ 0 := by
  intro h
  have hker : Finsupp.single emptyClosedFragment (1 : ℂ) ∈
      LinearMap.ker (connectionMap f.val 0) :=
    (Submodule.Quotient.mk_eq_zero _).mp h
  rw [LinearMap.mem_ker] at hker
  have hval := congrFun hker emptyClosedFragment
  rw [connectionMap_single, one_mul, connectionPairing_zero,
    f.iso_invariant _ _ (unionEmptyLeftEquiv emptyClosedFragment),
    f.val_empty] at hval
  exact one_ne_zero hval

/-- **The simple unit** (accompanying paper, Lemma 3.4): the
arity-zero Hom space is spanned by the class of the empty
fragment. -/
theorem homSpace_zero_spanned {R : ℕ} (f : EdgeRankParameter R)
    (u : HomSpace f.val 0) :
    ∃ c : ℂ, u = c • emptyClass f.val := by
  have hrank : Module.rank ℂ (HomSpace f.val 0) ≤ 1 := by
    have := HomSpace.rank_le f 0
    rwa [pow_zero] at this
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hrank
  obtain ⟨c₀, hc₀⟩ := hv₀ (emptyClass f.val)
  obtain ⟨cu, hcu⟩ := hv₀ u
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc₀
    exact emptyClass_ne_zero f hc₀.symm
  refine ⟨cu * c₀⁻¹, ?_⟩
  rw [← hcu, ← hc₀, smul_smul]
  congr 1
  field_simp

end RS
