/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.NonSeparatedStep
import LeanPool.RegtsSevenster.RS.Novel.Skein.SeparatedParity

/-!
# The non-separated count parities

The two orbit-counting inputs of
`RS.Novel.Skein.NonSeparatedStep`, proved:

* `nonSeparatedSegmentParity` — a same-component square preserves
  the circuit-count parity (`NonSeparatedSegmentParity`);
* `nonSeparatedMergeParity` — a square whose `c`-edge lies on a
  circuit not carrying `a` flips the count parity
  (`NonSeparatedMergeParity`).

## Method

Both are computed on the closed-up full walk `Π` of
`RS.Novel.Skein.SeparatedParity`: a localized square turns the repaired
full walk into `(a d)(b c) · Π` (`fullPerm_repair`), and
`permOrbitCount Π = permOrbitCount walkPermPeriodic + |B|` converts
full-walk orbit ledgers into circuit-count ledgers.

*Merge case* (`c` periodic, `a` off its orbit): exactly
`separatedCountParity` — the two swaps act
coherently (`permOrbitCount_swap_swap_mul`, `Δ = ±2` on `Π`-orbits,
`Δ = ±1` on circuits, parity flips).  The separated-orientation
exclusion `a ≁ c` is replaced by the orbit-disjointness hypothesis
via `sameCycle_periodic_val`.

*Segment case* (`WalkReach κ c a`): the walk gives `c ∼ a`, the
mirror symmetry gives `b ∼ σa ∼ σc ∼ d`, and the mirror collision
at `c` gives `b ≁ c`.  The first swap therefore **merges** the two
traversal orbits of the component and the second swap **splits**
the merged cycle again (`a ∼ d` after the merge): the net change of
the `Π`-orbit count is zero (`permOrbitCount_swap_swap_mul_cancel`
below), so the circuit count is unchanged and the parity is even.

The localization needed for `fullPerm_repair` comes from
`squareLocalized_of_walkReach` (segment case) and from
`periodic_or_onBoundaryChain` (merge case); their `[LinearOrder α]`
assumption is discharged by well-ordering the label type.
-/

namespace RS



/-! ## The incoherent double swap: merge then split -/

section AbstractCancel

open Equiv Equiv.Perm

variable {Y : Type}

/-- Along the swap-multiplied permutation, every point of a
`g`-trajectory of `x` is in the orbit of `x` or of `y`. -/
private theorem sameCycle_swap_mul_pow_left [DecidableEq Y]
    (g : Perm Y) (x y : Y) :
    ∀ k : ℕ, (Equiv.swap x y * g).SameCycle x ((g ^ k) x) ∨
      (Equiv.swap x y * g).SameCycle y ((g ^ k) x) := by
  intro k
  induction k with
  | zero => exact Or.inl (Equiv.Perm.SameCycle.refl _ _)
  | succ k ih =>
    have hstep : (g ^ (k + 1)) x = g ((g ^ k) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    by_cases h1 : g ((g ^ k) x) = x
    · refine Or.inl ?_
      rw [hstep, h1]
    by_cases h2 : g ((g ^ k) x) = y
    · refine Or.inr ?_
      rw [hstep, h2]
    · have happ : (Equiv.swap x y * g) ((g ^ k) x) =
          g ((g ^ k) x) := by
        rw [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne h1 h2]
      have hsc : (Equiv.swap x y * g).SameCycle ((g ^ k) x)
          ((g ^ (k + 1)) x) := by
        rw [hstep, ← happ]
        exact Equiv.Perm.sameCycle_apply_right.mpr
          (Equiv.Perm.SameCycle.refl _ _)
      rcases ih with h | h
      · exact Or.inl (h.trans hsc)
      · exact Or.inr (h.trans hsc)

/-- `SameCycle` out of a swapped point transfers to the
swap-multiplied permutation, up to landing in either swap orbit. -/
private theorem sameCycle_swap_mul_of_left [Fintype Y] [DecidableEq Y]
    {g : Perm Y} {x y u : Y}
    (h : g.SameCycle x u) :
    (Equiv.swap x y * g).SameCycle x u ∨
      (Equiv.swap x y * g).SameCycle y u := by
  obtain ⟨i, _, _, hiu⟩ := Equiv.Perm.SameCycle.exists_pow_eq _ h
  rw [← hiu]
  exact sameCycle_swap_mul_pow_left g x y i

/-- **The incoherent double swap**: if the first transposition
merges two distinct orbits (`c ∼ a`, `b ∼ d`, `b ≁ c`) then the
second transposition splits the merged cycle again (`a ∼ d` holds
after the merge), and the total orbit count is unchanged. -/
private theorem permOrbitCount_swap_swap_mul_cancel [Fintype Y] [DecidableEq Y]
    {g : Perm Y}
    {a b c d : Y} (hbc : b ≠ c) (had : a ≠ d)
    (hca : g.SameCycle c a) (hbd : g.SameCycle b d)
    (hnbc : ¬ g.SameCycle b c) :
    permOrbitCount (Equiv.swap a d * (Equiv.swap b c * g)) =
      permOrbitCount g := by
  have hmerge := permOrbitCount_swap_mul_not_sameCycle hbc hnbc
  have hbc' : (Equiv.swap b c * g).SameCycle b c :=
    sameCycle_swap_mul_of_not hbc hnbc
  have hca' : (Equiv.swap b c * g).SameCycle c a ∨
      (Equiv.swap b c * g).SameCycle b a := by
    rw [Equiv.swap_comm b c]
    exact sameCycle_swap_mul_of_left hca
  have hbd' : (Equiv.swap b c * g).SameCycle b d ∨
      (Equiv.swap b c * g).SameCycle c d :=
    sameCycle_swap_mul_of_left hbd
  have hac' : (Equiv.swap b c * g).SameCycle a c := by
    rcases hca' with h | h
    · exact h.symm
    · exact h.symm.trans hbc'
  have hcd' : (Equiv.swap b c * g).SameCycle c d := by
    rcases hbd' with h | h
    · exact hbc'.symm.trans h
    · exact h
  have had' : (Equiv.swap b c * g).SameCycle a d :=
    hac'.trans hcd'
  have hsplit := permOrbitCount_swap_mul_sameCycle had had'
  omega

end AbstractCancel

/-! ## The same-component parity (segment reversal, Δ = 0) -/

open EdgeSubset in
/-- **The segment count parity** (the input
`NonSeparatedSegmentParity`): a
same-component square preserves the circuit-count parity.  The
first swap merges the two traversal orbits of the component, the
second splits them again: `Δ permOrbitCount = 0`. -/
theorem nonSeparatedSegmentParity : NonSeparatedSegmentParity := by
  intro α W F κ a b c d v hsq hreach
  classical
  let : LinearOrder α := IsWellOrder.linearOrder WellOrderingRel
  -- localization and pathMatch invariance of the move
  have hloc : SquareLocalized κ a b c d :=
    squareLocalized_of_walkReach hsq hreach
  have hpm := pathMatch_repair_of_localized hsq hloc
  obtain ⟨m, hm1, hcont, hlast⟩ := hreach
  -- distinctness of the swap pairs in the flag subtype
  have hbcX : (⟨b, mem_flags_of_internalFlags F hsq.hb⟩ :
      {f : W.Flag // f ∈ F.flags}) ≠
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ := fun h =>
    hsq.hbc (congrArg Subtype.val h)
  have hadX : (⟨a, mem_flags_of_internalFlags F hsq.ha⟩ :
      {f : W.Flag // f ∈ F.flags}) ≠
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := fun h =>
    hsq.had (congrArg Subtype.val h)
  -- the walk relation `c ∼ a`
  have hca : (fullPerm κ).SameCycle
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩ := by
    refine sameCycle_of_pow_eq (n := m) (Subtype.ext ?_)
    rw [fullPerm_pow_val
      (x := ⟨c, mem_flags_of_internalFlags F hsq.hc⟩) hcont m
      le_rfl]
    exact hlast
  -- the single-step relations `σb ∼ a` and `σc ∼ d`
  have hstep_b : fullPerm κ (pairingPermSP F
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩) =
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩ := by
    apply Subtype.ext
    rw [fullPerm_apply_pairing,
      fullMatchFun_val_internal κ
        (show (⟨b, mem_flags_of_internalFlags F hsq.hb⟩ :
          {f : W.Flag // f ∈ F.flags}).val ∈ F.internalFlags from
          hsq.hb)]
    exact hsq.hmb
  have hstep_c : fullPerm κ (pairingPermSP F
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩) =
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := by
    apply Subtype.ext
    rw [fullPerm_apply_pairing,
      fullMatchFun_val_internal κ
        (show (⟨c, mem_flags_of_internalFlags F hsq.hc⟩ :
          {f : W.Flag // f ∈ F.flags}).val ∈ F.internalFlags from
          hsq.hc)]
    exact hsq.hcd
  have hrel_b : (fullPerm κ).SameCycle
      (pairingPermSP F ⟨b, mem_flags_of_internalFlags F hsq.hb⟩)
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩ := by
    rw [← hstep_b]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.SameCycle.refl _ _)
  have hrel_c : (fullPerm κ).SameCycle
      (pairingPermSP F ⟨c, mem_flags_of_internalFlags F hsq.hc⟩)
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := by
    rw [← hstep_c]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.SameCycle.refl _ _)
  -- the mirror of the walk relation: `σc ∼ σa`
  have hmir : (fullPerm κ).SameCycle
      (pairingPermSP F ⟨c, mem_flags_of_internalFlags F hsq.hc⟩)
      (pairingPermSP F ⟨a, mem_flags_of_internalFlags F hsq.ha⟩) :=
    sameCycle_pairingPermSP hca
  -- `b ∼ σa` (mirror of `σb ∼ a`)
  have hbσa := sameCycle_pairingPermSP hrel_b
  rw [pairingPermSP_invol] at hbσa
  -- hence `b ∼ d` through the mirror orbit
  have hbd : (fullPerm κ).SameCycle
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ :=
    (hbσa.trans hmir.symm).trans hrel_c
  -- mirror collision at `c`: `c ≁ σc`
  have hNc : ¬ (fullPerm κ).SameCycle
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩
      (pairingPermSP F ⟨c, mem_flags_of_internalFlags F hsq.hc⟩)
      := by
    rcases hloc with ⟨_hpa, hpc⟩ | ⟨β, hβ, hall⟩
    · exact not_sameCycle_pairingPermSP_of_periodic hpc
    · rcases hall c (Or.inr (Or.inr (Or.inl rfl))) with hpc | hchain
      · exact not_sameCycle_pairingPermSP_of_periodic hpc
      · obtain ⟨k, hkle, hcontk, htermk⟩ :=
          chain_terminates_with_data κ hβ
        obtain ⟨k', t, htk', hcont', hterm', hft⟩ := hchain
        have hkk : k' = k :=
          chain_exit_unique hcont' hterm' hcontk htermk
        subst hkk
        exact not_sameCycle_pairingPermSP_of_chain hβ hkle hcontk
          htermk (mem_flags_of_internalFlags F hsq.hc) htk' hft
  -- the two swap points are on distinct orbits: `b ≁ c`
  have hnbc : ¬ (fullPerm κ).SameCycle
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ := by
    intro h
    exact hNc ((h.symm.trans hbσa).trans hmir.symm)
  -- the incoherent double swap: net zero
  have hcnt := permOrbitCount_swap_swap_mul_cancel hbcX hadX hca
    hbd hnbc
  rw [← fullPerm_repair hsq hpm] at hcnt
  -- the orbit bookkeeping on both sides
  have h1 := permOrbitCount_fullPerm_eq κ
  have h2 := permOrbitCount_fullPerm_eq (κ.repair a b c d v hsq)
  have hc1 : κ.openCircuitCount =
      permOrbitCount κ.walkPermPeriodic / 2 := rfl
  have hc2 : (κ.repair a b c d v hsq).openCircuitCount =
      permOrbitCount (κ.repair a b c d v hsq).walkPermPeriodic / 2
      := rfl
  rw [Nat.even_iff, hc1, hc2]
  omega

/-! ## The distinct-component parity (splice merge, Δ = ±1) -/

open EdgeSubset in
/-- **The merge count parity** (the input
`NonSeparatedMergeParity`): a
square whose `c`-edge lies on a circuit not carrying `a` flips the
count parity.  The argument of `separatedCountParity`, with the
separated-orientation exclusion `a ≁ c` replaced by the
orbit-disjointness hypothesis. -/
theorem nonSeparatedMergeParity : NonSeparatedMergeParity := by
  intro α W F κ a b c d v hsq hpc hdisj
  classical
  let : LinearOrder α := IsWellOrder.linearOrder WellOrderingRel
  -- localization: `c`'s circuit is periodic, `a` is periodic or on
  -- a boundary chain carrying its whole edge
  have hloc : SquareLocalized κ a b c d := by
    by_cases hpa : κ.PeriodicFlag a
    · exact Or.inl ⟨hpa, hpc⟩
    · rcases periodic_or_onBoundaryChain κ hsq.ha with
        h | ⟨β, hβ, hchain⟩
      · exact absurd h hpa
      · refine Or.inr ⟨β, hβ, ?_⟩
        intro f hf
        rcases hf with rfl | rfl | rfl | rfl
        · exact Or.inr hchain
        · exact Or.inr (hsq.hab ▸
            onBoundaryChain_match hβ hsq.ha hchain)
        · exact Or.inl hpc
        · exact Or.inl (hsq.hcd ▸ periodicFlag_match hpc)
  have hpm := pathMatch_repair_of_localized hsq hloc
  -- ═══════ STAGE 1: THE SQUARE'S CORNERS AND THEIR STEPS ═══════
  -- distinctness of the square corners in the flag subtype
  have hbcX : (⟨b, mem_flags_of_internalFlags F hsq.hb⟩ :
      {f : W.Flag // f ∈ F.flags}) ≠
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ := fun h =>
    hsq.hbc (congrArg Subtype.val h)
  have hadX : (⟨a, mem_flags_of_internalFlags F hsq.ha⟩ :
      {f : W.Flag // f ∈ F.flags}) ≠
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := fun h =>
    hsq.had (congrArg Subtype.val h)
  -- the single-step relations `σb ∼ a` and `σc ∼ d`
  have hstep_b : fullPerm κ (pairingPermSP F
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩) =
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩ := by
    apply Subtype.ext
    rw [fullPerm_apply_pairing,
      fullMatchFun_val_internal κ
        (show (⟨b, mem_flags_of_internalFlags F hsq.hb⟩ :
          {f : W.Flag // f ∈ F.flags}).val ∈ F.internalFlags from
          hsq.hb)]
    exact hsq.hmb
  have hstep_c : fullPerm κ (pairingPermSP F
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩) =
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := by
    apply Subtype.ext
    rw [fullPerm_apply_pairing,
      fullMatchFun_val_internal κ
        (show (⟨c, mem_flags_of_internalFlags F hsq.hc⟩ :
          {f : W.Flag // f ∈ F.flags}).val ∈ F.internalFlags from
          hsq.hc)]
    exact hsq.hcd
  have hrel_b : (fullPerm κ).SameCycle
      (pairingPermSP F ⟨b, mem_flags_of_internalFlags F hsq.hb⟩)
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩ := by
    rw [← hstep_b]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.SameCycle.refl _ _)
  have hrel_c : (fullPerm κ).SameCycle
      (pairingPermSP F ⟨c, mem_flags_of_internalFlags F hsq.hc⟩)
      ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := by
    rw [← hstep_c]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.SameCycle.refl _ _)
  -- ═══════ STAGE 2: THE MIRROR EQUIVALENCE `b ∼ c ↔ a ∼ d` ═══════
  have hiff : (fullPerm κ).SameCycle
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ ↔
      (fullPerm κ).SameCycle
        ⟨a, mem_flags_of_internalFlags F hsq.ha⟩
        ⟨d, mem_flags_of_internalFlags F hsq.hd⟩ := by
    constructor
    · intro h
      exact (hrel_b.symm.trans (sameCycle_pairingPermSP h)).trans
        hrel_c
    · intro h
      have h2 := sameCycle_pairingPermSP
        ((hrel_b.trans h).trans hrel_c.symm)
      rw [pairingPermSP_invol, pairingPermSP_invol] at h2
      exact h2
  -- ═══════ STAGE 3: THE THREE EXCLUSIONS ═══════
  -- exclusion `¬ b ∼ σb` (mirror collision at `b`)
  have hN1 : ¬ (fullPerm κ).SameCycle
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩
      (pairingPermSP F ⟨b, mem_flags_of_internalFlags F hsq.hb⟩)
      := by
    rcases hloc with ⟨hpa, _hpc⟩ | ⟨β, hβ, hall⟩
    · exact not_sameCycle_pairingPermSP_of_periodic
        (show κ.PeriodicFlag b from
          hsq.hab ▸ periodicFlag_match hpa)
    · rcases hall b (Or.inr (Or.inl rfl)) with hpb | hchain
      · exact not_sameCycle_pairingPermSP_of_periodic hpb
      · obtain ⟨k, hkle, hcontk, htermk⟩ :=
          chain_terminates_with_data κ hβ
        obtain ⟨k', t, htk', hcont', hterm', hft⟩ := hchain
        have hkk : k' = k :=
          chain_exit_unique hcont' hterm' hcontk htermk
        subst hkk
        exact not_sameCycle_pairingPermSP_of_chain hβ hkle hcontk
          htermk (mem_flags_of_internalFlags F hsq.hb) htk' hft
  -- exclusion `¬ a ∼ b`
  have hab : ¬ (fullPerm κ).SameCycle
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩
      ⟨b, mem_flags_of_internalFlags F hsq.hb⟩ := by
    intro h
    exact hN1 (h.symm.trans hrel_b.symm)
  -- exclusion `¬ a ∼ c` (the orbit disjointness)
  have hac : ¬ (fullPerm κ).SameCycle
      ⟨a, mem_flags_of_internalFlags F hsq.ha⟩
      ⟨c, mem_flags_of_internalFlags F hsq.hc⟩ := by
    intro h
    obtain ⟨i, hi⟩ := sameCycle_periodic_val hpc h.symm
    exact hdisj ⟨i, Or.inl hi.symm⟩
  -- ═══════ ASSEMBLY: THE DOUBLE SWAP AND THE ORBIT LEDGER ═══════
  have hswap := permOrbitCount_swap_swap_mul (g := fullPerm κ)
    hbcX hadX hiff hab hac
  rw [← fullPerm_repair hsq hpm] at hswap
  -- the orbit bookkeeping on both sides
  have h1 := permOrbitCount_fullPerm_eq κ
  have h2 := permOrbitCount_fullPerm_eq (κ.repair a b c d v hsq)
  have hc1 : κ.openCircuitCount =
      permOrbitCount κ.walkPermPeriodic / 2 := rfl
  have hc2 : (κ.repair a b c d v hsq).openCircuitCount =
      permOrbitCount (κ.repair a b c d v hsq).walkPermPeriodic / 2
      := rfl
  rw [Nat.odd_iff, hc1, hc2]
  rcases hswap with h | h <;> omega

end RS
