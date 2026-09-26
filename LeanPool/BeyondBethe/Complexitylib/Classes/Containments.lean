/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P
public import LeanPool.BeyondBethe.Complexitylib.Classes.NP
public import LeanPool.BeyondBethe.Complexitylib.Classes.Randomized
public import LeanPool.BeyondBethe.Complexitylib.Classes.L
public import LeanPool.BeyondBethe.Complexitylib.Classes.Exponential

/-!
# Containment relations between complexity classes

This file collects the standard containment results between complexity classes.

## Theorems

- `DTIME_subset_NTIME` — `DTIME(T) ⊆ NTIME(T)`
- `P_subset_NP` — `P ⊆ NP`
- `DTIME_mono` — `T₁ =O T₂ → DTIME(T₁) ⊆ DTIME(T₂)`
- `NTIME_mono` — `T₁ =O T₂ → NTIME(T₁) ⊆ NTIME(T₂)`
- `DSPACE_mono` — `S₁ =O S₂ → DSPACE(S₁) ⊆ DSPACE(S₂)`
- `P_subset_EXP` — `P ⊆ EXP`
- `DTIME_subset_DSPACE` — `DTIME(T) ⊆ DSPACE(T)` (time bounds space)
- `P_subset_PSPACE` — `P ⊆ PSPACE`
- `RTIME_subset_NTIME` — `RTIME(T) ⊆ NTIME(T)` (one-sided error → nondeterministic)
- `RP_subset_NP` — `RP ⊆ NP`
- `DTIME_subset_BPTIME` — `DTIME(T) ⊆ BPTIME(T)` (deterministic → zero-error probabilistic)
- `P_subset_BPP` — `P ⊆ BPP`
- `NP_subset_NEXP` — `NP ⊆ NEXP`
- `EXP_subset_NEXP` — `EXP ⊆ NEXP`
- `BPTIME_subset_PPTIME` — `BPTIME(T) ⊆ PPTIME(T)` (bounded error → unbounded error)
- `BPP_subset_PP` — `BPP ⊆ PP`
- `P_compl` — `L ∈ P → Lᶜ ∈ P` (P closed under complement)
- `DSPACE_subset_NSPACE` — `DSPACE(S) ⊆ NSPACE(S)`
- `NSPACE_mono` — `S₁ =O S₂ → NSPACE(S₁) ⊆ NSPACE(S₂)`
- `L_subset_NL` — `L ⊆ NL`
- `ZPP_subset_RP` — `ZPP ⊆ RP`
- `ZPP_subset_coRP` — `ZPP ⊆ coRP`
- `DTIME_subset_NSPACE` — `DTIME(T) ⊆ NSPACE(T)`
- `P_subset_NPSPACE` — `P ⊆ NPSPACE`
- `P_subset_NEXP` — `P ⊆ NEXP`
- `P_subset_PP` — `P ⊆ PP`
- `P_union` — `L₁ ∈ P → L₂ ∈ P → L₁ ∪ L₂ ∈ P` (P closed under union)
- `P_inter` — `L₁ ∈ P → L₂ ∈ P → L₁ ∩ L₂ ∈ P` (P closed under intersection)
-/


@[expose] public section

namespace Complexity


/-- **DTIME ⊆ NTIME**: every language decidable by a DTM in time `O(T)` is also
    decidable by an NTM in time `O(T)`, via the `TM.toNTM` embedding. -/
theorem DTIME_subset_NTIME (T : ℕ → ℕ) : DTIME T ⊆ NTIME T := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm.toNTM, f, tm.toNTM_decidesInTime hdec, hbig⟩

/-- **P ⊆ NP** -/
theorem P_subset_NP : P ⊆ NP :=
  Set.iUnion_mono fun _ => DTIME_subset_NTIME _

/-- DTIME is monotone with respect to `=O`: if `T₁ =O T₂`, then `DTIME T₁ ⊆ DTIME T₂`. -/
theorem DTIME_mono {T₁ T₂ : ℕ → ℕ} (h : T₁ =O T₂) : DTIME T₁ ⊆ DTIME T₂ := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm, f, hdec, hbig.trans h⟩

/-- **P ⊆ EXP**: every polynomial-time language is also exponential-time. -/
theorem P_subset_EXP : P ⊆ EXP :=
  Set.iUnion_mono fun _ => DTIME_mono (BigO.of_le (fun _ => Nat.lt_two_pow_self.le))

/-- **DTIME ⊆ DSPACE**: a DTM running in time `T` uses at most
    `O(T)` auxiliary space, since every two-way tape head can move at most one
    cell per step. -/
theorem DTIME_subset_DSPACE (T : ℕ → ℕ) : DTIME T ⊆ DSPACE T := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  refine ⟨k, tm, f, ⟨?_, ?_⟩, hbig⟩
  · -- Space bound: all reachable configurations obey the honest tape bounds
    intro x c' hreach
    obtain ⟨c_halt, t_halt, hle, hreachIn_halt, hhalt, _, _⟩ := hdec x
    obtain ⟨t, hreachIn⟩ := TM.reaches_to_reachesIn tm hreach
    have ht_le := TM.reachesIn_le_halt tm hreachIn hreachIn_halt hhalt
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      have hbound := TM.work_head_reachesIn_bound tm hreachIn i
      have hzero := TM.initCfg_work_head_zero tm x i
      omega
    · have hbound := TM.input_head_reachesIn_bound tm hreachIn
      have hzero := TM.initCfg_input_head_zero tm x
      omega
    · have hbound := TM.output_head_reachesIn_bound tm hreachIn
      have hzero := TM.initCfg_output_head_zero tm x
      omega
  · -- Decision: reachesIn implies reaches, same output
    intro x
    obtain ⟨c', t, hle, hreachIn, hhalt, hyes, hno⟩ := hdec x
    refine ⟨c', ?_, hhalt, hyes, hno⟩
    exact TM.reachesIn.rec Relation.ReflTransGen.refl
      (fun hs _ ih => Relation.ReflTransGen.head hs ih) hreachIn

/-- **P ⊆ PSPACE**: every polynomial-time language uses polynomial space. -/
theorem P_subset_PSPACE : P ⊆ PSPACE :=
  Set.iUnion_mono fun _ => DTIME_subset_DSPACE _

/-- **RTIME ⊆ NTIME**: one-sided error implies nondeterministic.
    The same NTM works: `RejectsWithProb 0` means no accepting paths for `x ∉ L`,
    and `AcceptsWithProb (1/2)` means some accepting path exists for `x ∈ L`. -/
theorem RTIME_subset_NTIME (T : ℕ → ℕ) : RTIME T ⊆ NTIME T := by
  intro L ⟨k, tm, f, hhalt, hacc, hrej, hbig⟩
  refine ⟨k, tm, f, ⟨hhalt, fun x => ?_⟩, hbig⟩
  constructor
  · -- x ∈ L → AcceptsInTime: acceptProb ≥ 1/2 > 0 implies ∃ accepting path
    intro hx; by_contra hno
    simp only [NTM.AcceptsInTime] at hno; push Not at hno
    have hcount : tm.acceptCount x (f x.length) = 0 := by
      simp only [NTM.acceptCount]
      rw [Finset.filter_eq_empty_iff.mpr (fun ch _ => fun ⟨h1, h2⟩ => hno ch h1 h2)]
      exact Finset.card_empty
    have hprob := hacc x hx
    simp [NTM.acceptProb, hcount] at hprob; norm_num at hprob
  · -- AcceptsInTime → x ∈ L (contrapositive: x ∉ L → ¬AcceptsInTime)
    intro ⟨choices, hhalt_ch, hout_ch⟩; by_contra hx
    have hzero : tm.acceptProb x (f x.length) = 0 :=
      le_antisymm (hrej x hx) (by unfold NTM.acceptProb; positivity)
    have hcount : tm.acceptCount x (f x.length) = 0 := by
      unfold NTM.acceptProb at hzero
      have h2T : (0:ℚ) < 2 ^ f x.length := by positivity
      rw [div_eq_zero_iff] at hzero
      cases hzero with
      | inl h => exact_mod_cast h
      | inr h => linarith
    have hpos : 0 < tm.acceptCount x (f x.length) := by
      unfold NTM.acceptCount
      exact Finset.card_pos.mpr
        ⟨choices, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhalt_ch, hout_ch⟩⟩
    omega

/-- **RP ⊆ NP**. -/
theorem RP_subset_NP : RP ⊆ NP :=
  Set.iUnion_mono fun _ => RTIME_subset_NTIME _

/-- **DTIME ⊆ BPTIME**: every deterministic TM can be viewed as a PTM with
    zero error. When the DTM accepts, all paths accept (prob = 1 ≥ 2/3).
    When it rejects, no path accepts (prob = 0 ≤ 1/3). -/
theorem DTIME_subset_BPTIME (T : ℕ → ℕ) : DTIME T ⊆ BPTIME T := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  refine ⟨k, tm.toNTM, f, ?_, ?_, ?_, hbig⟩
  · -- AllPathsHaltIn: from toNTM_decidesInTime
    exact (tm.toNTM_decidesInTime hdec).1
  · -- AcceptsWithProb L f (2/3): acceptProb ≥ 2/3 for x ∈ L
    intro x hx
    have ⟨c', t, hle, hreach, hhalt, hyes, _⟩ := hdec x
    have htrace : ∀ ch, tm.toNTM.trace (f x.length) ch (tm.toNTM.initCfg x) = c' :=
      fun ch => tm.toNTM_trace_of_reachesIn hreach hhalt hle ch
    -- acceptCount = 2^(f x.length) since all paths accept
    have hcount : tm.toNTM.acceptCount x (f x.length) = 2 ^ f x.length := by
      simp only [NTM.acceptCount]
      have : (Finset.univ.filter fun (choices : Fin (f x.length) → Bool) =>
          let c' := tm.toNTM.trace (f x.length) choices (tm.toNTM.initCfg x)
          c'.state = tm.toNTM.qhalt ∧ c'.output.cells 1 = Γ.one) = Finset.univ := by
        ext ch; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show (tm.toNTM.trace (f x.length) ch (tm.toNTM.initCfg x)) = c' from htrace ch]
        exact ⟨fun _ => trivial, fun _ => ⟨hhalt, hyes hx⟩⟩
      rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    -- acceptProb = 1
    have hprob : tm.toNTM.acceptProb x (f x.length) = 1 := by
      simp [NTM.acceptProb, hcount]
    linarith
  · -- RejectsWithProb L f (1/3): acceptProb ≤ 1/3 for x ∉ L
    intro x hx
    have ⟨c', t, hle, hreach, hhalt, _, hno⟩ := hdec x
    have htrace : ∀ ch, tm.toNTM.trace (f x.length) ch (tm.toNTM.initCfg x) = c' :=
      fun ch => tm.toNTM_trace_of_reachesIn hreach hhalt hle ch
    -- acceptCount = 0 since no path accepts
    have hcount : tm.toNTM.acceptCount x (f x.length) = 0 := by
      simp only [NTM.acceptCount]
      rw [Finset.filter_eq_empty_iff.mpr]
      · exact Finset.card_empty
      · intro ch _
        rw [show (tm.toNTM.trace (f x.length) ch (tm.toNTM.initCfg x)) = c' from htrace ch]
        intro ⟨_, h2⟩
        have := hno hx; simp_all
    simp [NTM.acceptProb, hcount]

/-- **P ⊆ BPP**: every polynomial-time language is also in BPP. -/
theorem P_subset_BPP : P ⊆ BPP :=
  Set.iUnion_mono fun _ => DTIME_subset_BPTIME _

/-- NTIME is monotone: if `T₁ =O T₂`, then `NTIME T₁ ⊆ NTIME T₂`. -/
theorem NTIME_mono {T₁ T₂ : ℕ → ℕ} (h : T₁ =O T₂) : NTIME T₁ ⊆ NTIME T₂ := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm, f, hdec, hbig.trans h⟩

/-- DSPACE is monotone: if `S₁ =O S₂`, then `DSPACE S₁ ⊆ DSPACE S₂`. -/
theorem DSPACE_mono {S₁ S₂ : ℕ → ℕ} (h : S₁ =O S₂) : DSPACE S₁ ⊆ DSPACE S₂ := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm, f, hdec, hbig.trans h⟩

/-- **NP ⊆ NEXP**: every nondeterministic polynomial-time language is also
    nondeterministic exponential-time. -/
theorem NP_subset_NEXP : NP ⊆ NEXP :=
  Set.iUnion_mono fun _ => NTIME_mono (BigO.of_le (fun _ => Nat.lt_two_pow_self.le))

/-- **EXP ⊆ NEXP**: every deterministic exponential-time language is also
    nondeterministic exponential-time. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP :=
  Set.iUnion_mono fun _ => DTIME_subset_NTIME _

/-- **BPTIME ⊆ PPTIME**: two-sided bounded error implies unbounded error,
    since 2/3 > 1/2 and 1/3 < 1/2. -/
theorem BPTIME_subset_PPTIME (T : ℕ → ℕ) : BPTIME T ⊆ PPTIME T := by
  intro L ⟨k, tm, f, hhalt, hacc, hrej, hbig⟩
  refine ⟨k, tm, f, hhalt, fun x => ⟨fun hx => ?_, fun hprob => ?_⟩, hbig⟩
  · -- x ∈ L → acceptProb > 1/2: acceptProb ≥ 2/3 > 1/2
    have := hacc x hx; linarith
  · -- acceptProb > 1/2 → x ∈ L: contrapositive
    by_contra hx
    have := hrej x hx; linarith

/-- **BPP ⊆ PP**. -/
theorem BPP_subset_PP : BPP ⊆ PP :=
  Set.iUnion_mono fun _ => BPTIME_subset_PPTIME _

/-- **P is closed under complement**: if `L ∈ P` then `Lᶜ ∈ P`. -/
theorem P_compl {L : Language} (h : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨k, n_tapes, tm, f, hdec, hbig⟩ := Set.mem_iUnion.mp h
  refine Set.mem_iUnion.mpr ⟨k + 1, n_tapes, tm.complementTM, fun n => 2 * f n + 4,
    tm.complementTM_decidesInTime hdec, ?_⟩
  have hpow : f =O (· ^ (k + 1)) := hbig.trans (BigO.pow_le_pow_succ k)
  exact BigO.add (BigO.const_mul_left 2 hpow) (BigO.const_le_pow 4 (k + 1))

/-- **DSPACE ⊆ NSPACE**: every language decidable by a DTM in space `O(S)` is also
    decidable by an NTM in space `O(S)`, via the `TM.toNTM` embedding. -/
theorem DSPACE_subset_NSPACE (S : ℕ → ℕ) : DSPACE S ⊆ NSPACE S := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm.toNTM, f, tm.toNTM_decidesInSpace hdec, hbig⟩

/-- NSPACE is monotone: if `S₁ =O S₂`, then `NSPACE S₁ ⊆ NSPACE S₂`. -/
theorem NSPACE_mono {S₁ S₂ : ℕ → ℕ} (h : S₁ =O S₂) : NSPACE S₁ ⊆ NSPACE S₂ := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm, f, hdec, hbig.trans h⟩

/-- **L ⊆ NL**: every deterministic log-space transducer language is also in NL. -/
theorem L_subset_NL : L ⊆ NL := by
  intro L ⟨k, tm, f, htrans, hdec, hbig⟩
  exact ⟨k, tm.toNTM, f, tm.toNTM_isTransducer htrans, tm.toNTM_decidesInSpace hdec, hbig⟩

/-- **ZPP ⊆ RP**: zero-error probabilistic ⊆ one-sided error. -/
theorem ZPP_subset_RP : ZPP ⊆ RP := Set.inter_subset_left

/-- **ZPP ⊆ coRP**. -/
theorem ZPP_subset_coRP : ZPP ⊆ coRP := Set.inter_subset_right

/-- **ZPP ⊆ NP** via `ZPP ⊆ RP ⊆ NP`. -/
theorem ZPP_subset_NP : ZPP ⊆ NP := ZPP_subset_RP.trans RP_subset_NP

/-- **RP ⊆ NEXP** via `RP ⊆ NP ⊆ NEXP`. -/
theorem RP_subset_NEXP : RP ⊆ NEXP := RP_subset_NP.trans NP_subset_NEXP

/-- **ZPP ⊆ NEXP** via `ZPP ⊆ NP ⊆ NEXP`. -/
theorem ZPP_subset_NEXP : ZPP ⊆ NEXP := ZPP_subset_NP.trans NP_subset_NEXP

/-- **DTIME ⊆ NSPACE** (composition of `DTIME ⊆ DSPACE` and `DSPACE ⊆ NSPACE`). -/
theorem DTIME_subset_NSPACE (T : ℕ → ℕ) : DTIME T ⊆ NSPACE T :=
  (DTIME_subset_DSPACE T).trans (DSPACE_subset_NSPACE T)

/-- **P ⊆ NPSPACE** via `P ⊆ PSPACE ⊆ NPSPACE`. -/
theorem P_subset_NPSPACE : P ⊆ NPSPACE :=
  Set.iUnion_mono fun _ => (DTIME_subset_DSPACE _).trans (DSPACE_subset_NSPACE _)

/-- **P ⊆ NEXP** via `P ⊆ EXP ⊆ NEXP`. -/
theorem P_subset_NEXP : P ⊆ NEXP :=
  P_subset_EXP.trans EXP_subset_NEXP

/-- **P ⊆ PP** via `P ⊆ BPP ⊆ PP`. -/
theorem P_subset_PP : P ⊆ PP := P_subset_BPP.trans BPP_subset_PP

/-- **P is closed under union**: derived from `DTIME_union` and
    polynomial-bound composition. -/
theorem P_union {L₁ L₂ : Language} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) : L₁ ∪ L₂ ∈ P := by
  obtain ⟨k₁, hdt₁⟩ := Set.mem_iUnion.mp h₁
  obtain ⟨k₂, hdt₂⟩ := Set.mem_iUnion.mp h₂
  have hunion := DTIME_union hdt₁ hdt₂
  refine Set.mem_iUnion.mpr ⟨max k₁ k₂, DTIME_mono ?_ hunion⟩
  exact BigO.add
    (BigO.pow_le_pow_right (Nat.le_max_left k₁ k₂))
    (BigO.pow_le_pow_right (Nat.le_max_right k₁ k₂))

/-- **P is closed under intersection**: via `L₁ ∩ L₂ = (L₁ᶜ ∪ L₂ᶜ)ᶜ`. -/
theorem P_inter {L₁ L₂ : Language} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) : L₁ ∩ L₂ ∈ P := by
  have hcomp : (L₁ᶜ ∪ L₂ᶜ)ᶜ ∈ P := P_compl (P_union (P_compl h₁) (P_compl h₂))
  have heq : (L₁ᶜ ∪ L₂ᶜ)ᶜ = L₁ ∩ L₂ := by
    ext x; simp
  rwa [heq] at hcomp

/-- **P is closed under set difference**: `L₁ \ L₂ = L₁ ∩ L₂ᶜ`. -/
theorem P_diff {L₁ L₂ : Language} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) : L₁ \ L₂ ∈ P := by
  rw [Set.diff_eq]
  exact P_inter h₁ (P_compl h₂)

/-- **P is closed under symmetric difference**:
    `L₁ △ L₂ = (L₁ \ L₂) ∪ (L₂ \ L₁)`. Together with `P_compl`/`P_union`/`P_inter`
    this makes `P` a Boolean subalgebra of the languages. -/
theorem P_symmDiff {L₁ L₂ : Language} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    (L₁ \ L₂) ∪ (L₂ \ L₁) ∈ P :=
  P_union (P_diff h₁ h₂) (P_diff h₂ h₁)

end Complexity
