/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.ConsistencyPropertyEqOn
/-!
# Fair enumeration for a fragment-relative consistency property (issue #8 tranche 2, commit 3)

Generic over a universe `U` and a `ConsistencyPropertyEqOn U`: a finite consistent `S₀ ⊆ U`
extends to a Henkin-complete `S* ⊇ S₀`. The schedule is a **prefix sweep** — `stage (n+1)`
processes requests `0,…,n` starting from `stage n` — so, given a surjection `e : ℕ → Request U`,
each request `e k` is processed during every sweep after `k` (fairness with no arithmetic about
`Nat.pair`), while each sweep adds only finitely many sentences.

Branching / witness rules make a classical choice at the moment the request fires; the
triggering sentence stays present, so re-processing is harmless. The union `S*` is never claimed
to be in `C.sets` (Finding 1) — only that each closure target cohabits a later stage.

The remaining piece (the `HenkinComplete Sstar` acceptance theorem) is the per-field limit proof;
it consumes `request_fires_after` plus per-request "what `process` adds" facts.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {U : Set L[[ℕ]].Sentenceω}

/-- A scheduling request. Decomposition rules dispatch on the trigger's outermost shape; `idx`
supplies the per-index parameter (component / instance / which negated-implication conclusion)
and is ignored by the classical-choice rules. -/
inductive Request (U : Set L[[ℕ]].Sentenceω) where
  | decompose (t : U) (idx : ℕ)
  | impC1 (t : U)
  | eqRefl (c : ℕ)
  | eqSymm (a b : ℕ)
  | eqTrans (a b d : ℕ)
  | relCongr (l : ℕ) (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l) (b : ℕ)

namespace Request

/-- The request type is countable when `U` and the relation symbols are. -/
instance instCountable [Countable U] [Countable (Σ l, L.Relations l)] :
    Countable (Request U) := by
  have : ∀ l, Countable (L.Relations l) := countable_relations_each
  let f : Request U → (U × ℕ) ⊕ U ⊕ ℕ ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ) ⊕
      (Σ l, L.Relations l × (Fin l → ℕ) × Fin l × ℕ) :=
    fun r => match r with
      | .decompose t idx => .inl (t, idx)
      | .impC1 t => .inr (.inl t)
      | .eqRefl c => .inr (.inr (.inl c))
      | .eqSymm a b => .inr (.inr (.inr (.inl (a, b))))
      | .eqTrans a b d => .inr (.inr (.inr (.inr (.inl (a, b, d)))))
      | .relCongr l R g i b => .inr (.inr (.inr (.inr (.inr ⟨l, R, g, i, b⟩))))
  have hf : Function.Injective f := by
    intro r₁ r₂ h
    cases r₁ <;> cases r₂ <;>
      simp only [f, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
        Sigma.mk.injEq] at h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain rfl := h; rfl
    · obtain rfl := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, h⟩ := h
      rw [heq_eq_eq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  exact hf.countable

end Request

/-! ## One processing step -/

/-- A member of the consistency family, bundled with its membership proof. -/
abbrev SetIn (P : ConsistencyPropertyEqOn U) := {T : Set L[[ℕ]].Sentenceω // T ∈ P.sets}

variable {P : ConsistencyPropertyEqOn U}

/-- Process a decomposition request: if the trigger `t` is present, add the target dictated by
its outermost shape (the per-index rules use `idx`; the branching/witness rules choose
classically). -/
private noncomputable def processDecompose (S : SetIn P) (t : U) (idx : ℕ) : SetIn P := by
  classical
  exact if hs : (t : L[[ℕ]].Sentenceω) ∈ S.1 then
    match heq : (t : L[[ℕ]].Sentenceω) with
    | .imp (.imp φ ψ) .falsum =>
      -- C1' (also subsumes C2 double-negation when `ψ = falsum`): add `φ` or `ψ.not`.
      have hmem : ((BoundedFormulaInf.imp φ ψ).imp BoundedFormulaInf.falsum) ∈ S.1 := heq ▸ hs
      if idx = 0 then ⟨S.1 ∪ {φ}, (P.C1_neg_imp S.1 S.2 φ ψ hmem).1⟩
      else ⟨S.1 ∪ {ψ.not}, (P.C1_neg_imp S.1 S.2 φ ψ hmem).2⟩
    | .imp (.iInf φs) .falsum =>
      -- C3': choose a component whose negation stays consistent.
      have hmem : ((BoundedFormulaInf.iInf φs).imp BoundedFormulaInf.falsum) ∈ S.1 := heq ▸ hs
      let h := P.C3_neg_iInf S.1 S.2 φs hmem
      ⟨S.1 ∪ {(φs (Classical.choose h)).not}, Classical.choose_spec h⟩
    | .imp (.iSup φs) .falsum =>
      -- C4': every component's negation is consistent; add the `idx`-th.
      have hmem : ((BoundedFormulaInf.iSup φs).imp BoundedFormulaInf.falsum) ∈ S.1 := heq ▸ hs
      ⟨S.1 ∪ {(φs idx).not}, P.C4_neg_iSup S.1 S.2 φs hmem idx⟩
    | .imp (.all φ) .falsum =>
      -- negated universal: choose a witness.
      have hmem : ((BoundedFormulaInf.all φ).imp BoundedFormulaInf.falsum) ∈ S.1 := heq ▸ hs
      let h := P.neg_all_witness S.1 S.2 φ hmem
      ⟨S.1 ∪ {(instConst (Classical.choose h) φ).not}, Classical.choose_spec h⟩
    | .imp φ ψ =>
      -- C1: add whichever branch is consistent.
      have hmem : (BoundedFormulaInf.imp φ ψ) ∈ S.1 := heq ▸ hs
      if hb : S.1 ∪ {φ.not} ∈ P.sets then ⟨S.1 ∪ {φ.not}, hb⟩
      else ⟨S.1 ∪ {ψ}, (P.C1_imp S.1 S.2 φ ψ hmem).resolve_left hb⟩
    | .iInf φs =>
      have hmem : (BoundedFormulaInf.iInf φs) ∈ S.1 := heq ▸ hs
      ⟨S.1 ∪ {φs idx}, P.C3_iInf S.1 S.2 φs hmem idx⟩
    | .iSup φs =>
      have hmem : (BoundedFormulaInf.iSup φs) ∈ S.1 := heq ▸ hs
      let h := P.C4_iSup S.1 S.2 φs hmem
      ⟨S.1 ∪ {φs (Classical.choose h)}, Classical.choose_spec h⟩
    | .all φ =>
      have hmem : (BoundedFormulaInf.all φ) ∈ S.1 := heq ▸ hs
      ⟨S.1 ∪ {instConst idx φ}, P.all_inst S.1 S.2 φ hmem idx⟩
    | _ => S
  else S

/-- Process a `C1` request: inspects only the **outer** `imp` constructor (so it reduces on
`φ.imp ψ` regardless of whether `φ`/`ψ` later specialize to the negation encoding — the field
that a shape-dispatching `decompose` leaves stuck). -/
private noncomputable def processImpC1 (S : SetIn P) (t : U) : SetIn P := by
  classical
  exact if hs : (t : L[[ℕ]].Sentenceω) ∈ S.1 then
    match heq : (t : L[[ℕ]].Sentenceω) with
    | .imp φ ψ =>
      have hmem : (BoundedFormulaInf.imp φ ψ) ∈ S.1 := heq ▸ hs
      if hb : S.1 ∪ {φ.not} ∈ P.sets then ⟨S.1 ∪ {φ.not}, hb⟩
      else ⟨S.1 ∪ {ψ}, (P.C1_imp S.1 S.2 φ ψ hmem).resolve_left hb⟩
    | _ => S
  else S

/-- Process one request. -/
private noncomputable def process (S : SetIn P) : Request U → SetIn P := by
  classical
  intro request
  exact match request with
    | .decompose t idx => processDecompose S t idx
    | .impC1 t => processImpC1 S t
    | .eqRefl c => ⟨S.1 ∪ {constEq c c}, P.eq_refl S.1 S.2 c⟩
    | .eqSymm a b =>
      if h : constEq a b ∈ S.1 then
        ⟨S.1 ∪ {constEq b a}, P.eq_symm S.1 S.2 a b h⟩
      else S
    | .eqTrans a b d =>
      if h : constEq a b ∈ S.1 ∧ constEq b d ∈ S.1 then
        ⟨S.1 ∪ {constEq a d}, P.eq_trans S.1 S.2 a b d h.1 h.2⟩
      else S
    | .relCongr l R g i b =>
      if h : relInst R g ∈ S.1 ∧ constEq (g i) b ∈ S.1 then
        ⟨S.1 ∪ {relInst R (Function.update g i b)},
          P.rel_congr S.1 S.2 l R g i b h.1 h.2⟩
      else S

/-- Processing only grows the set (`processDecompose`). -/
private theorem subset_processDecompose (S : SetIn P) (t : U) (idx : ℕ) :
    S.1 ⊆ (processDecompose S t idx).1 := by
  unfold processDecompose
  split
  · split <;> (try split) <;>
      first | exact Set.subset_union_left | exact subset_rfl
  · exact subset_rfl

private theorem subset_processImpC1 (S : SetIn P) (t : U) : S.1 ⊆ (processImpC1 S t).1 := by
  unfold processImpC1
  split
  · split <;> (try split) <;> first | exact Set.subset_union_left | exact subset_rfl
  · exact subset_rfl

/-- Processing only grows the set. -/
private theorem subset_process (S : SetIn P) (r : Request U) : S.1 ⊆ (process S r).1 := by
  cases r with
  | decompose t idx => exact subset_processDecompose S t idx
  | impC1 t => exact subset_processImpC1 S t
  | eqRefl c => exact Set.subset_union_left
  | eqSymm a b =>
    simp only [process]; split_ifs <;> first | exact Set.subset_union_left | exact subset_rfl
  | eqTrans a b d =>
    simp only [process]; split_ifs <;> first | exact Set.subset_union_left | exact subset_rfl
  | relCongr l R g i b =>
    simp only [process]; split_ifs <;> first | exact Set.subset_union_left | exact subset_rfl

/-! ## The prefix-sweep schedule -/

variable (e : ℕ → Request U)

/-- One sweep: process requests `e 0, …, e n` in order. -/
private noncomputable def sweep (S : SetIn P) : ℕ → SetIn P
  | 0 => process S (e 0)
  | (n + 1) => process (sweep S n) (e (n + 1))

/-- `stage (n+1)` processes requests `0,…,n` starting from `stage n`. -/
noncomputable def stage (S₀ : SetIn P) : ℕ → SetIn P
  | 0 => S₀
  | (n + 1) => sweep e (stage S₀ n) n

private theorem subset_sweep (S : SetIn P) (n : ℕ) : S.1 ⊆ (sweep e S n).1 := by
  induction n with
  | zero => exact subset_process S (e 0)
  | succ n ih => exact ih.trans (subset_process (sweep e S n) (e (n + 1)))

/-- **Stage monotonicity** (one step). -/
private theorem stage_subset_succ (S₀ : SetIn P) (n : ℕ) :
    (stage e S₀ n).1 ⊆ (stage e S₀ (n + 1)).1 :=
  subset_sweep e (stage e S₀ n) n

/-- **Stage monotonicity**. -/
private theorem stage_mono (S₀ : SetIn P) {m n : ℕ} (h : m ≤ n) :
    (stage e S₀ m).1 ⊆ (stage e S₀ n).1 := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (stage_subset_succ e S₀ n)
    · exact subset_rfl
/-- **Each stage lies in `U`**. -/
private theorem stage_subset_U (S₀ : SetIn P) (n : ℕ) : (stage e S₀ n).1 ⊆ U :=
  P.subset_U _ (stage e S₀ n).2

/-- **The limit** of the enumeration. -/
noncomputable def Sstar (S₀ : SetIn P) : Set L[[ℕ]].Sentenceω := ⋃ n, (stage e S₀ n).1

private theorem subset_Sstar (S₀ : SetIn P) : S₀.1 ⊆ Sstar e S₀ :=
  fun _ hx => Set.mem_iUnion.mpr ⟨0, hx⟩

private theorem Sstar_subset_U (S₀ : SetIn P) : Sstar e S₀ ⊆ U :=
  Set.iUnion_subset fun n => stage_subset_U e S₀ n

private theorem mem_Sstar_iff (S₀ : SetIn P) {x : L[[ℕ]].Sentenceω} :
    x ∈ Sstar e S₀ ↔ ∃ n, x ∈ (stage e S₀ n).1 := Set.mem_iUnion

/-! ## The firing API -/

/-- The accumulated set just before request `e k` is processed in a sweep from `S`. -/
private noncomputable def beforeRequest (S : SetIn P) : ℕ → SetIn P
  | 0 => S
  | (k + 1) => sweep e S k

private theorem subset_beforeRequest (S : SetIn P) (k : ℕ) : S.1 ⊆ (beforeRequest e S k).1 := by
  cases k with
  | zero => exact subset_rfl
  | succ k => exact subset_sweep e S k

/-- Processing `e k` at its accumulated point advances the sweep by one — nearly definitional. -/
private theorem process_beforeRequest_eq_sweep (S : SetIn P) (k : ℕ) :
    process (beforeRequest e S k) (e k) = sweep e S k := by
  cases k <;> rfl

/-- Sweeps are monotone in the number of requests processed. -/
private theorem sweep_mono (S : SetIn P) {k n : ℕ} (h : k ≤ n) :
    (sweep e S k).1 ⊆ (sweep e S n).1 := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (subset_process (sweep e S n) (e (n + 1)))
    · exact subset_rfl

/-- **The firing consumer lemma** (fairness): for a surjective schedule, every request fires in
some sweep after any given stage `m` — the pre-accumulator contains `stage m`, and the process
output at the firing lands inside `stage (n+1)`. -/
private theorem request_fires_after
    (he : Function.Surjective e) (S₀ : SetIn P) (r : Request U) (m : ℕ) :
    ∃ n, m ≤ n ∧ ∃ acc : SetIn P,
      (stage e S₀ m).1 ⊆ acc.1 ∧ (process acc r).1 ⊆ (stage e S₀ (n + 1)).1 := by
  obtain ⟨k, rfl⟩ := he r
  refine ⟨max m k, le_max_left m k, beforeRequest e (stage e S₀ (max m k)) k,
    (stage_mono e S₀ (le_max_left m k)).trans (subset_beforeRequest e _ k), ?_⟩
  rw [process_beforeRequest_eq_sweep]
  exact sweep_mono e (stage e S₀ (max m k)) (le_max_right m k)

/-! ## What each firing adds (process specs) -/

private theorem spec_impC1 (acc : SetIn P) (φ ψ : L[[ℕ]].Sentenceω) (hU : (φ.imp ψ) ∈ U)
    (hmem : φ.imp ψ ∈ acc.1) :
    φ.not ∈ (process acc (.impC1 ⟨φ.imp ψ, hU⟩)).1 ∨
      ψ ∈ (process acc (.impC1 ⟨φ.imp ψ, hU⟩)).1 := by
  change φ.not ∈ (processImpC1 acc ⟨φ.imp ψ, hU⟩).1 ∨
    ψ ∈ (processImpC1 acc ⟨φ.imp ψ, hU⟩).1
  simp only [processImpC1, dite_eq_left hmem]
  split_ifs <;> [left; right] <;> exact Set.mem_union_right _ rfl

private theorem spec_negImp (acc : SetIn P) (φ ψ : L[[ℕ]].Sentenceω) (hU : ((φ.imp ψ).not) ∈ U)
    (hmem : (φ.imp ψ).not ∈ acc.1) (idx : ℕ) :
    (idx = 0 → φ ∈ (process acc (.decompose ⟨(φ.imp ψ).not, hU⟩ idx)).1) ∧
    (idx ≠ 0 → ψ.not ∈ (process acc (.decompose ⟨(φ.imp ψ).not, hU⟩ idx)).1) := by
  simp only [process, processDecompose, dite_eq_left hmem]
  by_cases hidx : idx = 0
  · rw [ite_eq_left hidx]
    exact ⟨fun _ => Set.mem_union_right _ rfl, fun h => absurd hidx h⟩
  · rw [ite_eq_right hidx]
    exact ⟨fun h => absurd h hidx, fun _ => Set.mem_union_right _ rfl⟩

private theorem spec_iInf (acc : SetIn P) (φs : ℕ → L[[ℕ]].Sentenceω)
    (hU : (BoundedFormulaω.iInf φs) ∈ U) (idx : ℕ) (hmem : BoundedFormulaω.iInf φs ∈ acc.1) :
    φs idx ∈ (process acc (.decompose ⟨BoundedFormulaω.iInf φs, hU⟩ idx)).1 := by
  change φs idx ∈ (processDecompose acc ⟨BoundedFormulaω.iInf φs, hU⟩ idx).1
  simp only [processDecompose, dite_eq_left hmem]
  exact Set.mem_union_right _ rfl

private theorem spec_negIInf (acc : SetIn P) (φs : ℕ → L[[ℕ]].Sentenceω)
    (hU : ((BoundedFormulaω.iInf φs).not) ∈ U) (idx : ℕ)
    (hmem : (BoundedFormulaω.iInf φs).not ∈ acc.1) :
    ∃ k, (φs k).not ∈ (process acc (.decompose ⟨(BoundedFormulaω.iInf φs).not, hU⟩ idx)).1 := by
  change ∃ k, (φs k).not ∈ (processDecompose acc ⟨(BoundedFormulaω.iInf φs).not, hU⟩ idx).1
  simp only [processDecompose, dite_eq_left hmem]
  exact ⟨_, Set.mem_union_right _ rfl⟩

private theorem spec_iSup (acc : SetIn P) (φs : ℕ → L[[ℕ]].Sentenceω)
    (hU : (BoundedFormulaω.iSup φs) ∈ U) (idx : ℕ) (hmem : BoundedFormulaω.iSup φs ∈ acc.1) :
    ∃ k, φs k ∈ (process acc (.decompose ⟨BoundedFormulaω.iSup φs, hU⟩ idx)).1 := by
  change ∃ k, φs k ∈ (processDecompose acc ⟨BoundedFormulaω.iSup φs, hU⟩ idx).1
  simp only [processDecompose, dite_eq_left hmem]
  exact ⟨_, Set.mem_union_right _ rfl⟩

private theorem spec_negISup (acc : SetIn P) (φs : ℕ → L[[ℕ]].Sentenceω)
    (hU : ((BoundedFormulaω.iSup φs).not) ∈ U) (idx : ℕ)
    (hmem : (BoundedFormulaω.iSup φs).not ∈ acc.1) :
    (φs idx).not ∈ (process acc (.decompose ⟨(BoundedFormulaω.iSup φs).not, hU⟩ idx)).1 := by
  change (φs idx).not ∈ (processDecompose acc ⟨(BoundedFormulaω.iSup φs).not, hU⟩ idx).1
  simp only [processDecompose, dite_eq_left hmem]
  exact Set.mem_union_right _ rfl

private theorem spec_allInst (acc : SetIn P) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hU : (φ.all) ∈ U) (idx : ℕ) (hmem : φ.all ∈ acc.1) :
    instConst idx φ ∈ (process acc (.decompose ⟨φ.all, hU⟩ idx)).1 := by
  change instConst idx φ ∈ (processDecompose acc ⟨φ.all, hU⟩ idx).1
  simp only [processDecompose, dite_eq_left hmem]
  exact Set.mem_union_right _ rfl

private theorem spec_negAll (acc : SetIn P) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hU : (φ.all.not) ∈ U) (idx : ℕ) (hmem : φ.all.not ∈ acc.1) :
    ∃ c, (instConst c φ).not ∈ (process acc (.decompose ⟨φ.all.not, hU⟩ idx)).1 := by
  change ∃ c, (instConst c φ).not ∈ (processDecompose acc ⟨φ.all.not, hU⟩ idx).1
  simp only [processDecompose, dite_eq_left hmem]
  exact ⟨_, Set.mem_union_right _ rfl⟩

private theorem spec_eqRefl (acc : SetIn P) (c : ℕ) :
    constEq c c ∈ (process acc (.eqRefl c)).1 := Set.mem_union_right _ rfl

private theorem spec_eqSymm (acc : SetIn P) (a b : ℕ) (hmem : constEq a b ∈ acc.1) :
    constEq b a ∈ (process acc (.eqSymm a b)).1 := by
  simp only [process, dite_eq_left hmem]; exact Set.mem_union_right _ rfl

private theorem spec_eqTrans (acc : SetIn P) (a b d : ℕ)
    (h1 : constEq a b ∈ acc.1) (h2 : constEq b d ∈ acc.1) :
    constEq a d ∈ (process acc (.eqTrans a b d)).1 := by
  simp only [process, dite_eq_left (⟨h1, h2⟩ : constEq a b ∈ acc.1 ∧ constEq b d ∈ acc.1)]
  exact Set.mem_union_right _ rfl

private theorem spec_relCongr
    (acc : SetIn P) (l : ℕ) (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l)
    (b : ℕ) (h1 : relInst R g ∈ acc.1) (h2 : constEq (g i) b ∈ acc.1) :
    relInst R (Function.update g i b) ∈ (process acc (.relCongr l R g i b)).1 := by
  simp only [process, dite_eq_left (⟨h1, h2⟩ : relInst R g ∈ acc.1 ∧ constEq (g i) b ∈ acc.1)]
  exact Set.mem_union_right _ rfl

/-! ## The limit is Henkin-complete -/

variable (he : Function.Surjective e) (S₀ : SetIn P)

include he

/-- If a firing of `r` on any accumulator containing `member` adds `target`, and `member ∈ S*`,
then `target ∈ S*`. -/
private theorem mem_Sstar_of_fires {member target : L[[ℕ]].Sentenceω} (r : Request U)
    (hmem : member ∈ Sstar e S₀)
    (hspec : ∀ acc : SetIn P, member ∈ acc.1 → target ∈ (process acc r).1) :
    target ∈ Sstar e S₀ := by
  obtain ⟨m, hm⟩ := (mem_Sstar_iff e S₀).mp hmem
  obtain ⟨n, _, acc, hacc, hout⟩ := request_fires_after e he S₀ r m
  exact (mem_Sstar_iff e S₀).mpr ⟨n + 1, hout (hspec acc (hacc hm))⟩

/-- Disjunctive variant (for branching fields). -/
private theorem or_mem_Sstar_of_fires {member t₁ t₂ : L[[ℕ]].Sentenceω} (r : Request U)
    (hmem : member ∈ Sstar e S₀)
    (hspec : ∀ acc : SetIn P, member ∈ acc.1 →
      t₁ ∈ (process acc r).1 ∨ t₂ ∈ (process acc r).1) :
    t₁ ∈ Sstar e S₀ ∨ t₂ ∈ Sstar e S₀ := by
  obtain ⟨m, hm⟩ := (mem_Sstar_iff e S₀).mp hmem
  obtain ⟨n, _, acc, hacc, hout⟩ := request_fires_after e he S₀ r m
  rcases hspec acc (hacc hm) with h | h
  · exact Or.inl ((mem_Sstar_iff e S₀).mpr ⟨n + 1, hout h⟩)
  · exact Or.inr ((mem_Sstar_iff e S₀).mpr ⟨n + 1, hout h⟩)

/-- Existential variant (for witness fields). -/
private theorem exists_mem_Sstar_of_fires {member : L[[ℕ]].Sentenceω} {α : Sort*}
    {motive : α → L[[ℕ]].Sentenceω} (r : Request U) (hmem : member ∈ Sstar e S₀)
    (hspec : ∀ acc : SetIn P, member ∈ acc.1 → ∃ a, motive a ∈ (process acc r).1) :
    ∃ a, motive a ∈ Sstar e S₀ := by
  obtain ⟨m, hm⟩ := (mem_Sstar_iff e S₀).mp hmem
  obtain ⟨n, _, acc, hacc, hout⟩ := request_fires_after e he S₀ r m
  obtain ⟨a, ha⟩ := hspec acc (hacc hm)
  exact ⟨a, (mem_Sstar_iff e S₀).mpr ⟨n + 1, hout ha⟩⟩

/-- Unconditional variant (for reflexivity, which has no trigger). -/
private theorem mem_Sstar_of_fires_uncond {target : L[[ℕ]].Sentenceω} (r : Request U)
    (hspec : ∀ acc : SetIn P, target ∈ (process acc r).1) : target ∈ Sstar e S₀ := by
  obtain ⟨n, _, acc, _, hout⟩ := request_fires_after e he S₀ r 0
  exact (mem_Sstar_iff e S₀).mpr ⟨n + 1, hout (hspec acc)⟩

/-- Two-premise variant (for transitivity / relation congruence). -/
private theorem mem_Sstar_of_fires₂ {m₁ m₂ target : L[[ℕ]].Sentenceω} (r : Request U)
    (h₁ : m₁ ∈ Sstar e S₀) (h₂ : m₂ ∈ Sstar e S₀)
    (hspec : ∀ acc : SetIn P, m₁ ∈ acc.1 → m₂ ∈ acc.1 → target ∈ (process acc r).1) :
    target ∈ Sstar e S₀ := by
  obtain ⟨n₁, hn₁⟩ := (mem_Sstar_iff e S₀).mp h₁
  obtain ⟨n₂, hn₂⟩ := (mem_Sstar_iff e S₀).mp h₂
  obtain ⟨n, _, acc, hacc, hout⟩ := request_fires_after e he S₀ r (max n₁ n₂)
  exact (mem_Sstar_iff e S₀).mpr ⟨n + 1, hout (hspec acc
    (hacc (stage_mono e S₀ (le_max_left n₁ n₂) hn₁))
    (hacc (stage_mono e S₀ (le_max_right n₁ n₂) hn₂)))⟩

/-- **The limit is Henkin-complete.** -/
private theorem henkinComplete_Sstar : HenkinComplete U (Sstar e S₀) where
  subset_U := Sstar_subset_U e S₀
  no_falsum := by
    intro hf
    obtain ⟨n, hn⟩ := (mem_Sstar_iff e S₀).mp hf
    exact P.C0_no_falsum _ (stage e S₀ n).2 hn
  no_contradiction φ := by
    rintro ⟨h₁, h₂⟩
    obtain ⟨m₁, hm₁⟩ := (mem_Sstar_iff e S₀).mp h₁
    obtain ⟨m₂, hm₂⟩ := (mem_Sstar_iff e S₀).mp h₂
    exact P.C0_no_contradiction _ (stage e S₀ (max m₁ m₂)).2 φ
      ⟨stage_mono e S₀ (le_max_left m₁ m₂) hm₁, stage_mono e S₀ (le_max_right m₁ m₂) hm₂⟩
  imp φ ψ h :=
    or_mem_Sstar_of_fires e he S₀ (.impC1 ⟨φ.imp ψ, Sstar_subset_U e S₀ h⟩) h
      (fun acc hacc => spec_impC1 acc φ ψ _ hacc)
  neg_imp φ ψ h :=
    ⟨mem_Sstar_of_fires e he S₀ (.decompose ⟨(φ.imp ψ).not, Sstar_subset_U e S₀ h⟩ 0) h
        (fun acc hacc => (spec_negImp acc φ ψ _ hacc 0).1 rfl),
     mem_Sstar_of_fires e he S₀ (.decompose ⟨(φ.imp ψ).not, Sstar_subset_U e S₀ h⟩ 1) h
        (fun acc hacc => (spec_negImp acc φ ψ _ hacc 1).2 (by decide))⟩
  not_not φ h :=
    mem_Sstar_of_fires e he S₀ (.decompose ⟨φ.not.not, Sstar_subset_U e S₀ h⟩ 0) h
      (fun acc hacc => (spec_negImp acc φ BoundedFormulaω.falsum _ hacc 0).1 rfl)
  iInf φs h k :=
    mem_Sstar_of_fires e he S₀ (.decompose ⟨BoundedFormulaω.iInf φs, Sstar_subset_U e S₀ h⟩ k) h
      (fun acc hacc => spec_iInf acc φs _ k hacc)
  neg_iInf φs h :=
    exists_mem_Sstar_of_fires e he S₀
      (.decompose ⟨(BoundedFormulaω.iInf φs).not, Sstar_subset_U e S₀ h⟩ 0) h
      (fun acc hacc => spec_negIInf acc φs _ 0 hacc)
  iSup φs h :=
    exists_mem_Sstar_of_fires e he S₀
      (.decompose ⟨BoundedFormulaω.iSup φs, Sstar_subset_U e S₀ h⟩ 0) h
      (fun acc hacc => spec_iSup acc φs _ 0 hacc)
  neg_iSup φs h k :=
    mem_Sstar_of_fires e he S₀
      (.decompose ⟨(BoundedFormulaω.iSup φs).not, Sstar_subset_U e S₀ h⟩ k) h
      (fun acc hacc => spec_negISup acc φs _ k hacc)
  eq_refl c := mem_Sstar_of_fires_uncond e he S₀ (.eqRefl c) (fun acc => spec_eqRefl acc c)
  eq_symm a b h :=
    mem_Sstar_of_fires e he S₀ (.eqSymm a b) h (fun acc hacc => spec_eqSymm acc a b hacc)
  eq_trans a b d h₁ h₂ :=
    mem_Sstar_of_fires₂ e he S₀ (.eqTrans a b d) h₁ h₂
      (fun acc hm₁ hm₂ => spec_eqTrans acc a b d hm₁ hm₂)
  rel_congr l R g i b h₁ h₂ :=
    mem_Sstar_of_fires₂ e he S₀ (.relCongr l R g i b) h₁ h₂
      (fun acc hm₁ hm₂ => spec_relCongr acc l R g i b hm₁ hm₂)
  all_inst φ h c :=
    mem_Sstar_of_fires e he S₀ (.decompose ⟨φ.all, Sstar_subset_U e S₀ h⟩ c) h
      (fun acc hacc => spec_allInst acc φ _ c hacc)
  neg_all_witness φ h :=
    exists_mem_Sstar_of_fires e he S₀ (.decompose ⟨φ.all.not, Sstar_subset_U e S₀ h⟩ 0) h
      (fun acc hacc => spec_negAll acc φ _ 0 hacc)

omit he in
/-- **Fair enumeration** (the acceptance theorem): a consistent set in a `ConsistencyPropertyEqOn
U` (over a countable `U` and countable relation symbols) extends to a Henkin-complete `S* ⊇ S₀`
inside `U`. -/
theorem exists_henkinComplete [Countable U] [Countable (Σ l, L.Relations l)] :
    ∃ Sstar : Set L[[ℕ]].Sentenceω,
      S₀.1 ⊆ Sstar ∧ Sstar ⊆ U ∧ HenkinComplete U Sstar := by
  have : Nonempty (Request U) := ⟨.eqRefl 0⟩
  obtain ⟨e', he'⟩ := exists_surjective_nat (Request U)
  exact ⟨Sstar e' S₀, subset_Sstar e' S₀, Sstar_subset_U e' S₀,
    henkinComplete_Sstar e' he' S₀⟩

end FirstOrder.Language
