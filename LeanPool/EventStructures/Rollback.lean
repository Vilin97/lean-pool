/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
import LeanPool.EventStructures.Configuration
import LeanPool.EventStructures.Path
import LeanPool.EventStructures.FinitePoset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card

/-!
# Rollback

This module formalises rollback of an event on a configuration: a maximal
sub-configuration omitting the chosen event. It shows the canonical rollback
(removing the future of the event) is the unique rollback, proves redoability
and causal safety, and—given a finite representation—correctness (the original
configuration is reachable from the rollback) and minimality.
-/

namespace EventStructures

variable (es : EventStructure)

namespace Rollback

open Configuration
local infix:50 " ⊢ " => enables es

/-- A rollback of event `e` on configuration `c` is a maximal configuration `m`
    with `m ⊆ c` and `e ∉ m`. -/
def isRollback (c : Conf es) (e : es.Event) (m : Conf es) : Prop :=
  m.1 ⊆ c.1 ∧ e ∉ m.1 ∧
  ∀ m' : Conf es, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1

/-- The set of all rollbacks of event `e` on configuration `c`. -/
def Rollbacks (c : Conf es) (e : es.Event) : Set (Conf es) :=
  {m | isRollback es c e m}

/-- Candidate configurations for rollback. -/
def RollbackCandidates (c : Conf es) (e : es.Event) : Set (Conf es) :=
  {m | m.1 ⊆ c.1 ∧ e ∉ m.1}

@[simp] lemma rollback_subset {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) : m.1 ⊆ c.1 :=
  h.1

@[simp] lemma rollback_not_mem {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) : e ∉ m.1 :=
  h.2.1

lemma rollback_maximal {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) :
    ∀ m' : Conf es, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 :=
  h.2.2

lemma isRollback_iff_maximal {c : Conf es} {e : es.Event} {m : Conf es} :
    isRollback es c e m ↔ m ∈ RollbackCandidates es c e ∧
      ∀ m' : Conf es, m' ∈ RollbackCandidates es c e → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, fun m' ⟨hm'sub, hm'not⟩ hsubset => h.2.2 m' hm'sub hm'not hsubset⟩
  · rintro ⟨⟨hmsub, hmnot⟩, hmax⟩
    exact ⟨hmsub, hmnot, fun m' hm'sub hm'not hsubset =>
      hmax m' ⟨hm'sub, hm'not⟩ hsubset⟩

lemma rollback_subset_future {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) : m.1 ⊆ c.1 \ es.future e := by
  intro x hx
  exact ⟨h.1 hx, fun hxFuture => h.2.1 ((m.2).2 hx hxFuture)⟩

/-- Removing the future of `e` from a configuration keeps it a configuration. -/
lemma rollback_future_isConf {c : Conf es} {e : es.Event} :
    isConf es (c.1 \ es.future e) := by
  refine ⟨fun ⟨h₁c, _⟩ ⟨h₂c, _⟩ => c.2.1 h₁c h₂c, ?_⟩
  intro x y ⟨hxc, hxf⟩ hy
  exact ⟨c.2.2 hxc hy, fun hyf => hxf (le_trans hyf hy)⟩

/-- The canonical rollback configuration: remove all events causally after `e`. -/
def rollbackFuture (c : Conf es) (e : es.Event) : Conf es :=
  ⟨c.1 \ es.future e, rollback_future_isConf (es := es) (c := c)⟩

@[simp] lemma rollbackFuture_val (c : Conf es) (e : es.Event) :
    (@rollbackFuture es c e).1 = c.1 \ es.future e :=
  rfl

lemma rollbackFuture_mem {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (@rollbackFuture es c e).1 ↔ x ∈ c.1 ∧ x ∉ es.future e :=
  Iff.rfl

/-- Redoability: `e` is enabled in `rollback(c,e)` when `e ∈ c`. -/
lemma rollback_redoable {c : Conf es} {e : es.Event} (he : e ∈ c.1) :
    (@rollbackFuture es c e).1 ⊢ e := by
  refine ⟨rollback_future_isConf (es := es) (c := c), fun hmem => hmem.2 le_rfl,
    fun e' he' => c.2.1 he he'.1, ?_⟩
  -- The strict past of e is contained in rollback
  intro x hx
  exact ⟨c.2.2 he (le_of_lt hx), fun h => not_le_of_gt hx h⟩

/-- Causal safety: Rollback removes exactly the causal consequences of `e`. -/
lemma rollback_causal_safety {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (@rollbackFuture es c e).1 → x ∉ es.future e :=
  fun hx => hx.2

/-- The canonical rollback is a rollback for `c` and `e`. -/
lemma rollback_future {c : Conf es} {e : es.Event} :
    isRollback es c e (@rollbackFuture es c e) := by
  -- Subset of c, e not in rollback, and maximality.
  refine ⟨fun _ hx => hx.1, fun he => he.2 le_rfl, ?_⟩
  intro m' hm'sub hm'not _ _ hx
  exact ⟨hm'sub hx, fun h => hm'not (m'.2.2 hx h)⟩

/-- Any rollback coincides with the canonical rollback. -/
@[simp] lemma rollback_eq_future {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) : m.1 = c.1 \ es.future e := by
  refine Set.Subset.antisymm (rollback_subset_future (es := es) h) ?_
  -- The canonical rollback is also a candidate, so m must contain it by maximality.
  exact h.2.2 (@rollbackFuture es c e) (fun x hx => hx.1) (fun he => he.2 le_rfl)
    (rollback_subset_future (es := es) h)

/-- Rollbacks are unique when they exist. -/
lemma rollback_unique {c : Conf es} {e : es.Event}
    {m₁ m₂ : Conf es} (h₁ : isRollback es c e m₁) (h₂ : isRollback es c e m₂) :
    m₁ = m₂ := by
  apply Subtype.ext
  rw [rollback_eq_future (es := es) h₁, rollback_eq_future (es := es) h₂]

/-- The rollback is the maximum element among rollback candidates. -/
lemma rollback_maximum {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es c e m) :
    ∀ m' : Conf es, m' ∈ RollbackCandidates es c e → m'.1 ⊆ m.1 := by
  -- By uniqueness, m equals the canonical rollback; any candidate is a subset of it.
  cases rollback_unique (es := es) h (rollback_future (es := es))
  intro m' ⟨hm'sub, hm'not⟩ x hx
  exact ⟨hm'sub hx, fun hxFuture => hm'not (m'.2.2 hx hxFuture)⟩

/-- Helper: An event in the future that is not yet in a partial configuration is
    enabled there, provided the partial configuration contains its strict past
    and is consistent. -/
lemma event_enabled_when_past_present {c : Conf es} {e x : es.Event}
    (hx : x ∈ c.1 ∩ es.future e) (c' : Conf es)
    (hxnot : x ∉ c'.1)
    (hpast : ∀ y, y < x → y ∈ c.1 ∩ es.future e → y ∈ c'.1)
    (hbase : (@rollbackFuture es c e).1 ⊆ c'.1)
    (hconf : c'.1 ⊆ c.1) :
    c'.1 ⊢ x := by
  refine ⟨c'.2, hxnot, fun y hy => c.2.1 hx.1 (hconf hy), ?_⟩
  -- Past: the strict past of x is in c'
  intro y hy
  have hyc : y ∈ c.1 := c.2.2 hx.1 (le_of_lt hy)
  by_cases hyf : y ∈ es.future e
  · -- y is in the future of e, so it was added before x
    exact hpast y hy ⟨hyc, hyf⟩
  · -- y is not in the future of e, so it's in the rollback
    exact hbase ⟨hyc, hyf⟩

/-- Constructive: given a `Finset` representation `cF` of the underlying configuration `c`,
    there is an executable list from the rollback configuration to `c`.
    Uses decidable equality and decidable strict order on events. -/
theorem execList_exists_finite [DecidableEventStructure es] {c : Conf es} {e : es.Event}
    (cF : Finset es.Event) (hcF : ∀ x, x ∈ cF ↔ x ∈ c.1) :
    Nonempty (Σ t : List es.Event, Path.ExecList es (@rollbackFuture es c e) t c) := by
  suffices H : ∀ (n : Nat) (c' : Conf es) (cF' : Finset es.Event),
      (∀ x, x ∈ cF' ↔ x ∈ c'.1) → cF' ⊆ cF →
      (cF \ cF').card = n →
      Nonempty (Σ t : List es.Event, Path.ExecList es c' t c) by
    let cR : Finset es.Event := cF.filter (fun x => ¬ e ≤ x)
    have hcR : ∀ x, x ∈ cR ↔ x ∈ (@rollbackFuture es c e).1 := by
      intro x
      simp only [cR, Finset.mem_filter, hcF, rollbackFuture_mem,
        EventStructure.future, Set.mem_setOf_eq]
    exact H _ _ cR hcR (Finset.filter_subset _ _) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c' cF' hcF' hcF'sub hcard
    by_cases hzero : n = 0
    · subst hzero
      have hsdiff_empty : cF \ cF' = ∅ := Finset.card_eq_zero.mp hcard
      have heq_finset : cF = cF' := by
        apply Finset.Subset.antisymm _ hcF'sub
        intro x hxcF
        by_cases hxcF' : x ∈ cF'
        · exact hxcF'
        · exact absurd (Finset.mem_sdiff.mpr ⟨hxcF, hxcF'⟩)
            (hsdiff_empty ▸ Finset.notMem_empty x)
      have hc_eq : c.1 = c'.1 := by
        ext x; rw [← hcF, heq_finset, hcF']
      have heq : c' = c := Subtype.ext hc_eq.symm
      subst heq
      exact ⟨⟨[], Path.ExecList.nil _⟩⟩
    · have hpos : 0 < n := Nat.pos_of_ne_zero hzero
      have hsdiff_ne : (cF \ cF').Nonempty := Finset.card_pos.mp (hcard ▸ hpos)
      obtain ⟨x, hxsdiff, hxMin⟩ := Finset.exists_minimal_dec (cF \ cF') hsdiff_ne
      obtain ⟨hxcF, hxnotcF'⟩ := Finset.mem_sdiff.mp hxsdiff
      have hxc : x ∈ c.1 := (hcF x).mp hxcF
      have hxnotc' : x ∉ c'.1 := fun h => hxnotcF' ((hcF' x).mpr h)
      have henab : c'.1 ⊢ x := by
        refine ⟨c'.2, hxnotc', ?_, ?_⟩
        · intro y hy
          have hyc : y ∈ c.1 := (hcF y).mp (hcF'sub ((hcF' y).mpr hy))
          exact c.2.1 hxc hyc
        · intro y hyx
          have hyc : y ∈ c.1 := c.2.2 hxc (le_of_lt hyx)
          have hycF : y ∈ cF := (hcF y).mpr hyc
          by_cases hycF' : y ∈ cF'
          · exact (hcF' y).mp hycF'
          · exact absurd hyx (hxMin y (Finset.mem_sdiff.mpr ⟨hycF, hycF'⟩))
      let c'' : Conf es := Path.nextConf es c' x henab
      let cF'' : Finset es.Event := insert x cF'
      have hcF'' : ∀ y, y ∈ cF'' ↔ y ∈ c''.1 := by
        intro y
        simp only [cF'', Finset.mem_insert, c'', Path.nextConf, Set.mem_union,
          Set.mem_singleton_iff]
        rw [hcF']
        tauto
      have hcF''sub : cF'' ⊆ cF := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxcF
        · exact hcF'sub hy
      have hcard'' : (cF \ cF'').card = n - 1 := by
        have h_eq : cF \ cF'' = (cF \ cF').erase x := by
          ext y
          simp only [cF'', Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
          tauto
        rw [h_eq, Finset.card_erase_of_mem hxsdiff, hcard]
      obtain ⟨⟨t, hexec⟩⟩ := ih (n - 1) (by omega) c'' cF'' hcF'' hcF''sub hcard''
      exact ⟨⟨x :: t, Path.ExecList.cons x henab hexec⟩⟩

/-- Correctness: the original configuration `c` is reachable from `rollback(c,e)`
    when `c.1` admits a `Finset` representation. -/
lemma rollback_correctness_finite [DecidableEventStructure es] {c : Conf es} {e : es.Event}
    (cF : Finset es.Event) (hcF : ∀ x, x ∈ cF ↔ x ∈ c.1) :
    Nonempty (Path es (@rollbackFuture es c e) c) := by
  obtain ⟨⟨t, hExec⟩⟩ := execList_exists_finite (es := es) cF hcF
  exact ⟨Path.execListToPath (es := es) hExec⟩

/-- Minimality of Rollback - Any path from a redo-candidate configuration `c'` to `c` is at
    least as long as the number of events in `c` causally after `e`. -/
lemma rollback_minimality {c : Conf es} {e : es.Event}
    {c' : Conf es} (_hredo : c'.1 ⊢ e) (hsafe : ∀ x ∈ c'.1, x ∉ es.future e)
    (p' : Path es c' c) :
    (c.1 ∩ es.future e).ncard ≤ Path.length es p' := by
  classical
  have hexec : Path.ExecList es c' (Path.trace es p') c :=
    Path.execListOfPath es p'
  have htgt : c.1 = c'.1 ∪ {x | x ∈ Path.trace es p'} :=
    Path.execList_target_eq_union es hexec
  have hsub_set : c.1 ∩ es.future e ⊆ ↑(Path.trace es p').toFinset := by
    intro x ⟨hxc, hxfut⟩
    have hx_target : x ∈ c'.1 ∪ {y | y ∈ Path.trace es p'} := htgt ▸ hxc
    rcases hx_target with hxc' | hxt
    · exact absurd hxfut (hsafe x hxc')
    · exact List.mem_toFinset.mpr hxt
  have hFsetFin : ((Path.trace es p').toFinset : Set es.Event).Finite :=
    (Path.trace es p').toFinset.finite_toSet
  calc (c.1 ∩ es.future e).ncard
      ≤ (↑(Path.trace es p').toFinset : Set es.Event).ncard :=
        Set.ncard_le_ncard hsub_set hFsetFin
    _ = (Path.trace es p').toFinset.card := Set.ncard_coe_finset _
    _ ≤ (Path.trace es p').length := List.toFinset_card_le _
    _ = Path.length es p' := rfl

end Rollback

end EventStructures
