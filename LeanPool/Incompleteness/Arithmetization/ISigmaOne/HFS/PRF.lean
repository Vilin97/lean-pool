/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.HFS.Seq

/-!

# Primitive Recursive Functions in $\mathsf{I} \Sigma_1$

-/

noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

namespace PR

/-- Imported declaration from the Incompleteness formalization. -/
structure Blueprint (k : ℕ) where
  /-- Imported declaration from the Incompleteness formalization. -/
  zero : Sg1.Semisentence (k + 1)
  /-- Imported declaration from the Incompleteness formalization. -/
  succ : Sg1.Semisentence (k + 3)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.PR.Blueprint.cseqDef (p : Blueprint k) : Sg1.Semisentence (k + 1) := .mkSigma
  “s.
    :Seq s
    ∧ (∃ z < s, !p.zero z ⋯ ∧ 0 ∼[s] z)
    ∧ (∀ i < 2 * s,
        (∃ l <⁺ 2 * s, !lhDef l s ∧ i + 1 < l) →
        ∀ z < s, i ∼[s] z → ∃ u < s, !p.succ u z i ⋯ ∧ i + 1 ∼[s] u)” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.PR.Blueprint.resultDef (p : Blueprint k) : Sg1.Semisentence (k + 2) := .mkSigma
  “z u. ∃ s, !p.cseqDef s ⋯ ∧ u ∼[s] z” (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.PR.Blueprint.resultDeltaDef (p : Blueprint k) :
    Dlt1.Semisentence (k + 2) :=
  p.resultDef.graphDelta

variable (V)

/-- Imported declaration from the Incompleteness formalization. -/
structure Construction {k : ℕ} (p : Blueprint k) where
  /-- Imported declaration from the Incompleteness formalization. -/
  zero : (Fin k → V) → V
  /-- Imported declaration from the Incompleteness formalization. -/
  succ : (Fin k → V) → V → V → V
  zero_defined : Sg1.DefinedFunction zero p.zero
  succ_defined : Sg1.DefinedFunction (fun v ↦ succ (v ·.succ.succ) (v 1) (v 0)) p.succ

variable {V}

namespace Construction

variable {k : ℕ} {p : Blueprint k} (c : Construction V p) (v : Fin k → V)

/-- Imported declaration from the Incompleteness formalization. -/
def CSeq (s : V) :
    Prop :=
  Seq s ∧ ⟪0, c.zero v⟫ ∈ s ∧ ∀ i < lh s - 1, ∀ z, ⟪i, z⟫ ∈ s → ⟪i + 1, c.succ v i z⟫ ∈ s

private lemma cseq_iff (s : V) : c.CSeq v s ↔
    Seq s
    ∧ (∃ z < s, z = c.zero v ∧ ⟪0, z⟫ ∈ s)
    ∧ (∀ i < 2 * s,
      (∃ l ≤ 2 * s, l = lh s ∧ i + 1 < l) → ∀ z < s, ⟪i, z⟫ ∈ s → ∃ u < s, u =
        c.succ v i z ∧ ⟪i + 1, u⟫ ∈ s) :=
  ⟨by rintro ⟨Hs, hz, hs⟩
      exact ⟨Hs, ⟨c.zero v, lt_of_mem_rng hz, rfl, hz⟩, fun i _ hi z _ hiz ↦
      ⟨c.succ v i z, by
        have := hs i (by rcases hi with ⟨l, _, rfl, hl⟩; simp [lt_tsub_iff_right, hl]) z hiz
        exact ⟨lt_of_mem_rng this, rfl, this⟩⟩⟩,
   by rintro ⟨Hs, ⟨z, _, rfl, hz⟩, h⟩
      exact ⟨Hs, hz, fun i hi z hiz ↦ by
        rcases h i
          (lt_of_lt_of_le hi (by exact le_trans tsub_le_self (lh_bound _)))
          ⟨lh s, by simp , rfl,
            by simpa [lt_tsub_iff_right] using hi⟩ z (lt_of_mem_rng hiz) hiz with ⟨_, _, rfl, h⟩
        exact h⟩⟩

lemma cseq_defined : Sg1.Defined (fun v ↦ c.CSeq (v ·.succ) (v 0) :
    (Fin (k + 1) → V) → Prop) p.cseqDef := by
  intro v; simp [Blueprint.cseqDef, cseq_iff, c.zero_defined.df.iff, c.succ_defined.df.iff]

lemma cseq_defined_iff (v) :
    Semiformula.Evalbm V v p.cseqDef.val ↔ c.CSeq (v ·.succ) (v 0) := c.cseq_defined.df.iff v

variable {c v}

namespace CSeq

variable {s : V}

lemma seq (h : c.CSeq v s) : Seq s := h.1

lemma zero (h : c.CSeq v s) : ⟪0, c.zero v⟫ ∈ s := h.2.1

lemma succ (h : c.CSeq v s) : ∀ i < lh s - 1, ∀ z, ⟪i, z⟫ ∈ s → ⟪i + 1, c.succ v i z⟫ ∈ s := h.2.2

lemma unique {s₁ s₂ : V} (H₁ : c.CSeq v s₁) (H₂ : c.CSeq v s₂) (h₁₂ : lh s₁ ≤ lh s₂) {i} (hi :
    i < lh s₁) {z₁ z₂} :
    ⟪i, z₁⟫ ∈ s₁ → ⟪i, z₂⟫ ∈ s₂ → z₁ = z₂ := by
  revert z₁ z₂
  suffices ∀ z₁ < s₁, ∀ z₂ < s₂, ⟪i, z₁⟫ ∈ s₁ → ⟪i, z₂⟫ ∈ s₂ → z₁ = z₂
  by intro z₁ z₂ hz₁ hz₂; exact this z₁ (lt_of_mem_rng hz₁) z₂ (lt_of_mem_rng hz₂) hz₁ hz₂
  intro z₁ hz₁ z₂ hz₂ h₁ h₂
  induction i using induction_sigma1 generalizing z₁ z₂
  · definability
  case zero =>
    have : z₁ = c.zero v := H₁.seq.isMapping.uniq h₁ H₁.zero
    have : z₂ = c.zero v := H₂.seq.isMapping.uniq h₂ H₂.zero
    simp_all
  case succ i ih =>
    have hi' : i < lh s₁ := lt_of_le_of_lt (by simp) hi
    let z' := H₁.seq.nth hi'
    have ih₁ : ⟪i, z'⟫ ∈ s₁ := H₁.seq.nth_mem hi'
    have ih₂ : ⟪i, z'⟫ ∈ s₂ := by
      have : z' = H₂.seq.nth (lt_of_lt_of_le hi' h₁₂) :=
        ih hi' z' (by simp [z']) (H₂.seq.nth (lt_of_lt_of_le hi' h₁₂)) (by simp ) (by simp [z'])
          (by simp)
      simp [this]
    have h₁' : ⟪i + 1, c.succ v i z'⟫ ∈ s₁ := H₁.succ i (by simp [lt_tsub_iff_right, hi]) z' ih₁
    have h₂' : ⟪i + 1, c.succ v i z'⟫ ∈ s₂ :=
      H₂.succ i (by exact lt_tsub_iff_right.mpr (lt_of_lt_of_le hi h₁₂)) z' ih₂
    have e₁ : z₁ = c.succ v i z' := H₁.seq.isMapping.uniq h₁ h₁'
    have e₂ : z₂ = c.succ v i z' := H₂.seq.isMapping.uniq h₂ h₂'
    simp [e₁, e₂]

end CSeq

lemma _root_.LO.Arith.PR.Construction.CSeq.initial : c.CSeq v !⟦c.zero v⟧ :=
  ⟨by simp, by simp [seqCons], by simp⟩

lemma _root_.LO.Arith.PR.Construction.CSeq.successor {s l z : V} (Hs : c.CSeq v s) (hl :
    l + 1 = lh s) (hz :
    ⟪l, z⟫ ∈ s) :
    c.CSeq v (s ⁀' c.succ v l z) :=
  ⟨ Hs.seq.seqCons _, by simp [seqCons, Hs.zero], by
    simp only [Hs.seq.lh_seqCons, add_tsub_cancel_right]
    intro i hi w hiw
    have hiws : ⟪i, w⟫ ∈ s := by
      simp only [mem_seqCons_iff] at hiw; rcases hiw with (⟨rfl, rfl⟩ | h)
      · simp at hi
      · assumption
    have : i ≤ l := by simpa [←hl, lt_succ_iff_le] using hi
    rcases this with (rfl | hil)
    · have : w = z := Hs.seq.isMapping.uniq hiws hz
      simp [this, hl]
    · simp only [mem_seqCons_iff]
      right
      exact Hs.succ i (by simp [←hl, hil]) w hiws ⟩

variable (c v)

lemma _root_.LO.Arith.PR.Construction.CSeq.exists (l : V) : ∃ s, c.CSeq v s ∧ l + 1 = lh s := by
  induction l using induction_sigma1
  · apply HierarchySymbol.Boldface.ex
    apply HierarchySymbol.Boldface.and
    · exact ⟨p.cseqDef.rew (Rew.embSubsts <| #0 :> fun i ↦ &(v i)), by
        intro w
        simpa [Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
          c.cseq_defined_iff (w 0 :> v) |>.symm⟩
    · definability
  case zero =>
    exact ⟨!⟦c.zero v⟧, CSeq.initial, by simp⟩
  case succ l ih =>
    rcases ih with ⟨s, Hs, hls⟩
    have hl : l < lh s := by simp [←hls]
    have : ∃ z, ⟪l, z⟫ ∈ s := Hs.seq.exists hl
    rcases this with ⟨z, hz⟩
    exact ⟨s ⁀' c.succ v l z, Hs.successor hls hz, by simp [Hs.seq, hls]⟩

lemma cSeq_result_existsUnique (l : V) : ∃! z, ∃ s, c.CSeq v s ∧ l + 1 = lh s ∧ ⟪l, z⟫ ∈ s := by
  rcases CSeq.exists c v l with ⟨s, Hs, h⟩
  have : ∃ z, ⟪l, z⟫ ∈ s := Hs.seq.exists (show l < lh s from by simp [←h])
  rcases this with ⟨z, hz⟩
  exact ExistsUnique.intro z ⟨s, Hs, h, hz⟩ (by
    rintro z' ⟨s', Hs', h', hz'⟩
    exact Eq.symm <| Hs.unique Hs' (by simp [←h, ←h']) (show l < lh s from by simp [←h]) hz hz')

/-- Imported declaration from the Incompleteness formalization. -/
def result (u : V) : V := Classical.choose! (c.cSeq_result_existsUnique v u)

lemma result_spec (u : V) : ∃ s, c.CSeq v s ∧ u + 1 = lh s ∧ ⟪u, c.result v u⟫ ∈ s :=
  Classical.choose!_spec (c.cSeq_result_existsUnique v u)

@[simp] theorem result_zero : c.result v 0 = c.zero v := by
  rcases c.result_spec v 0 with ⟨s, Hs, _, h0⟩
  exact Hs.seq.isMapping.uniq h0 Hs.zero

@[simp] theorem result_succ (u : V) : c.result v (u + 1) = c.succ v u (c.result v u) := by
  rcases c.result_spec v u with ⟨s, Hs, hk, h⟩
  have : CSeq c v (s ⁀' c.succ v u (result c v u) ) := Hs.successor hk h
  exact Eq.symm
    <| Classical.choose_uniq (c.cSeq_result_existsUnique v (u + 1))
    ⟨_, this, by simp [Hs.seq, hk], by simp [hk]⟩

lemma result_graph (z u : V) : z = c.result v u ↔ ∃ s, c.CSeq v s ∧ ⟪u, z⟫ ∈ s :=
  ⟨by rintro rfl
      rcases c.result_spec v u with ⟨s, Hs, _, h⟩
      exact ⟨s, Hs, h⟩,
   by rintro ⟨s, Hs, h⟩
      rcases c.result_spec v u with ⟨s', Hs', hu, h'⟩
      exact Eq.symm <| Hs'.unique Hs
        (by simp only [←hu, succ_le_iff_lt]; exact Hs.seq.lt_lh_iff.mpr (mem_domain_of_pair_mem h))
        (by simp [←hu]) h' h⟩

lemma result_defined : Sg1.DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) :
    (Fin (k + 1) → V) → V) p.resultDef := by
  intro v
  simp only [Fin.succ_zero_eq_one, result_graph, Blueprint.resultDef, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Semiterm.val_bvar, Matrix.vecCons_zero,
    Matrix.vecCons_succ, Semiformula.eval_operator₃, Matrix.cons_app_two, Matrix.cons_val_one,
    eval_memRel, LogicalConnective.Prop.and_eq]
  apply exists_congr; intro x
  simp [c.cseq_defined_iff]

lemma result_defined_delta : Dlt1.DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) :
    (Fin (k + 1) → V) → V) p.resultDeltaDef :=
  c.result_defined.graph_delta

lemma result_defined_iff (v) :
    Semiformula.Evalbm V v p.resultDef.val ↔ v 0 = c.result (v ·.succ.succ) (v 1) :=
      c.result_defined.df.iff v

instance result_definable : Sg1.BoldfaceFunction (fun v ↦ c.result (v ·.succ) (v 0) :
    (Fin (k + 1) → V) → V) :=
  c.result_defined.to_definable

instance result_definable_delta₁ : Dlt1.BoldfaceFunction (fun v ↦ c.result (v ·.succ) (v 0) :
    (Fin (k + 1) → V) → V) :=
  c.result_defined_delta.to_definable

end Construction

end PR

end Arith
end LO

end «lp_nc_section_1»
