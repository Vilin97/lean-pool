/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
import LeanPool.EventStructures.Basic
import LeanPool.EventStructures.Configuration
import LeanPool.EventStructures.Trace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Nat.Find

/-!
# Paths in the configuration graph

This module defines edges and paths in the configuration graph of an event
structure, their composition, traces and lengths, the minimal path length, the
quotient of paths by trace equivalence (asynchronous paths), and the resulting
(synchronous and asynchronous) path categories.
-/

namespace EventStructures

variable (es : EventStructure)
open EventStructure
open Configuration

/-- Notation for the enabling relation. -/
local infix:50 " ⊢ " => enables es

/-- An edge in the configuration graph of an event structure:
    from configuration c₁ to configuration c₂ by adding event e. -/
structure Edge (c₁ c₂ : Conf es) where
  /-- The event added along this edge. -/
  event : es.Event
  /-- The source configuration enables the added event. -/
  conf₁_enables : (c₁.val) ⊢ event
  /-- The target configuration is the source configuration extended by the event. -/
  conf₂_equals : c₂.val = (c₁.val ∪ {event})

/-- A path in the configuration graph of an event structure. -/
inductive Path : Conf es → Conf es → Type _
  | refl {c : Conf es} : Path c c
  | step {c₁ c₂ c₃ : Conf es} (hEdge : Edge es c₁ c₂) (hPath : Path c₂ c₃) : Path c₁ c₃

namespace Path

/-- Identity path. -/
def pathId (c : Conf es) : Path es c c :=
  Path.refl

/-- Composition of paths. -/
def pathComp {c₁ c₂ c₃ : Conf es} (h₁₂ : Path es c₁ c₂) (h₂₃ : Path es c₂ c₃) :
    Path es c₁ c₃ :=
  match h₁₂ with
  | refl => h₂₃
  | step hEdge hPath => Path.step hEdge (pathComp hPath h₂₃)

/-- Next configuration after executing an enabled event. -/
def nextConf (c : Conf es) (e : es.Event) (h : c.val ⊢ e) : Conf es :=
  ⟨c.val ∪ {e}, enables_extension (es:=es) h⟩

/-- Execute a list of events from a configuration. -/
inductive ExecList : Conf es → List es.Event → Conf es → Type _
  | nil (c : Conf es) : ExecList c [] c
  | cons {c c' : Conf es} {t : List es.Event} (e : es.Event)
      (h : c.val ⊢ e)
      (hnext : ExecList (nextConf es c e h) t c') :
      ExecList c (e :: t) c'

/-- Left identity law: composing with the identity path on the right. -/
lemma path_comp_id {c₁ c₂ : Conf es} (h : Path es c₁ c₂) :
    pathComp es h (pathId es c₂) = h := by
  induction h with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [pathComp, pathId] at ih ⊢
    rw [ih]

/-- Right identity law: composing with the identity path on the left. -/
lemma path_id_comp {c₁ c₂ : Conf es} (h : Path es c₁ c₂) :
    pathComp es (pathId es c₁) h = h := rfl

/-- Associativity law: composition of paths is associative. -/
lemma path_comp_assoc {c₁ c₂ c₃ c₄ : Conf es}
    (h₁₂ : Path es c₁ c₂) (h₂₃ : Path es c₂ c₃) (h₃₄ : Path es c₃ c₄) :
    pathComp es (pathComp es h₁₂ h₂₃) h₃₄ = pathComp es h₁₂ (pathComp es h₂₃ h₃₄) := by
  induction h₁₂ with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [pathComp]
    rw [ih]

/-- Trace of the path -/
def trace {c₁ c₂ : Conf es} (hPath : Path es c₁ c₂) : List es.Event :=
  match hPath with
  | refl => []
  | step hEdge hPath' => hEdge.event :: trace hPath'

/-- Length of a path, defined as the length of its trace. -/
def length {c₁ c₂ : Conf es} (hPath : Path es c₁ c₂) : Nat :=
  (trace es hPath).length

@[simp] lemma length_refl {c : Conf es} : length es (Path.refl (c:=c)) = 0 :=
  rfl

@[simp] lemma length_step {c₁ c₂ c₃ : Conf es} (hEdge : Edge es c₁ c₂)
    (hPath : Path es c₂ c₃) :
    length es (Path.step hEdge hPath) = Nat.succ (length es hPath) := by
  simp [length, trace]

/-- Build a path from an executable list. -/
def execListToPath {c₁ c₂ : Conf es} {t : List es.Event} (h : ExecList es c₁ t c₂) :
    Path es c₁ c₂ :=
  match h with
  | ExecList.nil c => Path.refl
  | ExecList.cons e h hnext =>
      Path.step
        { event := e
          conf₁_enables := h
          conf₂_equals := rfl }
        (execListToPath hnext)

@[simp] lemma execList_trace {c₁ c₂ : Conf es} {t : List es.Event}
    (h : ExecList es c₁ t c₂) : trace es (execListToPath (es:=es) h) = t := by
  induction h with
  | nil c => rfl
  | cons e h hnext ih =>
      simp [execListToPath, trace, ih]

@[simp] lemma execList_length {c₁ c₂ : Conf es} {t : List es.Event}
    (h : ExecList es c₁ t c₂) : length es (execListToPath (es:=es) h) = t.length := by
  simp [length, execList_trace (es:=es) h]

/-- Target configuration from an exec list is the source plus the list's events. -/
lemma execList_target_eq_union {c₁ c₂ : Conf es} {t : List es.Event}
    (h : ExecList es c₁ t c₂) :
    c₂.1 = c₁.1 ∪ {e | e ∈ t} := by
  induction h with
  | nil c =>
    ext x
    simp
  | cons e h hnext ih =>
    ext x
    simp [nextConf, ih, List.mem_cons, Set.mem_union, Set.mem_setOf_eq]
    tauto

/-- Lift an exec list from a smaller configuration to a larger one,
    assuming monotone enabling under subset. -/
noncomputable def execListLift {c_small c_large c_target : Conf es} {t : List es.Event}
    (hsub : c_small.1 ⊆ c_large.1)
    (hmono : ∀ {c₁ c₂ : Conf es} {e : es.Event}, c₁.1 ⊆ c₂.1 → c₁.1 ⊢ e → c₂.1 ⊢ e)
    (h : ExecList es c_small t c_target) :
    Σ c_target', ExecList es c_large t c_target' := by
  induction h generalizing c_large with
  | nil c =>
    exact ⟨c_large, ExecList.nil _⟩
  | @cons c c' t e h hnext ih =>
    have h' : c_large.1 ⊢ e := hmono hsub h
    let c_large' := nextConf es c_large e h'
    have hsub_next : (nextConf es c e h).1 ⊆ c_large'.1 := by
      intro x hx
      have hx' : x = e ∨ x ∈ c.1 := by
        simpa [nextConf, Set.mem_union, Set.mem_singleton_iff] using hx
      have hx'' : x ∈ c_large.1 ∪ {e} := by
        cases hx' with
        | inl hxe => exact Or.inr hxe
        | inr hxc => exact Or.inl (hsub hxc)
      simpa [c_large', nextConf, Set.mem_union, Set.mem_singleton_iff] using hx''
    obtain ⟨c_target', h_exec'⟩ := ih hsub_next
    exact ⟨c_target', ExecList.cons e h' h_exec'⟩

/-- Existence of a path length. -/
lemma pathLengthExists {c₁ c₂ : Conf es} (h : Nonempty (Path es c₁ c₂)) :
    ∃ n, ∃ p : Path es c₁ c₂, length es p = n := by
  rcases h with ⟨p⟩
  exact ⟨length es p, p, rfl⟩

/-- Minimal path length between two configurations, given existence of a path. -/
noncomputable def minPathLength {c₁ c₂ : Conf es} (h : Nonempty (Path es c₁ c₂)) : Nat := by
  classical
  exact Nat.find (pathLengthExists (es := es) h)

lemma minPathLength_spec {c₁ c₂ : Conf es} (h : Nonempty (Path es c₁ c₂)) :
    ∃ p : Path es c₁ c₂, length es p = minPathLength (es := es) h := by
  classical
  simpa [minPathLength] using (Nat.find_spec (pathLengthExists (es := es) h))

lemma minPathLength_le {c₁ c₂ : Conf es} (h : Nonempty (Path es c₁ c₂)) (p : Path es c₁ c₂) :
    minPathLength (es := es) h ≤ length es p := by
  classical
  simpa [minPathLength] using (Nat.find_min' (H := pathLengthExists (es := es) h) ⟨p, rfl⟩)
/-- The trace of an execListToPath is exactly the original list. -/
lemma execList_to_path_trace {c₁ c₂ : Conf es} {t : List es.Event}
    (h : ExecList es c₁ t c₂) :
    trace es (execListToPath (es := es) h) = t :=
  execList_trace (es := es) h
/-- Extract an executable list from a path. -/
def execListOfPath {c₁ c₂ : Conf es} (p : Path es c₁ c₂) : ExecList es c₁ (trace es p) c₂ :=
  match p with
  | Path.refl => ExecList.nil _
  | Path.step (c₁:=c₁) (c₂:=c₂) (c₃:=c₃) hEdge hPath =>
      have hconf : nextConf es c₁ hEdge.event hEdge.conf₁_enables = c₂ := by
        apply Subtype.ext
        simpa [nextConf] using hEdge.conf₂_equals.symm
      have hnext : ExecList es (nextConf es c₁ hEdge.event hEdge.conf₁_enables)
          (trace es hPath) c₃ := by
        simpa [hconf] using execListOfPath hPath
      ExecList.cons hEdge.event hEdge.conf₁_enables hnext

/-- Notation for trace equivalence. -/
local infixr:60 " ≈ₜ " => TraceEquiv es

/-- Path equivalence is the kernel of the trace function. -/
instance pathSetoid (c₁ c₂ : Conf es) : Setoid (Path es c₁ c₂) :=
  Setoid.ker (trace es)

/-- Two paths are equivalent if their traces are trace equivalent -/
def PathEquiv {c₁ c₂ : Conf es} (p₁ p₂ : Path es c₁ c₂) : Prop :=
  (pathSetoid es c₁ c₂).r p₁ p₂

/-- Notation for path equivalence. -/
local infixr:60 " ≈ₚ " => PathEquiv es

/-- Path equivalence is reflexive. -/
lemma pathEquiv_refl {c₁ c₂ : Conf es} : ∀ p, @PathEquiv es c₁ c₂ p p :=
  (pathSetoid es c₁ c₂).iseqv.refl

/-- Path equivalence is symmetric. -/
lemma pathEquiv_symm {c₁ c₂ : Conf es} : Symmetric (@PathEquiv es c₁ c₂) :=
  fun _ _ => (pathSetoid es c₁ c₂).iseqv.symm

/-- Path equivalence is transitive. -/
lemma pathEquiv_trans {c₁ c₂ : Conf es} : ∀ ⦃p₁ p₂ p₃⦄,
    @PathEquiv es c₁ c₂ p₁ p₂ → @PathEquiv es c₁ c₂ p₂ p₃ → @PathEquiv es c₁ c₂ p₁ p₃ :=
  fun _ _ _ => (pathSetoid es c₁ c₂).iseqv.trans

/-- Path equivalence is an equivalence relation. -/
lemma pathEquivEquivalence (c₁ c₂ : Conf es) : Equivalence (@PathEquiv es c₁ c₂) where
  refl := pathEquiv_refl es
  symm := @pathEquiv_symm es c₁ c₂
  trans := @pathEquiv_trans es c₁ c₂

/-- Trace of path composition is concatenation of traces. -/
lemma trace_comp {c₁ c₂ c₃ : Conf es} (p₁₂ : Path es c₁ c₂) (p₂₃ : Path es c₂ c₃) :
    trace es (pathComp es p₁₂ p₂₃) = trace es p₁₂ ++ trace es p₂₃ := by
  induction p₁₂ with
  | refl => rfl
  | step hEdge hPath ih =>
    simp only [pathComp, trace, ih]
    rw [List.cons_append]

/-- Asynchronous path: paths quotiented by path equivalence. -/
def Async (c₁ c₂ : Conf es) : Type _ :=
  Quotient (pathSetoid es c₁ c₂)

namespace Async

/-- Lift a path to an asynchronous path. -/
def mk {c₁ c₂ : Conf es} (p : Path es c₁ c₂) : Async es c₁ c₂ :=
  Quotient.mk (pathSetoid es c₁ c₂) p

/-- Identity asynchronous path. -/
def asyncPathId (c : Conf es) : Async es c c :=
  mk es (Path.pathId es c)

/-- Composition of asynchronous paths. -/
def asyncPathComp {c₁ c₂ c₃ : Conf es}
    (p₁₂ : Async es c₁ c₂) (p₂₃ : Async es c₂ c₃) : Async es c₁ c₃ :=
  Quotient.lift₂
    (fun p₁₂ p₂₃ => mk es (Path.pathComp es p₁₂ p₂₃))
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound <| by
      calc Path.trace es (Path.pathComp es a₁ b₁)
          = Path.trace es a₁ ++ Path.trace es b₁ := Path.trace_comp es a₁ b₁
        _ = Path.trace es a₂ ++ Path.trace es b₂ := by rw [ha, hb]
        _ = Path.trace es (Path.pathComp es a₂ b₂) := (Path.trace_comp es a₂ b₂).symm)
    p₁₂ p₂₃

/-- Left identity law for asynchronous path composition. -/
lemma async_path_id_comp {c₁ c₂ : Conf es} (p : Async es c₁ c₂) :
    asyncPathComp es (asyncPathId es c₁) p = p := by
  induction p using Quotient.ind
  rfl

/-- Right identity law for asynchronous path composition. -/
lemma async_path_comp_id {c₁ c₂ : Conf es} (p : Async es c₁ c₂) :
    asyncPathComp es p (asyncPathId es c₂) = p := by
  induction p using Quotient.ind
  unfold asyncPathComp asyncPathId mk Path.pathId
  simp only [Quotient.lift₂_mk]
  congr 1
  exact Path.path_comp_id es _

/-- Associativity law for asynchronous path composition. -/
lemma assoc {c₁ c₂ c₃ c₄ : Conf es}
    (p₁₂ : Async es c₁ c₂) (p₂₃ : Async es c₂ c₃) (p₃₄ : Async es c₃ c₄) :
    asyncPathComp es (asyncPathComp es p₁₂ p₂₃) p₃₄ =
    asyncPathComp es p₁₂ (asyncPathComp es p₂₃ p₃₄) := by
  induction p₁₂ using Quotient.ind
  induction p₂₃ using Quotient.ind
  induction p₃₄ using Quotient.ind
  simp only [asyncPathComp, Quotient.lift₂_mk]
  apply Quotient.sound
  rw [Path.path_comp_assoc]

end Async

/-- For a path from c₁ to c₂, every event in the trace appears exactly once. -/
lemma trace_length_eq_length {c₁ c₂ : Conf es} (p : Path es c₁ c₂) :
    (trace es p).length = length es p :=
  rfl

/-- Paths are monotone: the source configuration is a subset of the target. -/
lemma path_subset {c₁ c₂ : Conf es} (p : Path es c₁ c₂) : c₁.1 ⊆ c₂.1 := by
  induction p with
  | refl => exact Set.Subset.rfl
  | @step c₁ c₂ c₃ hEdge hPath ih =>
    have h₁₂ : c₁.1 ⊆ c₂.1 := by
      intro x hx
      have hx' : x ∈ c₁.1 ∪ {hEdge.event} := Or.inl hx
      simpa [hEdge.conf₂_equals] using hx'
    exact Set.Subset.trans h₁₂ ih

/-- Events executed in a path must be added to reach the target configuration. -/
lemma trace_of_path {c₁ c₂ : Conf es} (p : Path es c₁ c₂) :
    ∀ e ∈ trace es p, e ∈ c₂.1 := by
  induction p with
  | refl => simp [trace]
  | @step c₁ c₂ c₃ hEdge hPath ih =>
    intro e he
    simp only [trace, List.mem_cons] at he
    rcases he with rfl | h_in_rest
    · -- Head event is in c₂, and c₂ ⊆ c₃ by path_subset
      have h_in_c₂ : hEdge.event ∈ c₂.1 := by
        rw [hEdge.conf₂_equals]
        simp
      exact (path_subset (es := es) hPath) h_in_c₂
    · -- Tail event is in c₃ by IH
      exact ih e h_in_rest

/-- A path requires executing at least the events in its trace. -/
lemma path_length_ge_trace_length {c₁ c₂ : Conf es} (p : Path es c₁ c₂) :
    length es p = (trace es p).length :=
  rfl

end Path

/-- The path category of an event structure. -/
instance pathCategory : CategoryTheory.Category (Conf es) where
  Hom := Path es
  id := Path.pathId es
  comp := Path.pathComp es
  id_comp := Path.path_id_comp es
  comp_id := Path.path_comp_id es
  assoc := Path.path_comp_assoc es

/-- The asynchronous path category of an event structure. -/
instance asyncPathCategory : CategoryTheory.Category (Conf es) where
  Hom := Path.Async es
  id := Path.Async.asyncPathId es
  comp := Path.Async.asyncPathComp es
  id_comp := Path.Async.async_path_id_comp es
  comp_id := Path.Async.async_path_comp_id es
  assoc := Path.Async.assoc es

end EventStructures
