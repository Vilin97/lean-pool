/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Representation
import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.PeanoMinus
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.Sub.Basic

/-! # Vorspiel -/


instance [Zero α] : Nonempty α := ⟨0⟩

/-- Imported declaration from the Incompleteness formalization. -/
notation "exp " x:90 => Exp.exp x

namespace Matrix

lemma _root_.Matrix.forall_vecCons_iff {n : ℕ} (φ : (Fin (n + 1) → α) → Prop) :
    (∀ v, φ v) ↔ (∀ a, ∀ v, φ (a :> v)) :=
  ⟨fun h a v ↦ h (a :> v), fun h v ↦ by simpa [←eq_vecCons v] using h (v 0) (v ∘ Fin.succ)⟩

lemma comp_vecCons₂' (g : β → γ) (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ g <| f <| (a :> s) x) = (g (f a) :> fun i ↦ g <| f <| s i) := by
  funext x
  cases x using Fin.cases <;> simp

end Matrix

namespace Set

@[simp 1100] lemma subset_union_three₁ (s t u : Set α) :
    s ⊆ s ∪ t ∪ u :=
  Set.subset_union_of_subset_left (by simp) _

@[simp] lemma subset_union_three₂ (s t u : Set α) :
    t ⊆ s ∪ t ∪ u :=
  Set.subset_union_of_subset_left (by simp) _

@[simp 1100] lemma subset_union_three₃ (s t u : Set α) :
    u ⊆ s ∪ t ∪ u :=
  Set.subset_union_of_subset_right (by rfl) _

end Set

namespace Matrix

lemma fun_eq_vec₃ {v : Fin 3 → α} : v = ![v 0, v 1, v 2] := by
  funext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
    cases x using Fin.cases with
    | zero => rfl
    | succ x =>
      rw [Fin.eq_zero x]
      rfl

lemma fun_eq_vec₄ {v : Fin 4 → α} : v = ![v 0, v 1, v 2, v 3] := by
  funext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
    cases x using Fin.cases with
    | zero => rfl
    | succ x =>
      cases x using Fin.cases with
      | zero => rfl
      | succ x =>
        rw [Fin.eq_zero x]
        rfl

@[simp] lemma cons_app_four {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ → α) :
    (a :> s) 4 = s 3 :=
  rfl

@[simp] lemma cons_app_five {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ → α) :
    (a :> s) 5 = s 4 :=
  rfl

@[simp] lemma cons_app_six {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ → α) :
    (a :> s) 6 = s 5 :=
  rfl

@[simp] lemma cons_app_seven {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ → α) :
    (a :> s) 7 = s 6 :=
  rfl

@[simp] lemma cons_app_eight {n : ℕ} (a : α) (s :
    Fin n.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    (a :> s) 8 = s 7 :=
  rfl

lemma eq_vecCons' (s : Fin (n + 1) → C) : s 0 :> (s ·.succ) = s :=
   funext <| Fin.cases (by simp) (by simp)

end Matrix

lemma forall_fin_iff_zero_and_forall_succ {P : Fin (k + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i :
    Fin k, P i.succ :=
  ⟨fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩, by
    rintro ⟨hz, hs⟩ i
    cases i using Fin.cases with
    | zero => exact hz
    | succ i => exact hs i⟩

lemma exists_fin_iff_zero_or_exists_succ {P : Fin (k + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i :
    Fin k, P i.succ :=
  ⟨by rintro ⟨i, hi⟩
      cases i using Fin.cases
      · left; exact hi
      · right; exact ⟨_, hi⟩,
   by rintro (hz | ⟨i, h⟩)
      · exact ⟨0, hz⟩
      · exact ⟨_, h⟩⟩

lemma forall_vec_iff_forall_forall_vec {P : (Fin (k + 1) → α) → Prop} :
    (∀ v : Fin (k + 1) → α, P v) ↔ ∀ x, ∀ v : Fin k → α, P (x :> v) := by
  constructor
  · intro h x v; exact h _
  · intro h v; simpa using h (v 0) (v ·.succ)

lemma exists_vec_iff_exists_exists_vec {P : (Fin (k + 1) → α) → Prop} :
    (∃ v : Fin (k + 1) → α, P v) ↔ ∃ x, ∃ v : Fin k → α, P (x :> v) := by
  constructor
  · rintro ⟨v, h⟩; exact ⟨v 0, (v ·.succ), by simpa using h⟩
  · rintro ⟨x, v, h⟩; exact ⟨_, h⟩

lemma exists_le_vec_iff_exists_le_exists_vec [LE α] {P : (Fin (k + 1) → α) → Prop} {f :
    Fin (k + 1) → α} :
    (∃ v ≤ f, P v) ↔ ∃ x ≤ f 0, ∃ v ≤ (f ·.succ), P (x :> v) := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w 0, hw 0, (w ·.succ), fun i ↦ hw i.succ, by simpa using h⟩
  · rintro ⟨x, hx, v, hv, h⟩
    refine ⟨x :> v, ?_, h⟩
    intro i
    cases i using Fin.cases with
    | zero => exact hx
    | succ i => exact hv i

lemma forall_le_vec_iff_forall_le_forall_vec [LE α] {P : (Fin (k + 1) → α) → Prop} {f :
    Fin (k + 1) → α} :
    (∀ v ≤ f, P v) ↔ ∀ x ≤ f 0, ∀ v ≤ (f ·.succ), P (x :> v) := by
  constructor
  · intro h x hx v hv
    refine h (x :> v) ?_
    intro i
    cases i using Fin.cases with
    | zero => exact hx
    | succ i => exact hv i
  · intro h v hv
    simpa using h (v 0) (hv 0) (v ·.succ) (hv ·.succ)

instance instToStringEmptyOfVorspiel : ToString Empty := ⟨Empty.elim⟩

/-- Imported declaration from the Incompleteness formalization. -/
class Hash (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  hash : α → α → α

/-- Imported declaration from the Incompleteness formalization. -/
infix:80 " # " => Hash.hash

/-- Imported declaration from the Incompleteness formalization. -/
class Length (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  length : α → α

namespace Length

/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "‖" x "‖" => Length.length x

end Length

namespace LO

namespace Polarity

variable {α : Type*} [SigmaSymbol α] [PiSymbol α]

/-- Imported declaration from the Incompleteness formalization. -/
protected def coe : Polarity → α
 | Sg => Sg
 | Pg => Pg

instance : Coe Polarity α := ⟨Polarity.coe⟩

@[simp] lemma coe_sigma : ((Sg : Polarity) : α) = Sg := rfl

@[simp] lemma coe_pi : ((Pg : Polarity) : α) = Pg := rfl

end Polarity

namespace SigmaPiDelta

@[simp] lemma alt_coe (Γ : Polarity) : SigmaPiDelta.alt Γ = (Γ.alt : SigmaPiDelta) := by
  rcases Γ <;> rfl

end SigmaPiDelta

namespace FirstOrder

namespace Semiterm

/-- Imported declaration from the Incompleteness formalization. -/
def fvarList : Semiterm L ξ n → List ξ
  | #_       => []
  | &x       => [x]
  | func _ v => List.flatten <| Matrix.toList fun i ↦ fvarList (v i)

/-- Imported declaration from the Incompleteness formalization. -/
def fvarEnum [DecidableEq ξ] (t : Semiterm L ξ n) : ξ → ℕ := t.fvarList.idxOf

/-- Imported declaration from the Incompleteness formalization. -/
def fvarEnumInv [Inhabited ξ] (t : Semiterm L ξ n) : ℕ → ξ :=
  fun i ↦ if hi : i < t.fvarList.length then t.fvarList.get ⟨i, hi⟩ else default

lemma fvarEnumInv_fvarEnum [DecidableEq ξ] [Inhabited ξ] {t : Semiterm L ξ n} {x : ξ} (hx :
    x ∈ t.fvarList) :
    fvarEnumInv t (fvarEnum t x) = x := by
  simp [fvarEnumInv, fvarEnum, List.idxOf_lt_length_of_mem hx, List.getElem_idxOf]

lemma «mem_fvarList_iff_fvar?» [DecidableEq ξ] {t : Semiterm L ξ n} :
    x ∈ t.fvarList ↔ t.FVar? x:= by
  induction t with
  | bvar _ =>
    simp only [fvarList, List.not_mem_nil, fvar?_bvar]
  | fvar y =>
    simp only [fvarList, List.mem_singleton, fvar?_fvar, eq_comm]
  | func _ v ih =>
    simp only [fvarList, List.mem_flatten, Matrix.mem_toList_iff, fvar?_func]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hx⟩
      exact ⟨i, (ih i).mp hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨(v i).fvarList, ⟨i, rfl⟩, (ih i).mpr hx⟩

end Semiterm

namespace Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
def fvarList {n : ℕ} : Semiformula L ξ n → List ξ
  | ⊤        => []
  | ⊥        => []
  | rel _ v  => List.flatten <| Matrix.toList fun i ↦ (v i).fvarList
  | nrel _ v => List.flatten <| Matrix.toList fun i ↦ (v i).fvarList
  | p ⋏ q    => p.fvarList ++ q.fvarList
  | p ⋎ q    => p.fvarList ++ q.fvarList
  | ∀' p     => p.fvarList
  | ∃' p     => p.fvarList

/-- Imported declaration from the Incompleteness formalization. -/
def fvarEnum [DecidableEq ξ] (φ : Semiformula L ξ n) : ξ → ℕ := φ.fvarList.idxOf

/-- Imported declaration from the Incompleteness formalization. -/
def fvarEnumInv [Inhabited ξ] (φ : Semiformula L ξ n) : ℕ → ξ :=
  fun i ↦ if hi : i < φ.fvarList.length then φ.fvarList.get ⟨i, hi⟩ else default

lemma fvarEnumInv_fvarEnum [DecidableEq ξ] [Inhabited ξ] {φ : Semiformula L ξ n} {x : ξ} (hx :
    x ∈ φ.fvarList) :
    fvarEnumInv φ (fvarEnum φ x) = x := by
  simp [fvarEnumInv, fvarEnum, List.idxOf_lt_length_of_mem hx, List.getElem_idxOf]

lemma «mem_fvarList_iff_fvar?» [DecidableEq ξ] {φ : Semiformula L ξ n} :
    x ∈ φ.fvarList ↔ φ.FVar? x := by
  induction φ using rec' <;> simp [fvarList, Semiterm.mem_fvarList_iff_fvar?, *]

end Semiformula

namespace Arith

attribute [simp] Semiformula.eval_substs Semiformula.eval_embSubsts
  Matrix.vecHead Matrix.vecTail

section «lp_section_1»

variable [ToString μ]

open Semiterm Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
def termToStr : Semiterm ℒₒᵣ μ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  | func Language.One.one _   => "1"
  | func Language.Add.add v   => "(" ++ termToStr (v 0) ++ " + " ++ termToStr (v 1) ++ ")"
  | func Language.Mul.mul v   => "(" ++ termToStr (v 0) ++ " \\cdot " ++ termToStr (v 1) ++ ")"

instance : Repr (Semiterm ℒₒᵣ μ n) := ⟨fun t _ => termToStr t⟩

instance : ToString (Semiterm ℒₒᵣ μ n) := ⟨termToStr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def formulaToStr : ∀ {n}, Semiformula ℒₒᵣ μ n → String
  | _, ⊤                             => "\\top"
  | _, ⊥                             => "\\bot"
  | _, rel Language.Eq.eq v          => termToStr (v 0) ++ " = " ++ termToStr (v 1)
  | _, rel Language.LT.lt v          => termToStr (v 0) ++ " < " ++ termToStr (v 1)
  | _, nrel Language.Eq.eq v         => termToStr (v 0) ++ " \\not = " ++ termToStr (v 1)
  | _, nrel Language.LT.lt v         => termToStr (v 0) ++ " \\not < " ++ termToStr (v 1)
  | _, φ ⋏ ψ                         =>
    "[" ++ formulaToStr φ ++ "]" ++ " \\land " ++ "[" ++ formulaToStr ψ ++ "]"
  | _, φ ⋎ ψ                         =>
    "[" ++ formulaToStr φ ++ "]" ++ " \\lor "  ++ "[" ++ formulaToStr ψ ++ "]"
  | n, ∀' (rel Language.LT.lt v ==> φ) =>
    "(\\forall x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++
      "[" ++ formulaToStr φ ++ "]"
  | n, ∃' (rel Language.LT.lt v ⋏ φ) =>
    "(\\exists x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++
      "[" ++ formulaToStr φ  ++ "]"
  | n, ∀' φ                          =>
    "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr φ ++ "]"
  | n, ∃' φ                          =>
    "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr φ ++ "]"

instance : Repr (Semiformula ℒₒᵣ μ n) := ⟨fun t _ => formulaToStr t⟩

instance : ToString (Semiformula ℒₒᵣ μ n) := ⟨formulaToStr⟩

end «lp_section_1»

section «lp_section_2»

variable {T : Theory ℒₒᵣ} [𝐄𝐐 wkn T]

variable (M : Type*) [ORingStruc M] [M ⊧ₘ* T]

instance indScheme_of_indH (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃Γ n] :
    M ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ n) := models_indScheme_of_models_indH Γ n

end «lp_section_2»

end Arith

section «lp_section_3»

variable {L : Language}

namespace Semiformula

variable {M : Type*} {s : Structure L M}

variable {n : ℕ} {ε : ξ → M}

@[simp] lemma eval_operator₃ {o : Operator L 3} {t₁ t₂ t₃ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂, t₃]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε, t₃.val s e ε] := by
  simp [eval_operator, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

@[simp] lemma eval_operator₄ {o : Operator L 4} {t₁ t₂ t₃ t₄ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂, t₃, t₄]) ↔
        o.val ![t₁.val s e ε, t₂.val s e ε, t₃.val s e ε, t₄.val s e ε] := by
  simp [eval_operator, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

end Semiformula

end «lp_section_3»

section «lp_section_4»

variable {M : Type*} [Nonempty M] [Structure L M]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Semiterm.Rlz (t : Semiterm L M n) (e : Fin n → M) : M := t.valm M e id

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Semiformula.Rlz (φ : Semiformula L M n) (e : Fin n → M) : Prop :=
  Semiformula.Evalm M e id φ

@[simp] lemma models₀_not_iff (σ : Sentence L) : M ⊧ₘ₀ (∼σ) ↔ ¬M ⊧ₘ₀ σ := by simp [models₀_iff]

@[simp] lemma models₀_or_iff (σ π : Sentence L) :
    M ⊧ₘ₀ (σ ⋎ π) ↔ M ⊧ₘ₀ σ ∨ M ⊧ₘ₀ π := by
  simp [models₀_iff]

@[simp] lemma models₀_imply_iff (σ π : Sentence L) :
    M ⊧ₘ₀ (σ ==> π) ↔ M ⊧ₘ₀ σ → M ⊧ₘ₀ π := by
  simp [models₀_iff]

end «lp_section_4»

namespace Arith

namespace Hierarchy

section «lp_section_5»
variable {L : FirstOrder.Language} [L.LT] {μ : Type v}

@[simp]
lemma exItr {n} : {k : ℕ} → {φ :
    Semiformula L μ (n + k)} → Hierarchy Sg (s + 1) (∃^[k] φ) ↔ Hierarchy Sg (s + 1) φ
  | 0,     φ => by simp
  | k + 1, φ => by simp [LO.exItr_succ, exItr]

@[simp]
lemma univItr {n} : {k : ℕ} → {φ :
    Semiformula L μ (n + k)} → Hierarchy Pg (s + 1) (∀^[k] φ) ↔ Hierarchy Pg (s + 1) φ
  | 0,     φ => by simp
  | k + 1, φ => by simp [LO.univItr_succ, univItr]

end «lp_section_5»

end Hierarchy

variable (M : Type*) [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻]

instance : M ⊧ₘ* 𝐑₀ := by refine models_of_subtheory (T := 𝐏𝐀⁻) inferInstance

lemma nat_extention_sigmaOne {σ : Sentence ℒₒᵣ} (hσ : Hierarchy Sg 1 σ) :
    ℕ ⊧ₘ₀ σ → M ⊧ₘ₀ σ := fun h ↦ by
  simpa [Matrix.empty_eq] using LO.Arith.sigma_one_completeness (M := M) hσ h

lemma nat_extention_piOne {σ : Sentence ℒₒᵣ} (hσ : Hierarchy Pg 1 σ) :
    M ⊧ₘ₀ σ → ℕ ⊧ₘ₀ σ := by
  contrapose
  simpa using nat_extention_sigmaOne M (σ := ∼σ) (by simpa using hσ)

end Arith

end FirstOrder

end LO

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith ORingStruc

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐑₀]

lemma bold_sigma_one_completeness' {n} {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy Sg 1 σ) {e} :
    Semiformula.Evalbm ℕ e σ → Semiformula.Evalbm M (fun x ↦ numeral (e x)) σ := fun h ↦ by
  simpa [Empty.eq_elim] using bold_sigma_one_completeness (M :=
    M) (φ := σ) hσ (f := Empty.elim) (e := e) h

end Arith
end LO

namespace List
namespace Vector

variable {α : Type*}

@[simp] lemma nil_get (v : Vector α 0) : v.get = ![] := by
  ext i; exact i.elim0

end Vector
end List
