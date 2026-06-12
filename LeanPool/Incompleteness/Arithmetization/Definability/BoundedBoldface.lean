/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.Definability.Boldface
import LeanPool.Incompleteness.Arithmetization.Definability.Init

/-! # BoundedBoldface -/


namespace LO
namespace FirstOrder
namespace Arith

open LO.Arith

variable {ξ : Type*} {n : ℕ}

variable {V : Type*} [ORingStruc V]

variable {ℌ : HierarchySymbol} {Γ Γ' : SigmaPiDelta}

variable (ℌ)

/-- Imported declaration from the Incompleteness formalization. -/
class Bounded (f : (Fin k → V) → V) : Prop where
  bounded : ∃ t : Semiterm ℒₒᵣ V k, ∀ v : Fin k → V, f v ≤ t.valm V v id

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Bounded₁ (f : V → V) : Prop := Bounded (k := 1) (fun v ↦ f (v 0))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Bounded₂ (f : V → V → V) : Prop := Bounded (k := 2) (fun v ↦ f (v 0) (v 1))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Bounded₃ (f : V → V → V → V) : Prop := Bounded (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

instance (f : (Fin k → V) → V) [h : Bounded f] : Bounded f := by
  rcases h with ⟨t, ht⟩
  exact ⟨Semiterm.lMap Language.oringEmb t, by simpa⟩

variable {ℌ}

namespace Bounded

@[simp] lemma var [V ⊧ₘ* 𝐏𝐀⁻] {k} (i : Fin k) : Bounded fun v :
    Fin k → V ↦ v i :=
  ⟨#i, by intro _; simp⟩

@[simp] lemma const [V ⊧ₘ* 𝐏𝐀⁻] {k} (c : V) : Bounded (fun _ :
    Fin k → V ↦ c) :=
  ⟨&c, by intro _; simp⟩

@[simp 1100] lemma term_retraction [V ⊧ₘ* 𝐏𝐀⁻] (t : Semiterm ℒₒᵣ V n) (e : Fin n → Fin k) :
    Bounded fun v : Fin k → V ↦ Semiterm.valm V (fun x ↦ v (e x)) id t :=
  ⟨Rew.substs (fun x ↦ #(e x)) t, by intro _; simp [Semiterm.val_substs]⟩

lemma term [V ⊧ₘ* 𝐏𝐀⁻] (t : Semiterm ℒₒᵣ V k) : Bounded fun v :
    Fin k → V => Semiterm.valm V v id t :=
  ⟨t, by intro _; simp⟩

lemma retraction {f : (Fin k → V) → V} (hf : Bounded f) (e : Fin k → Fin n) :
    Bounded fun v ↦ f (fun i ↦ v (e i)) := by
  rcases hf with ⟨t, ht⟩
  exact ⟨Rew.substs (fun x ↦ #(e x)) t, by intro; simp [Semiterm.val_substs, ht]⟩

lemma comp [V ⊧ₘ* 𝐏𝐀⁻] {k} {f : (Fin l → V) → V} {g : Fin l → (Fin k → V) → V} (hf :
    Bounded f) (hg :
    ∀ i, Bounded (g i)) :
    Bounded (fun v ↦ f (g · v)) where
  bounded := by
    rcases hf.bounded with ⟨tf, htf⟩
    choose tg htg using fun i ↦ (hg i).bounded
    exact ⟨Rew.substs tg tf, by
      intro v; simp only [Semiterm.val_substs]
      exact le_trans (htf (g · v)) (Structure.Monotone.term_monotone tf (fun i ↦ htg i v) (by
        simp))⟩

end Bounded

lemma _root_.LO.FirstOrder.Arith.Bounded₁.comp
    [V ⊧ₘ* 𝐏𝐀⁻] {f : V → V} {k} {g : (Fin k → V) → V} (hf :
    Bounded₁ f) (hg :
    Bounded g) :
    Bounded (fun v ↦ f (g v)) := Bounded.comp hf (l := 1) (fun _ ↦ hg)

lemma _root_.LO.FirstOrder.Arith.Bounded₂.comp [V ⊧ₘ* 𝐏𝐀⁻] {f : V → V → V} {k} {g₁ g₂ :
    (Fin k → V) → V}
    (hf : Bounded₂ f) (hg₁ : Bounded g₁) (hg₂ : Bounded g₂) :
    Bounded (fun v ↦ f (g₁ v) (g₂ v)) :=
      Bounded.comp hf (g := ![g₁, g₂]) (fun i ↦ by cases i using Fin.cases <;> simp [*])

lemma _root_.LO.FirstOrder.Arith.Bounded₃.comp [V ⊧ₘ* 𝐏𝐀⁻] {f : V → V → V → V} {k} {g₁ g₂ g₃ :
    (Fin k → V) → V}
    (hf : Bounded₃ f) (hg₁ : Bounded g₁) (hg₂ : Bounded g₂) (hg₃ : Bounded g₃) :
    Bounded (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := Bounded.comp hf (g := ![g₁, g₂, g₃])
      (fun i ↦ by
        cases i using Fin.cases with
        | zero => simp [*]
        | succ i =>
          cases i using Fin.cases with
          | zero => simp [*]
          | succ i => simp [*])

namespace Bounded₂

variable [V ⊧ₘ* 𝐏𝐀⁻]

instance add : Bounded₂ ((· + ·) : V → V → V) where
  bounded := ⟨‘x y. x + y’, by intro _; simp⟩

instance mul : Bounded₂ ((· * ·) : V → V → V) where
  bounded := ⟨‘x y. x * y’, by intro _; simp⟩

instance hAdd : Bounded₂ (HAdd.hAdd : V → V → V) where
  bounded := ⟨‘x y. x + y’, by intro _; simp⟩

instance hMul : Bounded₂ (HMul.hMul : V → V → V) where
  bounded := ⟨‘x y. x * y’, by intro _; simp⟩

end Bounded₂

/-- Imported declaration from the Incompleteness formalization. -/
def BoldfaceBoundedFunction {k} (f : (Fin k → V) → V) := Bounded f ∧ Sg0.BoldfaceFunction f

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceBoundedFunction₁ (f : V → V) :
    Prop :=
  BoldfaceBoundedFunction (k := 1) (fun v => f (v 0))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceBoundedFunction₂ (f : V → V → V) :
    Prop :=
  BoldfaceBoundedFunction (k := 2) (fun v => f (v 0) (v 1))

/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceBoundedFunction₃ (f : V → V → V → V) :
    Prop :=
  BoldfaceBoundedFunction (k := 3) (fun v => f (v 0) (v 1) (v 2))

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.bounded {f : (Fin k → V) → V} (h :
    BoldfaceBoundedFunction f) :
    Bounded f :=
  h.1

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₁.bounded {f : V → V} (h :
    BoldfaceBoundedFunction₁ f) :
    Bounded₁ f :=
  h.1

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₂.bounded {f : V → V → V} (h :
    BoldfaceBoundedFunction₂ f) :
    Bounded₂ f :=
  h.1

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₃.bounded {f : V → V → V → V} (h :
    BoldfaceBoundedFunction₃ f) :
    Bounded₃ f :=
  h.1

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.definable {f : (Fin k → V) → V} (h :
    BoldfaceBoundedFunction f) :
    ℌ.BoldfaceFunction f :=
  .of_zero h.2

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₁.definable {f : V → V} (h :
    BoldfaceBoundedFunction₁ f) :
    ℌ.BoldfaceFunction₁ f :=
  .of_zero h.2

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₂.definable {f : V → V → V} (h :
    BoldfaceBoundedFunction₂ f) :
    ℌ.BoldfaceFunction₂ f :=
  .of_zero h.2

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₃.definable {f : V → V → V → V} (h :
    BoldfaceBoundedFunction₃ f) :
    ℌ.BoldfaceFunction₃ f :=
  .of_zero h.2

namespace BoldfaceBoundedFunction

lemma of_polybounded_of_definable (f : (Fin k → V) → V) [hb : Bounded f] [hf :
    Sg0.BoldfaceFunction f] :
    BoldfaceBoundedFunction f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₁ (f : V → V) [hb : Bounded₁ f] [hf :
    Sg0.BoldfaceFunction₁ f] :
    BoldfaceBoundedFunction₁ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₂ (f : V → V → V) [hb : Bounded₂ f] [hf :
    Sg0.BoldfaceFunction₂ f] :
    BoldfaceBoundedFunction₂ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₃ (f : V → V → V → V) [hb : Bounded₃ f] [hf :
    Sg0.BoldfaceFunction₃ f] :
    BoldfaceBoundedFunction₃ f := ⟨hb, hf⟩

lemma retraction {f : (Fin k → V) → V} (hf : BoldfaceBoundedFunction f) (e : Fin k → Fin n) :
    BoldfaceBoundedFunction fun v ↦ f (fun i ↦ v (e i)) :=
      ⟨hf.bounded.retraction e, hf.definable.retraction e⟩

end BoldfaceBoundedFunction

namespace HierarchySymbol
namespace Boldface

variable [V ⊧ₘ* 𝐏𝐀⁻]

variable {P Q : (Fin k → V) → Prop}

lemma ball_blt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : ℌ.Boldface fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Boldface fun v ↦ ∀ x < f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨φ, hp⟩
  have : ℌ.DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm V v id bf, x = f v ∧ ∀ y < x, P v y)
    (HierarchySymbol.Semiformula.bex ‘!!bf + 1’
      (f_graph ⋏ HierarchySymbol.Semiformula.ball (#0)
        (HierarchySymbol.Semiformula.rew
          (Rew.substs (#0 :> fun i ↦ #i.succ.succ)) φ))) := by
    simpa [←le_iff_lt_succ, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (hf_graph.and ((hp.retraction (0 :> (·.succ.succ))).ball #0)).bex ‘!!bf + 1’
  exact .of_iff ⟨_, this⟩ (fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by
    rintro ⟨y, hy, rfl, h⟩
    exact h⟩)


lemma bex_blt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : ℌ.Boldface fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Boldface fun v ↦ ∃ x < f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨φ, hp⟩
  have : ℌ.DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm V v id bf, x = f v ∧ ∃ y < x, P v y)
    (HierarchySymbol.Semiformula.bex ‘!!bf + 1’
      (f_graph ⋏ HierarchySymbol.Semiformula.bex (#0)
        (HierarchySymbol.Semiformula.rew
          (Rew.substs (#0 :> fun i => #i.succ.succ)) φ))) := by
    simpa [←le_iff_lt_succ, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (hf_graph.and ((hp.retraction (0 :> (·.succ.succ))).bex #0)).bex ‘!!bf + 1’
  exact .of_iff ⟨_, this⟩ (fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by
    rintro ⟨y, hy, rfl, h⟩
    exact h⟩)

lemma ball_ble {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : ℌ.Boldface fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Boldface fun v ↦ ∀ x ≤ f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨φ, hp⟩
  have : ℌ.DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm V v id bf, x = f v ∧ ∀ y ≤ x, P v y)
    (HierarchySymbol.Semiformula.bex ‘!!bf + 1’
      (f_graph ⋏ HierarchySymbol.Semiformula.ball ‘x. x + 1’
        (HierarchySymbol.Semiformula.rew
          (Rew.substs (#0 :> fun i => #i.succ.succ)) φ))) := by
    simpa [←le_iff_lt_succ, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (hf_graph.and ((hp.retraction (0 :> (·.succ.succ))).ball ‘x. x + 1’)).bex ‘!!bf + 1’
  exact .of_iff ⟨_, this⟩ (fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by
    rintro ⟨y, hy, rfl, h⟩
    exact h⟩)

lemma bex_ble {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : ℌ.Boldface fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Boldface fun v ↦ ∃ x ≤ f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨φ, hp⟩
  have : ℌ.DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm V v id bf, x = f v ∧ ∃ y ≤ x, P v y)
    (HierarchySymbol.Semiformula.bex ‘!!bf + 1’
      (f_graph ⋏ HierarchySymbol.Semiformula.bex ‘x. x + 1’
        (HierarchySymbol.Semiformula.rew
          (Rew.substs (#0 :> fun i => #i.succ.succ)) φ))) := by
    simpa [←le_iff_lt_succ, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (hf_graph.and ((hp.retraction (0 :> (·.succ.succ))).bex ‘x. x + 1’)).bex ‘!!bf + 1’
  exact .of_iff ⟨_, this⟩ (fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by
    rintro ⟨y, hy, rfl, h⟩
    exact h⟩)

lemma ball_blt_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : Γ-[0].Boldface fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Boldface fun v ↦ ∀ x < f v, P v x := ball_blt hf h

lemma bex_blt_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : Γ-[0].Boldface fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Boldface fun v ↦ ∃ x < f v, P v x := bex_blt hf h

lemma ball_ble_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : Γ-[0].Boldface fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Boldface fun v ↦ ∀ x ≤ f v, P v x := ball_ble hf h

lemma bex_ble_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : Γ-[0].Boldface fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Boldface fun v ↦ ∃ x ≤ f v, P v x := bex_ble hf h

lemma bex_vec_le_boldfaceBoundedFunction {k} {φ : Fin l → (Fin k → V) → V} {P :
    (Fin k → V) → (Fin l → V) → Prop}
    (pp : ∀ i, BoldfaceBoundedFunction (φ i)) (hP : ℌ.Boldface fun w : Fin (k + l) →
      V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    ℌ.Boldface fun v ↦ ∃ w ≤ (φ · v), P v w := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq (α := V)] using hP
  case succ l ih =>
    simp only [exists_le_vec_iff_exists_le_exists_vec]
    apply bex_ble (pp 0)
    apply ih
    · intro i; apply BoldfaceBoundedFunction.retraction (pp i.succ)
    · let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
      Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
      exact of_iff (retraction hP g) <| by
        intro v; simp only [g]
        apply iff_of_eq; congr
        · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · ext i
          cases i using Fin.cases with
          | zero =>
            simp only [Matrix.vecCons_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          | succ i =>
            simp only [Matrix.vecCons_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]

lemma substitution_boldfaceBoundedFunction {f : Fin k → (Fin l → V) → V}
    (hP : ℌ.Boldface P) (hf : ∀ i, BoldfaceBoundedFunction (f i)) :
    ℌ.Boldface fun z ↦ P (f · z) := by
  have : ℌ.Boldface fun v ↦ ∃ w ≤ (f · v), (∀ i, w i = f i v) ∧ P w := by
    apply bex_vec_le_boldfaceBoundedFunction hf
    apply and
    · apply conj; intro i
      simpa using retraction (.of_zero (hf i).2) (i.natAdd l :> Fin.castAdd k)
    · apply retraction hP
  apply of_iff this <| by
    intro v; constructor
    · intro h; exact ⟨(f · v), by intro i; simp, by simp, h⟩
    · rintro ⟨w, hw, e, h⟩
      rcases funext e
      exact h

end Boldface
end HierarchySymbol

namespace BoldfaceBoundedFunction

lemma of_iff {f g : (Fin k → V) → V} (H : BoldfaceBoundedFunction f) (h : ∀ v, f v = g v) :
    BoldfaceBoundedFunction g := by
  have : f = g := by funext v; simp [h]
  rcases this; exact H

variable [V ⊧ₘ* 𝐏𝐀⁻]

@[simp] lemma var {k} (i : Fin k) : BoldfaceBoundedFunction (fun v :
    Fin k → V ↦ v i) :=
  ⟨by simp, by simp⟩

@[simp] lemma const {k} (c : V) : BoldfaceBoundedFunction (fun _ :
    Fin k → V ↦ c) :=
  ⟨by simp, by simp⟩

@[simp 1100] lemma term_retraction (t : Semiterm ℒₒᵣ V n) (e : Fin n → Fin k) :
    BoldfaceBoundedFunction fun v : Fin k → V ↦ Semiterm.valm V (fun x ↦ v (e x)) id t :=
      ⟨by simp, by simp⟩

lemma term (t : Semiterm ℒₒᵣ V k) :
  BoldfaceBoundedFunction fun v : Fin k → V ↦ Semiterm.valm V v id t := ⟨by simp, by simp⟩

end BoldfaceBoundedFunction

namespace HierarchySymbol
namespace Boldface

open BoldfaceBoundedFunction

variable [V ⊧ₘ* 𝐏𝐀⁻]

lemma bcomp₁ {k} {P : V → Prop} {f : (Fin k → V) → V} [hP : ℌ.BoldfacePred P] (hf :
    BoldfaceBoundedFunction f) :
    ℌ.Boldface fun v ↦ P (f v) :=
  substitution_boldfaceBoundedFunction (f := ![f]) hP (by simp [*])

lemma bcomp₂ {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V} [hR : ℌ.BoldfaceRel R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    ℌ.Boldface fun v ↦ R (f₁ v) (f₂ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₃ {k} {R : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V} [hR : ℌ.BoldfaceRel₃ R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    ℌ.Boldface fun v ↦ R (f₁ v) (f₂ v) (f₃ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂, f₃]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₄ {k} {R : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V} [hR : ℌ.BoldfaceRel₄ R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) (hf₄ : BoldfaceBoundedFunction f₄) :
    ℌ.Boldface fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂, f₃, f₄]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₁_zero {k} {P : V → Prop} {f : (Fin k → V) → V} [hP : Γ-[0].BoldfacePred P] (hf :
    BoldfaceBoundedFunction f) :
    Γ-[0].Boldface fun v ↦ P (f v) :=
  substitution_boldfaceBoundedFunction (f := ![f]) hP (by simp [*])

lemma bcomp₂_zero {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V} [hR : Γ-[0].BoldfaceRel R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    Γ-[0].Boldface fun v ↦ R (f₁ v) (f₂ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₃_zero {k} {R : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V} [hR :
    Γ-[0].BoldfaceRel₃ R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    Γ-[0].Boldface fun v ↦ R (f₁ v) (f₂ v) (f₃ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂, f₃]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₄_zero {k} {R : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V} [hR :
    Γ-[0].BoldfaceRel₄ R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) (hf₄ : BoldfaceBoundedFunction f₄) :
    Γ-[0].Boldface fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂, f₃, f₄]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])

end Boldface
end HierarchySymbol

variable [V ⊧ₘ* 𝐏𝐀⁻]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction.bcomp {k} {F :
    (Fin l → V) → V} {f :
    Fin l → (Fin k → V) → V}
    (hF : ℌ.BoldfaceFunction F) (hf : ∀ i, BoldfaceBoundedFunction (f i)) :
    ℌ.BoldfaceFunction (fun v ↦ F (f · v)) := by
  simpa using HierarchySymbol.Boldface.substitution_boldfaceBoundedFunction
    (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <| by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using BoldfaceBoundedFunction.retraction (hf i) Fin.succ

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₁.bcomp {k} {F : V → V} {f :
    (Fin k → V) → V}
    (hF : ℌ.BoldfaceFunction₁ F) (hf : BoldfaceBoundedFunction f) :
    ℌ.BoldfaceFunction (fun v ↦ F (f v)) :=
  HierarchySymbol.BoldfaceFunction.bcomp (f := ![f]) hF (by simp [*])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₂.bcomp {k} {F :
    V → V → V} {f₁ f₂ :
    (Fin k → V) → V}
    (hF : ℌ.BoldfaceFunction₂ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    ℌ.BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  HierarchySymbol.BoldfaceFunction.bcomp (f :=
    ![f₁, f₂]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₃.bcomp {k} {F :
    V → V → V → V} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    (hF : ℌ.BoldfaceFunction₃ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    ℌ.BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  HierarchySymbol.BoldfaceFunction.bcomp (f :=
    ![f₁, f₂, f₃]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₁.comp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : BoldfaceBoundedFunction₁ F) (hf : BoldfaceBoundedFunction f) :
    BoldfaceBoundedFunction (fun v ↦ F (f v)) := ⟨hF.bounded.comp hf.bounded, hF.definable.bcomp hf⟩

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₂.comp {k} {F : V → V → V} {f₁ f₂ :
    (Fin k → V) → V}
    (hF : BoldfaceBoundedFunction₂ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    BoldfaceBoundedFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
      ⟨hF.bounded.comp hf₁.bounded hf₂.bounded, hF.definable.bcomp hf₁ hf₂⟩

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₃.comp {k} {F : V → V → V → V} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    (hF : BoldfaceBoundedFunction₃ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    BoldfaceBoundedFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  ⟨hF.bounded.comp hf₁.bounded hf₂.bounded hf₃.bounded, hF.definable.bcomp hf₁ hf₂ hf₃⟩

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.comp₁ {k} {F : V → V} {f : (Fin k → V) → V}
    [hFb : Bounded₁ F] [hFd : Sg0.BoldfaceFunction₁ F] (hf : BoldfaceBoundedFunction f) :
    BoldfaceBoundedFunction (fun v ↦ F (f v)) := BoldfaceBoundedFunction₁.comp ⟨hFb, hFd⟩ hf

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.comp₂ {k} {F : V → V → V} {f₁ f₂ :
    (Fin k → V) → V}
    [hFb : Bounded₂ F] [hFd : Sg0.BoldfaceFunction₂ F]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    BoldfaceBoundedFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
      BoldfaceBoundedFunction₂.comp ⟨hFb, hFd⟩ hf₁ hf₂

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.comp₃ {k} {F : V → V → V → V} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    [hFb : Bounded₃ F] [hFd : Sg0.BoldfaceFunction₃ F]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    BoldfaceBoundedFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
      BoldfaceBoundedFunction₃.comp ⟨hFb, hFd⟩ hf₁ hf₂ hf₃

section «lp_section_1»

-- Source:
-- https://github.com/leanprover-community/mathlib4/blob/
-- 77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26
open Lean.Parser.Tactic (config)

open HierarchySymbol

attribute [aesop (rule_sets := [Definability]) norm]
  sq
  Arith.pow_three
  pow_four

attribute [aesop 5 (rule_sets := [Definability]) safe]
  BoldfaceFunction.comp₁
  BoldfaceFunction.comp₂
  BoldfaceFunction.comp₃
  BoldfaceBoundedFunction.comp₁
  BoldfaceBoundedFunction.comp₂
  BoldfaceBoundedFunction.comp₃

attribute [aesop 6 (rule_sets := [Definability]) safe]
  Boldface.comp₁
  Boldface.comp₂
  Boldface.comp₃
  Boldface.comp₄
  Boldface.const
  Boldface.bcomp₁_zero
  Boldface.bcomp₂_zero
  Boldface.bcomp₃_zero
  Boldface.bcomp₄_zero

attribute [aesop 8 (rule_sets := [Definability]) safe]
  Boldface.ball_lt
  Boldface.ball_le
  Boldface.bex_lt
  Boldface.bex_le
  Boldface.ball_blt_zero
  Boldface.ball_ble_zero
  Boldface.bex_blt_zero
  Boldface.bex_ble_zero

attribute [aesop 10 (rule_sets := [Definability]) safe]
  Boldface.not
  Boldface.imp
  Boldface.iff

attribute [aesop 11 (rule_sets := [Definability]) safe]
  Boldface.and
  Boldface.or
  Boldface.all
  Boldface.ex

/-- Imported declaration from the Incompleteness formalization. -/
macro "definability" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Definability):ident]) safe)

/-- Imported declaration from the Incompleteness formalization. -/
macro (name := definabilityTactic) "definability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent
    `Definability):ident]))

/-- Imported declaration from the Incompleteness formalization. -/
macro (name := definabilityQuestionTactic) "definability?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent
    `Definability):ident]))

example (c : V) : BoldfaceBoundedFunction₂ (fun x _y : V ↦ c + 2 * x ^ 2) := by definability

example {ex : V → V} [Sg0.BoldfaceFunction₁ ex] (c : V) :
    Pg0.BoldfaceRel (fun x y : V ↦ ∃ z < x + c * y, (ex x = x ∧ x < y) ↔
        ex x = z ∧ ex (x + 1) = 2 * z) := by
  simp only [Function.Graph.iff_left ex]
  definability?

example {ex : V → V} [h : Dlt1.BoldfaceFunction₁ ex] :
    Sg1.BoldfaceRel (fun x y : V ↦ ∃ z, x < y ↔ ex (ex x) = z) := by
  definability?

example {ex : V → V} [h : Sg1.BoldfaceFunction₁ ex] :
    Sg1.BoldfaceRel (fun x y : V ↦ ∀ z < ex y, x < y ↔ ex (ex x) = z) := by
  definability?

end «lp_section_1»

end Arith
end FirstOrder
end LO
