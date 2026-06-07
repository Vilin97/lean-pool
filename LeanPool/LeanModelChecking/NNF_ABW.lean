/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Discrete

import LeanPool.LeanModelChecking.LTL_NNF
import LeanPool.LeanModelChecking.ABW

theorem subtype_val_injective {α} {P : α → Prop} : @Function.Injective (Subtype P) α Subtype.val := by simp

abbrev Iic {α} [LE α] (v : α) := { x // x ≤ v }

abbrev Subtype.embed_le {α} [Preorder α] {x y : α} (hle : x ≤ y) : Iic x → Iic y := fun v => ⟨v.val, v.prop.trans hle⟩

theorem antitone_nat_eventually_constant
  {f : ℕ → ℕ} (hf : Antitone f)
    : ∃ N c, (∀ n ≥ N, f n = c) ∧ c ≤ f 0 := by
  have h := tendsto_atTop_ciInf hf ⟨0, Set.forall_mem_range.mpr fun _ => Nat.zero_le _⟩
  simp only [nhds_discrete, Filter.tendsto_pure, Filter.eventually_atTop, ge_iff_le] at h
  obtain ⟨N, h⟩ := h
  refine ⟨N, f N, ?_, hf (Nat.zero_le N)⟩
  intro n hn
  simp_all only [ge_iff_le, le_refl]

def NNF.repeat_and_next {AP} (f g : NNF AP) : ℕ → NNF AP
| 0 => g
| n + 1 => f.and (repeat_and_next f g n).next

theorem release_expand {AP} (f g : NNF AP) : (f.release g).language = (g.and (f.or (f.release g).next)).language := by
  funext w; apply propext
  constructor
  · simp [NNF.language]
    intros H
    rcases H 0 with lg0|⟨_, _⟩
    · refine ⟨lg0, ?_⟩
      by_cases hf : f.language w
      · left; exact hf
      · right
        intros i
        rcases H (i + 1) with lgi1|⟨k, hk, H⟩
        · left; exact lgi1
        · right
          cases k with
          | zero => contradiction
          | succ k => exists k, (by omega)
    · exfalso; omega
  · simp [NNF.language]
    rintro lg H (_|i)
    · left; assumption
    · rcases H with H|H
      · right; exists 0; grind
      · specialize H i
        rcases H with _|⟨k, _, _⟩
        · left; assumption
        · right; exists k + 1, (by omega)

theorem until_expand_repeat {AP} (f g : NNF AP) : ∀ w, (f.until g).language w ↔ ∃ n, (NNF.repeat_and_next f g n).language w := by
  intros w
  constructor
  · simp [NNF.language]
    intros n hg hf
    exists n
    revert w
    induction n
    · simp [NNF.repeat_and_next]
    next n ih =>
      simp [NNF.repeat_and_next, NNF.language]
      intros w hg hf
      constructor
      · specialize hf 0 (by omega)
        exact hf
      · apply ih
        · exact hg
        · intros k hk
          specialize hf (k + 1) (by omega)
          exact hf
  · simp [NNF.language]
    intros n h
    exists n
    revert w
    induction n
    · simp [NNF.repeat_and_next]
    next n ih =>
      simp [NNF.repeat_and_next, NNF.language]
      intros w hf0 h
      specialize ih (fun j => w (j + 1)) h
      rcases ih with ⟨hg, hf⟩
      refine ⟨hg, ?_⟩
      intros k hk
      cases k with
      | zero => exact hf0
      | succ k => apply hf k; omega

namespace PositiveBool

theorem Sat.and_union {Q} (f g : PositiveBool Q) {A B : Set Q} : PositiveBool.Sat A f → PositiveBool.Sat B g → PositiveBool.Sat (A ∪ B) (f.and g) := by
  intros HA HB
  simp [Sat]
  constructor
  · apply Sat.monotone Set.subset_union_left; assumption
  · apply Sat.monotone Set.subset_union_right; assumption

def map {Q P} (f : Q → P) : PositiveBool Q → PositiveBool P
| atom q => .atom (f q)
| true => true
| false => false
| and ψ₁ ψ₂ => .and (map f ψ₁) (map f ψ₂)
| or ψ₁ ψ₂ => .or (map f ψ₁) (map f ψ₂)

instance : Functor PositiveBool where
  map := map

def Forall (p : α → Prop) : PositiveBool α → Prop
| atom q => p q
| true | false => True
| and f g | or f g => f.Forall p ∧ g.Forall p

theorem Forall.imp {α} {p q : α → Prop} (h : ∀ x, p x → q x) {φ : PositiveBool α} (pf : φ.Forall p) : φ.Forall q := by
  induction φ <;> simp [PositiveBool.Forall] at pf ⊢ <;> grind

def map_subtype {α} {p : α → Prop} (ψ : PositiveBool α) (pf : ψ.Forall p) : PositiveBool (Subtype p) :=
  match ψ, pf with
  | atom q, h => .atom ⟨q, h⟩
  | true, _ => .true
  | false, _ => .false
  | and ψ₁ ψ₂, pf => .and (map_subtype ψ₁ (by simp [Forall] at pf; exact pf.left)) ((map_subtype ψ₂ (by simp [Forall] at pf; exact pf.right)))
  | or ψ₁ ψ₂, pf => .or (map_subtype ψ₁ (by simp [Forall] at pf; exact pf.left)) ((map_subtype ψ₂ (by simp [Forall] at pf; exact pf.right)))

def map_subtype_imp {α : Type} {p q : α → Prop} (ψ : PositiveBool (Subtype p)) (h : ∀ x, p x → q x) : PositiveBool (Subtype q) :=
  (fun x => ⟨x.val, by grind⟩) <$> ψ

@[simp]
lemma map_subtype_imp_collapse
  {α} {p q : α → Prop} (ψ : PositiveBool α)
  {pf : ψ.Forall p} {h : ∀ x, p x → q x}
    : (ψ.map_subtype pf).map_subtype_imp h = ψ.map_subtype (pf.imp h) := by
  induction ψ <;> simp [map_subtype_imp, Functor.map, map, map_subtype] at * <;> constructor <;> grind

lemma map_subtype_contract
  {α} {P Q : α → Prop}
  {φ : PositiveBool α}
  {Y : Set (Subtype P)} {fq : φ.Forall Q} {fp : φ.Forall P}
  (hsat : (φ.map_subtype fp).Sat Y) (f : Subtype P → Subtype Q)
  (hf : ∀ (x : Subtype P), Q (x.val) → (f x).val = x)
    : (φ.map_subtype fq).Sat (f '' Y) := by
  induction φ <;> simp [map_subtype, Sat] at hsat ⊢ <;> simp [Forall] at fp fq <;> grind

lemma map_sat_le
  {T} {Q Q' : T} [Preorder T] (hle : Q' ≤ Q) {ψ : PositiveBool (Iic Q')} {Y : Set (Iic Q)}
  (Hsat : (ψ.map_subtype_imp (fun _ qp => qp.trans hle)).Sat Y)
    : ψ.Sat { q | q.embed_le hle ∈ Y } := by
  induction ψ <;> simp [Sat, map_subtype_imp, Functor.map, map] at Hsat ⊢
  next a => exact Hsat
  next f g f_ih g_ih => exact ⟨f_ih Hsat.left, g_ih Hsat.right⟩
  next f g f_ih g_ih =>
    rcases Hsat with Hsat|Hsat
    · left; apply f_ih Hsat
    · right; apply g_ih Hsat

lemma map_subtype_imp_embed
  {T : Type} [PartialOrder T] {x y : T} (hle : x ≤ y)
  (ψ : PositiveBool {q // q ≤ x}) (Y : Set {q // q ≤ x})
    : PositiveBool.Sat (Subtype.embed_le hle '' Y) (ψ.map_subtype_imp (fun _ x => x.trans hle)) ↔ ψ.Sat Y := by
  induction ψ <;> simp [Sat, map_subtype_imp, Functor.map, map] at * <;> grind

lemma sat_map_image
  {T : Type} [PartialOrder T] {Q' Q : T} (hq : Q' ≤ Q)
  {ψ : PositiveBool T} {Y : Set { q // q ≤ Q' }}
  (H2 : Forall (fun x => x ≤ Q') ψ)
    : (ψ.map_subtype H2).Sat Y ↔ (ψ.map_subtype (H2.imp (by grind))).Sat (Subtype.embed_le hq '' Y) := by
  induction ψ <;> simp [Sat, map_subtype] <;> simp [Forall] at H2 <;> grind

lemma map_subtype_restrict {T : Type} {α β : T → Prop} {ψ : PositiveBool T} {Y : Set (Subtype α)}
  (all_α : ψ.Forall α) (all_β : ψ.Forall β) (hle : ∀ {q}, β q → α q)
  (p_sat : PositiveBool.Sat Y (ψ.map_subtype all_α))
    : PositiveBool.Sat {q | ⟨q.val, hle q.prop⟩ ∈ Y} (ψ.map_subtype all_β) := by
  induction ψ <;> simp [map_subtype, Sat] at p_sat ⊢ <;> grind

end PositiveBool

namespace DAG

instance : Functor DAG where
  map f G := {
    V := (fun (q, l) => (f q, l)) '' G.V,
    E := (fun ((q, l), q') => ((f q, l), f q')) '' G.E
    edge_closure := by
      rintro ⟨⟨_, _⟩, _⟩
      simp
      rintro _ _ hE rfl rfl
      have := G.edge_closure _ hE
      grind
  }

theorem path_mapped {α β} [Nonempty α] (G : DAG α) (f : α → β) (f_inj : Function.Injective f) (p : ℕ → β) (p_path : (f <$> G).path p) : G.path ((Function.invFun f) ∘ p) := by
  obtain ⟨n, p_path⟩ := p_path
  exists n
  intros i
  specialize p_path i
  simp [Functor.map] at p_path
  obtain ⟨a, b, h_in, h1, h3⟩ := p_path
  simp
  rw [←h1, ←h3]
  have h := Function.leftInverse_invFun f_inj
  grind

theorem path_elems_prop {α} {P : α → Prop} {G : DAG (Subtype P)} {p : ℕ → α} (p_path : (Subtype.val <$> G).path p) : ∀ i, P (p i) := by
  simp [DAG.path, Functor.map] at p_path
  grind

end DAG

namespace replace_root

variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)

section

variable (r₁ : Iic φ₁) (r₂ : Iic φ₂) (G : DAG (Iic φ₁))

def base : DAG.Base {q // q ≤ φ₂} := {
  V := {(r₂, 0)} ∪ (fun (q, l) => (⟨q.val, by grind⟩, l)) '' (G.V \ {(r₁, 0)})
  E := (fun ((q, l), q') =>
    if (q, l) = (r₁, 0) then
      ((r₂, 0), ⟨q'.val, by grind⟩)
    else
      ((⟨q.val, by grind⟩, l), ⟨q'.val, by grind⟩)
    ) '' G.E
}

def dag : DAG {q // q ≤ φ₂} := {
  replace_root.base hle r₁ r₂ G with
  edge_closure := by
    simp only [replace_root.base]
    have := G.edge_closure
    intros e he
    simp; grind
}

lemma path_after_1_prop (p : ℕ → {q // q ≤ φ₂}) (p_path : (dag hle r₁ r₂ G).path p) : ∀ i > 0, (p i).val ≤ φ₁ := by
  simp only [DAG.path, dag, base] at p_path
  grind

lemma preserves_path
  (p : ℕ → {q // q ≤ φ₂}) (p_path : (dag hle r₁ r₂ G).path p)
    : G.path (fun i => ⟨(p (i + 1)).val, path_after_1_prop hle r₁ r₂ G p p_path _ (by omega)⟩) := by
  simp [DAG.path] at p_path
  obtain ⟨n, p_path⟩ := p_path
  simp [DAG.path]
  exists (n + 1)
  intros i
  specialize p_path (i + 1)
  simp [dag, base] at p_path
  grind

end

def run_dag
  {S}
  {M : ABW S (Iic φ₁)} {M' : ABW S (Iic φ₂)} {w : ℕ → S}
  (G : RunDAG M w)
  (h_delta_root : ∀ Q, PositiveBool.Sat Q (M.δ M.q₀ (w 0)) → PositiveBool.Sat ((Subtype.embed_le hle) '' Q) (M'.δ M'.q₀ (w 0)))
  (h_delta_eq : ∀ (q : Iic φ₁) i, M'.δ (q.embed_le hle) (w i) = (M.δ q (w i)).map_subtype_imp (fun _ p => p.trans hle))
    : RunDAG M' w := {
  dag hle M.q₀ M'.q₀ G.toDAG with
  p_root := by simp [dag, base]
  p_sat := by
    have p_sat := G.p_sat
    simp at p_sat
    simp only [dag, base]
    rintro ⟨q, l⟩
    intros hq
    simp only [Set.mem_union] at hq
    rcases hq with hq|hq
    · simp at hq; cases hq; subst_vars
      simp
      obtain ⟨Y, p_sat, p_sub⟩ := p_sat M.q₀ _ 0 G.p_root
      exists Subtype.embed_le hle '' Y
      constructor
      · apply h_delta_root
        exact p_sat
      · rw [Set.subset_def]
        simp only [Set.mem_image, Set.mem_prod]
        rintro ⟨⟨q, l⟩, q'⟩ H
        simp at H
        rcases H with ⟨⟨rfl, rfl⟩, q, qp, qY, rfl⟩
        rw [Set.subset_def] at p_sub
        simp only [Set.mem_prod] at p_sub
        specialize p_sub ((M.q₀, 0), ⟨q, qp⟩)
        grind
    · simp at hq
      rcases hq with ⟨q, qp, ⟨hV, not_root⟩, rfl⟩
      obtain ⟨Y, p_sat, p_sub⟩ := p_sat q qp l hV
      exists Subtype.embed_le hle '' Y
      constructor
      · specialize h_delta_eq ⟨q, qp⟩ l
        rw [h_delta_eq]
        rw [PositiveBool.map_subtype_imp_embed hle]
        assumption
      · rw [Set.subset_def]
        simp only [Set.mem_image, Set.mem_prod]
        rintro ⟨⟨q, l⟩, q'⟩ H
        simp at H
        rcases H with ⟨⟨rfl, rfl⟩, q', q'p, qY, rfl⟩
        rw [Set.subset_def] at p_sub
        simp only [Set.mem_prod] at p_sub
        specialize p_sub ((⟨q, qp⟩, l), ⟨q', q'p⟩)
        grind
}

end replace_root

namespace shift_dag

variable
  {T : Type} [PartialOrder T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)

section

variable (r₁ : {q // q ≤ φ₁}) (r₂ : {q // q ≤ φ₂}) (G : DAG (Iic φ₁))

def dag (hrx : (r₁, 0) ∈ G.V) : DAG (Iic φ₂) := {
  V := {(r₂, 0)} ∪ (fun (q, i) => (q.embed_le hle, i + 1)) '' G.V
  E := {((r₂, 0), r₁.embed_le hle)} ∪ (fun ((q, i), q') => ((q.embed_le hle, i + 1), q'.embed_le hle)) '' G.E
  edge_closure := by have := G.edge_closure; grind
}

lemma path_after_1_prop (hrx : (r₁, 0) ∈ G.V) (p : ℕ → Iic φ₂) (p_path : (dag hle r₁ r₂ G hrx).path p) : ∀ i > 0, (p i).val ≤ φ₁ := by
  grind [DAG.path, dag]

lemma preserves_path
  (G : DAG (Iic φ₁)) (hrx : (r₁, 0) ∈ G.V)
  (p : ℕ → Iic φ₂) (p_path : (dag hle r₁ r₂ G hrx).path p)
    : G.path (fun i => ⟨(p (i + 1)).val, path_after_1_prop hle r₁ r₂ G hrx p p_path _ (by omega)⟩) := by
  simp [DAG.path] at p_path
  obtain ⟨n, p_path⟩ := p_path
  simp [DAG.path]
  exists n
  grind [dag]

end

def run_dag
  {S}
  {M : ABW S (Iic φ₁)} {M' : ABW S (Iic φ₂)} {w : ℕ → S}
  (G : RunDAG M (fun j => w (j + 1)))
  (h_root : PositiveBool.Sat {⟨M.q₀.val, M.q₀.prop.trans hle⟩} (M'.δ M'.q₀ (w 0)))
  (h_delta_eq : ∀ (q : Iic φ₁) i, M'.δ (q.embed_le hle) (w i) = (M.δ q (w i)).map_subtype_imp (fun _ q => q.trans hle))
    : RunDAG M' w := {
  dag hle M.q₀ M'.q₀ G.toDAG G.p_root with
  p_root := by simp [dag]
  p_sat := by
    have p_sat := G.p_sat
    rintro ⟨q, l⟩
    intros hV
    simp
    simp [dag] at hV ⊢
    rcases hV with ⟨rfl, rfl⟩|⟨z, hz, l, hV, rfl, rfl⟩
    · exists {⟨M.q₀.val, M.q₀.prop.trans hle⟩}
      constructor
      · exact h_root
      · simp
    · specialize p_sat _ hV
      simp at p_sat
      obtain ⟨Y, p_sat, p_sub⟩ := p_sat
      exists Subtype.embed_le hle '' Y
      constructor
      · specialize h_delta_eq ⟨z, hz⟩ (l + 1)
        rw [h_delta_eq]
        rw [PositiveBool.map_subtype_imp_embed hle]
        assumption
      · rw [Set.subset_def]
        simp only [Set.mem_image, Set.mem_prod]
        rintro ⟨⟨q, l⟩, q'⟩ H
        simp at H
        rcases H with ⟨⟨rfl, rfl⟩, q', q'p, qY, rfl⟩
        rw [Set.subset_def] at p_sub
        simp only [Set.mem_prod] at p_sub
        specialize p_sub ((⟨z, hz⟩, l), ⟨q', q'p⟩)
        grind
}

end shift_dag

namespace conjoin_dag

variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ Φ : T}
  (leφ₁ : φ₁ ≤ Φ) (leφ₂ : φ₂ ≤ Φ)

section

variable
  (r₁ : Iic φ₁) (r₂ : Iic φ₂) (R : Iic Φ)
  (G₁ : DAG (Iic φ₁)) (G₂ : DAG (Iic φ₂))

def base : DAG.Base (Iic Φ) := {
  V :=
    {(R, 0)} ∪
    ((fun (q, l) => (q.embed_le leφ₁, l)) '' (G₁.V \ {(r₁, 0)})) ∪
    (fun (q, l) => (q.embed_le leφ₂, l)) '' (G₂.V \ { (q, l) | l = 0 ∧ (q.val = r₁ ∨ q.val = r₂)})
  E :=
    ((fun ((q, l), q') => (((if (q, l) = (r₁, 0) then R else q.embed_le leφ₁), l), q'.embed_le leφ₁) ) '' G₁.E) ∪
    {
      ((q.embed_le leφ₂, l), q'.embed_le leφ₂) | (q) (l) (q') (_ :
        (q, l) ∈ G₂.V ∧
        (q.val, l) ∉ (Subtype.val <$> G₁).V ∧
        (q.val, l) ≠ (r₁.val, 0) ∧
        (q.val, l) ≠ (r₂.val, 0) ∧
        ((q, l), q') ∈ G₂.E)
    } ∪
    { ((R, 0), q'.embed_le leφ₂) | (q') (_ : ((r₂, 0), q') ∈ G₂.E) }
}

def dag : DAG (Iic Φ) := {
  base leφ₁ leφ₂ r₁ r₂ R G₁ G₂ with
  edge_closure := by
    have G₁_closure := G₁.edge_closure
    have G₂_closure := G₂.edge_closure
    simp only [base]
    intros e he
    simp only [Set.mem_union] at he
    rcases he with (he|he)|he
    · simp only [Set.mem_image, Prod.exists] at he
      obtain ⟨q, qp, l, q', q'p, hqe, rfl⟩ := he
      constructor
      · split
        next q_root =>
          cases q_root
          left; left
          simp only [Set.mem_singleton_iff]
        · left; right
          simp only [Set.mem_image, Set.mem_diff]
          grind
      · simp only [Set.singleton_union, Set.mem_union, Set.mem_insert_iff, Set.mem_image, Set.mem_diff, Set.mem_singleton_iff]
        grind
    · simp only [exists_prop, Subtype.exists] at he
      obtain ⟨q, qp, l, q', q'p, ⟨hV₂, hnV₁, hE₂⟩, rfl⟩ := he
      constructor
      · right
        simp only [Set.mem_image, Set.mem_diff]
        exists (⟨q, qp⟩, l)
        simp [hV₂]
        rintro rfl
        grind
      · simp only [Set.singleton_union, Set.mem_union, Set.mem_insert_iff, Set.mem_image, Set.mem_diff, Set.mem_singleton_iff]
        grind
    · simp at he
      rcases he with ⟨q, pq, he, rfl⟩
      simp only [Set.mem_union, Set.mem_image, Set.mem_diff]
      grind
}

lemma preserves_path
  (op : ℕ → Iic Φ) (op_path : (dag leφ₁ leφ₂ r₁ r₂ R G₁ G₂).path op)
  : (∃ k, (Subtype.val <$> G₁).path (fun i => (op (k + i)).val)) ∨ (Subtype.val <$> G₂).path (fun i => (op (i + 1)).val) := by
  obtain ⟨n, op_path⟩ := op_path
  by_cases h_all_not_G₁ : ∀ i, ((op (1 + i)).val, n + 1 + i) ∉ (Subtype.val <$> G₁).V
  · right
    simp [Functor.map] at h_all_not_G₁
    exists n + 1
    intros i
    specialize op_path (i + 1)
    rcases op_path with (op_path|op_path)|op_path
    · exfalso; cases G₁; grind
    · simp [Functor.map]; grind
    · grind
  · left
    simp [Functor.map] at h_all_not_G₁
    obtain ⟨k, entry_p, entry_V₁⟩ := h_all_not_G₁
    suffices ∀ i, (((op (1 + k + i)).val, n + 1 + k + i), (op (1 + k + (i + 1))).val) ∈ (Subtype.val <$> G₁).E by exists 1 + k; exists n + 1 + k
    simp [Functor.map]
    intros i
    induction i
    · simp
      specialize op_path (1 + k)
      simp only [dag, base, Functor.map] at op_path
      rcases op_path with (op_path|op_path)|op_path <;> grind
    next i ih =>
      specialize op_path (1 + k + (i + 1))
      simp only [dag, base, Functor.map] at op_path
      rcases op_path with (op_path|op_path)|op_path
      · grind
      · exfalso; cases G₁; grind
      · exfalso; grind

end

def run_dag
  {S}
  {M₁ : ABW S (Iic φ₁)} {M₂ : ABW S (Iic φ₂)} {M : ABW S (Iic Φ)}
  {w : ℕ → S}
  (G₁ : RunDAG M₁ w) (G₂ : RunDAG M₂ w)
  (delta_eq_1 : ∀ (q : Iic φ₁) i, M.δ (q.embed_le leφ₁) (w i) = (M₁.δ q (w i)).map_subtype_imp (fun _ q => q.trans leφ₁))
  (delta_eq_2 : ∀ (q : Iic φ₂) i, M.δ (q.embed_le leφ₂) (w i) = (M₂.δ q (w i)).map_subtype_imp (fun _ q => q.trans leφ₂))
  (delta_root : ∀ Y₁ Y₂, (M₁.δ M₁.q₀ (w 0)).Sat Y₁ → (M₂.δ M₂.q₀ (w 0)).Sat Y₂ → (M.δ M.q₀ (w 0)).Sat (((Subtype.embed_le leφ₁) '' Y₁) ∪ ((Subtype.embed_le leφ₂) '' Y₂)))
    : RunDAG M w := {
  dag leφ₁ leφ₂ M₁.q₀ M₂.q₀ M.q₀ G₁.toDAG G₂.toDAG with
  p_root := by simp only [dag, base, Set.singleton_union, Set.mem_union, Set.mem_insert_iff, true_or]
  p_sat := by
    intros v hv
    simp only [dag, base, Set.mem_union] at hv
    rcases hv with (hv|hv)|hv
    · simp only [Set.mem_singleton_iff] at hv; subst hv
      obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat (M₁.q₀, 0) G₁.p_root
      obtain ⟨Y₂, p_sat₂, p_sub₂⟩ := G₂.p_sat (M₂.q₀, 0) G₂.p_root
      exists (((Subtype.embed_le leφ₁) '' Y₁) ∪ ((Subtype.embed_le leφ₂) '' Y₂))
      constructor
      · grind
      · rw [Set.subset_def]
        simp only [
          Set.prod_union, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff,
          Set.mem_image, Subtype.exists, dag, base, Set.singleton_union, Prod.mk.eta, Prod.mk.injEq,
          Functor.map, Prod.exists, Prod.forall, Subtype.forall,
        ]
        rintro q pq l q' _
        rintro (⟨⟨q_eq, rfl⟩, ⟨pq', q'_in_Y₁⟩⟩|⟨⟨q_eq, rfl⟩, ⟨pq', q'_in_Y₂⟩⟩)
        · left; grind
        · right; grind
    · simp at hv
      rcases hv with ⟨q, pq, l, ⟨hV₁, not_root⟩, rfl⟩
      obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat _ hV₁
      exists Subtype.embed_le leφ₁ '' Y₁
      constructor
      · rw [delta_eq_1]
        rw [PositiveBool.map_subtype_imp_embed leφ₁]
        exact p_sat₁
      · rw [Set.subset_def]
        simp only [dag, base]
        simp only [Set.mem_image, Subtype.exists, Set.mem_union, Prod.exists, Set.mem_setOf_eq]
        grind
    · simp at hv
      rcases hv with ⟨q, pq, l, ⟨hV₂, not_root⟩, rfl⟩
      by_cases H₁ : (q, l) ∈ (Subtype.val <$> G₁.toDAG).V
      · simp [Functor.map] at H₁
        rcases H₁ with ⟨hq1, hV₁⟩
        obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat _ hV₁
        exists Subtype.embed_le leφ₁ '' Y₁
        constructor
        · rw [show Subtype.embed_le leφ₂ ⟨q, pq⟩ = Subtype.embed_le leφ₁ ⟨q, hq1⟩ by rfl]
          rw [delta_eq_1]
          rw [PositiveBool.map_subtype_imp_embed leφ₁]
          exact p_sat₁
        · rw [Set.subset_def]
          simp only [dag, base]
          intros e he
          simp only [Set.mem_union, Set.mem_image]
          left; left
          simp at he
          rcases he with ⟨e1_eq, q', pq', q'_in_Y₁, e2_eq⟩
          exists ((⟨q, hq1⟩, l), ⟨q', pq'⟩)
          exists Set.mem_of_subset_of_mem p_sub₁ (by grind)
          grind
      · obtain ⟨Y₂, p_sat₂, p_sub₂⟩ := G₂.p_sat _ hV₂
        exists Subtype.embed_le leφ₂ '' Y₂
        constructor
        · rw [delta_eq_2]
          rw [PositiveBool.map_subtype_imp_embed leφ₂]
          exact p_sat₂
        · rw [Set.subset_def]
          simp only [dag, base]
          intros e he
          simp at he
          simp only [Set.mem_union, Set.mem_image]
          left; right
          simp only [Subtype.exists]
          grind
}

end conjoin_dag

def shift_conjoin_dag.run_dag
  {S T} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T}
  (leφ₁ : φ₁ ≤ φ₂)
  {M₁ : ABW S (Iic φ₁)} {M₂ : ABW S (Iic φ₂)}
  {w : ℕ → S}
  (G₁ : RunDAG M₁ w) (G₂ : RunDAG M₂ (fun j => w (j + 1)))
  (delta_eq_1 : ∀ (q : Iic φ₁) i, M₂.δ (q.embed_le leφ₁) (w i) = (M₁.δ q (w i)).map_subtype_imp (fun _ q => q.trans leφ₁))
  (delta_root : ∀ Y₁, (M₁.δ M₁.q₀ (w 0)).Sat Y₁ → (M₂.δ M₂.q₀ (w 0)).Sat (((Subtype.embed_le leφ₁) '' Y₁) ∪ {M₂.q₀}))
    : RunDAG M₂ w := {
  conjoin_dag.dag leφ₁ (le_refl φ₂) M₁.q₀ M₂.q₀ M₂.q₀ G₁.toDAG
    (shift_dag.dag (le_refl φ₂) M₂.q₀ M₂.q₀ G₂.toDAG G₂.p_root) with
  p_root := by simp [conjoin_dag.dag, conjoin_dag.base]
  p_sat := by
    intros v hv
    simp only [conjoin_dag.dag, conjoin_dag.base, shift_dag.dag, Set.mem_union, Set.mem_image] at hv
    rcases hv with (hv|hv)|hv
    · simp at hv; subst hv
      simp only
      obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat _ G₁.p_root
      exists ((Subtype.embed_le leφ₁) '' Y₁) ∪ {M₂.q₀}
      constructor
      · exact delta_root _ p_sat₁
      · rw [Set.subset_def]
        simp only [
          conjoin_dag.dag, conjoin_dag.base, shift_dag.dag,
          Set.mem_image, Subtype.exists, Set.singleton_union,
          Prod.exists, exists_prop, Set.mem_union, Set.mem_setOf_eq
        ]
        grind
    · simp at hv
      rcases hv with ⟨q, qp, l, ⟨hV₁, not_root⟩, rfl⟩
      simp only
      obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat _ hV₁
      exists Subtype.embed_le leφ₁ '' Y₁
      constructor
      · rw [delta_eq_1]
        rw [PositiveBool.map_subtype_imp_embed leφ₁]
        exact p_sat₁
      · rw [Set.subset_def]
        simp only [
          conjoin_dag.dag, conjoin_dag.base,
          Set.mem_image, Subtype.exists,
          Prod.mk.injEq, Prod.exists, Set.mem_union, Prod.forall, Set.mem_prod
        ]
        grind
    · simp at hv
      rcases hv with ⟨⟨q, pq, l, hV₂, rfl⟩, not_root⟩
      simp at not_root
      by_cases H₁ : (q, l + 1) ∈ (Subtype.val <$> G₁.toDAG).V
      · simp [Functor.map] at H₁
        rcases H₁ with ⟨hq1, hV₁⟩
        obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat _ hV₁
        exists Subtype.embed_le leφ₁ '' Y₁
        constructor
        · rw [delta_eq_1 ⟨q, hq1⟩]
          rw [PositiveBool.map_subtype_imp_embed leφ₁]
          exact p_sat₁
        · rw [Set.subset_def]
          simp only [conjoin_dag.dag, conjoin_dag.base, shift_dag.dag]
          intros e he
          simp only [Set.mem_union, Set.mem_image]
          left; left
          simp at he
          rcases he with ⟨e1_eq, q', pq', q'_in_Y₁, e2_eq⟩
          exists ((⟨q, hq1⟩, l + 1), ⟨q', pq'⟩)
          simp
          grind
      · obtain ⟨Y₂, p_sat₂, p_sub₂⟩ := G₂.p_sat _ hV₂
        simp
        exists Y₂
        constructor
        · exact p_sat₂
        · rw [Set.subset_def]
          intros e he
          simp only [conjoin_dag.dag, conjoin_dag.base]
          simp only [Set.mem_union]
          left; right
          simp only [shift_dag.dag]
          simp only [Subtype.coe_eta, Set.singleton_union, Set.mem_insert_iff, Prod.mk.injEq,
            Set.mem_image, Prod.exists, Subtype.exists, Functor.map, exists_eq_right_right,
            exists_and_right, exists_eq_right, not_exists, ne_eq, not_and, exists_prop,
            Subtype.mk.injEq, Set.mem_setOf_eq]
          simp at he
          exists q, pq, l + 1, e.2.val, e.2.prop
          simp [Functor.map] at H₁
          grind
  }

namespace filter_dag

variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (leφ : φ ≤ Φ)

section

variable (G : DAG (Iic Φ)) (rΦ : Iic Φ) (rφ : Iic φ) (shift : ℕ)

def dag : DAG (Iic φ) := {
  V := { (q, l) | (q.embed_le leφ, shift + l) ∈ G.V } ∪ {(rφ, 0)}
  E := { ((q, l), q') : _ | ((q.embed_le leφ, shift + l), q'.embed_le leφ) ∈ G.E ∨ (l = 0 ∧ q = rφ ∧ ((rΦ, shift), q'.embed_le leφ) ∈ G.E) }
  edge_closure := by cases G; simp; grind
}

theorem preserves_path {p : ℕ → Iic φ} (p_path : (dag leφ G rΦ rφ shift).path p) : G.path (fun i => (p (i + 1)).embed_le leφ) := by
  obtain ⟨start, p_path⟩ := p_path
  exists shift + start + 1
  intros i
  specialize p_path (i + 1)
  grind [dag]

end

def run_dag
  {S} {M : ABW S (Iic Φ)} {M' : ABW S (Iic φ)} {w : ℕ → S} (G : RunDAG M w)
  (rΦ : Iic Φ)
  (shift : ℕ)
  (h_root : ∃ Y, (M'.δ M'.q₀ (w shift)).Sat Y ∧ Y ⊆ { q | ((rΦ, shift), q.embed_le leφ) ∈ G.E })
  (h_delta_eq : ∀ (q : Iic φ) i, M.δ (q.embed_le leφ) (w i) = (M'.δ q (w i)).map_subtype_imp (fun _ q => q.trans leφ))
    : RunDAG M' (fun j => w (j + shift)) := {
  dag leφ G.toDAG rΦ M'.q₀ shift with
  p_root := by simp [dag]
  p_sat := by
    intros v hv
    simp [dag] at hv
    rcases hv with rfl|hv
    · grind [dag]
    · obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ hv
      exists { q | q.embed_le leφ ∈ Y }
      constructor
      · rw [h_delta_eq] at p_sat
        rw [show v.2 + shift = shift + v.2 by omega]
        exact PositiveBool.map_sat_le leφ p_sat
      · grind [dag]
}

end filter_dag

namespace always_dag

variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (ltφ : φ < Φ)

section

variable (G : ℕ → DAG (Iic φ))

def Vb := ⋃ k, { (q, i + k) | (q) (i) (_ : (q, i) ∈ (G k).V) }

def V : Set (Iic Φ × ℕ) := { (q, _) | q = ⟨Φ, le_refl _⟩ } ∪ (fun (q, l) => ⟨q.embed_le ltφ.le, l⟩) '' Vb G

noncomputable def mini (v : Iic φ × ℕ) : ℕ := sInf { i | i ≤ v.2 ∧ (v.1, v.2 - i) ∈ (G i).V }

lemma mini_le q l (H : (q, l) ∈ Vb G) : mini G (q, l) ≤ l := by
  simp [mini]
  simp [Vb] at H
  rcases H with ⟨i, q, pq, l, hV, rfl, rfl⟩
  apply (show ∀ x y z, x ≤ z → x ≤ y + z by omega)
  apply csInf_le ⟨0, by intro i _; exact Nat.zero_le i⟩
  simp; exact hV

lemma mini_in q l (H : (q, l) ∈ Vb G) : let i' := mini G (q, l); (q, l - i') ∈ (G i').V := by
  have hne : Set.Nonempty { i | i ≤ l ∧ (q, l - i) ∈ (G i).V } := by
    simp [Vb] at H
    rcases H with ⟨i, q, pq, l, hV, rfl, rfl⟩
    simp [Set.Nonempty]
    grind
  exact (csInf_mem hne).2

def E : Set ((Iic Φ × ℕ) × Iic Φ) := { ((q, l), q') : _ |
  q = ⟨Φ, le_refl _⟩ ∧ (q' = ⟨Φ, le_refl _⟩ ∨ ∃ (hq' : q' ≤ φ), ((⟨φ, le_refl _⟩, 0), ⟨q'.val, hq'⟩) ∈ (G l).E)
} ∪ { ((q, l), q') : _ |
  q ≠ ⟨Φ, le_refl _⟩ ∧ ∃ (hq : q ≤ φ) (hq' : q' ≤ φ) (_ : (⟨q.val, hq⟩, l) ∈ Vb G), let i' := mini G (⟨q.val, hq⟩, l); ((⟨q.val, hq⟩, l - i'), ⟨q'.val, hq'⟩) ∈ (G i').E
}

lemma mini_not_increasing q l q' (He : ((q.embed_le ltφ.le, l), q'.embed_le ltφ.le) ∈ E G) : mini G (q', l + 1) ≤ mini G (q, l) := by
  simp [E] at He
  simp [show q ≠ Φ by grind] at He
  rcases He with ⟨HVb, _, _, He⟩
  have ec := (G (mini G (q, l))).edge_closure _ He
  simp at ec
  apply csInf_le ⟨0, by intro i _; exact Nat.zero_le i⟩
  simp
  have := mini_le _ _ _ HVb
  grind

def base : DAG.Base (Iic Φ) := { V := V ltφ G, E := E G }

def dag : DAG (Iic Φ) := {
  base ltφ G with
  edge_closure := by
    rintro ⟨⟨q, l⟩, q'⟩ he
    simp only [base, V, E, Set.mem_setOf, Set.mem_union] at he
    rcases he with ⟨rfl, he⟩|⟨h_not_root, qp, q'p, qvb, he⟩
    · rcases he with rfl|⟨q'p, he⟩
      · simp [base, V]
      · constructor
        · simp [base, V]
        · simp only [base, V, Set.mem_union]
          right
          simp only [Set.mem_image, Vb]
          exists (⟨q', q'p⟩, l + 1)
          simp
          exists l, q'.val, q'p, 1
          have := (G l).edge_closure _ he
          grind
    · constructor
      · simp [base, V, h_not_root]
        exists q, qp
      · simp [base, V]; right
        exists q', q'p
        simp
        obtain ⟨-, ec⟩ := DAG.edge_closure _ _ he
        simp at ec
        simp [Vb, Set.mem_iUnion]
        exists mini _ _, _, q'p, _, ec
        have := mini_le G ⟨q, qp⟩ l
        grind
}

lemma preserves_path
  (op : ℕ → Iic Φ) (op_path : (dag ltφ G).path op)
    : op = (fun _ => ⟨Φ, le_refl _⟩) ∨ (∃ i k, (Subtype.val <$> (G i)).path (fun i => (op (k + i)).val)) := by
  by_cases H_spine : op = (fun _ => ⟨Φ, le_refl _⟩); { left; exact H_spine }; right
  obtain ⟨bp, H_bp⟩ : ∃ i, op i ≠ ⟨Φ, le_refl _⟩ := by grind
  obtain ⟨n, op_path⟩ := op_path
  have bp_branch : (op bp).val ≤ φ := by
    simp only [dag, base, E] at op_path
    grind
  have pres_branch : ∀ {i}, (op i).val ≤ φ → ∀ j ≥ i, (op j).val ≤ φ := by
    simp only [dag, base, E, Set.mem_union] at op_path
    intros _ _ j
    induction j
    · grind
    next n _ => have := op_path n; grind
  let ι := fun i => mini G (⟨(op (bp + i)).val, (pres_branch bp_branch _ (by omega))⟩, n + (bp + i))
  have ι_antitone : Antitone ι := by
    apply antitone_nat_of_succ_le
    intros n
    specialize op_path (bp + n)
    exact mini_not_increasing ltφ _ _ _ _ op_path
  obtain ⟨sp, i, hi, _⟩ := antitone_nat_eventually_constant ι_antitone
  simp only [dag, base, E] at op_path
  have : i ≤ n + bp := by
    have : ι 0 ≤ n + bp := by apply mini_le G _ _; grind
    grind
  exists i, bp + sp
  simp [Functor.map, DAG.path]
  simp [ι] at hi
  exists n + bp + sp - i
  intros l
  specialize op_path (bp + sp + l)
  have not_root : op (bp + sp + l) ≠ ⟨Φ, le_refl _⟩ := by
    grind [pres_branch bp_branch (bp + sp + l) (by omega)]
  simp [not_root] at op_path
  rcases op_path with ⟨p1, _, p2, he⟩
  exists p1, p2
  specialize hi (sp + l) (by omega)
  grind

end

def run_dag
  {S} {M : ABW S (Iic Φ)} {M' : ABW S (Iic φ)} {w : ℕ → S} (G : ∀ (i : ℕ), RunDAG M' (fun j => w (j + i)))
  (h_M_root : M.q₀ = ⟨Φ, le_refl _⟩) (h_M'_root : M'.q₀ = ⟨φ, le_refl _⟩)
  (h_delta_root : ∀ Y l, (M'.δ M'.q₀ (w l)).Sat Y → (M.δ ⟨Φ, le_refl _⟩ (w l)).Sat (Subtype.embed_le ltφ.le '' Y ∪ {M.q₀}))
  (h_delta_eq : ∀ (q : Iic φ) i, M.δ (q.embed_le ltφ.le) (w i) = (M'.δ q (w i)).map_subtype_imp (fun _ q => q.trans ltφ.le))
    : RunDAG M w := {
  dag ltφ (fun i => (G i).toDAG) with
  p_root := by simp [dag, base, V]; left; exact h_M_root
  p_sat := by
    rintro ⟨q, l⟩ hv
    simp [dag, base, V] at hv
    rcases hv with rfl|⟨q, pq, ⟨hv, rfl⟩⟩
    · obtain ⟨Y, p_sat, p_sub⟩ := (G l).p_sat _ (G l).p_root
      exists ((Subtype.embed_le ltφ.le) '' Y) ∪ {M.q₀}
      constructor
      · apply h_delta_root
        simpa using p_sat
      · simp only [dag, base, E]
        grind only [
          = Set.subset_def,
          = Set.mem_union,
          = Set.mem_prod,
          = Set.mem_singleton_iff,
          = Set.mem_image,
          usr Set.mem_setOf_eq
        ]
    · let i' := mini (fun i => (G i).toDAG) (⟨q, pq⟩, l)
      obtain ⟨Y, p_sat, _⟩ := (G i').p_sat (⟨q, pq⟩, l - i') (by apply mini_in (G := (fun i => (G i).toDAG)); exact hv)
      exists Subtype.embed_le ltφ.le '' Y
      constructor
      · rw [h_delta_eq]
        rw [PositiveBool.map_subtype_imp_embed]
        have eq : l - i' + i' = l := by have := mini_le (fun i => (G i).toDAG); grind
        rwa [eq] at p_sat
      · simp only [dag, base, E]
        grind only [
          = Set.subset_def,
          = Set.mem_union,
          = Set.mem_prod,
          = Set.mem_singleton_iff,
          = Set.mem_image,
          usr Set.mem_setOf_eq
        ]
}

end always_dag

section sub

-- Refactoring the old cl and coming up with this subformula relation was done
-- by Claude 4.5 Opus
/-- Subformula relation: `φ ≤ ψ` means φ is a subformula of ψ -/
inductive sub {AP} : NNF AP → NNF AP → Prop where
| refl {φ} : sub φ φ
| and_left {φ f g} : sub φ f → sub φ (.and f g)
| and_right {φ f g} : sub φ g → sub φ (.and f g)
| or_left {φ f g} : sub φ f → sub φ (.or f g)
| or_right {φ f g} : sub φ g → sub φ (.or f g)
| next {φ f} : sub φ f → sub φ (.next f)
| until_left {φ f g} : sub φ f → sub φ (.until f g)
| until_right {φ f g} : sub φ g → sub φ (.until f g)
| release_left {φ f g} : sub φ f → sub φ (.release f g)
| release_right {φ f g} : sub φ g → sub φ (.release f g)

instance {AP} : LE (NNF AP) := ⟨sub⟩

-- TODO: could we use the built-in sizeOf instead?
def size {AP} : NNF AP → ℕ
| .atom _ => 1
| .not_atom _ => 1
| .next φ₁ => size φ₁ + 1
| .and φ₁ φ₂ | .or φ₁ φ₂ | .until φ₁ φ₂ | .release φ₁ φ₂ => max (size φ₁) (size φ₂) + 1

lemma size_le_of_sub {AP} {φ ψ : NNF AP} (h : φ ≤ ψ) : size φ ≤ size ψ := by
  induction h
  case refl => rfl
  all_goals (rename_i ih; simp only [size]; omega)

lemma size_lt_of_sub {AP} {φ ψ : NNF AP} (h : φ ≤ ψ) (hne : ψ ≠ φ) : size φ < size ψ := by
  cases h
  case refl => contradiction
  all_goals (rename_i hsub; have := size_le_of_sub hsub; simp only [size]; omega)

theorem sub_antisymm {AP} {φ₁ φ₂ : NNF AP} (h1 : φ₁ ≤ φ₂) (h2 : φ₂ ≤ φ₁) : φ₁ = φ₂ := by
  by_contra hne
  have : size φ₁ < size φ₂ := size_lt_of_sub h1 (Ne.symm hne)
  have : size φ₂ < size φ₁ := size_lt_of_sub h2 hne
  omega

theorem sub_trans {AP} {a b c : NNF AP} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  induction h2 generalizing a
  case refl => exact h1
  all_goals rename_i ih; first
    | exact sub.and_left (ih h1)
    | exact sub.and_right (ih h1)
    | exact sub.or_left (ih h1)
    | exact sub.or_right (ih h1)
    | exact sub.next (ih h1)
    | exact sub.until_left (ih h1)
    | exact sub.until_right (ih h1)
    | exact sub.release_left (ih h1)
    | exact sub.release_right (ih h1)

instance {AP} : PartialOrder (NNF AP) where
  le_refl _ := sub.refl
  le_trans _ _ _ := sub_trans
  le_antisymm _ _ := sub_antisymm

instance {AP} {ψ : NNF AP} : Nonempty { q // q ≤ ψ } := ⟨ψ, sub.refl⟩

-- By GPT-5.2
def sub_finset {AP} [DecidableEq AP] : NNF AP → Finset (NNF AP)
| .atom p        => { .atom p }
| .not_atom p    => { .not_atom p }
| .next f        => insert (.next f) (sub_finset f)
| .and f g       => insert (.and f g) (sub_finset f ∪ sub_finset g)
| .or f g        => insert (.or f g) (sub_finset f ∪ sub_finset g)
| .until f g     => insert (.until f g) (sub_finset f ∪ sub_finset g)
| .release f g   => insert (.release f g) (sub_finset f ∪ sub_finset g)

lemma mem_sub_finset {AP} [DecidableEq AP] {q f : NNF AP} : q ≤ f → q ∈ sub_finset f := by
  intro h; induction h
  { cases q <;> grind [sub_finset] }
  all_goals grind [sub_finset]

-- By GPT-5.2
lemma sub_finite {AP} [DecidableEq AP] (f : NNF AP) : Finite { q // q ≤ f } := by
  refine Finite.of_injective (fun q => (⟨q.1, ?_⟩ : { r // r ∈ sub_finset f })) ?_
  · exact mem_sub_finset q.2
  · intro a b h; grind

end sub

def delta {AP} (φ : NNF AP) (σ : Letter AP) [DecidablePred (· ∈ σ)] : PositiveBool (NNF AP) :=
  match φ with
  | .atom p => if p ∈ σ then .true else .false
  | .not_atom p => if p ∈ σ then .false else .true
  | .and φ₁ φ₂ => (delta φ₁ σ).and (delta φ₂ σ)
  | .or φ₁ φ₂ => (delta φ₁ σ).or (delta φ₂ σ)
  | .next φ₁ => .atom φ₁
  | .until φ₁ φ₂ => (delta φ₂ σ).or ((delta φ₁ σ).and (.atom (.until φ₁ φ₂)))
  | .release φ₁ φ₂ => (delta φ₂ σ).and ((delta φ₁ σ).or (.atom (.release φ₁ φ₂)))

theorem delta_forall {AP} {φ : NNF AP} {σ : Letter AP} [DecidablePred (· ∈ σ)] : (delta φ σ).Forall (· ≤ φ) := by
  induction φ with
  | atom q => by_cases h : q ∈ σ <;> simp [PositiveBool.Forall, delta, h]
  | not_atom q => by_cases h : q ∈ σ <;> simp [PositiveBool.Forall, delta, h]
  | and f g f_ih g_ih => exact ⟨f_ih.imp (fun _ => sub.and_left), g_ih.imp (fun _ => sub.and_right)⟩
  | or f g f_ih g_ih => exact ⟨f_ih.imp (fun _ => sub.or_left), g_ih.imp (fun _ => sub.or_right)⟩
  | next f f_ih => exact sub.next sub.refl
  | «until» f g f_ih g_ih => exact ⟨g_ih.imp (fun _ => sub.until_right), f_ih.imp (fun _ => sub.until_left), sub.refl⟩
  | «release» f g f_ih g_ih => exact ⟨g_ih.imp (fun _ => sub.release_right), f_ih.imp (fun _ => sub.release_left), sub.refl⟩

open Classical in
noncomputable def NNF.toABW {AP} (ψ : NNF AP) : ABW (Letter AP) { x // x ≤ ψ } := {
  q₀ := ⟨ψ, sub.refl⟩
  δ φ σ := (delta φ σ).map_subtype (by classical apply PositiveBool.Forall.imp ?_ delta_forall; grind)
  F := { φ |
    match φ.val with
    | .release _ _ => True
    | _ => False
  }
}

lemma subformula_toABW_lang
  {S} {Φ φ : NNF S} (leφ : φ ≤ Φ)
  {w : ℕ → Letter S}
  {G : RunDAG Φ.toABW w} (G_acc : G.accepting)
  {k : ℕ} {q : Iic Φ} {Y : Set (Iic Φ)}
  (p_sat : PositiveBool.Sat Y (Φ.toABW.δ ⟨φ, leφ⟩ (w k)))
  (p_sub : {(q, k)} ×ˢ Y ⊆ G.E)
    : φ.toABW.language (fun j => w (j + k)) := by
  exists filter_dag.run_dag (M' := φ.toABW) leφ G q k
    (by
      simp [NNF.toABW]
      exists { q | q.embed_le leφ ∈ Y }
      constructor
      · let : DecidablePred (· ∈ w k) := by classical infer_instance
        simp [Subtype.embed_le]
        exact PositiveBool.map_subtype_restrict (delta_forall.imp (by grind)) delta_forall (by grind) p_sat
      · simp
        intros _ _ _
        apply p_sub
        grind
    )
    (by simp [NNF.toABW])
  intros p p_path
  have p_pres := filter_dag.preserves_path leφ G.toDAG q φ.toABW.q₀ _ p_path
  intros i
  obtain ⟨j, Hij, G_acc⟩ := G_acc _ p_pres (i + 1)
  exists j + 1, (by omega)

lemma and_mp.left {S} {φ₁ φ₂ : NNF S} {w} : (φ₁.and φ₂).toABW.language w → φ₁.toABW.language w := by
  simp [ABW.language]
  intros G G_acc
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ G.p_root
  apply subformula_toABW_lang (sub.and_left sub.refl) G_acc p_sat.left p_sub

lemma and_mp.right {S} {φ₁ φ₂ : NNF S} {w} : (φ₁.and φ₂).toABW.language w → φ₂.toABW.language w := by
  simp [ABW.language]
  intros G G_acc
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ G.p_root
  apply subformula_toABW_lang (sub.and_right sub.refl) G_acc p_sat.right p_sub

theorem and_mpr {AP : Type} {φ₁ φ₂ : NNF AP} {w : ℕ → Letter AP} (H1 : φ₁.toABW.language w) (H2 : φ₂.toABW.language w)
    : (φ₁.and φ₂).toABW.language w := by
  obtain ⟨G1, G1_acc⟩ := H1
  obtain ⟨G2, G2_acc⟩ := H2
  have : DecidableEq AP := by classical infer_instance
  exists conjoin_dag.run_dag
    (sub.and_left sub.refl) (sub.and_right sub.refl) G1 G2
    (by simp [NNF.toABW])
    (by simp [NNF.toABW])
    (by
      simp [NNF.toABW]
      intros
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      apply PositiveBool.Sat.and_union
      · rwa [←PositiveBool.sat_map_image (sub.and_left sub.refl) delta_forall]
      · rwa [←PositiveBool.sat_map_image (sub.and_right sub.refl) delta_forall]
    )
  intros op op_path
  rcases conjoin_dag.preserves_path _ _ _ _ _ _ _ _ op_path with ⟨k, p_path⟩|p_path
  · have : Nonempty { q // q ≤ φ₁ } := by infer_instance
    have G1_path := DAG.path_mapped G1.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G1_acc _ G1_path i
    exists (k + j), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (k + j)).val, DAG.path_elems_prop p_path j⟩, rfl⟩] at H
    exact H
  · have : Nonempty { q // q ≤ φ₂ } := by infer_instance
    have G2_path := DAG.path_mapped G2.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G2_acc _ G2_path i
    exists (j + 1), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (j + 1)).val, DAG.path_elems_prop p_path j⟩, rfl⟩] at H
    exact H

lemma or_mp {S} {φ₁ φ₂ : NNF S} {w} : (φ₁.or φ₂).toABW.language w → φ₁.toABW.language w ∨ φ₂.toABW.language w := by
  simp [NNF.toABW, ABW.language]
  intros G G_acc
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ G.p_root
  simp [PositiveBool.Sat, delta, PositiveBool.map_subtype] at p_sat
  rcases p_sat with p_sat|p_sat
  · left; apply subformula_toABW_lang (sub.or_left sub.refl) G_acc p_sat p_sub
  · right; apply subformula_toABW_lang (sub.or_right sub.refl) G_acc p_sat p_sub

namespace or_mpr

variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}

lemma left : φ₁.toABW.language w → (φ₁.or φ₂).toABW.language w := by
  rintro ⟨G, G_acc⟩
  exists replace_root.run_dag (sub.or_left sub.refl) G
    (by
      simp [NNF.toABW, PositiveBool.Sat, delta, PositiveBool.map_subtype]
      intros
      left
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      rw [←PositiveBool.sat_map_image (sub.or_left sub.refl) delta_forall]
      assumption
    )
    (by simp [NNF.toABW])
  intros _ p_path
  have p_path' := replace_root.preserves_path _ _ _ _ _ p_path
  specialize G_acc _ p_path'
  simp [NNF.toABW] at G_acc ⊢
  intros i
  specialize G_acc i
  grind

lemma right : φ₂.toABW.language w → (φ₁.or φ₂).toABW.language w := by
  rintro ⟨G, G_acc⟩
  exists replace_root.run_dag (sub.or_right sub.refl) G
    (by
      simp [NNF.toABW, PositiveBool.Sat, delta, PositiveBool.map_subtype]
      intros
      right
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      rw [←PositiveBool.sat_map_image (sub.or_right sub.refl) delta_forall]
      assumption
    )
    (by simp [NNF.toABW])
  intros _ p_path
  have p_path' := replace_root.preserves_path _ _ _ _ _ p_path
  specialize G_acc _ p_path'
  simp [NNF.toABW] at G_acc ⊢
  intros i
  specialize G_acc i
  grind

end or_mpr

lemma next_mp {AP : Type} {φ : NNF AP} {w} : φ.next.toABW.language w → φ.toABW.language (fun j => w (j + 1)) := by
  rintro ⟨G, G_acc⟩
  have in_1 : (⟨φ, sub.next sub.refl⟩, 1) ∈ G.V := by
    have := G.p_sat _ G.p_root
    simp [NNF.toABW, delta, PositiveBool.Sat, PositiveBool.map_subtype] at this
    rcases this with ⟨Y, p_sat, p_sub⟩
    have := G.edge_closure ((⟨φ.next, le_refl _⟩, 0), ⟨φ, sub.next sub.refl⟩)
    refine (this ?_).right
    apply p_sub
    grind
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ in_1
  apply subformula_toABW_lang (sub.next sub.refl) G_acc p_sat p_sub

lemma next_mpr {AP : Type} {φ : NNF AP} {w} : (φ.toABW.language fun j => w (j + 1)) → φ.next.toABW.language w := by
  intros H
  rcases H with ⟨G, G_acc⟩
  have : DecidableEq AP := by classical infer_instance
  exists shift_dag.run_dag (sub.next sub.refl) G
    (by simp [NNF.toABW, delta, PositiveBool.map_subtype, PositiveBool.Sat])
    (by simp [NNF.toABW])
  simp [RunDAG.accepting, shift_dag.run_dag, NNF.toABW] at G_acc ⊢
  intros p p_path i
  have p_path := shift_dag.preserves_path _ _ _ _ _ _ p_path
  specialize G_acc _ p_path i
  obtain ⟨j, G_acc⟩ := G_acc
  exists (j + 1)
  grind

lemma until_mp {S} {φ₁ φ₂ : NNF S} {w} (H : (φ₁.until φ₂).toABW.language w) : ∃ n, φ₂.toABW.language (fun j => w (j + n)) ∧ ∀ k < n, φ₁.toABW.language (fun j => w (j + k)) := by
  obtain ⟨G, G_acc⟩ := H
  by_contra never_φ₂
  simp at never_φ₂
  suffices root_forever : ∀ i, ((⟨φ₁.until φ₂, sub.refl⟩, i), ⟨φ₁.until φ₂, sub.refl⟩) ∈ G.E ∧ ∀ k ≤ i, φ₁.toABW.language (fun j => w (k + j)) by
    have p_path : G.path (fun _ => ⟨φ₁.until φ₂, sub.refl⟩) := by exists 0; grind
    obtain ⟨n, _, G_acc⟩ := G_acc _ p_path 0
    simp [NNF.toABW] at G_acc
  intros i; induction i
  · have := G.p_sat _ G.p_root
    simp [NNF.toABW] at this
    obtain ⟨Y, p_sat, p_sub⟩ := this
    simp [delta, PositiveBool.map_subtype, PositiveBool.Sat] at p_sat
    rcases p_sat with p_sat|⟨p_sat, inY⟩
    · suffices φ₂.toABW.language (fun j => w j) by exfalso; specialize never_φ₂ 0; grind
      apply subformula_toABW_lang (sub.until_right sub.refl) G_acc p_sat p_sub
    · rw [Set.subset_def] at p_sub
      constructor
      · exact p_sub ((⟨φ₁.until φ₂, sub.refl⟩, 0), ⟨φ₁.until φ₂, sub.refl⟩) (by grind)
      · intros k hk; simp at hk; subst hk
        simp
        apply subformula_toABW_lang (sub.until_left sub.refl) G_acc p_sat p_sub
  next i ih =>
    rcases ih with ⟨root_edge, sat_φ₁⟩
    obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ (G.edge_closure _ root_edge).right
    simp [NNF.toABW, delta, PositiveBool.map_subtype, PositiveBool.Sat] at p_sat
    rcases p_sat with p_sat|⟨p_sat, inY⟩
    · suffices φ₂.toABW.language (fun j => w (j + (i + 1))) by
        exfalso
        specialize never_φ₂ (i + 1) this
        grind
      apply subformula_toABW_lang (sub.until_right sub.refl) G_acc p_sat p_sub
    · rw [Set.subset_def] at p_sub
      constructor
      · exact p_sub ((⟨φ₁.until φ₂, sub.refl⟩, i + 1), ⟨φ₁.until φ₂, sub.refl⟩) (by grind)
      · intros k hk
        by_cases k_eq : k = i + 1
        · subst k_eq
          conv => right; intro j; right; rw [Nat.add_comm]
          apply subformula_toABW_lang (sub.until_left sub.refl) G_acc p_sat p_sub
        · exact sat_φ₁ k (by omega)

lemma until_mpr.base
  {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
  (h2 : φ₂.toABW.language w)
    : (φ₁.until φ₂).toABW.language w := by
  simp [NNF.toABW, ABW.language]
  obtain ⟨G, G_acc⟩ := h2
  exists
    replace_root.run_dag (sub.until_right sub.refl) G
    (by
      simp [PositiveBool.Sat, delta, PositiveBool.map_subtype]
      intros
      left
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      rw [←PositiveBool.sat_map_image (sub.until_right sub.refl) delta_forall]
      assumption
    )
    (by simp [NNF.toABW])
  simp [RunDAG.accepting] at G_acc ⊢
  intros p p_path
  have p_path' := replace_root.preserves_path _ _ _ _ _ p_path
  specialize G_acc _ p_path'
  simp [NNF.toABW] at G_acc
  intros i
  specialize G_acc i
  grind

lemma until_mpr.next
  {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
  (h1 : φ₁.toABW.language w)
  (h2 : (φ₁.until φ₂).toABW.language (fun j => w (j + 1)))
    : (φ₁.until φ₂).toABW.language w := by
  obtain ⟨G₁, G₁_acc⟩ := h1
  obtain ⟨G₂, G₂_acc⟩ := h2
  exists shift_conjoin_dag.run_dag (sub.until_left sub.refl) G₁ G₂
    (by simp [NNF.toABW])
    (by
      simp [NNF.toABW, delta, PositiveBool.map_subtype, PositiveBool.Sat]
      intros Y hsat
      right
      apply PositiveBool.Sat.monotone (show Subtype.embed_le (sub.until_left sub.refl) '' Y ⊆ _ by grind)
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      rwa [←PositiveBool.sat_map_image _ delta_forall]
    )
  intros op op_path
  rcases conjoin_dag.preserves_path _ _ _ _ _ _ _ _ op_path with ⟨k, p_path⟩|p_path
  · have : Nonempty { q // q ≤ φ₁ } := by infer_instance
    have G₁_path := DAG.path_mapped G₁.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G₁_acc _ G₁_path i
    exists (k + j), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (k + j)).val, DAG.path_elems_prop p_path j⟩, rfl⟩] at H
    exact H
  · have Gs_path := DAG.path_mapped _ _ subtype_val_injective _ p_path
    have p_path := shift_dag.preserves_path _ _ _ _ _ _ Gs_path
    intros i
    have ⟨j, Hj, H⟩ := G₂_acc _ p_path i
    exists (j + 1 + 1), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (j + 1 + 1)).val, _⟩, rfl⟩] at H
    exact H

namespace release_mp

variable {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S} {G : RunDAG (φ₁.release φ₂).toABW w}

lemma right (G_acc : G.accepting) {l} (H : (⟨φ₁.release φ₂, le_refl _⟩, l) ∈ G.V) : φ₂.toABW.language (fun j => w (j + l)) := by
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ H
  apply subformula_toABW_lang (sub.release_right sub.refl) G_acc p_sat.left p_sub

lemma left (G_acc : G.accepting) {l} (H₁ : (⟨φ₁.release φ₂, le_refl _⟩, l) ∈ G.V) (H₂ : (⟨φ₁.release φ₂, le_refl _⟩, l + 1) ∉ G.V) : φ₁.toABW.language (fun j => w (j + l)) := by
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ H₁
  rcases p_sat with ⟨_, p_sat|p_sat⟩
  · apply subformula_toABW_lang (sub.release_left sub.refl) G_acc p_sat p_sub
  · exfalso
    have := G.edge_closure
    simp [PositiveBool.map_subtype, PositiveBool.Sat] at p_sat
    have : ((⟨φ₁.release φ₂, le_refl _⟩, l), ⟨φ₁.release φ₂, le_refl _⟩) ∈ G.E := by grind
    grind

end release_mp

namespace release_mpr

variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}

omit [DecidableEq S] in
lemma always
  (hg : ∀ i, φ₂.toABW.language (fun j => w (j + i)))
    : (φ₁.release φ₂).toABW.language w := by
  simp [ABW.language] at *
  let G : ∀ i, RunDAG φ₂.toABW (fun j => w (j + i)) := fun i => (hg i).choose
  exists always_dag.run_dag
    (by
      simp [LT.lt]
      have h : φ₂ ≤ φ₁.release φ₂ := sub.release_right sub.refl
      exists h
      intro H
      have := PartialOrder.le_antisymm _ _ h H
      cases this
    )
    G rfl rfl
    (by
      intros Y l p_sat
      simp [NNF.toABW, delta, PositiveBool.Sat, PositiveBool.map_subtype] at p_sat ⊢
      apply PositiveBool.Sat.monotone (Set.subset_insert _ _)
      apply PositiveBool.map_subtype_contract p_sat
      grind
    )
    (by simp [NNF.toABW])
  intros op op_path
  rcases always_dag.preserves_path _ _ _ op_path with rfl|⟨i, k, p_path⟩
  · simp [NNF.toABW]; intros i; exists i
  · have Gi_path := DAG.path_mapped (G i).toDAG _ subtype_val_injective _ p_path
    intros l
    have ⟨j, Hj, H⟩ := (hg i).choose_spec _ Gi_path l
    exists (k + j), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (k + j)).val, DAG.path_elems_prop p_path j⟩, rfl⟩] at H
    exact H

-- By Claude 4.5 Opus
lemma base
  (h1 : φ₁.toABW.language w)
  (h2 : φ₂.toABW.language w)
    : (φ₁.release φ₂).toABW.language w := by
  obtain ⟨G₁, G₁_acc⟩ := h1
  obtain ⟨G₂, G₂_acc⟩ := h2
  exists conjoin_dag.run_dag
    (sub.release_left sub.refl) (sub.release_right sub.refl) G₁ G₂
    (by simp [NNF.toABW])
    (by simp [NNF.toABW])
    (by
      simp [NNF.toABW]
      intros Y₁ Y₂ hsat₁ hsat₂
      constructor
      · apply PositiveBool.Sat.monotone (show Subtype.embed_le (sub.release_right sub.refl) '' Y₂ ⊆ _ by grind)
        let : DecidablePred (· ∈ w 0) := by classical infer_instance
        rwa [←PositiveBool.sat_map_image _ delta_forall]
      · left
        apply PositiveBool.Sat.monotone (show Subtype.embed_le (sub.release_left sub.refl) '' Y₁ ⊆ _ by grind)
        let : DecidablePred (· ∈ w 0) := by classical infer_instance
        rwa [←PositiveBool.sat_map_image _ delta_forall]
    )
  simp [RunDAG.accepting] at G₁_acc G₂_acc ⊢
  intros op op_path
  rcases conjoin_dag.preserves_path _ _ _ _ _ _ _ _ op_path with ⟨k, p_path⟩|p_path
  · have G₁_path := DAG.path_mapped G₁.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G₁_acc _ G₁_path i
    exists (k + j), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (k + j)).val, DAG.path_elems_prop p_path j⟩, rfl⟩] at H
    exact H
  · have : Nonempty { q // q ≤ φ₂ } := by infer_instance
    have G₂_path := DAG.path_mapped G₂.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G₂_acc _ G₂_path i
    exists (j + 1), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (j + 1)).val, DAG.path_elems_prop p_path j⟩, rfl⟩] at H
    exact H

-- By Claude 4.5 Opus
lemma next
  (h2 : φ₂.toABW.language w)
  (h3 : (φ₁.release φ₂).toABW.language (fun j => w (j + 1)))
    : (φ₁.release φ₂).toABW.language w := by
  obtain ⟨G₂, G₂_acc⟩ := h2
  obtain ⟨G₃, G₃_acc⟩ := h3
  exists shift_conjoin_dag.run_dag (sub.release_right sub.refl) G₂ G₃
    (by simp [NNF.toABW])
    (by
      simp only [NNF.toABW, delta, PositiveBool.map_subtype, PositiveBool.Sat]
      intros Y hsat
      -- Goal: delta_g AND (delta_f OR atom_release)
      -- We satisfy delta_g from Y, and take atom_release branch
      constructor
      · apply PositiveBool.Sat.monotone (show Subtype.embed_le (sub.release_right sub.refl) '' Y ⊆ _ by grind)
        let : DecidablePred (· ∈ w 0) := by classical infer_instance
        rwa [←PositiveBool.sat_map_image _ delta_forall]
      · right
        simp
    )
  intros op op_path
  rcases conjoin_dag.preserves_path _ _ _ _ _ _ _ _ op_path with ⟨k, p_path⟩|p_path
  · have G₂_path := DAG.path_mapped G₂.toDAG _ subtype_val_injective _ p_path
    intros i
    have ⟨j, Hj, H⟩ := G₂_acc _ G₂_path i
    exists (k + j), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (k + j)).val, DAG.path_elems_prop p_path j⟩, rfl⟩] at H
    exact H
  · have Gs_path := DAG.path_mapped _ _ subtype_val_injective _ p_path
    have p_path := shift_dag.preserves_path _ _ _ _ _ _ Gs_path
    intros i
    have ⟨j, Hj, H⟩ := G₃_acc _ p_path i
    exists (j + 1 + 1), (by omega)
    simp [NNF.toABW] at H ⊢
    rw [Function.invFun_eq (f := Subtype.val) ⟨⟨(op (j + 1 + 1)).val, _⟩, rfl⟩] at H
    exact H

end release_mpr

theorem NNF.toABW_lang {AP} (ψ : NNF AP) : ψ.toABW.language = ψ.language := by
  have : DecidableEq AP := by classical infer_instance
  induction ψ

  -- atom
  next p =>
    simp [NNF.language]
    funext w; apply propext
    constructor
    · simp [ABW.language, RunDAG.accepting]
      intros G G_acc
      by_contra hc
      obtain ⟨Y, p_sat⟩ := G.p_sat _ G.p_root
      simp [NNF.toABW, delta, hc, PositiveBool.map_subtype, PositiveBool.Sat] at p_sat
    · intros H
      let G : RunDAG (NNF.atom p).toABW w := {
        V := { (⟨.atom p, sub.refl⟩, 0) }
        E := ∅
        p_root := by rfl
        p_sat := by simp; simp [NNF.toABW, delta, H]; constructor
        edge_closure := by simp
      }
      exists G
      simp [RunDAG.accepting, DAG.path]
      intros _ _ he _
      simp [G] at he

  -- not_atom
  next p =>
    simp [NNF.language]
    funext w; apply propext
    constructor
    · simp [ABW.language, RunDAG.accepting]
      intros G G_acc
      by_contra hc
      obtain ⟨Y, p_sat⟩ := G.p_sat _ G.p_root
      simp [NNF.toABW, delta, hc, PositiveBool.map_subtype, PositiveBool.Sat] at p_sat
    · intros H
      let G : RunDAG (NNF.not_atom p).toABW w := {
        V := { (⟨.not_atom p, sub.refl⟩, 0) }
        E := ∅
        p_root := by rfl
        p_sat := by simp; simp [NNF.toABW, delta, H]; constructor
        edge_closure := by simp
      }
      exists G
      simp [RunDAG.accepting, DAG.path]
      intros _ _ he _
      simp [G] at he

  -- and
  next f g f_ih g_ih =>
    funext w; simp [NNF.language]
    rw [←f_ih, ←g_ih]; clear f_ih g_ih
    constructor
    · intros H
      exact ⟨and_mp.left H, and_mp.right H⟩
    · rintro ⟨H1, H2⟩
      exact and_mpr H1 H2

  -- or
  next f g f_ih g_ih =>
    funext w; simp [NNF.language]
    rw [←f_ih, ←g_ih]; clear f_ih g_ih
    constructor
    · exact or_mp
    · rintro (H|H)
      · exact or_mpr.left H
      · exact or_mpr.right H

  -- next
  next f f_ih =>
    funext w; simp [NNF.language]
    rw [←f_ih]; clear f_ih
    exact ⟨next_mp, next_mpr⟩

  -- until
  next f g f_ih g_ih =>
    funext w; apply propext
    rw [until_expand_repeat]
    constructor
    · intros H
      obtain ⟨n, h1, h2⟩ := until_mp H
      clear H
      exists n
      revert w
      induction n
      · simp [NNF.repeat_and_next]; rw [←g_ih]; grind
      next n ih =>
        intros w h1 h2
        simp [NNF.repeat_and_next, NNF.language]
        constructor
        · rw [←f_ih]
          exact h2 0 (by omega)
        · apply ih
          · exact h1
          · intros k hk
            exact h2 (k + 1) (by omega)
    · intros H
      obtain ⟨n, H⟩ := H
      revert w
      induction n
      · intros w H
        simp [NNF.repeat_and_next] at H
        rw [←g_ih] at H
        exact until_mpr.base H
      next n ih =>
        intros w H
        simp [NNF.repeat_and_next, NNF.language] at H
        rcases H with ⟨lf, H⟩
        specialize ih (fun j => w (j + 1)) H
        rw [←f_ih] at lf
        exact until_mpr.next lf ih

  -- release
  next f g f_ih g_ih =>
    funext w; apply propext
    constructor
    · intros H
      simp [NNF.language]
      obtain ⟨G, G_acc⟩ := H
      rw [←f_ih, ←g_ih]; clear f_ih g_ih
      by_cases ha : ∃ l, (∀ l' ≤ l, (⟨f.release g, le_refl _⟩, l') ∈ G.V) ∧ (⟨f.release g, le_refl _⟩, l + 1) ∉ G.V
      · rcases ha with ⟨l, h1, h2⟩
        intros i
        by_cases i ≤ l
        · left
          specialize h1 i (by omega)
          exact release_mp.right G_acc h1
        · right
          exists l, (by omega)
          specialize h1 l (by omega)
          exact release_mp.left G_acc h1 h2
      · simp at ha
        have ha : ∀ l, (⟨f.release g, le_refl _⟩, l) ∈ G.V := by
          suffices ∀ l, ∀ l' ≤ l, (⟨f.release g, le_refl _⟩, l') ∈ G.V by
            intros l; specialize this l; grind
          intros l
          induction l
          next => intros _ h; simp at h; subst h; exact G.p_root
          next l ih =>
            specialize ha _ ih
            grind
        intros i
        left
        specialize ha i
        exact release_mp.right G_acc ha
    · intros H
      by_cases hAlways : ∀ i, g.language (fun j => w (j + i))
      · apply release_mpr.always
        rw [g_ih]
        exact hAlways
      · simp at hAlways
        obtain ⟨n, hgn⟩ := hAlways
        revert w
        induction n
        · intros w H hgn
          specialize H 0
          simp at H
          contradiction
        next n ih =>
          intros w H hgn
          rw [release_expand] at H
          rcases H with ⟨lg, lf | H⟩
          · rw [←f_ih] at lf
            rw [←g_ih] at lg
            exact release_mpr.base lf lg
          · rw [←g_ih] at lg
            apply release_mpr.next lg
            apply ih (fun j => w (j + 1)) H hgn

theorem exists_ABW_lang_for_LTL {AP} (f : LTL AP) : ∃ (Q : Type) (_ : Finite Q) (A : ABW (Letter AP) Q), f.language = A.language := by
  obtain ⟨nnf, eqv⟩ := f.exists_equiv_nnf
  have q_fin : Finite { q // q ≤ nnf } := by classical apply sub_finite
  exists _, q_fin, nnf.toABW
  rw [eqv, NNF.toABW_lang]
