/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import LeanPool.UlmsTheorem.Ulm.Extension

/-!
# Classification machinery for countable reduced abelian p-groups

This module contains the hard-direction interface for Ulm's theorem:
the back-and-forth construction on finite partial isomorphisms and the final
isomorphism-from-invariants statement.
-/

namespace UlmsTheorem

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]


/-!
## Isomorphism-from-equivalences back-and-forth assembly

`BFIsoStep` is a finite stage carrying an actual `AddEquiv` (rather than a plain hom).
The chain construction below proves `iso_of_ulmInvariant_eq_of_backAndForth`:
given abstract `hforth`/`hback` hypotheses that supply `BFIsoStep` extensions,
the colimit is an isomorphism.  `kaplansky_extend` supplies the concrete forth
hypothesis, and applying it to the inverse stage supplies the back hypothesis.
-/

/-- A finite stage carrying a true partial isomorphism. -/
abbrev BFIsoStep := UlmStage p (G := G) (H := H)

/-- Policy for extending a finite stage so that it covers a chosen source element. -/
private abbrev BFForthPolicy :=
  ∀ s : BFIsoStep p (G := G) (H := H), ∀ g : G,
    ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a

/-- Policy for extending a finite stage so that it covers a chosen target element. -/
private abbrev BFBackPolicy :=
  ∀ s : BFIsoStep p (G := G) (H := H), ∀ h : H,
    ∃ (s' : BFIsoStep p (G := G) (H := H)) (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧ ∀ a : s.A, (s'.e ⟨a.val, hAA a.prop⟩ : H) = s.e a

/-- The initial empty stage. -/
private def BFIsoStep.init : BFIsoStep p (G := G) (H := H) where
  A    := ⊥
  B    := ⊥
  hAfinite := by
    rw [show ((⊥ : AddSubgroup G) : Set G) = {0} by ext; simp]
    exact Set.finite_singleton 0
  hBfinite := by
    rw [show ((⊥ : AddSubgroup H) : Set H) = {0} by ext; simp]
    exact Set.finite_singleton 0
  e    := {
    toFun    := fun a ↦ ⟨0, AddSubgroup.zero_mem _⟩
    invFun   := fun b ↦ ⟨0, AddSubgroup.zero_mem _⟩
    left_inv := fun a ↦ Subtype.ext (by simp [AddSubgroup.mem_bot.mp a.prop])
    right_inv:= fun b ↦ Subtype.ext (by simp [AddSubgroup.mem_bot.mp b.prop])
    map_add' := fun a b ↦ by
      simp }
  hφ   := by
    intro a α
    have ha : (a : G) = 0 := AddSubgroup.mem_bot.mp a.prop
    constructor <;> intro h <;> simp [ha]

omit hp in
/-- Combine one forth step and one back step into a single chain step. -/
private lemma bf_forth_back
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (s : BFIsoStep p (G := G) (H := H)) (g : G) (h : H) :
    ∃ (s' : BFIsoStep p (G := G) (H := H)) (hle : s.A ≤ s'.A),
      s.B ≤ s'.B ∧ g ∈ s'.A ∧ h ∈ s'.B ∧
      ∀ a : s.A, (s'.e ⟨a.val, hle a.prop⟩ : H) = s.e a := by
  obtain ⟨s₁, h₁, h₂, hg₁, h₃⟩ := hforth s g
  obtain ⟨s₂, h₄, h₅, hh₂, h₆⟩ := hback s₁ h
  exact ⟨s₂, h₁.trans h₄, h₂.trans h₅, h₄ hg₁, hh₂,
         fun a ↦ by simpa [h₃ a] using h₆ ⟨a, h₁ a.2⟩⟩

/-- The ℕ-indexed chain of `BFIsoStep`s, covering one element of G and H at each stage. -/
private noncomputable def bf_chain
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) : ℕ → BFIsoStep p (G := G) (H := H)
  | 0     => BFIsoStep.init p
  | n + 1 => (bf_forth_back p hforth hback
                (bf_chain hforth hback enumG enumH n) (enumG n) (enumH n)).choose

omit hp in
/-- Key monotonicity and coverage properties of consecutive chain steps. -/
private lemma bf_chain_step_props
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) (n : ℕ) :
    let c := bf_chain p hforth hback enumG enumH
    ∃ (hle : (c n).A ≤ (c (n+1)).A),
      (c n).B ≤ (c (n+1)).B ∧ enumG n ∈ (c (n+1)).A ∧ enumH n ∈ (c (n+1)).B ∧
      ∀ a : (c n).A, ((c (n+1)).e ⟨a.val, hle a.prop⟩ : H) = (c n).e a :=
  (bf_forth_back p hforth hback
    (bf_chain p hforth hback enumG enumH n) (enumG n) (enumH n)).choose_spec

omit hp in
/-- The A-subgroups of the chain are monotone. -/
private lemma bf_chain_A_le
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) {m n : ℕ} (hmn : m ≤ n) :
    (bf_chain p hforth hback enumG enumH m).A ≤
      (bf_chain p hforth hback enumG enumH n).A := by
  induction n with
  | zero => aesop
  | succ n ih =>
    obtain rfl | hmn := hmn.eq_or_lt
    · rfl
    · obtain ⟨hle, _, _, _, _⟩ := bf_chain_step_props p hforth hback enumG enumH n
      exact le_trans (ih (Nat.le_of_lt_succ hmn)) hle

omit hp in
/-- The partial isomorphisms are compatible across chain stages. -/
private lemma bf_chain_compat
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) {m n : ℕ} (hmn : m ≤ n)
    (a : (bf_chain p hforth hback enumG enumH m).A) :
    ((bf_chain p hforth hback enumG enumH n).e
      ⟨a.val, bf_chain_A_le p hforth hback enumG enumH hmn a.prop⟩ : H) =
    (bf_chain p hforth hback enumG enumH m).e a := by
  induction hmn with
  | refl => rfl
  | @step n hmn ih =>
    obtain ⟨hle, _, _, _, h⟩ := bf_chain_step_props p hforth hback enumG enumH n
    exact h ⟨a, bf_chain_A_le p hforth hback enumG enumH hmn a.2⟩ ▸ ih

omit hp in
/-- The B-subgroups of the chain are monotone. -/
private lemma bf_chain_B_le
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (enumH : ℕ → H) {m n : ℕ} (hmn : m ≤ n) :
    (bf_chain p hforth hback enumG enumH m).B ≤
      (bf_chain p hforth hback enumG enumH n).B := by
  induction hmn with
  | refl => rfl
  | @step n _ ih =>
    exact le_trans ih (by have := bf_chain_step_props p hforth hback enumG enumH n; tauto)

/-- The limit map: send g to its image under the first chain stage that covers it. -/
private noncomputable def bf_limit_map
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H) (g : G) : H :=
  let n     := (hG_surj g).choose
  let c     := bf_chain p hforth hback enumG enumH
  let props := bf_chain_step_props p hforth hback enumG enumH n
  c (n + 1) |>.e ⟨g, by rw [← (hG_surj g).choose_spec]; exact props.choose_spec.2.1⟩

omit hp in
/-- The limit map evaluates consistently at any stage that already covers g. -/
private lemma bf_limit_map_eq_at
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H)
    (g : G) (n : ℕ) (hg : g ∈ (bf_chain p hforth hback enumG enumH n).A) :
    bf_limit_map p hforth hback enumG hG_surj enumH g =
      ((bf_chain p hforth hback enumG enumH n).e ⟨g, hg⟩ : H) := by
  by_cases h : n ≤ (hG_surj g).choose + 1
  · have := bf_chain_compat p hforth hback enumG enumH h ⟨g, hg⟩; aesop
  · have hle : (hG_surj g).choose + 1 ≤ n := by omega
    have hgbase := (bf_chain_step_props (G := G) (H := H) p hforth hback enumG enumH
      (hG_surj g).choose).choose_spec.2.1
    rw [(hG_surj g).choose_spec] at hgbase
    have hcompat := bf_chain_compat p hforth hback enumG enumH hle ⟨g, hgbase⟩
    unfold bf_limit_map
    exact hcompat.symm

omit hp in
/-- The limit map is additive. -/
private lemma bf_limit_map_add
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H)
    (g₁ g₂ : G) :
    bf_limit_map p hforth hback enumG hG_surj enumH (g₁ + g₂) =
    bf_limit_map p hforth hback enumG hG_surj enumH g₁ +
    bf_limit_map p hforth hback enumG hG_surj enumH g₂ := by
  obtain ⟨n₁, hn₁⟩ := hG_surj g₁
  obtain ⟨n₂, hn₂⟩ := hG_surj g₂
  set N := Nat.max (n₁ + 1) (n₂ + 1)
  have hg₁ : g₁ ∈ (bf_chain p hforth hback enumG enumH N).A := by
    have hg₁' : g₁ ∈ (bf_chain p hforth hback enumG enumH (n₁ + 1)).A := by
      have := bf_chain_step_props p hforth hback enumG enumH n₁; grind +ring
    exact bf_chain_A_le p hforth hback enumG enumH (Nat.le_max_left _ _) hg₁'
  have hg₂ : g₂ ∈ (bf_chain p hforth hback enumG enumH N).A := by
    have := bf_chain_step_props p hforth hback enumG enumH n₂
    have henum := this.2.2.1
    rw [hn₂] at henum
    exact bf_chain_A_le p hforth hback enumG enumH
      (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)))
      henum
  have hg₁g₂ : g₁ + g₂ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    AddSubgroup.add_mem _ hg₁ hg₂
  set eN := (bf_chain p hforth hback enumG enumH N).e
  rw [bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₁ N hg₁,
      bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₂ N hg₂,
      bf_limit_map_eq_at p hforth hback enumG hG_surj enumH (g₁ + g₂) N hg₁g₂]
  exact eN.map_add ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ ▸ rfl

omit hp in
/-- The limit map is injective. -/
private lemma bf_limit_map_injective
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG) (enumH : ℕ → H) :
    Function.Injective (bf_limit_map p hforth hback enumG hG_surj enumH) := by
  intro g₁ g₂ h_eq
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, g₁ ∈ (bf_chain p hforth hback enumG enumH (n₁ + 1)).A := by
    obtain ⟨n₁, hn₁⟩ := hG_surj g₁
    exact ⟨n₁, by have := bf_chain_step_props p hforth hback enumG enumH n₁; aesop⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n₂, g₂ ∈ (bf_chain p hforth hback enumG enumH (n₂ + 1)).A := by
    obtain ⟨n₂, rfl⟩ := hG_surj g₂
    exact ⟨n₂, (bf_chain_step_props p hforth hback enumG enumH n₂).choose_spec.2.1⟩
  set N := max n₁ n₂ + 1
  have hN₁ : g₁ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    bf_chain_A_le p hforth hback enumG enumH (by omega) hn₁
  have hN₂ : g₂ ∈ (bf_chain p hforth hback enumG enumH N).A :=
    bf_chain_A_le p hforth hback enumG enumH (Nat.succ_le_succ (le_max_right _ _)) hn₂
  have h_eq_N :
      ((bf_chain p hforth hback enumG enumH N).e ⟨g₁, hN₁⟩ : H) =
      ((bf_chain p hforth hback enumG enumH N).e ⟨g₂, hN₂⟩ : H) := by
    rw [← bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₁ N hN₁,
        ← bf_limit_map_eq_at p hforth hback enumG hG_surj enumH g₂ N hN₂, h_eq]
  exact congrArg Subtype.val
    ((bf_chain p hforth hback enumG enumH N).e.injective (Subtype.ext h_eq_N))

omit hp in
/-- The limit map is surjective. -/
private lemma bf_limit_map_surjective
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H))
    (enumG : ℕ → G) (hG_surj : Function.Surjective enumG)
    (enumH : ℕ → H) (hH_surj : Function.Surjective enumH) :
    Function.Surjective (bf_limit_map p hforth hback enumG hG_surj enumH) := by
  intro h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, h ∈ (bf_chain p hforth hback enumG enumH n).B := by
    obtain ⟨n, rfl⟩ := hH_surj h
    exact ⟨n + 1, by
      simpa using (bf_chain_step_props p hforth hback enumG enumH n).choose_spec.2.2.1⟩
  let a := (bf_chain p hforth hback enumG enumH n).e.symm ⟨h, hn⟩
  use a.val
  have ha : (bf_chain p hforth hback enumG enumH n).e a = ⟨h, hn⟩ := by simp [a]
  rw [bf_limit_map_eq_at p hforth hback enumG hG_surj enumH a.val n a.prop]
  exact congrArg Subtype.val ha

omit hp in
/-- Back-and-forth assembly: abstract `hforth`/`hback` hypotheses for `BFIsoStep`
imply the two groups are isomorphic.  Proved in full; no open obligation within. -/
lemma iso_of_ulmInvariant_eq_of_backAndForth
    [Countable G] [Countable H]
    (hforth : BFForthPolicy p (G := G) (H := H))
    (hback : BFBackPolicy p (G := G) (H := H)) :
    Nonempty (G ≃+ H) := by
  obtain ⟨enumG, hG_surj⟩ := exists_surjective_nat G
  obtain ⟨enumH, hH_surj⟩ := exists_surjective_nat H
  have h_bij : Function.Bijective (bf_limit_map p hforth hback enumG hG_surj enumH) :=
    ⟨bf_limit_map_injective p hforth hback enumG hG_surj enumH,
     bf_limit_map_surjective p hforth hback enumG hG_surj enumH hH_surj⟩
  exact ⟨{ Equiv.ofBijective _ h_bij with
             map_add' := fun x y ↦ by
               simpa using bf_limit_map_add p hforth hback enumG hG_surj enumH x y }⟩

/-- The back extension obtained by applying Kaplansky's extension lemma to the
inverse finite partial isomorphism. -/
private lemma kaplansky_extend_back
    (hH : IsReducedPGroup p H)
    (hinv : ∀ β : Ordinal.{0},
      ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : BFIsoStep p (G := G) (H := H)) (h : H) :
    ∃ (s' : BFIsoStep p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      h ∈ s'.B ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  obtain ⟨t, hBB, hAA, hh, hcomp⟩ :=
    kaplansky_extend (p := p) hH (fun β ↦ (hinv β).symm) s.symm h
  refine ⟨t.symm, hAA, hBB, hh, ?_⟩
  intro a
  have ht :
      t.e ⟨s.e a, hBB (s.e a).prop⟩ = ⟨a, hAA a.prop⟩ := by
    apply Subtype.ext
    have hc := hcomp (s.e a)
    change (t.e ⟨s.e a, hBB (s.e a).prop⟩ : G) =
      (s.e.symm (s.e a) : G) at hc
    exact hc.trans (congrArg Subtype.val (s.e.symm_apply_apply a))
  have hsymm := congrArg t.e.symm ht
  have hvals :
      (s.e a : H) = (t.e.symm ⟨a, hAA a.prop⟩ : H) := by
    simpa using congrArg Subtype.val hsymm
  exact hvals.symm

/-- Hard direction of Ulm's theorem: equal Ulm invariants imply isomorphism,
using the proved Kaplansky finite-stage extension in both directions. -/
lemma iso_of_ulmInvariant_eq
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G)
    (hH : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by
  apply iso_of_ulmInvariant_eq_of_backAndForth (p := p)
  · exact fun s g ↦ kaplansky_extend (p := p) hG hinv s g
  · exact fun s h ↦ kaplansky_extend_back (p := p) hH hinv s h

end UlmsTheorem
