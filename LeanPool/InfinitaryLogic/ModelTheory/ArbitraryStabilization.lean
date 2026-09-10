/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import LeanPool.InfinitaryLogic.Scott.Sentence
/-!
# Arbitrary-target stabilization (issue #17 chunk 5.1)

The kernel of the Scott completion, and the point of contact between #13 and #17: the existing
stabilization theory (`StabilizesCompletely`, from the proved countable refinement hypothesis)
upgrades `BFEquiv α → BFEquiv (succ α)` only against COUNTABLE targets. This file extends it to
ARBITRARY targets using the fragment Löwenheim–Skolem machinery:

for each required extension, take a countable A-elementary substructure of the arbitrary
target containing the current tuple (and, in the back direction, the requested new element),
where the controlling fragment contains the CLOSED level-`α` Scott formulas of all finite
tuples of the countable source (`scottSeed` — countably many, since the source is countable;
closing is `relabel Sum.inr`, with `realize_relabel_sumInr` as the bridge). A-elementarity
transfers Scott-formula realization between the target and the substructure, where the
countable-target stabilization supplies the witness.

The generic extension-family bridge (`bfEquiv_all_of_extensionFamily`, the two-structure form
of the audited thin bridge) then upgrades stabilized `BFEquiv α` to EVERY ordinal
(`bfEquiv_all_of_stabilizesCompletely_arbitrary`).
-/

namespace FirstOrder

namespace Language

open Lomega1omega

universe u v w

variable {L : Language.{u, v}}

/-! ## The generic extension-family bridge (two arbitrary structures) -/

/-- The two-structure form of the audited thin bridge: any tuple relation with atomic
agreement and the forth/back extensions is `BFEquiv` at every ordinal. -/
theorem bfEquiv_all_of_extensionFamily {M' N' : Type w} [L.Structure M'] [L.Structure N']
    (R : ∀ n : ℕ, (Fin n → M') → (Fin n → N') → Prop)
    (hzero : ∀ {n : ℕ} {a : Fin n → M'} {b : Fin n → N'}, R n a b →
      SameAtomicType (L := L) (M := M') (N := N') a b)
    (hforth : ∀ {n : ℕ} {a : Fin n → M'} {b : Fin n → N'}, R n a b →
      ∀ a' : M', ∃ b' : N', R (n + 1) (Fin.snoc a a') (Fin.snoc b b'))
    (hback : ∀ {n : ℕ} {a : Fin n → M'} {b : Fin n → N'}, R n a b →
      ∀ b' : N', ∃ a' : M', R (n + 1) (Fin.snoc a a') (Fin.snoc b b'))
    (α : Ordinal) :
    ∀ {n : ℕ} (a : Fin n → M') (b : Fin n → N'), R n a b → BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro n a b hab
    rw [BFEquiv.zero]
    exact hzero hab
  | add_one β ih =>
    intro n a b hab
    rw [show (β + 1 : Ordinal) = Order.succ β from (Order.succ_eq_add_one β).symm,
      BFEquiv.succ]
    refine ⟨ih a b hab, fun m => ?_, fun b' => ?_⟩
    · obtain ⟨b', hb'⟩ := hforth hab m
      exact ⟨b', ih _ _ hb'⟩
    · obtain ⟨a', ha'⟩ := hback hab b'
      exact ⟨a', ih _ _ ha'⟩
  | limit β hβ ih =>
    intro n a b hab
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ a b hab

/-! ## The closed Scott seed and its fragment -/

variable [L.IsRelational] [Countable (Σ l, L.Relations l)]
variable {N : Type w} [L.Structure N] [Countable N]

/-- The closed level-`α` Scott formulas of all finite tuples of the countable source. -/
private noncomputable def scottSeed (N : Type w) [L.Structure N] [Countable N] (α : Ordinal) :
    Set (Σ n, L.BoundedFormulaω Empty n) :=
  ⋃ m : ℕ, (fun a : Fin m → N =>
    (⟨m, (scottFormula (L := L) a α).relabel (Sum.inr : Fin m → Empty ⊕ Fin m)⟩ :
      Σ n, L.BoundedFormulaω Empty n)) '' Set.univ

omit [L.IsRelational] in
private theorem scottSeed_countable (α : Ordinal) : (scottSeed (L := L) N α).Countable :=
  Set.countable_iUnion fun _ => Set.countable_univ.image _

/-- The controlling fragment for arbitrary-target stabilization. -/
private noncomputable def scottFragment (N : Type w) [L.Structure N] [Countable N] (α : Ordinal) :
    Fragment L :=
  Fragment.generated (scottSeed N α)

omit [L.IsRelational] in
private theorem scottFragment_countable (α : Ordinal) :
    (scottFragment (L := L) N α).toSet.Countable :=
  Fragment.generated_countable (scottSeed_countable α)

omit [L.IsRelational] in
private theorem closedScott_mem_scottFragment (α : Ordinal) {m : ℕ} (a : Fin m → N) :
    (⟨m, (scottFormula (L := L) a α).relabel (Sum.inr : Fin m → Empty ⊕ Fin m)⟩ :
      Σ n, L.BoundedFormulaω Empty n) ∈ (scottFragment (L := L) N α).toSet :=
  Fragment.subset_generated _ (Set.mem_iUnion.mpr ⟨m, Set.mem_image_of_mem _ (Set.mem_univ a)⟩)

omit [L.IsRelational] in
/-- The closed Scott formula realizes exactly as the open one. -/
private theorem realize_closedScott_iff {P : Type w} [L.Structure P] (α : Ordinal) {m : ℕ}
    (a : Fin m → N) (b : Fin m → P) :
    ((scottFormula (L := L) a α).relabel
        (Sum.inr : Fin m → Empty ⊕ Fin m)).Realize (Empty.elim : Empty → P) b
      ↔ (scottFormula (L := L) a α).Realize b := by
  have h := BoundedFormulaω.realize_relabel_sumInr (M := P)
    (φ := scottFormula (L := L) a α) (xs := b)
  rw [show (b ∘ Fin.castAdd 0 : Fin m → P) = b from funext fun i => congrArg b (Fin.ext rfl),
    show (b ∘ Fin.natAdd m : Fin 0 → P) = Fin.elim0 from funext fun i => i.elim0] at h
  exact h

/-! ## Arbitrary-target stabilization -/

variable {P : Type w} [L.Structure P]

omit [Countable (Σ l, L.Relations l)] in
/-- Relational languages have (vacuously) countably many function symbols. -/
theorem countable_functions_of_isRelational :
    Countable (Σ n, L.Functions n) := by
  have : ∀ n, IsEmpty (L.Functions n) := ‹L.IsRelational›
  exact inferInstance

omit [L.IsRelational] in
/-- BFEquiv transfers between the arbitrary target and a fragment-elementary substructure,
through the closed Scott formulas. -/
private theorem bfEquiv_iff_of_scottFragment_aElementary {α : Ordinal} (hα : α < Ordinal.omega 1)
    {P₀ : L.Substructure P} (hAe : AElementary (scottFragment (L := L) N α) P₀.subtype)
    {m : ℕ} (a : Fin m → N) (b : Fin m → P₀) :
    BFEquiv (L := L) α m a (fun i => (b i : P)) ↔ BFEquiv (L := L) α m a b := by
  rw [← realize_scottFormula_iff_BFEquiv (L := L) a _ α hα,
    ← realize_scottFormula_iff_BFEquiv (L := L) a b α hα,
    ← realize_closedScott_iff (L := L) α a (fun i => (b i : P)),
    ← realize_closedScott_iff (L := L) α a b]
  exact hAe _ (closedScott_mem_scottFragment α a) b

/-- **Arbitrary-target stabilization** (the #13 × #17 kernel): a complete stabilization level
of the countable source upgrades `BFEquiv` against an ARBITRARY target. -/
private theorem bfEquiv_succ_of_stabilizesCompletely_arbitrary {α : Ordinal}
    (hα : α < Ordinal.omega 1) (hstab : StabilizesCompletely (L := L) N α)
    {n : ℕ} {a : Fin n → N} {b : Fin n → P} (h : BFEquiv (L := L) α n a b) :
    BFEquiv (L := L) (Order.succ α) n a b := by
  have : Countable (Σ n, L.Functions n) := countable_functions_of_isRelational
  rw [BFEquiv.succ]
  refine ⟨h, ?_, ?_⟩
  · -- forth: a' : N gets a target match
    intro a'
    obtain ⟨P₀, hbP₀, hAe, hcnt⟩ := exists_countable_aElementary_substructure
      (scottFragment (L := L) N α) (X := Set.range b) (Set.finite_range b).countable
      (scottFragment_countable α)
    set b₀ : Fin n → P₀ := fun i => ⟨b i, hbP₀ (Set.mem_range_self i)⟩ with hb₀
    have hdown : BFEquiv (L := L) α n a b₀ :=
      (bfEquiv_iff_of_scottFragment_aElementary hα hAe a b₀).mp h
    have hsucc₀ := (hstab n P₀ a b₀).mp hdown
    rw [BFEquiv.succ] at hsucc₀
    obtain ⟨b₀', hb₀'⟩ := hsucc₀.2.1 a'
    refine ⟨(b₀' : P), ?_⟩
    have hup := (bfEquiv_iff_of_scottFragment_aElementary hα hAe
      (Fin.snoc a a') (Fin.snoc b₀ b₀')).mpr hb₀'
    rwa [show (fun i => ((Fin.snoc b₀ b₀' : Fin (n + 1) → P₀) i : P))
        = Fin.snoc b (b₀' : P) from by
      rw [show (fun i => ((Fin.snoc b₀ b₀' : Fin (n + 1) → P₀) i : P))
          = ⇑P₀.subtype ∘ Fin.snoc b₀ b₀' from rfl, Fin.comp_snoc]
      rfl] at hup
  · -- back: b' : P gets a source match
    intro b'
    obtain ⟨P₀, hbP₀, hAe, hcnt⟩ := exists_countable_aElementary_substructure
      (scottFragment (L := L) N α) (X := Set.range b ∪ {b'})
      ((Set.finite_range b).countable.union (Set.countable_singleton b'))
      (scottFragment_countable α)
    set b₀ : Fin n → P₀ := fun i => ⟨b i, hbP₀ (Set.mem_union_left _ (Set.mem_range_self i))⟩
      with hb₀
    set b₀' : P₀ := ⟨b', hbP₀ (Set.mem_union_right _ rfl)⟩ with hb₀'
    have hdown : BFEquiv (L := L) α n a b₀ :=
      (bfEquiv_iff_of_scottFragment_aElementary hα hAe a b₀).mp h
    have hsucc₀ := (hstab n P₀ a b₀).mp hdown
    rw [BFEquiv.succ] at hsucc₀
    obtain ⟨a', ha'⟩ := hsucc₀.2.2 b₀'
    refine ⟨a', ?_⟩
    have hup := (bfEquiv_iff_of_scottFragment_aElementary hα hAe
      (Fin.snoc a a') (Fin.snoc b₀ b₀')).mpr ha'
    rwa [show (fun i => ((Fin.snoc b₀ b₀' : Fin (n + 1) → P₀) i : P))
        = Fin.snoc b b' from by
      rw [show (fun i => ((Fin.snoc b₀ b₀' : Fin (n + 1) → P₀) i : P))
          = ⇑P₀.subtype ∘ Fin.snoc b₀ b₀' from rfl, Fin.comp_snoc]
      rfl] at hup

/-- **Stabilized `BFEquiv` holds at every ordinal against arbitrary targets** — the extension
family is `BFEquiv α` itself. -/
theorem bfEquiv_all_of_stabilizesCompletely_arbitrary {α : Ordinal}
    (hα : α < Ordinal.omega 1) (hstab : StabilizesCompletely (L := L) N α)
    {n : ℕ} {a : Fin n → N} {b : Fin n → P} (h : BFEquiv (L := L) α n a b) (β : Ordinal) :
    BFEquiv (L := L) β n a b := by
  refine bfEquiv_all_of_extensionFamily
    (fun n a b => BFEquiv (L := L) α n a b) ?_ ?_ ?_ β a b h
  · intro n a b hab
    rw [← BFEquiv.zero]
    exact BFEquiv.monotone zero_le hab
  · intro n a b hab a'
    have := bfEquiv_succ_of_stabilizesCompletely_arbitrary hα hstab hab
    rw [BFEquiv.succ] at this
    exact this.2.1 a'
  · intro n a b hab b'
    have := bfEquiv_succ_of_stabilizesCompletely_arbitrary hα hstab hab
    rw [BFEquiv.succ] at this
    exact this.2.2 b'

end Language

end FirstOrder
