/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.CountableCompanion
import LeanPool.InfinitaryLogic.Scott.BackAndForth
import LeanPool.InfinitaryLogic.Karp.CarrierTheorem
/-!
# The type-preserving back-and-forth (issue #17 chunk 3)

The relation `TypeAgree N a b`: tuples of the ambient `M` and of the companion substructure
`N` agree when their complete `L_{ω₁ω}`-types — both computed IN `M`, viewing `b` through the
inclusion — coincide. The two extension properties hold by the isolator machinery:

* **forth** (`TypeAgree.forth`): isolate `tp_M(ā, a')`; its one-variable existential holds at
  `ā`, transfers to `ι b̄` across the type equality, descends to `N` by A-elementarity of the
  controlling fragment, and the witness comes back up at arity `n+1`;
* **back** (`TypeAgree.back`): isolate `tp_M(ι b̄, ι b')`; its existential transfers across
  the type equality to `ā`, and the witness is chosen directly in `M` — no A-elementarity.

The audited thin bridge (`bfEquiv_all_of_typeAgree`): any relation with type agreement and the
two extensions is `BFEquiv` at EVERY ordinal — one `limitRecOn` induction whose zero stage is
`TypeAgree.sameAtomicType` (atomic indices are realizations of atomic `L_{ω₁ω}`-formulas, and
the substructure inclusion reflects them).
-/

namespace FirstOrder

namespace Language

open Lomega1omega

universe u v w uι

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- **Type agreement**: the complete types in the AMBIENT structure coincide. -/
def TypeAgree (N : L.Substructure M) {n : ℕ} (a : Fin n → M) (b : Fin n → N) : Prop :=
  infinitaryType (L := L) M a = infinitaryType (L := L) M (fun i => (b i : M))

theorem typeAgree_elim0 (N : L.Substructure M) :
    TypeAgree N (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  congrArg (infinitaryType (L := L) M) (funext fun i => i.elim0)

theorem TypeAgree.realize_iff {N : L.Substructure M} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : TypeAgree N a b) (φ : L.BoundedFormulaω Empty n) :
    φ.Realize Empty.elim a ↔ φ.Realize Empty.elim (fun i => (b i : M)) :=
  Set.ext_iff.mp h φ

/-- **Forth**: every ambient element has a companion match extending the agreement. -/
theorem TypeAgree.forth {hsmall : Lomega1omegaSmall (L := L) M} {N : L.Substructure M}
    (hAe : AElementary (isolatorFragment hsmall) N.subtype)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (hab : TypeAgree N a b) (a' : M) :
    ∃ b' : N, TypeAgree N (Fin.snoc a a') (Fin.snoc b b') := by
  set p := infinitaryType (L := L) M (Fin.snoc a a') with hpdef
  have hpre : p ∈ RealizedInfinitaryTypes (L := L) M (n + 1) := ⟨_, rfl⟩
  have hexa : ((isolatingFormula (hsmall (n + 1)) p).ex).Realize Empty.elim a := by
    rw [BoundedFormulaω.realize_ex]
    exact ⟨a', (realize_isolatingFormula_iff (hsmall (n + 1)) p _).mpr rfl⟩
  have hexb := (hab.realize_iff _).mp hexa
  have hexbN : ((isolatingFormula (hsmall (n + 1)) p).ex).Realize Empty.elim b :=
    (hAe _ (isolatingFormula_ex_mem_isolatorFragment hsmall hpre) b).mp hexb
  rw [BoundedFormulaω.realize_ex] at hexbN
  obtain ⟨b', hb'⟩ := hexbN
  have hχN := hAe _ (isolatingFormula_mem_isolatorFragment hsmall hpre) (Fin.snoc b b')
  have hcomp : (⇑N.subtype ∘ Fin.snoc b b' : Fin (n + 1) → M)
      = Fin.snoc (fun i => (b i : M)) (b' : M) := Fin.comp_snoc _ _ _
  rw [hcomp] at hχN
  refine ⟨b', ?_⟩
  show infinitaryType (L := L) M (Fin.snoc a a')
    = infinitaryType (L := L) M (fun i => ((Fin.snoc b b' : Fin (n + 1) → N) i : M))
  have hsn : (fun i => ((Fin.snoc b b' : Fin (n + 1) → N) i : M))
      = Fin.snoc (fun i => (b i : M)) (b' : M) := Fin.comp_snoc _ _ _
  rw [hsn]
  exact ((realize_isolatingFormula_iff (hsmall (n + 1)) p _).mp (hχN.mpr hb')).symm

/-- **Back**: every companion element has an ambient match — the witness is chosen directly in
`M`; no A-elementarity is consumed. -/
theorem TypeAgree.back (hsmall : Lomega1omegaSmall (L := L) M) {N : L.Substructure M}
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (hab : TypeAgree N a b) (b' : N) :
    ∃ a' : M, TypeAgree N (Fin.snoc a a') (Fin.snoc b b') := by
  set q := infinitaryType (L := L) M (Fin.snoc (fun i => (b i : M)) (b' : M)) with hqdef
  have hexb : ((isolatingFormula (hsmall (n + 1)) q).ex).Realize Empty.elim
      (fun i => (b i : M)) := by
    rw [BoundedFormulaω.realize_ex]
    exact ⟨(b' : M), (realize_isolatingFormula_iff (hsmall (n + 1)) q _).mpr rfl⟩
  have hexa := (hab.realize_iff _).mpr hexb
  rw [BoundedFormulaω.realize_ex] at hexa
  obtain ⟨a', ha'⟩ := hexa
  refine ⟨a', ?_⟩
  show infinitaryType (L := L) M (Fin.snoc a a')
    = infinitaryType (L := L) M (fun i => ((Fin.snoc b b' : Fin (n + 1) → N) i : M))
  have hsn : (fun i => ((Fin.snoc b b' : Fin (n + 1) → N) i : M))
      = Fin.snoc (fun i => (b i : M)) (b' : M) := Fin.comp_snoc _ _ _
  rw [hsn]
  exact (realize_isolatingFormula_iff (hsmall (n + 1)) q _).mp ha'

/-- **The zero stage**: type agreement gives atomic agreement — atomic indices are
realizations of atomic `L_{ω₁ω}`-formulas, and the inclusion reflects them. -/
theorem TypeAgree.sameAtomicType {N : L.Substructure M} {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} (hab : TypeAgree N a b) :
    SameAtomicType (L := L) (M := M) (N := N) a b := by
  intro idx
  cases idx with
  | eq i j =>
    have hM := hab.realize_iff
      (BoundedFormulaω.equal (Term.var (Sum.inr i)) (Term.var (Sum.inr j)))
    simp only [BoundedFormulaω.realize_equal, Term.realize_var, Sum.elim_inr] at hM
    show a i = a j ↔ b i = b j
    exact hM.trans ⟨fun h => Subtype.ext h, fun h => congrArg _ h⟩
  | rel R f =>
    have hM := hab.realize_iff
      (BoundedFormulaω.rel R fun k => Term.var (Sum.inr (f k)))
    simp only [BoundedFormulaω.realize_rel, Term.realize_var, Sum.elim_inr] at hM
    show Structure.RelMap R (a ∘ f) ↔ Structure.RelMap R (b ∘ f)
    refine hM.trans ?_
    exact N.subtype.map_rel R (b ∘ f)

/-- **The audited thin bridge**: a type-agreeing relation with the forth and back extensions
is back-and-forth equivalent at EVERY ordinal. -/
theorem bfEquiv_all_of_typeAgree {N : L.Substructure M}
    (hforth : ∀ {n : ℕ} (a : Fin n → M) (b : Fin n → N), TypeAgree N a b →
      ∀ a' : M, ∃ b' : N, TypeAgree N (Fin.snoc a a') (Fin.snoc b b'))
    (hback : ∀ {n : ℕ} (a : Fin n → M) (b : Fin n → N), TypeAgree N a b →
      ∀ b' : N, ∃ a' : M, TypeAgree N (Fin.snoc a a') (Fin.snoc b b'))
    (α : Ordinal) :
    ∀ {n : ℕ} (a : Fin n → M) (b : Fin n → N),
      TypeAgree N a b → BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro n a b hab
    rw [BFEquiv.zero]
    exact hab.sameAtomicType
  | add_one β ih =>
    intro n a b hab
    rw [show (β + 1 : Ordinal) = Order.succ β from (Order.succ_eq_add_one β).symm,
      BFEquiv.succ]
    refine ⟨ih a b hab, fun m => ?_, fun b' => ?_⟩
    · obtain ⟨b', hb'⟩ := hforth a b hab m
      exact ⟨b', ih _ _ hb'⟩
    · obtain ⟨a', ha'⟩ := hback a b hab b'
      exact ⟨a', ih _ _ ha'⟩
  | limit β hβ ih =>
    intro n a b hab
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ a b hab

/-! ## The semantic countable-companion theorem (chunk 4) -/

/-- **Back-and-forth equivalence with a given companion** (identity-keeping form): any
countable companion from chunk 2 is `BFEquiv` at every ordinal with the ambient structure. -/
theorem bfEquiv_all_of_companion {hsmall : Lomega1omegaSmall (L := L) M}
    {N : L.Substructure M} (hAe : AElementary (isolatorFragment hsmall) N.subtype)
    (α : Ordinal) :
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  bfEquiv_all_of_typeAgree (fun _ _ hab a' => hab.forth hAe a')
    (fun _ _ hab b' => hab.back hsmall b') α Fin.elim0 Fin.elim0 (typeAgree_elim0 N)

/-- **The semantic countable-companion theorem** (issue #17 chunk 4 endpoint): a small
structure over countably many function symbols has a countable model back-and-forth
equivalent to it at every ordinal. -/
theorem exists_countable_bfEquiv_of_lomega1omegaSmall [Countable (Σ n, L.Functions n)]
    (hsmall : Lomega1omegaSmall (L := L) M) :
    ∃ (N : Type w) (_ : L.Structure N), Countable N ∧
      ∀ α : Ordinal, BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  obtain ⟨N, hcnt, hAe⟩ := exists_countable_companion hsmall
  exact ⟨N, inferInstance, hcnt, bfEquiv_all_of_companion hAe⟩

/-- **All-`L_∞ω`-formula agreement** with a companion — the relational packaging boundary
(`BFEquiv_implies_agreeQR`). -/
theorem realize_inf_iff_of_companion [L.IsRelational] {ι : Type uι}
    {hsmall : Lomega1omegaSmall (L := L) M} {N : L.Substructure M}
    (hAe : AElementary (isolatorFragment hsmall) N.subtype)
    (φ : L.BoundedFormulaInf ι (Fin 0) 0) :
    FormulaInf.Realize φ (Fin.elim0 : Fin 0 → M)
      ↔ FormulaInf.Realize φ (Fin.elim0 : Fin 0 → N) :=
  BFEquiv_implies_agreeQR φ.qrank Fin.elim0 Fin.elim0
    (bfEquiv_all_of_companion hAe φ.qrank) φ le_rfl

end Language

end FirstOrder
