/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.Reindex
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Quantifier rank of infinitary formulas

The quantifier rank of an infinitary formula: `0` on atoms, `max` on implication, successor
under `∀`, and the supremum over the branching carrier at an infinitary node.

## The universe of the rank

Because the infinitary cases take a supremum over the carrier `ι`, the natural target is
`Ordinal.{uι}` — the carrier's own ordinal universe. At `ι := ℕ` this is exactly
`Ordinal.{0}`, which is where Scott analysis wants it; no lifting appears in the `L_{ω₁ω}`
case.

Transport between carriers is therefore stated up to `Ordinal.lift`: `qrank_reindex` says
`reindex` preserves rank once both sides are lifted into a common universe. Padding is
invisible to rank, since the padded branches are `⊤`/`⊥`, both of rank `0` — which is why the
statement holds for empty carriers too, where every branch is padding.

## Main definitions

- `FirstOrder.Language.BoundedFormulaInf.qrank`

## Main results

- `qrank_reindex`: rank is preserved by carrier transport, up to `Ordinal.lift`.
- `qrank_alls`, `qrank_exs`: closing all free bound-variable slots adds exactly `n`.
- `qrank_toInf`: the finitary embedding's rank is carrier-independent (up to `Ordinal.lift`),
  since a finitary formula has no infinitary nodes.
-/

@[expose] public section

universe u v u' uι uκ w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- The quantifier rank of an infinitary formula, valued in the branching carrier's own
ordinal universe. -/
noncomputable def qrank : ∀ {n}, L.BoundedFormulaInf ι α n → Ordinal.{uι}
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qrank φ) (qrank ψ)
  | _, .all φ => Order.succ (qrank φ)
  | _, .iSup φs => ⨆ i, qrank (φs i)
  | _, .iInf φs => ⨆ i, qrank (φs i)

section Equations

@[simp]
theorem qrank_falsum : (falsum : L.BoundedFormulaInf ι α n).qrank = 0 := rfl

@[simp]
theorem qrank_imp {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.imp ψ).qrank = max φ.qrank ψ.qrank := rfl

@[simp]
theorem qrank_all {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.all.qrank = Order.succ φ.qrank := rfl

@[simp]
theorem qrank_iSup {φs : ι → L.BoundedFormulaInf ι α n} :
    (iSup φs).qrank = ⨆ i, (φs i).qrank := rfl

@[simp]
theorem qrank_iInf {φs : ι → L.BoundedFormulaInf ι α n} :
    (iInf φs).qrank = ⨆ i, (φs i).qrank := rfl

@[simp]
theorem qrank_not {φ : L.BoundedFormulaInf ι α n} : φ.not.qrank = φ.qrank :=
  max_bot_right _

@[simp]
theorem qrank_bot : (⊥ : L.BoundedFormulaInf ι α n).qrank = 0 := rfl

@[simp]
theorem qrank_top : (⊤ : L.BoundedFormulaInf ι α n).qrank = 0 :=
  max_self 0

@[simp]
theorem qrank_ex {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.ex.qrank = Order.succ φ.qrank := by
  simp [BoundedFormulaInf.ex]

end Equations

section Closure

/-- Ordinal addition is not commutative, but it is on the finite part, which is all that is
needed to reassociate the `n` successors that `alls`/`exs` contribute. -/
private theorem add_succ_natCast (a : Ordinal) (n : ℕ) :
    a + 1 + (n : Ordinal) = a + ((n + 1 : ℕ) : Ordinal) := by
  rw [Nat.cast_add, Nat.cast_one, add_assoc, Nat.cast_add_one_comm]

@[simp]
private theorem qrank_alls : ∀ {n} {φ : L.BoundedFormulaInf ι α n},
    φ.alls.qrank = φ.qrank + n
  | 0, φ => by simp [alls]
  | n + 1, φ => by
    rw [alls, qrank_alls, qrank_all, Order.succ_eq_add_one, add_succ_natCast]

@[simp]
private theorem qrank_exs : ∀ {n} {φ : L.BoundedFormulaInf ι α n},
    φ.exs.qrank = φ.qrank + n
  | 0, φ => by simp [exs]
  | n + 1, φ => by
    rw [exs, qrank_exs, qrank_ex, Order.succ_eq_add_one, add_succ_natCast]

end Closure

section Transport

/-- **`Ordinal.lift` commutes with a bounded indexed supremum.**

`Cardinal.lift_iSup` has no ordinal counterpart in this dependency, so it is derived here from
normality of the lift initial segment. Normality gives the supremum only over a nonempty index
type, so the empty case is discharged separately: there both sides are the bottom ordinal, and
there is no supremum for the lift to move through. -/
private theorem lift_iSup {β : Type w} {f : β → Ordinal.{uι}} (hf : BddAbove (Set.range f)) :
    Ordinal.lift.{uκ} (⨆ i, f i) = ⨆ i, Ordinal.lift.{uκ} (f i) := by
  rcases isEmpty_or_nonempty β with _ | _
  · simp
  · exact Ordinal.liftInitialSeg.isNormal.map_iSup hf

/-- The transport fact, isolated: **padding by a rank-zero formula does not change the lifted
supremum**. Both infinitary cases of `qrank_reindex` are this lemma — the `iInf` case pads with
`⊤` and the `iSup` case with `⊥`, and nothing else about them differs. -/
private theorem lift_iSup_qrank_pad {n : ℕ} (c : IndexCoding ι κ)
    (pad : L.BoundedFormulaInf κ α n) (hpad : pad.qrank = 0)
    (φs : ι → L.BoundedFormulaInf ι α n) (ψs : ι → L.BoundedFormulaInf κ α n)
    (ih : ∀ i, Ordinal.lift.{uι} (ψs i).qrank = Ordinal.lift.{uκ} (φs i).qrank) :
    Ordinal.lift.{uι} (⨆ k, (c.pad pad ψs k).qrank)
      = Ordinal.lift.{uκ} (⨆ i, (φs i).qrank) := by
  rw [lift_iSup Ordinal.bddAbove_of_small, lift_iSup Ordinal.bddAbove_of_small]
  refine le_antisymm (Ordinal.iSup_le fun k => ?_) (Ordinal.iSup_le fun i => ?_)
  · rcases hd : c.decode k with _ | i
    · rw [c.pad_of_decode_none hd, hpad, Ordinal.lift_zero]
      exact Ordinal.bot_eq_zero ▸ bot_le
    · rw [c.pad_of_decode_some hd, ih i]
      exact Ordinal.le_iSup (fun i => Ordinal.lift.{uκ} (φs i).qrank) i
  · rw [← ih i]
    have hb := Ordinal.le_iSup
      (fun k => Ordinal.lift.{uι} (c.pad pad ψs k).qrank) (c.encode i)
    rwa [IndexCoding.pad_encode] at hb

/-- **Rank transport**: carrier transport preserves quantifier rank, up to `Ordinal.lift` into
the common universe.

Padding is invisible: the branches a coding cannot decode are `⊤`/`⊥`, both of rank `0`, so
they never raise the supremum. In particular this holds when `ι` is empty, where every branch
of the transported formula is padding. -/
private theorem qrank_reindex (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n),
      Ordinal.lift.{uι} (reindex c φ).qrank = Ordinal.lift.{uκ} φ.qrank := by
  intro n φ
  induction φ with
  | falsum => simp only [reindex, qrank, Ordinal.lift_zero]
  | equal t₁ t₂ => simp only [reindex, qrank, Ordinal.lift_zero]
  | rel R ts => simp only [reindex, qrank, Ordinal.lift_zero]
  | imp φ ψ ihφ ihψ =>
    change Ordinal.lift.{uι} (max _ _) = Ordinal.lift.{uκ} (max _ _)
    rw [Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h),
      Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h), ihφ, ihψ]
  | all φ ih =>
    change Ordinal.lift.{uι} (Order.succ _) = Ordinal.lift.{uκ} (Order.succ _)
    rw [Ordinal.lift_succ, Ordinal.lift_succ, ih]
  | iSup φs ih => exact lift_iSup_qrank_pad c ⊥ qrank_bot φs _ ih
  | iInf φs ih => exact lift_iSup_qrank_pad c ⊤ qrank_top φs _ ih



end Transport

section Finitary

/-- **Carrier-independence of the finitary embedding's rank.** A finitary formula has no
infinitary nodes, so its rank is the same at every branching carrier — the ranks live in
different ordinal universes, so the statement is up to `Ordinal.lift`, exactly as in
`qrank_reindex`.

Unlike `qrank_reindex` this needs no coding between the carriers: there is nothing to
transport. -/
private theorem qrank_toInf : ∀ {n} (φ : L.BoundedFormula α n),
    Ordinal.lift.{uκ} (BoundedFormula.toInf (ι := ι) φ).qrank =
      Ordinal.lift.{uι} (BoundedFormula.toInf (ι := κ) φ).qrank := by
  intro n φ
  induction φ with
  | falsum =>
    change Ordinal.lift.{uκ} (0 : Ordinal.{uι}) = Ordinal.lift.{uι} (0 : Ordinal.{uκ})
    simp
  | equal t₁ t₂ =>
    change Ordinal.lift.{uκ} (0 : Ordinal.{uι}) = Ordinal.lift.{uι} (0 : Ordinal.{uκ})
    simp
  | rel R ts =>
    change Ordinal.lift.{uκ} (0 : Ordinal.{uι}) = Ordinal.lift.{uι} (0 : Ordinal.{uκ})
    simp
  | imp φ ψ ihφ ihψ =>
    change Ordinal.lift.{uκ} (max _ _) = Ordinal.lift.{uι} (max _ _)
    rw [Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h),
      Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h), ihφ, ihψ]
  | all φ ih =>
    change Ordinal.lift.{uκ} (Order.succ _) = Ordinal.lift.{uι} (Order.succ _)
    rw [Ordinal.lift_succ, Ordinal.lift_succ, ih]

end Finitary

end BoundedFormulaInf

end Language

end FirstOrder
