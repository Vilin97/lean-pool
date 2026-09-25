/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.SumLexOrder

/-!
# Monotonicity of the interface re-indexing equivalences

The gluing chain transports corrected constrained values along
label re-indexings; the through-factor is orientation-antisymmetric,
so only monotone relabelings preserve the corrected value.  This
file certifies the chain's equivalences as order isomorphisms for
the lexicographic order on sums:

* `finSumFinOrderIso`: `finSumFinEquiv` as an order isomorphism;
* `interfaceStepOrderIso`: the label re-indexing after gluing the
  top interface pair, as an order isomorphism;
* application lemmas (`interfaceStepEquiv_apply_inl`,
  `interfaceStepEquiv_apply_inr`) letting the chain rewrite states
  through the isos concretely, on top of the removals' value
  computations in `Composition.lean`.

**Instance discipline.**  Mathlib carries a global `Preorder (α ⊕ β)`
(the disjoint order, where `inl` and `inr` are incomparable), so a
`letI := sumLexLinearOrder α β` does *not* reliably route `<`/`≤`
notation to the lexicographic order — instance search can still pick
the global disjoint order.  Every statement here therefore pins the
sum orders explicitly through the reducible aliases
`sumLexPreorder`/`sumLexLE`/`sumLexSubtypeLinearOrder`/… below,
which are definitionally the projections of `sumLexLinearOrder`.
-/

@[expose] public section

namespace RS

/-! ### Pinned instances for the lexicographic sum order -/

section InstanceAliases

variable (α β : Type)

/-- The lexicographic preorder on a plain sum, as an explicit term
(never registered as an instance): pin it with `@` in statements. -/
abbrev sumLexPreorder [LinearOrder α] [LinearOrder β] : Preorder (α ⊕ β) :=
  (sumLexLinearOrder α β).toPartialOrder.toPreorder

/-- The lexicographic `≤` on a plain sum, as an explicit term. -/
abbrev sumLexLE [LinearOrder α] [LinearOrder β] : LE (α ⊕ β) :=
  (sumLexPreorder α β).toLE

/-- The linear order induced on a subtype of the lexicographically
ordered sum. -/
abbrev sumLexSubtypeLinearOrder [LinearOrder α] [LinearOrder β]
    (p : α ⊕ β → Prop) :
    LinearOrder (Subtype p) :=
  @Subtype.instLinearOrder _ (sumLexLinearOrder α β) p

/-- The preorder induced on a subtype of the lexicographically
ordered sum. -/
abbrev sumLexSubtypePreorder [LinearOrder α] [LinearOrder β]
    (p : α ⊕ β → Prop) :
    Preorder (Subtype p) :=
  (sumLexSubtypeLinearOrder α β p).toPartialOrder.toPreorder

/-- The `≤` induced on a subtype of the lexicographically ordered
sum. -/
abbrev sumLexSubtypeLE [LinearOrder α] [LinearOrder β]
    (p : α ⊕ β → Prop) : LE (Subtype p) :=
  (sumLexSubtypePreorder α β p).toLE

end InstanceAliases

/-! ### Strictly monotone equivalences of linear orders -/

section StrictMonoEquiv

variable {α β : Type}

/-- The inverse of a strictly monotone equivalence between linear
orders is strictly monotone. -/
theorem strictMono_equiv_symm [LinearOrder α] [LinearOrder β]
    (e : α ≃ β) (h : StrictMono e) :
    StrictMono e.symm := by
  intro b b' hbb
  rcases lt_trichotomy (e.symm b) (e.symm b') with h1 | h1 | h1
  · exact h1
  · exfalso
    have h2 : b = b' := by
      have h3 := congrArg e h1
      rwa [e.apply_symm_apply, e.apply_symm_apply] at h3
    exact absurd h2 (ne_of_lt hbb)
  · exfalso
    have h2 := h h1
    rw [e.apply_symm_apply, e.apply_symm_apply] at h2
    exact lt_asymm hbb h2

/-- A strictly monotone equivalence between linear orders, as an
order isomorphism (keeping the underlying equivalence on the
nose). -/
def orderIsoOfStrictMonoEquiv [LinearOrder α] [LinearOrder β]
    (e : α ≃ β) (h : StrictMono e) :
    α ≃o β :=
  e.toOrderIso h.monotone (strictMono_equiv_symm e h).monotone

/-- The order isomorphism built from a strictly monotone equivalence
acts as that equivalence. -/
@[simp] theorem orderIsoOfStrictMonoEquiv_apply [LinearOrder α] [LinearOrder β]
    (e : α ≃ β)
    (h : StrictMono e) (x : α) :
    orderIsoOfStrictMonoEquiv e h x = e x := rfl

/-- And carries it as its underlying equivalence. -/
@[simp] theorem orderIsoOfStrictMonoEquiv_toEquiv
    [LinearOrder α] [LinearOrder β]
    (e : α ≃ β)
    (h : StrictMono e) :
    (orderIsoOfStrictMonoEquiv e h).toEquiv = e := rfl

end StrictMonoEquiv

/-! ### `finSumFinEquiv` is monotone for the lexicographic order -/

/-- `finSumFinEquiv` is strictly monotone for the lexicographic sum
order: it lays the left block below the right. -/
theorem finSumFinEquiv_strictMono (m n : ℕ) :
    @StrictMono _ _ (sumLexPreorder (Fin m) (Fin n)) _
      (finSumFinEquiv : Fin m ⊕ Fin n → Fin (m + n)) := by
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl a' =>
      have ha : a < a' := sumLex_inl_lt_inl_iff.mp hxy
      rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
      exact Fin.strictMono_castAdd n ha
    | inr b =>
      rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      have ha : (a : ℕ) < m := a.isLt
      change (a : ℕ) < m + (b : ℕ)
      omega
  | inr b =>
    cases y with
    | inl a' => exact absurd hxy (sumLex_not_inr_lt_inl a' b)
    | inr b' =>
      have hb : b < b' := sumLex_inr_lt_inr_iff.mp hxy
      rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right]
      exact Fin.strictMono_natAdd m hb

/-- `finSumFinEquiv` as an order isomorphism for the lexicographic
order on `Fin m ⊕ Fin n`. -/
def finSumFinOrderIso (m n : ℕ) :
    @OrderIso (Fin m ⊕ Fin n) (Fin (m + n))
      (sumLexLE (Fin m) (Fin n)) _ :=
  @orderIsoOfStrictMonoEquiv _ _ (sumLexLinearOrder (Fin m) (Fin n)) _
    finSumFinEquiv (finSumFinEquiv_strictMono m n)

/-- The order isomorphism acts as `finSumFinEquiv`. -/
@[simp] theorem finSumFinOrderIso_apply (m n : ℕ) (x : Fin m ⊕ Fin n) :
    finSumFinOrderIso m n x = finSumFinEquiv x := rfl

/-- And carries it as its underlying equivalence. -/
@[simp] theorem finSumFinOrderIso_toEquiv (m n : ℕ) :
    (finSumFinOrderIso m n).toEquiv = finSumFinEquiv := rfl

/-! ### The removal equivalences are strictly monotone -/

/-- Reinstating a removed point is strictly monotone: `succAbove`
shifts indices up without reordering them. -/
theorem finRemoveEquiv_symm_strictMono {n : ℕ} (a : Fin (n + 1)) :
    StrictMono (finRemoveEquiv a).symm := by
  intro y y' h
  change a.succAbove y < a.succAbove y'
  exact Fin.strictMono_succAbove a h

/-- Hence removing a point is too. -/
theorem finRemoveEquiv_strictMono {n : ℕ} (a : Fin (n + 1)) :
    StrictMono (finRemoveEquiv a) :=
  strictMono_equiv_symm (finRemoveEquiv a).symm
    (finRemoveEquiv_symm_strictMono a)

/-- Removing label `t` on the right is strictly monotone. -/
theorem rightRemoveEquiv_strictMono (t u : ℕ) :
    StrictMono (rightRemoveEquiv t u) := by
  intro x y hxy
  exact finRemoveEquiv_strictMono _ hxy

/-! ### The interface step is an order isomorphism -/

/-- The step re-indexing on a surviving left label: the left
removal, injected. -/
theorem interfaceStepEquiv_apply_inl (s t u : ℕ) (v : Fin (s + t + 1))
    (h : (Sum.inl v : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
      (Sum.inl v : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inr ⟨t, by omega⟩) :
    interfaceStepEquiv s t u ⟨Sum.inl v, h⟩ =
      Sum.inl (finRemoveEquiv ⟨s + t, Nat.lt_succ_self _⟩
        ⟨v, fun he => h.1 (congrArg Sum.inl he)⟩) := rfl

/-- The step re-indexing on a surviving right label: the right
removal, injected. -/
theorem interfaceStepEquiv_apply_inr (s t u : ℕ) (w : Fin (t + 1 + u))
    (h : (Sum.inr w : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
      (Sum.inr w : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inr ⟨t, by omega⟩) :
    interfaceStepEquiv s t u ⟨Sum.inr w, h⟩ =
      Sum.inr (rightRemoveEquiv t u
        ⟨w, fun he => h.2 (congrArg Sum.inr he)⟩) := rfl

/-- **The step re-indexing is strictly monotone** for the
lexicographic order: left labels stay below right ones and each
block's removal preserves order.  This is what lets the gluing chain
carry corrected values, the through-factor being
orientation-antisymmetric. -/
theorem interfaceStepEquiv_strictMono (s t u : ℕ) :
    @StrictMono _ _
      (sumLexSubtypePreorder (Fin (s + t + 1)) (Fin (t + 1 + u))
        (fun x => x ≠ Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
          x ≠ Sum.inr ⟨t, by omega⟩))
      (sumLexPreorder (Fin (s + t)) (Fin (t + u)))
      (interfaceStepEquiv s t u) := by
  rintro ⟨xv, hx⟩ ⟨yv, hy⟩ hxy
  cases xv with
  | inl v =>
    cases yv with
    | inl v' =>
      have hv : v < v' := sumLex_inl_lt_inl_iff.mp hxy
      rw [interfaceStepEquiv_apply_inl, interfaceStepEquiv_apply_inl]
      exact sumLex_inl_lt_inl_iff.mpr (finRemoveEquiv_strictMono _ hv)
    | inr w' =>
      rw [interfaceStepEquiv_apply_inl, interfaceStepEquiv_apply_inr]
      exact sumLex_inl_lt_inr _ _
  | inr w =>
    cases yv with
    | inl v' => exact absurd hxy (sumLex_not_inr_lt_inl v' w)
    | inr w' =>
      have hw : w < w' := sumLex_inr_lt_inr_iff.mp hxy
      rw [interfaceStepEquiv_apply_inr, interfaceStepEquiv_apply_inr]
      exact sumLex_inr_lt_inr_iff.mpr
        (rightRemoveEquiv_strictMono t u hw)

/-- The interface-step re-indexing (`interfaceStepEquiv`) as an
order isomorphism for the lexicographic orders. -/
noncomputable def interfaceStepOrderIso (s t u : ℕ) :
    @OrderIso
      {x : Fin (s + t + 1) ⊕ Fin (t + 1 + u) //
        x ≠ Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
        x ≠ Sum.inr ⟨t, by omega⟩}
      (Fin (s + t) ⊕ Fin (t + u))
      (sumLexSubtypeLE (Fin (s + t + 1)) (Fin (t + 1 + u)) _)
      (sumLexLE (Fin (s + t)) (Fin (t + u))) :=
  @orderIsoOfStrictMonoEquiv _ _
    (sumLexSubtypeLinearOrder (Fin (s + t + 1)) (Fin (t + 1 + u)) _)
    (sumLexLinearOrder (Fin (s + t)) (Fin (t + u)))
    (interfaceStepEquiv s t u) (interfaceStepEquiv_strictMono s t u)

/-- The step order isomorphism acts as the step equivalence. -/
@[simp] theorem interfaceStepOrderIso_apply (s t u : ℕ)
    (x : {x : Fin (s + t + 1) ⊕ Fin (t + 1 + u) //
        x ≠ Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
        x ≠ Sum.inr ⟨t, by omega⟩}) :
    interfaceStepOrderIso s t u x = interfaceStepEquiv s t u x := rfl

/-- And carries it as its underlying equivalence. -/
@[simp] theorem interfaceStepOrderIso_toEquiv (s t u : ℕ) :
    (interfaceStepOrderIso s t u).toEquiv = interfaceStepEquiv s t u :=
  rfl

end RS
