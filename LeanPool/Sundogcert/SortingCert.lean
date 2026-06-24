/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.ByContra

/-!
# The 0-1 principle — a cheap, sound verification certificate for sorting networks

Another worked example of the discipline in `Sundogcert.Certificate`: **machine-check the deductive
cheap-CHECK core, name the imported hard-FIND wall.** The certificate is finite-field algebra;
this is its **combinatorics** sibling.

A *comparator network* on `n` wires is a list of comparators `(i,j)`; each replaces `(xᵢ, xⱼ)` by
`(min, max)`. The network **sorts** an input if its output is monotone. Two facts make sorting
networks a clean verify ≪ search instance:

* **CHEAP to VERIFY (this file, proved):** the **0-1 principle** — a network sorts *every* input
  over *every* linear order iff it sorts all `2ⁿ` **binary** inputs. So a claimed network is
  verifiable in `O(2ⁿ · size)` — polynomial in the *witness* — vs the naive `n!`-permutation check.
  The soundness is `sorts_of_sorts_bool` below: checking binary inputs SOUNDLY certifies sorting all
  inputs. The mechanism: comparator networks **commute with monotone maps** (`runNet_comm`), and
  threshold maps reduce the general case to binary.

* **HARD to FIND (the imported wall, NOT proved):** finding a *minimal*-size or minimal-depth
  network is a notoriously hard combinatorial search (optimal sizes are open / required massive SAT
  effort for `n ≳ 10`). That search-hardness is **named, not proved** here — exactly the role of the
  ISD/decoding hardness imported by the syndrome certificate.

## The one imported analytic input
The CORE (`comp_comm`) is **PROVED from mathlib**: `Monotone.map_min`/`Monotone.map_max` (a monotone
map commutes with `min`/`max`). Everything else is induction over the list plus a threshold map.

## References
* Knuth, *TAOCP* vol. 3, §5.3.4 (the 0-1 principle).
* `Monotone.map_min` / `Monotone.map_max` — monotone maps commute with `min`/`max`.
-/

namespace Sundog.SortingCert

variable {n : ℕ} {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- A single comparator `(i,j)`: send wire `i` to `min (xᵢ, xⱼ)` and wire `j` to `max (xᵢ, xⱼ)`. -/
def comp (i j : Fin n) (x : Fin n → α) : Fin n → α :=
  fun k => if k = i then min (x i) (x j) else if k = j then max (x i) (x j) else x k

/-- A comparator NETWORK applied left-to-right (a `List` of comparators folded over the wires). -/
def runNet (net : List (Fin n × Fin n)) (x : Fin n → α) : Fin n → α :=
  net.foldl (fun y p => comp p.1 p.2 y) x

@[simp] lemma runNet_nil (x : Fin n → α) : runNet [] x = x := rfl

lemma runNet_cons (p : Fin n × Fin n) (net : List (Fin n × Fin n)) (x : Fin n → α) :
    runNet (p :: net) x = runNet net (comp p.1 p.2 x) := by
  simp [runNet, List.foldl_cons]

/-- **CORE — a comparator commutes with any monotone map.** `comp i j (f ∘ x) = f ∘ comp i j x` for
monotone `f`, because `min`/`max` commute with monotone maps (`Monotone.map_min`/`map_max`). -/
lemma comp_comm {f : α → β} (hf : Monotone f) (i j : Fin n) (x : Fin n → α) :
    comp i j (f ∘ x) = f ∘ comp i j x := by
  funext k
  simp only [comp, Function.comp_apply]
  by_cases hi : k = i
  · simp [hi, hf.map_min]
  · by_cases hj : k = j
    · have hji : j ≠ i := fun h => hi (hj.trans h)
      simp [hj, hji, hf.map_max]
    · simp [hi, hj]

/-- **A whole network commutes with any monotone map.** Induction on the comparator list using
`comp_comm`. This is the engine of the 0-1 principle. -/
lemma runNet_comm {f : α → β} (hf : Monotone f) (net : List (Fin n × Fin n)) (x : Fin n → α) :
    runNet net (f ∘ x) = f ∘ runNet net x := by
  induction net generalizing x with
  | nil => rfl
  | cons p net ih => rw [runNet_cons, runNet_cons, comp_comm hf, ih]

/-- The threshold map `a ↦ (t ≤ a)` to `Bool`: monotone, and the family that reduces a general order
to binary inputs. -/
def thr (t : α) : α → Bool := fun a => decide (t ≤ a)

lemma thr_mono (t : α) : Monotone (thr t) := by
  intro a b hab
  by_cases h : t ≤ a
  · simp [thr, h, le_trans h hab]
  · simp [thr, h]

/--
**THE 0-1 PRINCIPLE (cheap-check soundness).** If a comparator network sorts every `2ⁿ` **binary**
input, then it sorts every input over **any** linear order `α`. So verifying a sorting network on
binary inputs is SOUND — it certifies the network sorts everything — at cost `O(2ⁿ · size)`,
polynomial in the network (the witness), versus the naive `n!` check.

Proof: if the network failed to sort some `x`, there are positions `i ≤ j` with
`runNet x j < runNet x i`. The threshold `thr (runNet x i)` is monotone, so the network commutes
with it (`runNet_comm`); applying it to `x` gives a BINARY input on which the (monotone, by hyp.)
output is `true` at `i` and `false` at `j` with `i ≤ j` — impossible. -/
theorem sorts_of_sorts_bool (net : List (Fin n × Fin n))
    (hbool : ∀ b : Fin n → Bool, Monotone (runNet net b)) (x : Fin n → α) :
    Monotone (runNet net x) := by
  intro i j hij
  by_contra hcon
  have hlt : runNet net x j < runNet net x i := not_le.mp hcon
  set t : α := runNet net x i with ht
  -- the network sorts the binary input `thr t ∘ x`, and commutes with `thr t`
  have hm : Monotone (thr t ∘ runNet net x) := by
    have h := hbool (thr t ∘ x)
    rwa [runNet_comm (thr_mono t)] at h
  have hle := hm hij
  -- threshold is `true` at i (t = runNet x i); so it must be `true` at j too ⟹ t ≤ runNet x j
  have hi : (thr t ∘ runNet net x) i = true := by simp [Function.comp_apply, thr, ← ht]
  rw [hi] at hle
  have hj : (thr t ∘ runNet net x) j = true := by
    cases hv : (thr t ∘ runNet net x) j with
    | false => rw [hv] at hle; exact absurd hle (by decide)
    | true => rfl
  simp only [Function.comp_apply, thr, decide_eq_true_eq] at hj
  exact absurd (ht ▸ hj) (not_le.mpr hlt)

/-- Concrete corollary — the binary (`2ⁿ`) check certifies sorting over `ℕ` (and, by
`sorts_of_sorts_bool`, over any linear order). The cheap, sound certificate in usable form. -/
theorem sorts_nat_of_sorts_bool (net : List (Fin n × Fin n))
    (hbool : ∀ b : Fin n → Bool, Monotone (runNet net b)) (x : Fin n → ℕ) :
    Monotone (runNet net x) :=
  sorts_of_sorts_bool net hbool x

end Sundog.SortingCert

-- Axiom audit: the cheap-check soundness should depend only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
