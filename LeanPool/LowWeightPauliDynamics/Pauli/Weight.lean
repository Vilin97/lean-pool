/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Mathlib.Data.Fin.VecNotation
public import LeanPool.LowWeightPauliDynamics.Pauli.Basic

/-!
# Pauli weight, and the `k_h - 1` bound on how far a rotation can move it

This file defines the support and the weight of a Pauli string (`def:pauli_weight`) and proves the
weight estimate the damped ladder is built on: if a Pauli string `G` anticommutes with `s`, then
the product `G s` satisfies `| |G s| - |s| | ≤ |G| - 1`, hence `≤ k_h - 1` for a `k_h`-local `G`.

## Main definitions

* `PauliString.site`: the single-qubit Pauli type carried at a site, as a pair of bits.
* `PauliString.support`, `PauliString.weight`: the qubits on which a string acts non-trivially,
  and their number (`def:pauli_weight`).
* `PauliString.cancelSites`, `PauliString.antiSites`, `PauliString.createSites`: the three kinds
  of site of `supp G`, relative to a second string `s`.

## Main results

* `PauliString.card_cancelSites_add_card_antiSites_add_card_createSites`,
  `PauliString.weight_mul_add_card_cancelSites`: the exact site bookkeeping.
* `PauliString.sympForm_eq_card_antiSites`: the symplectic form is `#antiSites` modulo two.
* `PauliString.weight_mul_le`, `PauliString.weight_le_weight_mul_add_weight`: the bounds with the
  full weight `|G|`, which need no hypothesis.
* `PauliString.abs_weight_mul_sub_weight_le`: the two-sided bound with `|G| - 1` for an
  anticommuting pair.
* `PauliString.weight_sub_le_weight_mul`, `PauliString.weight_le_weight_mul_add_kh`,
  `PauliString.weight_mul_le_weight_add_kh`: the `k_h` forms the ladder consumes.
* `PauliString.exists_commuting_weight_increase_by_full_weight`: the anticommutation hypothesis
  cannot be dropped.

## The estimate, and why it is `k_h - 1` rather than `k_h`

The proof of `apd:thm:local_flow_k_local` needs: when `G` anticommutes with `s`, the partner Pauli
`G s` satisfies

  `|G s| ≥ |s| - (k_h - 1)`   for   `|G| ≤ k_h`,

which places the partner one rung down rather than `k_h` rungs down, and so supports the rung
spacing `w_m = k_o + (m-1)(k_h-1)`. In the other direction, `|G s| ≤ |s| + (k_h - 1)` is the
one-step bound behind reading `w_m` as the largest weight reachable from weight `k_o` by `m-1`
anticommuting `k_h`-local rotations. The recursion needs only these inequalities; that the weight
`w_m` is actually attained is not formalized. The two-sided statement, that the weight changes by
at most `k - 1` when `G` has weight at most `k`, is one of the consequences of
`apd:eq:pauli_rotation_branch` on which the paper's analysis rests.

The arithmetic is exact rather than estimated. Split the support of `G` by what it does to `s`:

* `cancelSites G s` — `G` and `s` carry the *same* non-identity Pauli, so the site drops out;
* `antiSites G s` — both non-identity and *different*, so the site survives in `G s`;
* `createSites G s` — `G` acts where `s` does not, so the site is new.

These three partition `supp G` (`card_cancelSites_add_card_antiSites_add_card_createSites`), and
separately `|G s| + #cancel = |s| + #create` (`weight_mul_add_card_cancelSites`). So the weight
moves by `#create - #cancel`, and each of those is at most `|G| - #anti`.

The whole of the `-1` is then one observation: `sympForm` counts `antiSites` mod 2
(`sympForm_eq_card_antiSites`), so anticommuting forces `#anti` **odd**, hence non-zero. A pair
that merely *commutes* gets `#anti` even, which may be `0`, and then only the weaker `|G|` is
available — which is why the bound is a statement about the anticommuting branch and not a
general fact about Pauli products.

## Naming

`weight` is `def:pauli_weight`'s `|P|`. `k_h` appears in the corollaries as a variable `kh : ℕ`,
implicit and inferred from the hypothesis `weight G ≤ kh`, so the statements read as they do in
the paper. Bounds of the form `|s| - (k_h - 1) ≤ …` use natural-number subtraction; this is
harmless, because the additive forms (`weight_le_weight_mul_add`, `weight_le_weight_mul_add_kh`)
are proved first and the subtractive ones are derived from them.
-/

public section

namespace Lean4LPD

namespace PauliString

variable {n : ℕ} {G s t : PauliString n} {i : Fin n}

/-! ### Sites -/

/-- The single-qubit Pauli *type* that `s` carries at site `i`, as a pair of bits: `(0,0)` is
identity, `(1,0)` is `X`-type, `(0,1)` is `Z`-type, `(1,1)` is `Y`-type.

These are labels up to phase, which is all the weight needs. At phase zero the `(1,1)` factor is
literally `X Z = −i Y`, not `Y`; which of `Y`, `−Y` or a non-Hermitian multiple it is depends on
the string's global phase, and the weight cannot see that (`weight_phaseMul`). -/
@[expose] def site (s : PauliString n) (i : Fin n) : ZMod 2 × ZMod 2 := (s.x i, s.z i)

@[simp] lemma site_mul (s t : PauliString n) (i : Fin n) :
    site (s * t) i = site s i + site t i := rfl

@[simp] lemma site_one (i : Fin n) : site (1 : PauliString n) i = 0 := rfl

@[simp] lemma site_phaseMul (k : ZMod 4) (s : PauliString n) (i : Fin n) :
    site (phaseMul k s) i = site s i := rfl

/-- **The support** of a Pauli string: the qubits it acts on non-trivially. Defined here as a
`Finset`, since `def:pauli_weight` takes its cardinality.

This is the support of a *single* Pauli string. `def:support` builds the support of a general
operator from it, as the union of the supports of the Pauli strings that carry a non-zero
coefficient. -/
@[expose] def support (s : PauliString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => site s i ≠ 0)

@[simp] lemma mem_support : i ∈ support s ↔ site s i ≠ 0 := by simp [support]

/-- **The weight** `|s|` of a Pauli string, `def:pauli_weight`: the number of
qubits on which it acts non-trivially. -/
@[expose] def weight (s : PauliString n) : ℕ := (support s).card

@[simp] lemma weight_one : weight (1 : PauliString n) = 0 := by
  simp [weight, support]

/-- The weight does not see the phase: it is a function of the bit vectors alone. The partner
Pauli in the proof of `apd:thm:local_flow_k_local` is `±i G s` rather than the bare product
`G s`, and this is why bounding `|G s|` bounds it too. -/
@[simp] lemma weight_phaseMul (k : ZMod 4) (s : PauliString n) :
    weight (phaseMul k s) = weight s := rfl

/-! ### The three kinds of site -/

/-- Sites of `s` that the product `G * s` **cancels**: `G` and `s` carry the same non-identity
Pauli there, so it drops out. -/
def cancelSites (G s : PauliString n) : Finset (Fin n) := support s \ support (G * s)

/-- Sites that `G * s` **creates**: `G` acts there and `s` does not. -/
def createSites (G s : PauliString n) : Finset (Fin n) := support (G * s) \ support s

/-- Sites at which `G` and `s` **locally anticommute**: both act, with different Paulis. -/
def antiSites (G s : PauliString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => site G i ≠ 0 ∧ site s i ≠ 0 ∧ site G i ≠ site s i)

private lemma pair_add_eq_zero_iff {a b : ZMod 2 × ZMod 2} : a + b = 0 ↔ a = b := by
  revert a b; decide

lemma mem_cancelSites : i ∈ cancelSites G s ↔ site s i ≠ 0 ∧ site G i = site s i := by
  simp only [cancelSites, Finset.mem_sdiff, mem_support, site_mul, not_not,
    pair_add_eq_zero_iff]

lemma mem_createSites : i ∈ createSites G s ↔ site G i ≠ 0 ∧ site s i = 0 := by
  simp only [createSites, Finset.mem_sdiff, mem_support, site_mul, not_not]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h2, add_zero] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h2, add_zero]
    exact h1

@[simp] lemma mem_antiSites :
    i ∈ antiSites G s ↔ site G i ≠ 0 ∧ site s i ≠ 0 ∧ site G i ≠ site s i := by
  simp [antiSites]

/-! ### The partition of `supp G` -/

private lemma site_trichotomy (a b : ZMod 2 × ZMod 2) :
    a ≠ 0 ↔ ((b ≠ 0 ∧ a = b) ∨ (a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) ∨ (a ≠ 0 ∧ b = 0)) := by
  revert a b; decide

/-- The three kinds of site exhaust `supp G`. -/
theorem support_eq_union (G s : PauliString n) :
    support G = cancelSites G s ∪ antiSites G s ∪ createSites G s := by
  ext i
  simp only [Finset.mem_union, mem_support, mem_cancelSites, mem_antiSites, mem_createSites]
  rw [site_trichotomy (site G i) (site s i)]
  tauto

private lemma disjoint_cancel_anti (G s : PauliString n) :
    Disjoint (cancelSites G s) (antiSites G s) := by
  rw [Finset.disjoint_left]
  intro i hc ha
  rw [mem_cancelSites] at hc
  rw [mem_antiSites] at ha
  exact ha.2.2 hc.2

private lemma disjoint_union_create (G s : PauliString n) :
    Disjoint (cancelSites G s ∪ antiSites G s) (createSites G s) := by
  rw [Finset.disjoint_left]
  intro i h hcr
  rw [mem_createSites] at hcr
  rcases Finset.mem_union.1 h with hc | ha
  · exact (mem_cancelSites.1 hc).1 hcr.2
  · exact (mem_antiSites.1 ha).2.1 hcr.2

/-- **The site count of `G`.** Every site `G` acts on either cancels a site of `s`, survives as a
locally anticommuting site, or is new. -/
theorem card_cancelSites_add_card_antiSites_add_card_createSites (G s : PauliString n) :
    (cancelSites G s).card + (antiSites G s).card + (createSites G s).card = weight G := by
  rw [weight, support_eq_union G s,
    Finset.card_union_of_disjoint (disjoint_union_create G s),
    Finset.card_union_of_disjoint (disjoint_cancel_anti G s)]

/-- **The weight bookkeeping.** Cancelled sites are exactly what `s` loses and created sites
exactly what it gains, so the weight moves by `#create - #cancel`. -/
theorem weight_mul_add_card_cancelSites (G s : PauliString n) :
    weight (G * s) + (cancelSites G s).card = weight s + (createSites G s).card := by
  have h1 : (cancelSites G s).card + weight (G * s)
      = (support s ∪ support (G * s)).card :=
    Finset.card_sdiff_add_card _ _
  have h2 : (createSites G s).card + weight s
      = (support (G * s) ∪ support s).card :=
    Finset.card_sdiff_add_card _ _
  rw [Finset.union_comm] at h2
  omega

/-! ### The symplectic form counts locally anticommuting sites -/

private lemma site_symp (a b : ZMod 2 × ZMod 2) :
    a.1 * b.2 + a.2 * b.1 = if a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b then 1 else 0 := by
  revert a b; decide

/-- **`⟪G,s⟫` is `#antiSites` modulo two.** This is what turns a parity statement into a counting
statement, and it is the whole source of the `-1` in `|G s| ≥ |s| - (k_h - 1)`. -/
theorem sympForm_eq_card_antiSites (G s : PauliString n) :
    sympForm G s = ((antiSites G s).card : ZMod 2) := by
  rw [sympForm_eq_sum]
  have : ∀ i : Fin n, G.x i * s.z i + G.z i * s.x i
      = if site G i ≠ 0 ∧ site s i ≠ 0 ∧ site G i ≠ site s i then (1 : ZMod 2) else 0 :=
    fun i => site_symp (site G i) (site s i)
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_boole]
  rfl

/-- Anticommuting Pauli strings share at least one site at which they locally anticommute. -/
theorem one_le_card_antiSites (h : sympForm G s = 1) : 1 ≤ (antiSites G s).card := by
  rcases Nat.eq_zero_or_pos (antiSites G s).card with hz | hp
  · rw [sympForm_eq_card_antiSites, hz] at h
    exact absurd h (by decide)
  · exact hp

/-- A Pauli string that anticommutes with something is not a phase: it acts on at least one
qubit. -/
theorem one_le_weight_of_sympForm_eq_one (h : sympForm G s = 1) : 1 ≤ weight G :=
  le_trans (one_le_card_antiSites h)
    (by have := card_cancelSites_add_card_antiSites_add_card_createSites G s; omega)

/-! ### The general bound, and why the sharp one needs anticommutation -/

/-- Without any hypothesis only `|G|` is available: the weight can move by up to the full weight of
`G` in either direction. -/
theorem weight_mul_le (G s : PauliString n) : weight (G * s) ≤ weight s + weight G := by
  have hb := weight_mul_add_card_cancelSites G s
  have hp := card_cancelSites_add_card_antiSites_add_card_createSites G s
  omega

/-- The companion lower bound, again with no hypothesis. -/
theorem weight_le_weight_mul_add_weight (G s : PauliString n) :
    weight s ≤ weight (G * s) + weight G := by
  have hb := weight_mul_add_card_cancelSites G s
  have hp := card_cancelSites_add_card_antiSites_add_card_createSites G s
  omega

/-- **The anticommutation hypothesis cannot be dropped.** For the *commuting* pair `G = X₁X₂`,
`s = Z₃` on three qubits, the supports are disjoint, so `|G s| = 3 = |s| + |G|` and the sharp
bound `|G s| ≤ |s| + (|G| - 1) = 2` fails.

This is why `weight_mul_le_weight_add` carries `sympForm G s = 1` and why the general statement
`weight_mul_le` is the best available without it. It is also why "a `k_h`-local rotation
increases the weight by at most `k_h - 1`" is a statement about *anticommuting* rotations. A
commuting rotation leaves the Pauli operator unchanged (`pauli_rotation_branch_commute` in
`Pauli/Branch.lean`), so the bare product `G s` never arises in that branch and its weight is
irrelevant there. -/
theorem exists_commuting_weight_increase_by_full_weight :
    ∃ G s : PauliString 3,
      sympForm G s = 0 ∧ weight G = 2 ∧ weight s = 1 ∧ weight (G * s) = 3 :=
  ⟨⟨![1, 1, 0], 0, 0⟩, ⟨0, ![0, 0, 1], 0⟩, by decide, by decide, by decide, by decide⟩

/-! ### The weight bound -/

/-- At most `|G| - 1` sites of `s` can be cancelled by an anticommuting `G`. -/
theorem card_cancelSites_le (h : sympForm G s = 1) :
    (cancelSites G s).card ≤ weight G - 1 := by
  have hp := card_cancelSites_add_card_antiSites_add_card_createSites G s
  have ha := one_le_card_antiSites h
  omega

/-- At most `|G| - 1` new sites can be created by an anticommuting `G`. -/
theorem card_createSites_le (h : sympForm G s = 1) :
    (createSites G s).card ≤ weight G - 1 := by
  have hp := card_cancelSites_add_card_antiSites_add_card_createSites G s
  have ha := one_le_card_antiSites h
  omega

/-- **The lower half**, `|G s| ≥ |s| - (|G| - 1)` in the form that avoids truncated subtraction.
This is the direction the proof of `apd:thm:local_flow_k_local` uses. -/
theorem weight_le_weight_mul_add (h : sympForm G s = 1) :
    weight s ≤ weight (G * s) + (weight G - 1) := by
  have hb := weight_mul_add_card_cancelSites G s
  have hc := card_cancelSites_le h
  omega

/-- **The upper half**, `|G s| ≤ |s| + (|G| - 1)`. This is the direction behind the rung spacing
`w_m = k_o + (m-1)(k_h-1)`: applied `m - 1` times, it bounds by `w_m` the weight reachable from
weight `k_o` by anticommuting `k_h`-local rotations. That `w_m` is *attained* is not
formalized. -/
theorem weight_mul_le_weight_add (h : sympForm G s = 1) :
    weight (G * s) ≤ weight s + (weight G - 1) := by
  have hb := weight_mul_add_card_cancelSites G s
  have hc := card_createSites_le h
  omega

/-- **The two-sided weight bound**: an anticommuting generator of weight `|G|` changes the weight
of `s` by at most `|G| - 1`. Stated over `ℤ` so that no truncated subtraction is hiding in it.

The bound is in terms of the actual weight `|G|`, which is slightly stronger than the paper's
statement in terms of a locality parameter `k ≥ |G|` (the weight changes by at most `k - 1`, one
of the consequences drawn from `apd:eq:pauli_rotation_branch`). The parameterized forms are the
`k_h` corollaries `weight_sub_le_weight_mul` and `weight_mul_le_weight_add_kh` below, which follow
from the two halves above. -/
theorem abs_weight_mul_sub_weight_le (h : sympForm G s = 1) :
    |(weight (G * s) : ℤ) - (weight s : ℤ)| ≤ (weight G : ℤ) - 1 := by
  have h1 := weight_le_weight_mul_add h
  have h2 := weight_mul_le_weight_add h
  have h3 := one_le_weight_of_sympForm_eq_one h
  rw [abs_le]
  omega

/-! ### The `k_h` form the ladder consumes -/

variable {kh : ℕ}

/-- `|s| ≤ |G s| + (k_h - 1)` for `|G| ≤ k_h`: the lower bound on the partner's weight used in
the proof of `apd:thm:local_flow_k_local`, in additive form. -/
theorem weight_le_weight_mul_add_kh (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight s ≤ weight (G * s) + (kh - 1) := by
  have := weight_le_weight_mul_add h
  omega

/-- **`|G s| ≥ |s| - (k_h - 1)`** — the same bound in subtractive form, which is where the proof
of `apd:thm:local_flow_k_local` places the partner Pauli one rung down rather than `k_h` rungs
down. The natural-number subtraction is harmless: when `|s| < k_h - 1` the left-hand side is `0`
and the bound is trivially true, and otherwise it is the additive form rearranged. -/
theorem weight_sub_le_weight_mul (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight s - (kh - 1) ≤ weight (G * s) := by
  have := weight_le_weight_mul_add_kh hk h
  omega

/-- The same bound for the Hermitian partner `i G s`. In the proof of
`apd:thm:local_flow_k_local` a high-weight Pauli `s` is connected to its partner `i G s`, not to
the bare product `G s`. The two have the same weight, because the weight cannot see a phase
(`weight_phaseMul`), so this is `weight_sub_le_weight_mul` restated for the object the proof
actually uses. -/
theorem weight_sub_le_weight_phaseMul_one_mul (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight s - (kh - 1) ≤ weight (phaseMul 1 (G * s)) := by
  rw [weight_phaseMul]
  exact weight_sub_le_weight_mul hk h

/-- `|G s| ≤ |s| + (k_h - 1)` for `|G| ≤ k_h` — the direction that fixes the rung spacing
`w_m = k_o + (m-1)(k_h-1)` of `apd:thm:local_flow_k_local`. -/
theorem weight_mul_le_weight_add_kh (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight (G * s) ≤ weight s + (kh - 1) := by
  have := weight_mul_le_weight_add h
  omega

end PauliString

end Lean4LPD
