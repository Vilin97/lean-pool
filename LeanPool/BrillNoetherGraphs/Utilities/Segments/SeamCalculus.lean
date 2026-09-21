/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.EdgeAddition

/-!
# The seam displacement calculus

Fix a graph `H`, two marks `x ≠ y`, the *seam divisor* `α = (x) - (y)`
(`seamDivisor`, from `EdgeAddition.lean`), and a base divisor `C`.  For `m : ℤ`
the *`m`-twist* is `C + m • α` (`seamTwist`).  A firing script `f : V → ℤ` acts
on divisors through `prin H f` (the note's `Δf`), and its *displacement* is
`t(f) = f x - f y` (`displacement`).  The displacement set of the `m`-twist is

  `d(A_m) = { t(f) : C + m • α + Δf ≥ 0 }`   (`IsDisplacement`).

The *junction class* of the pair `m | m+1` is
`ξ_m = [C + m•α - (y)] = [C + (m+1)•α - (x)]` (`junction`), and the junction
*has a gap* when every displacement of the `(m+1)`-twist strictly exceeds every
displacement of the `m`-twist (`HasGap`).  The main theorem, `hasGap_iff`, is
Theorem C together with Theorem C′ of §5/§12:

  `HasGap C x y m  ↔  ¬ winnable H (junction C x y m)`.

## Index of the main results

* `script_min_at_of_qReduced` — the master lemma (level-set firing).
* `script_const_of_prin_eq_zero`, `displacement_eq_of_prin_eq` — `t` is well
  defined on representatives (uses connectedness).
* `winnable_sub_one_chip_iff_of_qReduced` — the chip test for reduced divisors.
* `isMaxDisplacement_of_qReduced_y`, `isMinDisplacement_of_qReduced_x` —
  Proposition 1, extremal half: `b_m` is attained at the `y`-reduced
  representative, `a_m` at the `x`-reduced one.
* `isDisplacement_succ_of_junction_winnable`,
  `isDisplacement_succ_of_isMaxDisplacement` — Theorem C.
* `isDisplacement_pred_of_junction_winnable`,
  `isDisplacement_of_isMinDisplacement_succ` — Theorem C from the `x`-side
  (the same junction class controls the junction from both sides).
* `le_displacement_of_qReduced_succ`, `exists_isDisplacement_succ_ge`,
  `isMaxDisplacement_mono`, `exists_isDisplacement_le` — Lemma M.
* `lt_script_of_qReduced_no_chip`, `hasGap_of_junction_not_winnable` —
  Theorem C′, and `hasGap_iff` for the equivalence.
* `not_hasGap_of_rank_pos` — Corollary C1.

## Phase-0 API survey (`.lake/packages/chip-firing-with-lean`)

What the library **has** (all of it used below):

* `CFDiv G = G.V → ℤ`, `one_chip v`, `effective D = ∀ v, D v ≥ 0`, `deg`,
  `winnable G D`, `linear_equiv G D D'`, `principal_divisors G`
  (`ChipFiringWithLean.Basic`).
* Firing scripts as plain functions: `firing_script G = G.V → ℤ` together with
  the additive map `prin G : firing_script G →+ CFDiv G`, given by
  `prin G σ v = ∑ u, (σ u - σ v) * num_edges G v u`.  This **is** the `Δ` of
  the note (the negative of the Laplacian action; see the docstring of `prin`).
  `principal_iff_eq_prin` identifies `principal_divisors` with the image of
  `prin`.  There is also `firing_vector`, `set_firing`, `laplacian_matrix`,
  `apply_laplacian`, none of which are needed here.
* `q_reduced G q D`: `q_effective q D` together with "every nonempty
  `S ⊆ V ∖ {q}` contains a vertex `v` with
  `D v < ∑ w ∉ S, num_edges G v w`" — i.e. no `q`-avoiding set is legal.
* `exists_q_reduced_representative` and `unique_q_reduced` (both need
  `graph_connected`), `q_reduced_unique`, `qReducedRep` (`RRGHelpers`),
  `winnable_iff_q_reduced_effective`, `effective_of_winnable_and_q_reduced`.
* `winnable_equiv_winnable`, `winnable_of_effective`, `rank`, `rank_geq_iff`,
  `rank_nonneg_iff_winnable`, Riemann–Roch.
* `seamDivisor x y = one_chip x - one_chip y` (`Utilities.EdgeAddition`).

What the library **lacks**, and how it is handled here:

* **Dhar's algorithm as a certified firing path.**  `Algorithms.lean` defines
  `dhar_outdeg`, `dharBurningSet`, `findQReducedDivisor`, `dhar`, `burn`, but
  proves *nothing* about them: there is no lemma "every effective divisor
  reaches its `q`-reduced representative by a finite sequence of legal
  `q`-avoiding firings".  Consequently the *interval* half of Proposition 1 of
  the note ("every intermediate displacement is attained") is **not**
  formalized here.  Nothing below needs it: the extremal half of Proposition 1,
  Lemma M, Theorem C and Theorem C′ are all proved by direct level-set
  (threshold-firing) arguments, unconditionally.
* **Level sets of a script.**  `Basic.lean` contains a `private lemma
  maxset_of_script` with exactly the required inequality, but it is private and
  hard-wired to one particular level set.  It is re-proved here as `topSet`,
  `prin_le_neg_outdeg_S`, and the `botSet` mirror `outdeg_S_le_prin`.
* **"A `q`-reduced `D` satisfies `D q ≥ 1` iff `[D] - (q)` is effective".**
  Absent; proved here as `winnable_sub_one_chip_iff_of_qReduced`.
* **"Two scripts with the same principal divisor differ by a constant".**
  Absent (only the connectivity-free `q_reducer` shadow, which is private);
  proved here as `script_const_of_prin_eq_zero`.
* ℚ-valued potentials and effective resistance: absent.  Theorems B and D of
  the note need them and are deliberately not attempted.

**No `sorry`, no new axioms, no stated-but-unproved hypotheses:** every result
below is proved outright from the library's API.
-/

open Finset

namespace Utilities

variable {H : CFGraph}

/-! ## Pointwise lemmas for chips and seams -/

lemma one_chip_self (v : H.V) : (one_chip v : CFDiv H) v = 1 := by
  simp [one_chip]

lemma sub_one_chip_apply_self (D : CFDiv H) (q : H.V) :
    (D - one_chip q) q = D q - 1 := by
  simp only [Pi.sub_apply, one_chip_self]

lemma sub_one_chip_apply_of_ne (D : CFDiv H) {q v : H.V} (h : v ≠ q) :
    (D - one_chip q) v = D v := by
  simp [one_chip, h]

lemma seamDivisor_apply_of_ne {x y v : H.V} (hvx : v ≠ x) (hvy : v ≠ y) :
    seamDivisor x y v = 0 := by
  simp [seamDivisor, one_chip, hvx, hvy]

lemma seamDivisor_apply_left {x y : H.V} (hxy : x ≠ y) :
    seamDivisor x y x = 1 := by
  simp [seamDivisor, one_chip, hxy]

lemma seamDivisor_apply_right {x y : H.V} (hxy : x ≠ y) :
    seamDivisor x y y = -1 := by
  simp [seamDivisor, one_chip, hxy.symm]

/-- Away from `y` the seam divisor is nonnegative. -/
lemma seamDivisor_nonneg_of_ne_right (x y : H.V) {w : H.V} (hw : w ≠ y) :
    0 ≤ seamDivisor x y w := by
  by_cases hwx : w = x
  · subst w
    simp [seamDivisor, one_chip, hw]
  · simp [seamDivisor_apply_of_ne hwx hw]

/-! ## Level sets of a firing script

The `argmax` level set `topSet g` and its mirror `botSet g = topSet (-g)`.
One fact drives the whole calculus: at a vertex of `topSet g` the script `g`
removes at least the out-degree of the level set (`prin_le_neg_outdeg_S`), so
a level set avoiding `q` is a legal firing set and therefore certifies
non-`q`-reducedness.
-/

/-- The set of vertices where a firing script attains its maximum. -/
def topSet (g : firing_script H) : Finset H.V :=
  Finset.univ.filter (fun v => ∀ u, g u ≤ g v)

/-- The set of vertices where a firing script attains its minimum. -/
def botSet (g : firing_script H) : Finset H.V := topSet (-g)

lemma mem_topSet {g : firing_script H} {v : H.V} :
    v ∈ topSet g ↔ ∀ u, g u ≤ g v := by
  simp [topSet]

lemma mem_botSet {g : firing_script H} {v : H.V} :
    v ∈ botSet g ↔ ∀ u, g v ≤ g u := by
  rw [botSet, mem_topSet]
  constructor
  · intro h u
    have := h u
    simp only [Pi.neg_apply] at this
    omega
  · intro h u
    have := h u
    simp only [Pi.neg_apply]
    omega

lemma topSet_nonempty (g : firing_script H) : (topSet g).Nonempty := by
  obtain ⟨v, hv⟩ := Finite.exists_max g
  exact ⟨v, mem_topSet.mpr hv⟩

lemma botSet_nonempty (g : firing_script H) : (botSet g).Nonempty :=
  topSet_nonempty _

/-- Outside the `argmax` level set the script is *strictly* smaller. -/
lemma lt_of_not_mem_topSet {g : firing_script H} {v u : H.V}
    (hv : v ∈ topSet g) (hu : u ∉ topSet g) : g u < g v := by
  rcases lt_or_eq_of_le (mem_topSet.mp hv u) with h | h
  · exact h
  · exact absurd (mem_topSet.mpr fun w => le_of_le_of_eq (mem_topSet.mp hv w) h.symm) hu

/-- **The level-set inequality.**  Firing a script whose maximum is attained at
`v` costs `v` at least its out-degree from the maximal level set. -/
lemma prin_le_neg_outdeg_S {g : firing_script H} {v : H.V} (hv : v ∈ topSet g) :
    prin H g v ≤ - outdeg_S H (topSet g) v := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset H.V)
      (fun z => z ∉ topSet g) (fun u => (g u - g v) * (num_edges H v u : ℤ))
  have h1 : ∑ u ∈ Finset.univ.filter (fun z => z ∉ topSet g),
        (g u - g v) * (num_edges H v u : ℤ)
      ≤ ∑ u ∈ Finset.univ.filter (fun z => z ∉ topSet g), (-(num_edges H v u : ℤ)) := by
    refine Finset.sum_le_sum fun u hu => ?_
    have hu' : u ∉ topSet g := (Finset.mem_filter.mp hu).2
    have hlt : g u - g v ≤ -1 := by
      have := lt_of_not_mem_topSet hv hu'
      omega
    calc (g u - g v) * (num_edges H v u : ℤ)
        ≤ (-1) * (num_edges H v u : ℤ) :=
          mul_le_mul_of_nonneg_right hlt (Int.natCast_nonneg _)
      _ = -(num_edges H v u : ℤ) := by ring
  have h2 : ∑ u ∈ Finset.univ.filter (fun z => ¬ (z ∉ topSet g)),
        (g u - g v) * (num_edges H v u : ℤ) ≤ 0 := by
    refine Finset.sum_nonpos fun u _ => ?_
    exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (mem_topSet.mp hv u)) (Int.natCast_nonneg _)
  have h3 : ∑ u ∈ Finset.univ.filter (fun z => z ∉ topSet g), (-(num_edges H v u : ℤ))
      = - outdeg_S H (topSet g) v := by
    rw [outdeg_S_eq_sum_filter]
    simp
  rw [prin_apply, ← hsplit]
  linarith

/-- The `argmin` mirror of `prin_le_neg_outdeg_S`. -/
lemma outdeg_S_le_prin {g : firing_script H} {v : H.V} (hv : v ∈ botSet g) :
    outdeg_S H (botSet g) v ≤ prin H g v := by
  have h := prin_le_neg_outdeg_S (g := -g) hv
  rw [map_neg] at h
  simp only [Pi.neg_apply] at h
  have hbot : botSet g = topSet (-g) := rfl
  rw [hbot]
  omega

/-- **Connectivity ⇒ the kernel of `Δ` consists of the constant scripts.** -/
lemma script_const_of_prin_eq_zero (hconn : graph_connected H)
    {g : firing_script H} (h : prin H g = 0) (u v : H.V) : g u = g v := by
  have hall : ∀ w : H.V, w ∈ topSet g := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := hcon
    obtain ⟨z, hz⟩ := topSet_nonempty g
    obtain ⟨a, haS, b, hbS, hab⟩ := hconn (topSet g) ⟨z, w, hz, hw⟩
    have h1 : prin H g a ≤ - outdeg_S H (topSet g) a := prin_le_neg_outdeg_S haS
    have h2 : (num_edges H a b : ℤ) ≤ outdeg_S H (topSet g) a := by
      unfold outdeg_S
      refine Finset.single_le_sum (f := fun w => (num_edges H a w : ℤ))
        (fun i _ => Int.natCast_nonneg _) ?_
      simpa using hbS
    have h3 : prin H g a = 0 := by rw [h]; rfl
    have h4 : 0 < (num_edges H a b : ℤ) := by exact_mod_cast hab
    omega
  have hu := mem_topSet.mp (hall u) v
  have hv := mem_topSet.mp (hall v) u
  omega

/-! ## `q`-reduced divisors: the chip test

A `q`-reduced divisor stays `q`-reduced after a chip is removed at `q`, which
converts "the class minus `(q)` is effective" into the pointwise test `D q ≥ 1`.
-/

lemma q_reduced_sub_one_chip {q : H.V} {D : CFDiv H} (h : q_reduced H q D) :
    q_reduced H q (D - one_chip q) := by
  refine ⟨fun v hv => ?_, fun S hS hne => ?_⟩
  · rw [sub_one_chip_apply_of_ne D hv]
    exact h.1 v hv
  · intro hLegal
    apply h.2 S hS hne
    intro v hvS
    have hvq : v ≠ q := fun hvq => hS (hvq ▸ hvS)
    have hv := hLegal v hvS
    rw [sub_one_chip_apply_of_ne D hvq] at hv
    exact hv

/-- **The chip test.**  For a `q`-reduced divisor `D`, the class `[D] - (q)` is
effective exactly when `D` already carries a chip at `q`. -/
lemma winnable_sub_one_chip_iff_of_qReduced {q : H.V} {D : CFDiv H}
    (h : q_reduced H q D) : winnable H (D - one_chip q) ↔ 1 ≤ D q := by
  constructor
  · intro hw
    have heff := effective_of_winnable_and_q_reduced H q _ hw (q_reduced_sub_one_chip h)
    have hq := heff q
    rw [sub_one_chip_apply_self] at hq
    omega
  · intro hq
    refine winnable_of_effective H _ fun v => ?_
    by_cases hv : v = q
    · subst v
      rw [sub_one_chip_apply_self]
      omega
    · rw [sub_one_chip_apply_of_ne D hv]
      exact h.1 v hv

/-! ## Scripts, twists and displacements -/

/-- The `m`-th seam twist `C + m • α` of the base divisor `C`. -/
def seamTwist (C : CFDiv H) (x y : H.V) (m : ℤ) : CFDiv H :=
  C + m • seamDivisor x y

/-- The displacement `t(f) = f x - f y` of a firing script. -/
def displacement (x y : H.V) (f : firing_script H) : ℤ := f x - f y

/-- `t` is a displacement of the `m`-twist: some script puts the `m`-twist into
effective position with displacement `t`. -/
def IsDisplacement (C : CFDiv H) (x y : H.V) (m t : ℤ) : Prop :=
  ∃ f : firing_script H,
    effective (seamTwist C x y m + prin H f) ∧ displacement x y f = t

/-- The displacement set `d(A_m)` of the `m`-twist. -/
def displacementSet (C : CFDiv H) (x y : H.V) (m : ℤ) : Set ℤ :=
  {t | IsDisplacement C x y m t}

@[simp] lemma mem_displacementSet {C : CFDiv H} {x y : H.V} {m t : ℤ} :
    t ∈ displacementSet C x y m ↔ IsDisplacement C x y m t := Iff.rfl

/-- `t` is the largest displacement of the `m`-twist (`b_m` of the note). -/
def IsMaxDisplacement (C : CFDiv H) (x y : H.V) (m t : ℤ) : Prop :=
  IsDisplacement C x y m t ∧ ∀ s, IsDisplacement C x y m s → s ≤ t

/-- `t` is the smallest displacement of the `m`-twist (`a_m` of the note). -/
def IsMinDisplacement (C : CFDiv H) (x y : H.V) (m t : ℤ) : Prop :=
  IsDisplacement C x y m t ∧ ∀ s, IsDisplacement C x y m s → t ≤ s

/-- The junction class `ξ_m = [C + m•α - (y)]` of the pair `m | m+1`. -/
def junction (C : CFDiv H) (x y : H.V) (m : ℤ) : CFDiv H :=
  seamTwist C x y m - one_chip y

/-- A constant script has zero displacement. -/
@[simp] lemma displacement_const (x y : H.V) (c : ℤ) :
    displacement x y (fun _ : H.V => c) = 0 := by
  simp [displacement]

lemma seamTwist_succ (C : CFDiv H) (x y : H.V) (m : ℤ) :
    seamTwist C x y (m + 1) = seamTwist C x y m + seamDivisor x y := by
  simp only [seamTwist, add_smul, one_smul]
  abel

/-- The junction class seen from the right: `ξ_m = [C + (m+1)•α - (x)]`. -/
lemma junction_eq_succ_sub_x (C : CFDiv H) (x y : H.V) (m : ℤ) :
    junction C x y m = seamTwist C x y (m + 1) - one_chip x := by
  rw [junction, seamTwist_succ, seamDivisor]
  abel

/-! ### Displacement is well defined on representatives -/

lemma linear_equiv_add_prin (D : CFDiv H) (f : firing_script H) :
    linear_equiv H D (D + prin H f) := by
  have hdiff : D + prin H f - D = prin H f := by abel
  exact (principal_iff_eq_prin H _).mpr ⟨f, hdiff⟩

lemma winnable_add_prin_iff (D : CFDiv H) (f : firing_script H) :
    winnable H (D + prin H f) ↔ winnable H D := by
  constructor
  · exact fun h => winnable_equiv_winnable H _ _ h (linear_equiv_add_prin D f).symm
  · exact fun h => winnable_equiv_winnable H _ _ h (linear_equiv_add_prin D f)

/-- **`t` is well defined on representatives.**  On a connected graph two
scripts with the same principal divisor differ by a constant, hence have the
same displacement. -/
theorem displacement_eq_of_prin_eq (hconn : graph_connected H) (x y : H.V)
    {f f' : firing_script H} (h : prin H f = prin H f') :
    displacement x y f = displacement x y f' := by
  have hzero : prin H (f - f') = 0 := by
    rw [map_sub, h, sub_self]
  have hx := script_const_of_prin_eq_zero hconn hzero x y
  simp only [Pi.sub_apply] at hx
  simp only [displacement]
  omega

/-- Hence the displacement attached to an effective representative of a twist
depends only on the representative. -/
theorem displacement_eq_of_div_eq (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (m : ℤ) {f f' : firing_script H}
    (h : seamTwist C x y m + prin H f = seamTwist C x y m + prin H f') :
    displacement x y f = displacement x y f' :=
  displacement_eq_of_prin_eq hconn x y (by
    have := congrArg (fun D => D - seamTwist C x y m) h
    simpa using this)

/-- Non-vacuity: an effective base divisor has displacement `0` at twist `0`. -/
lemma isDisplacement_zero_of_effective (C : CFDiv H) (x y : H.V)
    (hC : effective C) : IsDisplacement C x y 0 0 := by
  refine ⟨0, ?_, by simp [displacement]⟩
  have h : seamTwist C x y 0 + prin H 0 = C := by
    rw [seamTwist, zero_smul, map_zero, add_zero, add_zero]
  rw [h]
  exact hC

lemma winnable_of_isDisplacement {C : CFDiv H} {x y : H.V} {m t : ℤ}
    (h : IsDisplacement C x y m t) : winnable H (seamTwist C x y m) := by
  obtain ⟨f, heff, _⟩ := h
  exact (winnable_add_prin_iff _ f).mp (winnable_of_effective H _ heff)

/-- Every winnable divisor has a `q`-reduced effective representative, presented
as an explicit script. -/
lemma exists_qReduced_script (hconn : graph_connected H) (q : H.V) (A : CFDiv H)
    (hw : winnable H A) :
    ∃ f : firing_script H,
      effective (A + prin H f) ∧ q_reduced H q (A + prin H f) := by
  obtain ⟨D', hequiv, hred, heff⟩ := (winnable_iff_q_reduced_effective hconn q A).mp hw
  obtain ⟨f, hf⟩ := (principal_iff_eq_prin H (D' - A)).mp hequiv
  have hAf : A + prin H f = D' := by rw [← hf]; abel
  exact ⟨f, by rw [hAf]; exact heff, by rw [hAf]; exact hred⟩

/-! ## The master lemma

Everything below rests on one statement: if a `q`-reduced divisor is reached
from an effective divisor by adding a divisor that is nonnegative off `q` and
then firing a script `g`, then `g` attains its minimum at `q`.
-/

/-- **Master lemma.**  Let `D` be effective, let `β` be nonnegative away from
`q`, and suppose `D + β + Δg` is `q`-reduced.  Then `g` is minimized at `q`. -/
theorem script_min_at_of_qReduced (q : H.V) (D β : CFDiv H) (g : firing_script H)
    (hD : effective D) (hβ : ∀ w, w ≠ q → 0 ≤ β w)
    (hred : q_reduced H q (D + β + prin H g)) :
    ∀ w, g q ≤ g w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w₀, hw₀⟩ := hcon
  have hq : q ∉ botSet g := fun hmem => absurd (mem_botSet.mp hmem w₀) (not_le.mpr hw₀)
  obtain ⟨v, hvT, hlt⟩ := hred.exists_lt_outdeg hq (botSet_nonempty g)
  have hlt' : (D + β + prin H g) v < outdeg_S H (botSet g) v := hlt
  have hvq : v ≠ q := by rintro rfl; exact hq hvT
  have h1 : outdeg_S H (botSet g) v ≤ prin H g v := outdeg_S_le_prin hvT
  have h2 : (D + β + prin H g) v = D v + β v + prin H g v := rfl
  have h3 := hD v
  have h4 := hβ v hvq
  rw [h2] at hlt'
  omega

/-! ## Proposition 1 (extremal half): the reduced representatives are extremal

The `y`-reduced representative maximizes the displacement, the `x`-reduced one
minimizes it.  (The other half of Proposition 1 of the note — that every
intermediate integer is attained, so that `d(A_m)` is an *interval* — requires
the Dhar reduction path, which the library does not certify.  It is not used
anywhere below.)
-/

/-- The `y`-reduced effective representative attains the maximal displacement. -/
theorem isMaxDisplacement_of_qReduced_y (C : CFDiv H) (x y : H.V) (m : ℤ)
    {f : firing_script H}
    (heff : effective (seamTwist C x y m + prin H f))
    (hred : q_reduced H y (seamTwist C x y m + prin H f)) :
    IsMaxDisplacement C x y m (displacement x y f) := by
  refine ⟨⟨f, heff, rfl⟩, ?_⟩
  rintro s ⟨f', heff', rfl⟩
  have hkey : seamTwist C x y m + prin H f
      = (seamTwist C x y m + prin H f') + 0 + prin H (f - f') := by
    rw [map_sub]
    abel
  have hmin := script_min_at_of_qReduced y _ 0 (f - f') heff' (fun _ _ => le_refl 0)
    (by rw [← hkey]; exact hred)
  have hx := hmin x
  simp only [Pi.sub_apply] at hx
  simp only [displacement]
  omega

/-- The `x`-reduced effective representative attains the minimal displacement. -/
theorem isMinDisplacement_of_qReduced_x (C : CFDiv H) (x y : H.V) (m : ℤ)
    {f : firing_script H}
    (heff : effective (seamTwist C x y m + prin H f))
    (hred : q_reduced H x (seamTwist C x y m + prin H f)) :
    IsMinDisplacement C x y m (displacement x y f) := by
  refine ⟨⟨f, heff, rfl⟩, ?_⟩
  rintro s ⟨f', heff', rfl⟩
  have hkey : seamTwist C x y m + prin H f
      = (seamTwist C x y m + prin H f') + 0 + prin H (f - f') := by
    rw [map_sub]
    abel
  have hmin := script_min_at_of_qReduced x _ 0 (f - f') heff' (fun _ _ => le_refl 0)
    (by rw [← hkey]; exact hred)
  have hy := hmin y
  simp only [Pi.sub_apply] at hy
  simp only [displacement]
  omega

/-- A winnable twist has a maximal displacement. -/
theorem exists_isMaxDisplacement (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (m : ℤ) (hw : winnable H (seamTwist C x y m)) :
    ∃ b, IsMaxDisplacement C x y m b := by
  obtain ⟨f, heff, hred⟩ := exists_qReduced_script hconn y _ hw
  exact ⟨_, isMaxDisplacement_of_qReduced_y C x y m heff hred⟩

/-- A winnable twist has a minimal displacement. -/
theorem exists_isMinDisplacement (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (m : ℤ) (hw : winnable H (seamTwist C x y m)) :
    ∃ a, IsMinDisplacement C x y m a := by
  obtain ⟨f, heff, hred⟩ := exists_qReduced_script hconn x _ hw
  exact ⟨_, isMinDisplacement_of_qReduced_x C x y m heff hred⟩

lemma IsMaxDisplacement.unique {C : CFDiv H} {x y : H.V} {m b b' : ℤ}
    (h : IsMaxDisplacement C x y m b) (h' : IsMaxDisplacement C x y m b') :
    b = b' :=
  le_antisymm (h'.2 _ h.1) (h.2 _ h'.1)

lemma IsMinDisplacement.unique {C : CFDiv H} {x y : H.V} {m a a' : ℤ}
    (h : IsMinDisplacement C x y m a) (h' : IsMinDisplacement C x y m a') :
    a = a' :=
  le_antisymm (h.2 _ h'.1) (h'.2 _ h.1)

/-! ## Theorem C: an effective junction class kills the gap -/

/-- The junction class `ξ_m` is effective iff the `y`-reduced representative of
the `m`-twist carries a chip at `y`. -/
theorem junction_winnable_iff_chip (C : CFDiv H) (x y : H.V) (m : ℤ)
    {f : firing_script H}
    (hred : q_reduced H y (seamTwist C x y m + prin H f)) :
    winnable H (junction C x y m) ↔ 1 ≤ (seamTwist C x y m + prin H f) y := by
  rw [← winnable_sub_one_chip_iff_of_qReduced hred]
  have hshift : seamTwist C x y m + prin H f - one_chip y
      = junction C x y m + prin H f := by
    rw [junction]; abel
  rw [hshift, winnable_add_prin_iff]

/-- **Theorem C (forward form).**  If the junction class `ξ_m` is effective then
the `y`-reduced effective representative of the `m`-twist, translated by the
seam, is an effective representative of the `(m+1)`-twist *with the same
script* — hence with the same displacement. -/
theorem isDisplacement_succ_of_junction_winnable (C : CFDiv H) (x y : H.V)
    (hxy : x ≠ y) (m : ℤ) {f : firing_script H}
    (heff : effective (seamTwist C x y m + prin H f))
    (hred : q_reduced H y (seamTwist C x y m + prin H f))
    (hjun : winnable H (junction C x y m)) :
    IsDisplacement C x y (m + 1) (displacement x y f) := by
  have hchip := (junction_winnable_iff_chip C x y m hred).mp hjun
  refine ⟨f, ?_, rfl⟩
  intro v
  have hval : (seamTwist C x y (m + 1) + prin H f) v
      = (seamTwist C x y m + prin H f) v + seamDivisor x y v := by
    rw [seamTwist_succ]
    simp only [Pi.add_apply]
    ring
  rw [hval]
  by_cases hvy : v = y
  · subst v
    rw [seamDivisor_apply_right hxy]
    omega
  · have h1 := heff v
    have h2 := seamDivisor_nonneg_of_ne_right x y hvy
    omega

/-- **Theorem C, packaged.**  If the junction class is effective then the
maximal displacement of the `m`-twist is again a displacement of the
`(m+1)`-twist; in particular `b_{m+1} ≥ b_m`, i.e. `gap_m ≤ 0`. -/
theorem isDisplacement_succ_of_isMaxDisplacement (hconn : graph_connected H)
    (C : CFDiv H) (x y : H.V) (hxy : x ≠ y) (m b : ℤ)
    (hb : IsMaxDisplacement C x y m b)
    (hjun : winnable H (junction C x y m)) :
    IsDisplacement C x y (m + 1) b := by
  obtain ⟨f, heff, hred⟩ :=
    exists_qReduced_script hconn y _ (winnable_of_isDisplacement hb.1)
  have hmax := isMaxDisplacement_of_qReduced_y C x y m heff hred
  have hbf : b = displacement x y f := hb.unique hmax
  rw [hbf]
  exact isDisplacement_succ_of_junction_winnable C x y hxy m heff hred hjun

/-! ## Lemma M: monotonicity of the displacement interval -/

/-- **Lemma M (`b`-side, non-strict).**  Every displacement of the `m`-twist is
at most the displacement of the `y`-reduced representative of the
`(m+1)`-twist.  Equivalently `b_m ≤ b_{m+1}`. -/
theorem le_displacement_of_qReduced_succ (C : CFDiv H) (x y : H.V) (m : ℤ)
    {f f' : firing_script H}
    (heff : effective (seamTwist C x y m + prin H f))
    (hred' : q_reduced H y (seamTwist C x y (m + 1) + prin H f')) :
    displacement x y f ≤ displacement x y f' := by
  have hkey : seamTwist C x y (m + 1) + prin H f'
      = (seamTwist C x y m + prin H f) + seamDivisor x y + prin H (f' - f) := by
    rw [map_sub, seamTwist_succ]
    abel
  have hmin := script_min_at_of_qReduced y _ (seamDivisor x y) (f' - f) heff
    (fun w hw => seamDivisor_nonneg_of_ne_right x y hw) (by rw [← hkey]; exact hred')
  have hx := hmin x
  simp only [Pi.sub_apply] at hx
  simp only [displacement]
  omega

/-- **Lemma M, `∃`-representative form.**  If the `(m+1)`-twist is winnable then
every displacement of the `m`-twist is dominated by some displacement of the
`(m+1)`-twist. -/
theorem exists_isDisplacement_succ_ge (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (m s : ℤ) (hs : IsDisplacement C x y m s)
    (hw : winnable H (seamTwist C x y (m + 1))) :
    ∃ t, IsDisplacement C x y (m + 1) t ∧ s ≤ t := by
  obtain ⟨f, heff, rfl⟩ := hs
  obtain ⟨f', heff', hred'⟩ := exists_qReduced_script hconn y _ hw
  exact ⟨displacement x y f', ⟨f', heff', rfl⟩,
    le_displacement_of_qReduced_succ C x y m heff hred'⟩

/-- **Lemma M, maximal form**: `b_m ≤ b_{m+1}`. -/
theorem isMaxDisplacement_mono (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (m b b' : ℤ)
    (hb : IsMaxDisplacement C x y m b)
    (hb' : IsMaxDisplacement C x y (m + 1) b') :
    b ≤ b' := by
  obtain ⟨t, ht, hle⟩ := exists_isDisplacement_succ_ge hconn C x y m b hb.1
    (winnable_of_isDisplacement hb'.1)
  exact le_trans hle (hb'.2 t ht)

/-! ## Theorem C′: a non-effective junction class forces a gap

This is §12 of the note.  The argument there runs a terminating level-set
firing iteration; the proof below shortcuts it.  A *single* level set decides
the matter: a `y`-reduced representative of the `m`-twist with no chip at `y`
cannot tolerate `y` sitting at the top level of the transition script.
-/

/-- **The level-set core of Theorem C′.**  Let `D` be effective and `y`-reduced
with *no chip at* `y`, and suppose `D + α + Δg` is effective.  Then `g` is
strictly larger at `x` than at `y`: the seam step strictly increases the
displacement. -/
theorem lt_script_of_qReduced_no_chip (x y : H.V) (hxy : x ≠ y)
    {D : CFDiv H} {g : firing_script H}
    (hDred : q_reduced H y D) (hDy : D y = 0)
    (heff : effective (D + seamDivisor x y + prin H g)) :
    g y < g x := by
  by_contra hcon
  push Not at hcon
  -- Step 1: `y` lies at the top level of `g`.
  have hytop : y ∈ topSet g := by
    by_contra hy
    -- Then `x` is not at the top level either, ...
    have hx : x ∉ topSet g := by
      intro hxtop
      exact hy (mem_topSet.mpr fun u => le_trans (mem_topSet.mp hxtop u) hcon)
    -- ... so `topSet g` is a nonempty legal firing set for `D` avoiding `y`.
    obtain ⟨v, hvS, hlt⟩ := hDred.exists_lt_outdeg hy (topSet_nonempty g)
    have hlt' : D v < outdeg_S H (topSet g) v := hlt
    have hvx : v ≠ x := by rintro rfl; exact hx hvS
    have hvy : v ≠ y := by rintro rfl; exact hy hvS
    have h1 : prin H g v ≤ - outdeg_S H (topSet g) v := prin_le_neg_outdeg_S hvS
    have h2 := heff v
    simp only [Pi.add_apply] at h2
    rw [seamDivisor_apply_of_ne hvx hvy] at h2
    omega
  -- Step 2: `y` at the top level would force a chip at `y`.
  have h1 : prin H g y ≤ 0 := by
    have hle := prin_le_neg_outdeg_S hytop
    have hnn := outdeg_S_nonneg H (topSet g) y
    omega
  have h2 := heff y
  simp only [Pi.add_apply] at h2
  rw [seamDivisor_apply_right hxy] at h2
  omega

/-- The junction `m | m+1` *has a gap*: every displacement of the `(m+1)`-twist
strictly exceeds every displacement of the `m`-twist.  In the notation of the
note this is `gap_m = a_{m+1} - b_m ≥ 1`. -/
def HasGap (C : CFDiv H) (x y : H.V) (m : ℤ) : Prop :=
  ∀ s t : ℤ, IsDisplacement C x y m s → IsDisplacement C x y (m + 1) t → s < t

/-- **Theorem C′.**  A non-effective junction class forces a gap. -/
theorem hasGap_of_junction_not_winnable (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (hxy : x ≠ y) (m : ℤ)
    (hjun : ¬ winnable H (junction C x y m)) :
    HasGap C x y m := by
  rintro s t hs ⟨f', heff', rfl⟩
  -- The `y`-reduced representative of the `m`-twist.
  obtain ⟨f, heff, hred⟩ :=
    exists_qReduced_script hconn y _ (winnable_of_isDisplacement hs)
  have hmax := isMaxDisplacement_of_qReduced_y C x y m heff hred
  have hs' : s ≤ displacement x y f := hmax.2 s hs
  -- It carries no chip at `y`, since the junction class is not effective.
  have hchip : ¬ (1 ≤ (seamTwist C x y m + prin H f) y) := fun h =>
    hjun ((junction_winnable_iff_chip C x y m hred).mpr h)
  have hDy : (seamTwist C x y m + prin H f) y = 0 := by
    have := heff y
    omega
  -- Hence the seam step strictly increases the displacement.
  have hkey : (seamTwist C x y m + prin H f) + seamDivisor x y + prin H (f' - f)
      = seamTwist C x y (m + 1) + prin H f' := by
    rw [map_sub, seamTwist_succ]
    abel
  have hx := lt_script_of_qReduced_no_chip x y hxy hred hDy (by rw [hkey]; exact heff')
  simp only [Pi.sub_apply] at hx
  simp only [displacement] at hs' ⊢
  omega

/-- **Theorem C, contrapositive form.**  An effective junction class rules out a
gap (assuming the `m`-twist is winnable, so that there is something to rule
out). -/
theorem not_hasGap_of_junction_winnable (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (hxy : x ≠ y) (m : ℤ)
    (hw : winnable H (seamTwist C x y m))
    (hjun : winnable H (junction C x y m)) :
    ¬ HasGap C x y m := by
  intro hgap
  obtain ⟨f, heff, hred⟩ := exists_qReduced_script hconn y _ hw
  exact absurd (hgap _ _ ⟨f, heff, rfl⟩
    (isDisplacement_succ_of_junction_winnable C x y hxy m heff hred hjun)) (lt_irrefl _)

/-- **Theorem C ⟺ Theorem C′ (gap rigidity is an equivalence).**  For a winnable
`m`-twist on a connected graph, the junction `m | m+1` has a gap exactly when
its junction class `ξ_m = [C + m•α - (y)] = [C + (m+1)•α - (x)]` fails to be
effective. -/
theorem hasGap_iff (hconn : graph_connected H) (C : CFDiv H) (x y : H.V)
    (hxy : x ≠ y) (m : ℤ) (hw : winnable H (seamTwist C x y m)) :
    HasGap C x y m ↔ ¬ winnable H (junction C x y m) := by
  constructor
  · intro hgap hjun
    exact not_hasGap_of_junction_winnable hconn C x y hxy m hw hjun hgap
  · exact hasGap_of_junction_not_winnable hconn C x y hxy m

/-- **Corollary C1 (rank kills gaps).**  If the `m`-twist has positive rank then
its junction class is effective, so the junction `m | m+1` has no gap. -/
theorem not_hasGap_of_rank_pos (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (hxy : x ≠ y) (m : ℤ)
    (hrank : 1 ≤ rank H (seamTwist C x y m)) :
    ¬ HasGap C x y m := by
  have hjun : winnable H (junction C x y m) := by
    have hgeq : rank_geq H (seamTwist C x y m) 1 := (rank_geq_iff H _ 1).mpr hrank
    exact hgeq (one_chip y) ⟨eff_one_chip y, deg_one_chip y⟩
  have hw : winnable H (seamTwist C x y m) := by
    refine (rank_nonneg_iff_winnable H _).mp ((rank_geq_iff H _ 0).mpr ?_)
    omega
  exact not_hasGap_of_junction_winnable hconn C x y hxy m hw hjun

/-- **Lemma M, strict form.**  When the junction class is not effective the
displacement strictly increases: `b_{m+1} ≥ b_m + 1`. -/
theorem exists_isDisplacement_succ_gt (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (hxy : x ≠ y) (m s : ℤ) (hs : IsDisplacement C x y m s)
    (hw : winnable H (seamTwist C x y (m + 1)))
    (hjun : ¬ winnable H (junction C x y m)) :
    ∃ t, IsDisplacement C x y (m + 1) t ∧ s < t := by
  obtain ⟨t, ht, _⟩ := exists_isDisplacement_succ_ge hconn C x y m s hs hw
  exact ⟨t, ht, hasGap_of_junction_not_winnable hconn C x y hxy m hjun s t hs ht⟩

/-! ## The `x ↔ y` symmetry, and the `a`-side of Lemma M

Swapping the two marks negates the seam, the twist index and the displacement.
-/

lemma seamDivisor_swap (x y : H.V) : seamDivisor y x = - seamDivisor x y := by
  rw [seamDivisor, seamDivisor]
  abel

lemma seamTwist_swap (C : CFDiv H) (x y : H.V) (m : ℤ) :
    seamTwist C y x m = seamTwist C x y (-m) := by
  rw [seamTwist, seamTwist, seamDivisor_swap, smul_neg, ← neg_smul]

lemma displacement_swap (x y : H.V) (f : firing_script H) :
    displacement y x f = - displacement x y f := by
  simp only [displacement]; ring

lemma isDisplacement_swap (C : CFDiv H) (x y : H.V) (m t : ℤ) :
    IsDisplacement C y x m t ↔ IsDisplacement C x y (-m) (-t) := by
  constructor
  · rintro ⟨f, heff, rfl⟩
    exact ⟨f, by rwa [← seamTwist_swap], by rw [displacement_swap]⟩
  · rintro ⟨f, heff, hd⟩
    refine ⟨f, by rwa [seamTwist_swap], ?_⟩
    rw [displacement_swap]
    omega

lemma junction_swap (C : CFDiv H) (x y : H.V) (m : ℤ) :
    junction C y x m = junction C x y (-m - 1) := by
  rw [junction, seamTwist_swap, junction_eq_succ_sub_x]
  congr 2
  omega

/-- **Theorem C, `x`-side form.**  The junction has a *single* obstruction
class, seen from both sides (§5 of the note): the same hypothesis
`ξ_m = [C + (m+1)•α - (x)]` effective shows that the `x`-reduced effective
representative of the `(m+1)`-twist, translated back by the seam, is an
effective representative of the `m`-twist with the same script. -/
theorem isDisplacement_pred_of_junction_winnable (C : CFDiv H) (x y : H.V)
    (hxy : x ≠ y) (m : ℤ) {f : firing_script H}
    (heff : effective (seamTwist C x y (m + 1) + prin H f))
    (hred : q_reduced H x (seamTwist C x y (m + 1) + prin H f))
    (hjun : winnable H (junction C x y m)) :
    IsDisplacement C x y m (displacement x y f) := by
  have hts : seamTwist C y x (-(m + 1)) = seamTwist C x y (m + 1) := by
    rw [seamTwist_swap, neg_neg]
  have hjs : junction C y x (-(m + 1)) = junction C x y m := by
    have hidx : -(-(m + 1)) - 1 = m := by omega
    rw [junction_swap, hidx]
  have hmain := isDisplacement_succ_of_junction_winnable C y x hxy.symm (-(m + 1))
    (by rw [hts]; exact heff) (by rw [hts]; exact hred) (by rw [hjs]; exact hjun)
  have hm : -(m + 1) + 1 = -m := by omega
  rw [hm] at hmain
  have h := (isDisplacement_swap C x y (-m) (displacement y x f)).mp hmain
  rw [neg_neg, displacement_swap, neg_neg] at h
  exact h

/-- **Theorem C, `x`-side packaged.**  If the junction class is effective, the
minimal displacement of the `(m+1)`-twist is again a displacement of the
`m`-twist; in particular `a_m ≤ a_{m+1}` is not strict. -/
theorem isDisplacement_of_isMinDisplacement_succ (hconn : graph_connected H)
    (C : CFDiv H) (x y : H.V) (hxy : x ≠ y) (m a : ℤ)
    (ha : IsMinDisplacement C x y (m + 1) a)
    (hjun : winnable H (junction C x y m)) :
    IsDisplacement C x y m a := by
  obtain ⟨f, heff, hred⟩ :=
    exists_qReduced_script hconn x _ (winnable_of_isDisplacement ha.1)
  have hmin := isMinDisplacement_of_qReduced_x C x y (m + 1) heff hred
  have haf : a = displacement x y f := ha.unique hmin
  rw [haf]
  exact isDisplacement_pred_of_junction_winnable C x y hxy m heff hred hjun

/-- **Lemma M (`a`-side).**  If the `m`-twist is winnable then every
displacement of the `(m+1)`-twist dominates some displacement of the `m`-twist:
`a_m ≤ a_{m+1}`. -/
theorem exists_isDisplacement_le (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (m t : ℤ) (ht : IsDisplacement C x y (m + 1) t)
    (hw : winnable H (seamTwist C x y m)) :
    ∃ s, IsDisplacement C x y m s ∧ s ≤ t := by
  have hm : -(m + 1) + 1 = -m := by omega
  have hflip : IsDisplacement C y x (-(m + 1)) (-t) := by
    rw [isDisplacement_swap, neg_neg, neg_neg]
    exact ht
  have hwflip : winnable H (seamTwist C y x (-(m + 1) + 1)) := by
    rw [hm, seamTwist_swap, neg_neg]
    exact hw
  obtain ⟨u, hu, hle⟩ :=
    exists_isDisplacement_succ_ge hconn C y x (-(m + 1)) (-t) hflip hwflip
  have h := (isDisplacement_swap C x y (-(m + 1) + 1) u).mp hu
  have he : -(-(m + 1) + 1) = m := by omega
  rw [he] at h
  exact ⟨-u, h, by omega⟩

/-- **The `a`-side gap statement.**  A non-effective junction class also forces
the strict inequality on the `x`-reduced side. -/
theorem exists_isDisplacement_lt (hconn : graph_connected H) (C : CFDiv H)
    (x y : H.V) (hxy : x ≠ y) (m t : ℤ) (ht : IsDisplacement C x y (m + 1) t)
    (hw : winnable H (seamTwist C x y m))
    (hjun : ¬ winnable H (junction C x y m)) :
    ∃ s, IsDisplacement C x y m s ∧ s < t := by
  obtain ⟨s, hs, _⟩ := exists_isDisplacement_le hconn C x y m t ht hw
  exact ⟨s, hs, hasGap_of_junction_not_winnable hconn C x y hxy m hjun s t hs ht⟩

end Utilities
