/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Convex.Majorization

/-!
# Symmetric gauges on finitely supported nonnegative sequences

A **symmetric gauge** (Calkin's *symmetric norming function*) is a subadditive,
positively homogeneous, permutation-invariant and monotone functional on finitely
supported nonnegative sequences, normalized so that a single unit coordinate has
gauge one.  It is the scalar half of the theory of symmetrically normed operator
ideals: an ideal gauge is a symmetric gauge applied to a singular-value sequence.

* `TauCeti.SymmetricGauge` — the structure;
* `TauCeti.SymmetricGauge.single` — `Φ (single i c) = c`, the first consequence of
  normalization and permutation invariance together;
* `TauCeti.SymmetricGauge.le_apply` — `aᵢ ≤ Φ a` for every coordinate;
* `TauCeti.SymmetricGauge.apply_le_sum` — `Φ a ≤ ∑ aᵢ`;
* `TauCeti.SymmetricGauge.le_apply_and_le_sum` — the two-sided bound
  `sup aᵢ ≤ Φ a ≤ ∑ aᵢ` packaged together;
* `TauCeti.SymmetricGauge.extend` — the extension to arbitrary `ℝ≥0∞`-valued
  sequences, as a supremum over dominated finitely supported sequences;
* `TauCeti.SymmetricGauge.iSup_le_extend_le_tsum` — the same sandwich for the
  extension, `⨆ aₙ ≤ Φ.extend a ≤ ∑' aₙ`.

## Why this is not `FiniteSymmetricGauge`

`ForTauCeti.Analysis.Convex.Majorization` already has `FiniteSymmetricGauge n`, on
`(Fin n → ℝ) → ℝ`, with `real_smul'` and `neg_single'`.  That is the finite
*real-vector* gauge the majorization layer needs, and three concrete gauges are
built on it.  This structure is a different object: finitely supported sequences
indexed by `ℕ` rather than `Fin n`, values in `ℝ≥0` rather than `ℝ`, and `mono`
and `normalized` in place of the sign axioms.  Neither generalizes the other --
the finite one allows negative entries and does not fix a scale; this one fixes a
scale and takes monotonicity in the termwise order as an axiom, which is what the
two-sided bound below needs.

## The two-sided bound

`normalized` is what makes the sandwich `sup aᵢ ≤ Φ a ≤ ∑ aᵢ` available, and the
sandwich is what every later result is stated against.  Both halves come straight
from the axioms:

* **lower** -- `single i (a i) ≤ a` termwise, so `mono` and `single` give
  `a i ≤ Φ a`;
* **upper** -- `a` is the finite sum `∑ i ∈ a.support, single i (a i)`, so
  subadditivity and `single` give `Φ a ≤ ∑ i ∈ a.support, a i`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written for this repository against the target
  signature recorded in
  `TauCetiRoadmap/OperatorTheory/OperatorIdeals/Suggested.lean`, which states the
  structure and the two-sided bound; the field names and the shape of
  `SymmetricGauge` follow that file so the roadmap statement and the delivered
  one agree literally.
* Roadmap topic: `OperatorIdeals` (the symmetrically normed ideal layer).
* Original authors / copyright: Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti

/-- A **symmetric gauge** on finitely supported nonnegative sequences: Calkin's
symmetric norming function.

`symm` is stated against `Equiv.Perm ℕ` acting by precomposition on the finitely
supported sequence, which is what makes "symmetric" a property of `Φ` rather than
a property of the sequences it is applied to. -/
structure SymmetricGauge where
  /-- The underlying gauge on finitely supported nonnegative sequences. -/
  toFun : (ℕ →₀ ℝ≥0) → ℝ≥0
  /-- Subadditivity. -/
  add_le : ∀ a b : ℕ →₀ ℝ≥0, toFun (a + b) ≤ toFun a + toFun b
  /-- Positive homogeneity. -/
  smul : ∀ (c : ℝ≥0) (a : ℕ →₀ ℝ≥0), toFun (c • a) = c * toFun a
  /-- Permutation invariance -- the "symmetric" in symmetric norming function. -/
  symm : ∀ (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0),
    toFun (Finsupp.equivMapDomain σ a) = toFun a
  /-- Monotonicity in the termwise order. -/
  mono : ∀ ⦃a b : ℕ →₀ ℝ≥0⦄, a ≤ b → toFun a ≤ toFun b
  /-- Normalization: the first basis vector has gauge one.  This fixes the scale,
  and with it the two-sided bound `‖a‖_∞ ≤ Φ a ≤ ∑ aₙ`. -/
  normalized : toFun (Finsupp.single 0 1) = 1

namespace SymmetricGauge

/-- Apply a symmetric gauge directly to a sequence, writing `Φ a` for `Φ.toFun a`. -/
instance : CoeFun SymmetricGauge fun _ => (ℕ →₀ ℝ≥0) → ℝ≥0 :=
  ⟨SymmetricGauge.toFun⟩

variable (Φ : SymmetricGauge)

/-- The gauge of the zero sequence is zero.  Immediate from homogeneity at `c = 0`,
and needed before any sum argument can start from an empty support. -/
@[simp]
theorem map_zero : Φ 0 = 0 := by
  have h := Φ.smul 0 0
  simpa using h

/-- Every unit basis vector has gauge one: permutation invariance transports the
normalization at `0` to an arbitrary index.

This is the first place the `symm` axiom does real work, and it is why
`normalized` may be stated at the single index `0` rather than for all of them. -/

theorem single_one (i : ℕ) : Φ (Finsupp.single i 1) = 1 := by
  classical
  -- The transposition swapping `0` and `i` carries `single 0 1` to `single i 1`.
  have hmap : Finsupp.equivMapDomain (Equiv.swap 0 i) (Finsupp.single 0 (1 : ℝ≥0))
      = Finsupp.single i 1 := by
    ext j
    simp [Finsupp.single_apply]
  calc Φ (Finsupp.single i 1)
      = Φ (Finsupp.equivMapDomain (Equiv.swap 0 i) (Finsupp.single 0 1)) := by
        rw [hmap]
    _ = Φ (Finsupp.single 0 1) := Φ.symm _ _
    _ = 1 := Φ.normalized

/-- A single coordinate is measured by its value: `Φ (single i c) = c`. -/
@[simp]
theorem single (i : ℕ) (c : ℝ≥0) : Φ (Finsupp.single i c) = c := by
  have hsmul : c • Finsupp.single i (1 : ℝ≥0) = Finsupp.single i c := by
    ext j; simp [Finsupp.single_apply]
  calc Φ (Finsupp.single i c)
      = Φ (c • Finsupp.single i 1) := by rw [hsmul]
    _ = c * Φ (Finsupp.single i 1) := Φ.smul _ _
    _ = c := by rw [single_one]; exact mul_one c

/-- **Lower half of the two-sided bound.**  Every coordinate is dominated by the
gauge: `aᵢ ≤ Φ a`.

`single i (a i) ≤ a` holds termwise -- the two agree at `i` and the left side is
zero elsewhere -- so this is `mono` followed by `single`. -/
theorem le_apply (a : ℕ →₀ ℝ≥0) (i : ℕ) : a i ≤ Φ a := by
  have hle : Finsupp.single i (a i) ≤ a := by
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  calc a i = Φ (Finsupp.single i (a i)) := (single Φ i (a i)).symm
    _ ≤ Φ a := Φ.mono hle

/-- **Upper half of the two-sided bound.**  The gauge is dominated by the sum:
`Φ a ≤ ∑ aᵢ`.

`a` is the finite sum of its single-coordinate pieces over its support, so this is
subadditivity along that decomposition followed by `single`. -/
theorem apply_le_sum (a : ℕ →₀ ℝ≥0) : Φ a ≤ ∑ i ∈ a.support, a i := by
  classical
  -- Rebuild `a` from its support, then push the gauge through the finite sum.
  have hsum : a = ∑ i ∈ a.support, Finsupp.single i (a i) := by
    ext j; simp [Finsupp.single_apply]
  have hstep : ∀ (s : Finset ℕ),
      Φ (∑ i ∈ s, Finsupp.single i (a i)) ≤ ∑ i ∈ s, a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s his ih =>
        rw [Finset.sum_insert his, Finset.sum_insert his]
        calc Φ (Finsupp.single i (a i) + ∑ j ∈ s, Finsupp.single j (a j))
            ≤ Φ (Finsupp.single i (a i)) + Φ (∑ j ∈ s, Finsupp.single j (a j)) :=
              Φ.add_le _ _
          _ ≤ a i + ∑ j ∈ s, a j := by
              gcongr
              · exact le_of_eq (single Φ i (a i))
  calc Φ a = Φ (∑ i ∈ a.support, Finsupp.single i (a i)) := by rw [← hsum]
    _ ≤ ∑ i ∈ a.support, a i := hstep _

/-- **The two-sided bound**, packaged: every coordinate is below the gauge and the
gauge is below the sum.

This sandwich is what later results -- the extension to non-finitely-supported
sequences, the induced ideal family, and Ky Fan dominance -- are stated against,
and it is the reason `normalized` is an axiom rather than a convention. -/
theorem le_apply_and_le_sum (a : ℕ →₀ ℝ≥0) :
    (∀ i, a i ≤ Φ a) ∧ Φ a ≤ ∑ i ∈ a.support, a i :=
  ⟨fun i => le_apply Φ a i, apply_le_sum Φ a⟩

/-! ## Extension to arbitrary `ℝ≥0∞`-valued sequences -/

/-- The finitely supported nonnegative sequences dominated termwise by `a`.

This is the index set of the supremum defining `extend`.  It is nonempty for
every `a` -- the zero sequence always qualifies -- which is what makes the
extension total. -/
@[expose]
def Dominated (a : ℕ → ℝ≥0∞) : Type :=
  {b : ℕ →₀ ℝ≥0 // ∀ i, (b i : ℝ≥0∞) ≤ a i}

/-- The index set is never empty: the zero sequence is dominated by every `a`.

This is what makes `extend` total — a supremum over an empty index set would be
`0` regardless of `a`, which would break the lower bound. -/
instance (a : ℕ → ℝ≥0∞) : Nonempty (Dominated a) :=
  ⟨⟨0, by intro i; simp⟩⟩

/-- The extension of a symmetric gauge to arbitrary `ℝ≥0∞`-valued sequences: the
supremum of `Φ` over the finitely supported sequences dominated by `a`.

**A supremum, not a `tsum`.**  The gauge must be total and genuinely `∞` off its
ideal, and a supremum of an increasing net is total by construction; any route
through summability reintroduces the side conditions the interface avoids.

**On the decreasing rearrangement.**  The supremum is taken over *all* dominated
finitely supported sequences, with no rearrangement.  That is equivalent to
truncating the decreasing rearrangement, because `Φ` is permutation-invariant
(`symm`) and monotone (`mono`), so the supremum is already rearrangement-
independent; the rearrangement is a device for *computing* the value rather than
part of its specification, and avoiding it here keeps this file free of a
rearrangement API it would otherwise have to build first. -/
noncomputable def extend (Φ : SymmetricGauge) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ b : Dominated a, (Φ b.1 : ℝ≥0∞)

/-- Each dominated finitely supported sequence bounds the extension from below. -/
theorem le_extend_of_dominated (a : ℕ → ℝ≥0∞) (b : ℕ →₀ ℝ≥0)
    (hb : ∀ i, (b i : ℝ≥0∞) ≤ a i) : (Φ b : ℝ≥0∞) ≤ Φ.extend a :=
  le_iSup (f := fun b : Dominated a => (Φ b.1 : ℝ≥0∞)) ⟨b, hb⟩

/-- The extension is the *least* bound over dominated finitely supported sequences: this is
the eliminator for the supremum, stated without exposing `extend`'s body. -/
theorem extend_le {a : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ b : ℕ →₀ ℝ≥0, (∀ i, (b i : ℝ≥0∞) ≤ a i) → (Φ b : ℝ≥0∞) ≤ c) :
    Φ.extend a ≤ c :=
  iSup_le fun b => h b.1 b.2

/-- The truncation of `a` to its first `k` entries, capped at `m`.

Distinct from `truncate` below, whose input is already finite-valued; this one
is total, which is what the extension's supremum needs.

The cap is applied in `ℝ≥0∞`, **before** the conversion to `ℝ≥0`: `ENNReal.toNNReal ∞ = 0`,
so capping after the conversion would read an infinite entry as zero and destroy
monotonicity. -/
@[expose]
noncomputable def cappedTruncate (a : ℕ → ℝ≥0∞) (k : ℕ) (m : ℝ≥0) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset (Finset.range k)
    (fun n => if n < k then (min (a n) (m : ℝ≥0∞)).toNNReal else 0)
    (fun n hn => by
      by_cases h : n < k
      · simpa using h
      · simp [h] at hn)

/-- The capped truncation, pointwise.  Definitional -- see `cappedTruncate`. -/
@[simp] theorem cappedTruncate_apply (a : ℕ → ℝ≥0∞) (k : ℕ) (m : ℝ≥0) (n : ℕ) :
    cappedTruncate a k m n = if n < k then (min (a n) (m : ℝ≥0∞)).toNNReal else 0 := rfl

/-- Capped initial truncations are cofinal among the finitely supported sequences
used to define the extension. The cap handles infinite coordinates before conversion
to `NNReal`; finite-valued sequences instead use `extend_eq_iSup_truncate`. -/
theorem extend_eq_iSup_cappedTruncate (Φ : SymmetricGauge) (a : ℕ → ℝ≥0∞) :
    Φ.extend a = ⨆ k : ℕ, ⨆ m : ℝ≥0, (Φ (cappedTruncate a k m) : ℝ≥0∞) := by
  refine le_antisymm (iSup_le fun b => ?_) (iSup_le fun k => iSup_le fun m => ?_)
  · obtain ⟨k, hk⟩ : ∃ k, ∀ n ∈ b.1.support, n < k :=
      ⟨b.1.support.sup id + 1, fun n hn => Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
    refine le_iSup_of_le k (le_iSup_of_le (b.1.support.sup b.1) ?_)
    refine (ENNReal.coe_le_coe).2 (Φ.mono (Finsupp.le_def.2 fun n => ?_))
    simp only [cappedTruncate_apply]
    by_cases hn : n < k
    · simp only [hn, ite_true]
      have hb : (b.1 n : ℝ≥0∞) ≤ min (a n) ((b.1.support.sup b.1 : ℝ≥0) : ℝ≥0∞) := by
        refine le_min (b.2 n) ?_
        by_cases hmem : n ∈ b.1.support
        · exact_mod_cast Finset.le_sup (f := b.1) hmem
        · simp [Finsupp.notMem_support_iff.mp hmem]
      exact ENNReal.le_toNNReal_of_coe_le hb
        (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
    · have : n ∉ b.1.support := fun hmem => hn (hk n hmem)
      simp [Finsupp.notMem_support_iff.mp this, hn]
  · refine le_extend_of_dominated Φ a _ fun i => ?_
    simp only [cappedTruncate_apply]
    split
    · exact le_trans ENNReal.coe_toNNReal_le_self (min_le_left _ _)
    · simp

/-- **Lower half of the extended bound.**  Every coordinate is below the extension.

This reaches `∞` correctly: when `a n = ∞` the argument supplies `single n c` for
every finite `c`, so the supremum is not bounded by any real. -/
theorem le_extend (a : ℕ → ℝ≥0∞) (n : ℕ) : a n ≤ Φ.extend a := by
  -- It suffices to beat every finite `c` strictly below `a n`; when `a n = ∞`
  -- that ranges over all of `ℝ≥0`, so the supremum is forced to `∞` as well.
  refine ENNReal.le_of_forall_nnreal_lt fun c hc => ?_
  have hdom : ∀ i, ((Finsupp.single n c) i : ℝ≥0∞) ≤ a i := by
    intro i
    by_cases hin : i = n
    · subst hin; simpa using hc.le
    · simp [hin]
  have hb := le_extend_of_dominated Φ a (Finsupp.single n c) hdom
  rwa [single Φ n c] at hb

/-- The supremum of the sequence is below its extension. -/
theorem iSup_le_extend (a : ℕ → ℝ≥0∞) : (⨆ n, a n) ≤ Φ.extend a :=
  iSup_le (Φ.le_extend a)

/-- The extension of the zero sequence is zero. -/
@[simp] theorem extend_zero : Φ.extend (fun _ => 0) = 0 := by
  refine le_antisymm (iSup_le fun b => ?_) (by simp)
  have hb : b.1 = 0 := Finsupp.ext fun i => by simpa using b.2 i
  simp [hb]

/-- The extension of the everywhere-infinite sequence is `∞`.

Worth stating because it is the property `extend` was built as a supremum to have: a
definition routed through `tsum` would need the sequence summable before it said anything,
and would then say nothing here. -/
@[simp] theorem extend_top : Φ.extend (fun _ => ⊤) = ⊤ :=
  top_le_iff.1 (le_trans (by simp) (Φ.iSup_le_extend (fun _ => ⊤)))

/-- Subadditivity over a finitely supported sequence: `Φ f ≤ ∑ fₙ`.

Induction on the support, with `add_le` at each step and `single` at the leaves.
This is the finite half of the high end of the scale. -/
theorem le_sum (f : ℕ →₀ ℝ≥0) : Φ f ≤ f.sum fun _ v => v := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add n b g hng hb ih =>
      rw [Finsupp.sum_add_index' (by simp) (by simp)]
      refine (Φ.add_le _ _).trans ?_
      gcongr
      simp [Finsupp.sum_single_index]

/-- **Upper half of the extended bound.**  The extension is below the total sum. -/
theorem extend_le_tsum (a : ℕ → ℝ≥0∞) : Φ.extend a ≤ ∑' n, a n := by
  refine iSup_le fun b => ?_
  calc (Φ b.1 : ℝ≥0∞)
      ≤ ((∑ i ∈ b.1.support, b.1 i : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast apply_le_sum Φ b.1
    _ = ∑ i ∈ b.1.support, ((b.1 i : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ∑ i ∈ b.1.support, a i := Finset.sum_le_sum fun i _ => b.2 i
    _ ≤ ∑' n, a n := ENNReal.sum_le_tsum _

/-- **Both ends of the scale**, and the reason the normalization is not a
restriction: the extension sits between the supremum and the sum. -/
theorem iSup_le_extend_le_tsum (a : ℕ → ℝ≥0∞) :
    (⨆ n, a n) ≤ Φ.extend a ∧ Φ.extend a ≤ ∑' n, a n :=
  ⟨iSup_le fun n => le_extend Φ a n, extend_le_tsum Φ a⟩

/-! ## Bridge to the finite majorization theory

`ForTauCeti.Analysis.Convex.Majorization` proves the Hardy--Littlewood--Pólya
transfer descent for `FiniteSymmetricGauge`, on `(Fin n → ℝ) → ℝ`.  That layer is
not directly usable here -- this gauge lives on `(ℕ →₀ ℝ≥0) → ℝ≥0` and takes
`mono` and `normalized` as axioms where the finite one takes sign conditions --
so the descent is imported through an adapter rather than reproved.

The adapter sends `x : Fin n → ℝ` to `Φ` applied to the componentwise absolute
value, read as a finitely supported sequence on `ℕ`.
-/

/-- The componentwise absolute value of a finite real vector, as a finitely
supported nonnegative sequence on `ℕ`.

Uses `Real.nnabs` rather than an anonymous `⟨|x i|, _⟩`: the latter carries a
proof inside the term, so every rewrite has to happen under a dependent pair and
`rw` reports the motive as ill-typed.  `Real.nnabs` is a `MonoidWithZeroHom`, so
`map_mul` also supplies the scaling law below for free. -/
@[expose]
noncomputable def ofFin {n : ℕ} (x : Fin n → ℝ) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset (Finset.range n)
    (fun i => if h : i < n then Real.nnabs (x ⟨i, h⟩) else 0)
    (by
      intro i hi
      by_cases h : i < n
      · exact Finset.mem_range.mpr h
      · simp [h] at hi)

/-- `ofFin` reads off `Real.nnabs` at an in-range index. -/
@[simp]
theorem ofFin_apply {n : ℕ} (x : Fin n → ℝ) {i : ℕ} (h : i < n) :
    (ofFin x) i = Real.nnabs (x ⟨i, h⟩) := by
  simp only [ofFin, Finsupp.onFinset_apply, h, dite_eq_left]

/-- `ofFin` vanishes outside the range. -/
@[simp]
theorem ofFin_apply_of_le {n : ℕ} (x : Fin n → ℝ) {i : ℕ} (h : ¬ i < n) :
    (ofFin x) i = 0 := by
  simp only [ofFin, Finsupp.onFinset_apply, h, dite_eq_right, not_false_iff]

/-- `ofFin` is monotone in the componentwise order on absolute values. -/
theorem ofFin_le_ofFin {n : ℕ} {x y : Fin n → ℝ}
    (h : ∀ i, |x i| ≤ |y i|) : ofFin x ≤ ofFin y := by
  intro i
  by_cases hi : i < n
  · rw [ofFin_apply x hi, ofFin_apply y hi, ← NNReal.coe_le_coe,
      Real.coe_nnabs, Real.coe_nnabs]
    exact h ⟨i, hi⟩
  · simp [ofFin_apply_of_le, hi]

/-- The absolute value of a sum is dominated termwise by the sum of the absolute
values, transported to `ofFin`.  This is the step that needs `mono`. -/
theorem ofFin_add_le {n : ℕ} (x y : Fin n → ℝ) :
    ofFin (x + y) ≤ ofFin x + ofFin y := by
  intro i
  by_cases hi : i < n
  · rw [ofFin_apply (x + y) hi, Finsupp.add_apply, ofFin_apply x hi,
      ofFin_apply y hi, ← NNReal.coe_le_coe]
    simpa using abs_add_le (x ⟨i, hi⟩) (y ⟨i, hi⟩)
  · simp [ofFin_apply_of_le, hi]

/-- Scaling a finite vector scales its `ofFin` image by the absolute value. -/
theorem ofFin_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    ofFin (c • x) = Real.nnabs c • ofFin x := by
  ext i
  by_cases hi : i < n
  · rw [ofFin_apply (c • x) hi, Finsupp.smul_apply, ofFin_apply x hi,
      smul_eq_mul]
    simp [map_mul]
  · simp [ofFin_apply_of_le, hi]

/-- Flipping the sign of a single coordinate leaves the `ofFin` image unchanged. -/
theorem ofFin_update_neg {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    ofFin (Function.update x j (-(x j))) = ofFin x := by
  ext i
  by_cases hi : i < n
  · rw [ofFin_apply _ hi, ofFin_apply x hi]
    by_cases hij : (⟨i, hi⟩ : Fin n) = j
    · rw [hij, Function.update_self]
      simp
    · rw [Function.update_of_ne hij]
  · simp [ofFin_apply_of_le, hi]

/-- The capped truncation of a nonnegative real sequence sits below its `Fin k` view. -/
theorem cappedTruncate_le_ofFin {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (k : ℕ) (m : ℝ≥0) :
    cappedTruncate (fun n => ENNReal.ofReal (a n)) k m ≤ ofFin (fun i : Fin k => a i) := by
  refine Finsupp.le_def.2 fun i => ?_
  simp only [cappedTruncate_apply]
  by_cases hi : i < k
  · rw [ite_eq_left hi, ofFin_apply _ hi]
    have h2 : (min (ENNReal.ofReal (a i)) ((m : ℝ≥0∞))).toNNReal ≤ (a i).toNNReal := by
      refine (ENNReal.toNNReal_mono (by simp) (min_le_left _ _)).trans ?_
      rw [← ENNReal.ofNNReal_toNNReal, ENNReal.toNNReal_coe]
    rwa [Real.nnabs_of_nonneg (ha i)]
  · rw [ite_eq_right hi, ofFin_apply_of_le _ hi]

/-- Each `Fin k` view is below the extension of the sequence. -/
theorem ofFin_le_extend (Φ : SymmetricGauge) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (k : ℕ) :
    ((Φ (ofFin (fun i : Fin k => a i)) : ℝ≥0) : ℝ≥0∞)
      ≤ Φ.extend fun n => ENNReal.ofReal (a n) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℝ≥0, ∀ i : Fin k, (a i).toNNReal ≤ m :=
    ⟨(Finset.univ.image fun i : Fin k => (a i).toNNReal).sup id,
      fun i => Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
  have heq : ofFin (fun i : Fin k => a i)
      = cappedTruncate (fun n => ENNReal.ofReal (a n)) k m := by
    refine Finsupp.ext fun i => ?_
    simp only [cappedTruncate_apply]
    by_cases hi : i < k
    · rw [ite_eq_left hi, ofFin_apply _ hi]
      have hle : ENNReal.ofReal (a i) ≤ (m : ℝ≥0∞) := by
        rw [← ENNReal.ofNNReal_toNNReal, ENNReal.coe_le_coe]
        exact hm ⟨i, hi⟩
      rw [min_eq_left hle, ← ENNReal.ofNNReal_toNNReal, ENNReal.toNNReal_coe,
        Real.nnabs_of_nonneg (ha i)]
    · rw [ite_eq_right hi, ofFin_apply_of_le _ hi]
  rw [heq, Φ.extend_eq_iSup_cappedTruncate]
  exact le_iSup_of_le k (le_iSup
    (fun m : ℝ≥0 => ((Φ (cappedTruncate (fun n => ENNReal.ofReal (a n)) k m) : ℝ≥0) : ℝ≥0∞)) m)

/-- **The extension of a nonnegative real sequence collapses to one index.**

The dominated-sequence supremum is exhausted by initial finite views. No
antitonicity assumption is needed. -/
theorem extend_eq_iSup_ofFin (Φ : SymmetricGauge) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    Φ.extend (fun n => ENNReal.ofReal (a n))
      = ⨆ k : ℕ, ((Φ (ofFin (fun i : Fin k => a i)) : ℝ≥0) : ℝ≥0∞) := by
  refine le_antisymm ?_ (iSup_le fun k => Φ.ofFin_le_extend ha k)
  rw [Φ.extend_eq_iSup_cappedTruncate]
  refine iSup_le fun k => iSup_le fun m => ?_
  refine le_iSup_of_le k ?_
  exact_mod_cast Φ.mono (cappedTruncate_le_ofFin ha k m)

/-- A permutation of `Fin n` as a permutation of `ℕ`, fixing everything outside
the range.

Built by hand rather than through `Equiv.Perm.extendDomain` so that the transport
equation below can be proved by direct computation on indices. -/
def natPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm ℕ where
  toFun i := if h : i < n then (π ⟨i, h⟩ : ℕ) else i
  invFun i := if h : i < n then (π.symm ⟨i, h⟩ : ℕ) else i
  left_inv i := by
    by_cases h : i < n
    · simp only [dite_eq_left h, dite_eq_left (π ⟨i, h⟩).isLt]
      simp
    · simp [h]
  right_inv i := by
    by_cases h : i < n
    · simp only [dite_eq_left h, dite_eq_left (π.symm ⟨i, h⟩).isLt]
      simp
    · simp [h]

/-- `natPerm` acts as `π` inside the range. -/
@[simp]
theorem natPerm_apply_of_lt {n : ℕ} (π : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    natPerm π i = (π ⟨i, h⟩ : ℕ) := by
  simp [natPerm, h]

/-- `natPerm`'s inverse acts as `π.symm` inside the range. -/
@[simp]
theorem natPerm_symm_apply_of_lt {n : ℕ} (π : Equiv.Perm (Fin n)) {i : ℕ}
    (h : i < n) : (natPerm π).symm i = (π.symm ⟨i, h⟩ : ℕ) := by
  simp [natPerm, h]

/-- **The transport equation.**  Permuting the coordinates of a finite vector
corresponds to relabelling its `ofFin` image along `natPerm`.

This is the step that makes `SymmetricGauge.symm` -- an axiom about
`Equiv.Perm ℕ` -- usable against `FiniteSymmetricGauge.perm'`, which quantifies
over `Equiv.Perm (Fin n)`. -/
theorem ofFin_comp_perm {n : ℕ} (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    ofFin (x ∘ π) = Finsupp.equivMapDomain (natPerm π).symm (ofFin x) := by
  ext i
  rw [Finsupp.equivMapDomain_apply]
  by_cases hi : i < n
  · have h2 : ((natPerm π).symm).symm i = (π ⟨i, hi⟩ : ℕ) := by
      simp [natPerm, hi]
    rw [ofFin_apply _ hi, h2, ofFin_apply x (π ⟨i, hi⟩).isLt]
    rfl
  · have h2 : ((natPerm π).symm).symm i = i := by simp [natPerm, hi]
    rw [h2, ofFin_apply_of_le _ hi, ofFin_apply_of_le _ hi]

/-- **The adapter.**  A symmetric gauge restricts to a `FiniteSymmetricGauge` on
each `Fin n`, by applying it to the componentwise absolute value.

This is what lets the Hardy--Littlewood--Pólya transfer descent of
`ForTauCeti.Analysis.Convex.Majorization` be *used* here rather than reproved.
Each field is one axiom of `SymmetricGauge` composed with one `ofFin` lemma:

* `add_le'` -- `ofFin_add_le`, then `mono`, then `add_le`.  **This is the one
  field where `mono` does work that is invisible in the finite theory**, where
  the corresponding monotonicity is a consequence of the descent rather than an
  assumption;
* `real_smul'` -- `ofFin_smul` then `smul`;
* `perm'` -- `ofFin_comp_perm` then `symm`.  The axiom speaks of `Equiv.Perm ℕ`
  and the field of `Equiv.Perm (Fin n)`; the transport equation is what makes
  them meet, and it was the last obstruction;
* `neg_single'` -- `ofFin_update_neg`, which needs nothing about `Φ` at all. -/
noncomputable def toFiniteSymmetricGauge (Φ : SymmetricGauge) (n : ℕ) :
    FiniteSymmetricGauge n where
  toFun x := (Φ (ofFin x) : ℝ)
  add_le' x y := by
    have h : Φ (ofFin (x + y)) ≤ Φ (ofFin x) + Φ (ofFin y) :=
      (Φ.mono (ofFin_add_le x y)).trans (Φ.add_le _ _)
    exact_mod_cast h
  real_smul' c x := by
    rw [ofFin_smul, Φ.smul]
    simp [Real.coe_nnabs]
  perm' x π := by rw [ofFin_comp_perm, Φ.symm]
  neg_single' x j := by rw [ofFin_update_neg]

/-- **The transfer descent, available for `SymmetricGauge`.**  If `z` is antitone
and nonnegative and every prefix sum of `z` is dominated by that of `y`, then
`Φ (ofFin z) ≤ Φ (ofFin y)`.

This is `FiniteSymmetricGauge.le_of_prefixSum_le` pulled back along the adapter:
no part of the Hardy--Littlewood--Pólya argument is repeated here, which was the
point of building the adapter rather than reproving the descent. -/
theorem le_of_prefixSum_le (Φ : SymmetricGauge) {n : ℕ} {z y : Fin n → ℝ}
    (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i) (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ k : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k, y i) :
    Φ (ofFin z) ≤ Φ (ofFin y) := by
  have h := (Φ.toFiniteSymmetricGauge n).le_of_prefixSum_le hz_anti hz0 hy0 hpre
  exact_mod_cast h

/-- Weak majorization implies domination under every symmetric gauge. -/
theorem mono_weaklyMajorized (Φ : SymmetricGauge) {n : ℕ} {x y : Fin n → ℝ}
    (h : FiniteVector.WeaklyMajorized x y) : Φ (ofFin x) ≤ Φ (ofFin y) := by
  have := (Φ.toFiniteSymmetricGauge n).mono_weaklyMajorized h
  exact_mod_cast this

/-- If any coordinate is infinite, so is the extension.

This is the case that makes the `⨆`-definition of `extend` behave: the gauge is
`∞` off its ideal without any summability hypothesis. -/
theorem extend_eq_top_of_eq_top {a : ℕ → ℝ≥0∞} {n : ℕ} (h : a n = ⊤) :
    Φ.extend a = ⊤ :=
  top_unique (h ▸ le_extend Φ a n)

/-- Initial truncation of a finite-valued nonnegative sequence.

Finiteness belongs to the input type, not to a separate hypothesis. Capped truncations
remain the approximation tool for genuinely extended-real sequences. -/
@[expose]
noncomputable def truncate (a : ℕ → NNReal) (N : ℕ) : ℕ →₀ NNReal :=
  Finsupp.onFinset (Finset.range N)
    (fun i => if i < N then a i else 0)
    (by
      intro i hi
      by_cases h : i < N
      · exact Finset.mem_range.mpr h
      · simp [h] at hi)

/-- An initial truncation is dominated by its sequence. -/
theorem truncate_le (a : ℕ → NNReal) (N i : ℕ) : truncate a N i ≤ a i := by
  by_cases hi : i < N <;> simp [truncate, hi]

/-- A finite-valued sequence is exhausted by initial truncations, without an order assumption.

Every finitely supported dominated sequence fits inside one initial segment. This is why
no antitonicity hypothesis, and no second supremum over caps, belongs in this statement. -/
theorem extend_eq_iSup_truncate (a : ℕ → NNReal) :
    Φ.extend (fun n => (a n : ENNReal)) =
      ⨆ N : ℕ, (Φ (truncate a N) : ENNReal) := by
  classical
  refine le_antisymm (iSup_le fun b => ?_) (iSup_le fun N => ?_)
  · obtain ⟨N, hN⟩ := b.1.support.exists_nat_subset_range
    refine le_iSup_of_le N ?_
    exact_mod_cast Φ.mono (show b.1 ≤ truncate a N from fun i => by
      by_cases hi : i < N
      · simpa [truncate, hi] using (ENNReal.coe_le_coe.mp (b.2 i))
      · have hb : b.1 i = 0 := by
          apply Finsupp.notMem_support_iff.mp
          intro hbi
          exact hi (Finset.mem_range.mp (hN hbi))
        simp [truncate, hi, hb])
  · exact le_extend_of_dominated Φ _ (truncate a N)
      (fun i => ENNReal.coe_le_coe.mpr (truncate_le a N i))

/-- **Finiteness transfers backwards along prefix-sum domination.**

If every prefix sum of `a` is dominated by that of `b` and `b` is finite in every
coordinate, then so is `a`.  A single infinite coordinate of `a` would make its
prefix sum at `n + 1` equal `⊤`, which the hypothesis would force onto a prefix
sum of `b` that is a finite sum of finite terms.

This is the step that lets the majorization argument discharge `ℝ≥0∞` and work
with honest finitely supported truncations. -/
theorem ne_top_of_forall_sum_le {a b : ℕ → ℝ≥0∞}
    (hbtop : ∀ n, b n ≠ ⊤)
    (h : ∀ k, ∑ n ∈ Finset.range k, a n ≤ ∑ n ∈ Finset.range k, b n) :
    ∀ n, a n ≠ ⊤ := by
  intro n hn
  have hsum : ∑ m ∈ Finset.range (n + 1), a m = ⊤ :=
    ENNReal.sum_eq_top.mpr ⟨n, Finset.self_mem_range_succ n, hn⟩
  have hle := h (n + 1)
  rw [hsum, top_le_iff] at hle
  obtain ⟨m, _, hm⟩ := ENNReal.sum_eq_top.mp hle
  exact hbtop m hm

/-- Prefix sums over `Fin N` restricted to indices below `k` agree with prefix
sums over `Finset.range k`, when `k ≤ N`.

`FiniteVector.prefixSum` filters `Finset.univ : Finset (Fin N)`, while the
sequence hypotheses of the majorization argument are stated over
`Finset.range k`.  Reconciling the two index sets is the only friction in
transporting one to the other. -/
theorem sum_filter_fin_eq_sum_range {N k : ℕ} (hk : k ≤ N) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), g (i : ℕ)
      = ∑ n ∈ Finset.range k, g n := by
  classical
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun n => if n < k then g n else 0) N]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h hk, h⟩⟩

/-- The `Fin N` view of a finite-valued sequence: coordinates as reals. -/
noncomputable def finView (a : ℕ → ℝ≥0∞) (N : ℕ) (i : Fin N) : ℝ :=
  ((a (i : ℕ)).toNNReal : ℝ)

/-- `finView` is nonnegative. -/
theorem finView_nonneg (a : ℕ → ℝ≥0∞) (N : ℕ) (i : Fin N) : 0 ≤ finView a N i :=
  (a (i : ℕ)).toNNReal.coe_nonneg

/-- `finView` inherits antitonicity from the sequence.

Needs finiteness because `ENNReal.toNNReal` collapses `⊤` to `0`, which would
break monotonicity exactly at an infinite coordinate. -/
theorem finView_antitone {a : ℕ → ℝ≥0∞} (ha : Antitone a) (hfin : ∀ n, a n ≠ ⊤)
    (N : ℕ) : Antitone (finView a N) := by
  intro i j hij
  simp only [finView]
  exact_mod_cast ENNReal.toNNReal_mono (hfin _) (ha hij)

/-- The `ofFin` image of the `Fin N` view is exactly the truncation.

Both send `i < N` to `(a i).toNNReal` and everything else to `0`; the only
content is that `Real.nnabs` is the identity on a nonnegative coordinate. -/
theorem ofFin_finView (a : ℕ → ℝ≥0∞) (N : ℕ) :
    ofFin (finView a N) = truncate (fun n => (a n).toNNReal) N := by
  ext i
  by_cases hi : i < N
  · rw [ofFin_apply _ hi]
    have hn : Real.nnabs ((a i).toNNReal : ℝ) = (a i).toNNReal := by
      rw [← NNReal.coe_inj, Real.coe_nnabs]
      exact abs_of_nonneg (a i).toNNReal.coe_nonneg
    simp only [finView, truncate, Finsupp.onFinset_apply, hi, ite_eq_left]
    exact_mod_cast hn
  · rw [ofFin_apply_of_le _ hi]
    simp [truncate, hi]

/-- A finite prefix sum of finite terms, pushed through `toNNReal`. -/
theorem coe_sum_toNNReal {a : ℕ → ℝ≥0∞} (ha : ∀ n, a n ≠ ⊤) (k : ℕ) :
    ((∑ n ∈ Finset.range k, (a n).toNNReal : ℝ≥0) : ℝ≥0∞)
      = ∑ n ∈ Finset.range k, a n := by
  push_cast
  exact Finset.sum_congr rfl fun i _ => ENNReal.coe_toNNReal (ha i)

/-- Prefix sums of the `Fin N` views inherit the sequence domination. -/
theorem prefixSum_finView_le {a b : ℕ → ℝ≥0∞}
    (ha : ∀ n, a n ≠ ⊤) (hb : ∀ n, b n ≠ ⊤)
    (h : ∀ k, ∑ n ∈ Finset.range k, a n ≤ ∑ n ∈ Finset.range k, b n)
    (N k : ℕ) :
    FiniteVector.prefixSum k (finView a N)
      ≤ FiniteVector.prefixSum k (finView b N) := by
  classical
  -- The statement only has content for `k ≤ N`; past `N` both filters are all
  -- of `Finset.univ`, so the prefix sums are the ones at `N`.
  have key : ∀ m, m ≤ N →
      FiniteVector.prefixSum m (finView a N)
        ≤ FiniteVector.prefixSum m (finView b N) := by
    intro m hm
    simp only [FiniteVector.prefixSum, finView]
    rw [sum_filter_fin_eq_sum_range hm (fun n => ((a n).toNNReal : ℝ)),
      sum_filter_fin_eq_sum_range hm (fun n => ((b n).toNNReal : ℝ))]
    have hcoe : ((∑ n ∈ Finset.range m, (a n).toNNReal : ℝ≥0) : ℝ≥0∞)
        ≤ ((∑ n ∈ Finset.range m, (b n).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [coe_sum_toNNReal ha, coe_sum_toNNReal hb]; exact h m
    have hnn : (∑ n ∈ Finset.range m, (a n).toNNReal)
        ≤ ∑ n ∈ Finset.range m, (b n).toNNReal := by
      exact_mod_cast hcoe
    exact_mod_cast hnn
  by_cases hk : k ≤ N
  · exact key k hk
  · have hkN : N ≤ k := (not_le.mp hk).le
    have hfa : ∀ j : ℕ, N ≤ j →
        Finset.univ.filter (fun i : Fin N => (i : ℕ) < j) = Finset.univ :=
      fun j hj => Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hj
    rw [FiniteVector.prefixSum, FiniteVector.prefixSum, hfa k hkN]
    have hN := key N (le_refl N)
    rw [FiniteVector.prefixSum, FiniteVector.prefixSum, hfa N (le_refl N)] at hN
    exact hN

/-- **Weak majorization implies domination, for the extension.**

If `a` is antitone and every prefix sum of `a` is dominated by the
corresponding prefix sum of `b`, then `Φ.extend a ≤ Φ.extend b`.

Three cases, and only the last is the transfer descent:

* some `b n = ⊤`, so the right side is `⊤`;
* otherwise `ne_top_of_forall_sum_le` makes `a` finite everywhere too;
* with both finite, every finitely supported `c ≤ a` is bounded by a truncation
  of `a`, which *is* antitone, and `le_of_prefixSum_le` compares it to the
  matching truncation of `b`. -/
theorem extend_le_extend_of_forall_sum_le {a b : ℕ → ℝ≥0∞}
    (ha : Antitone a)
    (h : ∀ k, ∑ n ∈ Finset.range k, a n ≤ ∑ n ∈ Finset.range k, b n) :
    Φ.extend a ≤ Φ.extend b := by
  classical
  by_cases hbtop : ∃ n, b n = ⊤
  · obtain ⟨n, hn⟩ := hbtop
    rw [Φ.extend_eq_top_of_eq_top hn]
    exact le_top
  have hbfin : ∀ n, b n ≠ ⊤ := by
    intro n hn; exact hbtop ⟨n, hn⟩
  have hafin : ∀ n, a n ≠ ⊤ := ne_top_of_forall_sum_le hbfin h
  refine iSup_le fun c => ?_
  -- Pick `N` past the support of `c`.
  obtain ⟨N, hN⟩ := c.1.support.exists_nat_subset_range
  -- `c ≤ truncate a N`, so `mono` bounds `Φ c`.
  have hct : c.1 ≤ truncate (fun n => (a n).toNNReal) N := by
    intro i
    by_cases hi : i < N
    · have hle : (c.1 i : ℝ≥0∞) ≤ a i := c.2 i
      have : (c.1 i : ℝ≥0∞) ≤ ((truncate (fun n => (a n).toNNReal) N) i : ℝ≥0∞) := by
        simpa [truncate, hi, ENNReal.coe_toNNReal (hafin i)] using hle
      exact_mod_cast this
    · have : c.1 i = 0 := by
        by_contra hne
        exact hi (Finset.mem_range.mp (hN (Finsupp.mem_support_iff.mpr hne)))
      simp [this]
  -- The two truncations are the `ofFin` images of the `Fin N` views.
  have hAt : Φ (truncate (fun n => (a n).toNNReal) N)
      ≤ Φ (truncate (fun n => (b n).toNNReal) N) := by
    rw [← ofFin_finView a N, ← ofFin_finView b N]
    exact Φ.le_of_prefixSum_le (finView_antitone ha hafin N)
      (finView_nonneg a N) (finView_nonneg b N)
      (fun k => prefixSum_finView_le hafin hbfin h N k)
  calc (Φ c.1 : ℝ≥0∞)
      ≤ (Φ (truncate (fun n => (a n).toNNReal) N) : ℝ≥0∞) := by exact_mod_cast Φ.mono hct
    _ ≤ (Φ (truncate (fun n => (b n).toNNReal) N) : ℝ≥0∞) := by exact_mod_cast hAt
    _ ≤ Φ.extend b :=
        le_extend_of_dominated Φ b (truncate (fun n => (b n).toNNReal) N)
          (fun i => (ENNReal.coe_le_coe.mpr
            (truncate_le (fun n => (b n).toNNReal) N i)).trans_eq
              (ENNReal.coe_toNNReal (hbfin i)))

/-! ### Algebraic laws of the extension -/

/-- The extension is monotone: a larger sequence has more dominated truncations.

Immediate from the definition -- `Dominated a` embeds into `Dominated b` -- and
it is the reason no separate "restriction" lemma is needed downstream. -/
theorem extend_mono {a b : ℕ → ℝ≥0∞} (hab : ∀ i, a i ≤ b i) :
    Φ.extend a ≤ Φ.extend b := by
  refine iSup_le fun c => ?_
  exact le_extend_of_dominated Φ b c.1 fun i => (c.2 i).trans (hab i)

/-- Scaling a dominated sequence stays dominated, and scales the gauge. -/
theorem smul_le_extend_smul (c : ℝ≥0) (a : ℕ → ℝ≥0∞) (d : Dominated a) :
    (c : ℝ≥0∞) * (Φ d.1 : ℝ≥0∞) ≤ Φ.extend (fun i => (c : ℝ≥0∞) * a i) := by
  have hdom : ∀ i, (((c • d.1) i : ℝ≥0) : ℝ≥0∞) ≤ (c : ℝ≥0∞) * a i := by
    intro i
    simp only [Finsupp.smul_apply, smul_eq_mul, ENNReal.coe_mul]
    gcongr
    exact d.2 i
  have hb := le_extend_of_dominated Φ (fun i => (c : ℝ≥0∞) * a i) (c • d.1) hdom
  rwa [Φ.smul, ENNReal.coe_mul] at hb

/-- The extension is positively homogeneous.

One direction is `smul_le_extend_smul` plus `ENNReal.mul_iSup`; the other runs the
same argument at `c⁻¹`, which is why `c = 0` is handled separately -- scaling by
zero collapses the index set rather than permuting it. -/
theorem extend_smul (c : ℝ≥0) (a : ℕ → ℝ≥0∞) :
    Φ.extend (fun i => (c : ℝ≥0∞) * a i) = (c : ℝ≥0∞) * Φ.extend a := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [ENNReal.coe_zero, zero_mul]
    refine le_antisymm (iSup_le fun d => ?_) (zero_le)
    have hzero : d.1 = 0 := by
      ext i; simpa using d.2 i
    simp [hzero]
  refine le_antisymm (iSup_le fun d => ?_) ?_
  · -- `d ≤ c • a` gives `c⁻¹ • d ≤ a`, and `Φ d = c * Φ (c⁻¹ • d)`.
    have hdom : ∀ i, (((c⁻¹ • d.1) i : ℝ≥0) : ℝ≥0∞) ≤ a i := by
      intro i
      have h := d.2 i
      simp only [Finsupp.smul_apply, smul_eq_mul, ENNReal.coe_mul]
      calc ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * (d.1 i : ℝ≥0∞)
          ≤ ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * ((c : ℝ≥0∞) * a i) := by gcongr
        _ = a i := by
            rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc,
              ENNReal.coe_one, one_mul]
    have hb := le_extend_of_dominated Φ a (c⁻¹ • d.1) hdom
    rw [Φ.smul] at hb
    have hexp : (Φ d.1 : ℝ≥0∞) = (c : ℝ≥0∞) * ((c⁻¹ * Φ d.1 : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [hexp]
    gcongr
  · simp only [extend, ENNReal.mul_iSup]
    exact iSup_le fun d => smul_le_extend_smul Φ c a d

/-- The lower part of a splitting: `c` capped coordinatewise at `x`. -/
noncomputable def capAt (c : ℕ →₀ ℝ≥0) (x : ℕ → ℝ≥0∞) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset c.support (fun i => min (c i) (x i).toNNReal)
    (by
      intro i hi
      by_cases h : c i = 0
      · simp [h] at hi
      · exact Finsupp.mem_support_iff.mpr h)

/-- The cap reads off coordinatewise as a minimum. -/
@[simp]
theorem capAt_apply (c : ℕ →₀ ℝ≥0) (x : ℕ → ℝ≥0∞) (i : ℕ) :
    capAt c x i = min (c i) (x i).toNNReal := by
  simp [capAt]

/-- The cap is below `c`. -/
theorem capAt_le (c : ℕ →₀ ℝ≥0) (x : ℕ → ℝ≥0∞) : capAt c x ≤ c := by
  intro i; simp [capAt_apply]

/-- The cap is dominated by `x`, provided `x` is finite where it matters. -/
theorem capAt_le_ennreal (c : ℕ →₀ ℝ≥0) {x : ℕ → ℝ≥0∞} (hx : ∀ i, x i ≠ ⊤)
    (i : ℕ) : ((capAt c x i : ℝ≥0) : ℝ≥0∞) ≤ x i := by
  rw [capAt_apply]
  calc ((min (c i) (x i).toNNReal : ℝ≥0) : ℝ≥0∞)
      ≤ (((x i).toNNReal : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast min_le_right _ _
    _ = x i := ENNReal.coe_toNNReal (hx i)

/-- **Subadditivity of the extension.**

The two `⊤` cases collapse the right-hand side, so the splitting argument only
ever runs on finite-valued sequences -- the same reduction that makes
`extend_le_extend_of_forall_sum_le` work.

For the finite case, a dominated `c ≤ x + y` splits as `capAt c x` and the
truncated difference `c - capAt c x`, and `Φ.add_le` finishes. -/
theorem extend_add_le (x y : ℕ → ℝ≥0∞) :
    Φ.extend (fun i => x i + y i) ≤ Φ.extend x + Φ.extend y := by
  classical
  by_cases hx : ∃ i, x i = ⊤
  · obtain ⟨i, hi⟩ := hx
    rw [Φ.extend_eq_top_of_eq_top hi]
    simp
  by_cases hy : ∃ i, y i = ⊤
  · obtain ⟨i, hi⟩ := hy
    rw [Φ.extend_eq_top_of_eq_top hi]
    simp
  have hxf : ∀ i, x i ≠ ⊤ := fun i hi => hx ⟨i, hi⟩
  have hyf : ∀ i, y i ≠ ⊤ := fun i hi => hy ⟨i, hi⟩
  refine iSup_le fun c => ?_
  set c₁ := capAt c.1 x with hc₁
  set c₂ := c.1 - c₁ with hc₂
  -- `c₁ + c₂ = c` because `c₁ ≤ c` pointwise.
  have hsplit : c₁ + c₂ = c.1 := by
    ext i
    have h1 : c₁ i ≤ c.1 i := capAt_le c.1 x i
    simp only [hc₂, Finsupp.add_apply, Finsupp.tsub_apply]
    exact_mod_cast add_tsub_cancel_of_le h1
  -- `c₂` is dominated by `y`.
  have hc₂y : ∀ i, ((c₂ i : ℝ≥0) : ℝ≥0∞) ≤ y i := by
    intro i
    have hcxy : ((c.1 i : ℝ≥0) : ℝ≥0∞) ≤ x i + y i := c.2 i
    simp only [hc₂, Finsupp.tsub_apply, hc₁, capAt_apply]
    rcases le_total (c.1 i) ((x i).toNNReal) with hle | hle
    · simp [min_eq_left hle]
    · rw [min_eq_right hle]
      have hxc : ((x i).toNNReal : ℝ≥0∞) = x i := ENNReal.coe_toNNReal (hxf i)
      have : ((c.1 i - (x i).toNNReal : ℝ≥0) : ℝ≥0∞) = (c.1 i : ℝ≥0∞) - x i := by
        rw [ENNReal.coe_sub, hxc]
      rw [this]
      exact tsub_le_iff_right.mpr (by rwa [add_comm] at hcxy)
  calc (Φ c.1 : ℝ≥0∞)
      = (Φ (c₁ + c₂) : ℝ≥0∞) := by rw [hsplit]
    _ ≤ ((Φ c₁ + Φ c₂ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast Φ.add_le c₁ c₂
    _ = (Φ c₁ : ℝ≥0∞) + (Φ c₂ : ℝ≥0∞) := by push_cast; ring
    _ ≤ Φ.extend x + Φ.extend y := by
        gcongr
        · exact le_extend_of_dominated Φ x c₁ (capAt_le_ennreal c.1 hxf)
        · exact le_extend_of_dominated Φ y c₂ hc₂y

/-- **The extension is monotone in the gauge.**

If one gauge dominates another on every finitely supported sequence, the same
holds for their extensions.  Immediate, because both suprema range over the
*same* index set `Dominated a` and only the summand changes — which is what lets
scale comparisons (the `ℓᵖ` nesting, say) be proved once at the level of
finitely supported sequences and then transported. -/
theorem extend_le_extend_of_le {Φ₁ Φ₂ : SymmetricGauge}
    (h : ∀ c : ℕ →₀ ℝ≥0, Φ₁ c ≤ Φ₂ c) (a : ℕ → ℝ≥0∞) :
    Φ₁.extend a ≤ Φ₂.extend a := by
  refine iSup_le fun c => ?_
  calc (Φ₁ c.1 : ℝ≥0∞) ≤ (Φ₂ c.1 : ℝ≥0∞) := by exact_mod_cast h c.1
    _ ≤ Φ₂.extend a := le_extend_of_dominated Φ₂ a c.1 c.2

/-- **The extension agrees with the gauge on finitely supported sequences.**

The supremum defining `Φ.extend ↑c` is attained at `c` itself: `c` is dominated
by its own coercion, and `mono` bounds every other dominated sequence by it.

This is what reduces statements about `extend` to statements about `Φ`, and in
particular what lets an equality of extensions be tested on finsupps. -/
theorem extend_coe (c : ℕ →₀ ℝ≥0) :
    Φ.extend (fun i => (c i : ℝ≥0∞)) = (Φ c : ℝ≥0∞) := by
  refine le_antisymm (iSup_le fun d => ?_) ?_
  · -- Every dominated `d` is below `c` termwise, so `mono` applies.
    have hdc : d.1 ≤ c := by
      intro i
      have h := d.2 i
      simp only at h
      exact_mod_cast h
    exact_mod_cast Φ.mono hdc
  · exact le_extend_of_dominated Φ _ c fun i => le_rfl

/-- Two gauges agreeing on every finitely supported sequence have equal
extensions.

Antisymmetry of `extend_le_extend_of_le`.  Together with `extend_coe` this is the
reduction the Calkin-injectivity statement needs: it turns an equality of
extensions into an equality of gauges on finsupps, which is where a realization
argument can act. -/
theorem extend_eq_extend_of_eq {Φ₁ Φ₂ : SymmetricGauge}
    (h : ∀ c : ℕ →₀ ℝ≥0, Φ₁ c = Φ₂ c) (a : ℕ → ℝ≥0∞) :
    Φ₁.extend a = Φ₂.extend a :=
  le_antisymm (extend_le_extend_of_le (fun c => (h c).le) a)
    (extend_le_extend_of_le (fun c => (h c).ge) a)

end SymmetricGauge

end TauCeti
