/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm

/-!
# Real-valued view of a canonical symmetric ideal family

`TauCeti.SymmetricOperatorIdealFamily` stores its gauge in `ℝ≥0∞`, extended by `∞`
off the ideal.  That is the right presentation for the library: it makes the gauge
total, gives the structure an `ext` lemma, and is what a Mathlib-bound development
wants.  The Davis--Kahan estimates, by contrast, are stated and proved in `ℝ` — the
paper's constants are real, and the proofs run on `linarith`, `nlinarith` and
`mul_le_mul_of_nonneg_*`, none of which work over `ℝ≥0∞`.

This file supplies the missing `ℝ` view, so that migrating a theorem off the
historical free-data record — a membership predicate plus a real gauge, since
retired — is a **retype and not a re-proof**.

## Why this file exists at all

Phase C of the §13.2 migration was released three times without being started, and
the recorded reason each time was that it is "a re-proof over a differently-valued
gauge": every conclusion changes type from `ℝ` to `ℝ≥0∞`, `gauge_nonneg` goes
vacuous, `∞` cases appear, and Neumann summability in `ℝ` and in `ℝ≥0∞` are
different theorems.

All of that is true, and all of it is about a question the lane does not have to
answer.  *Which structure parameterizes a theorem* and *which numeric type its
estimate lives in* are separable, and they had been conflated because the canonical
family had no `ℝ` view to migrate onto — only `KyFanDominantIdealFamily` had one,
and that structure is strictly stronger, so retyping onto it would weaken every
theorem it touched.  With the view below, the 18 remaining legacy-binder modules
change their binder and keep their proofs; restating the estimates in `ℝ≥0∞` becomes
a separate and genuinely optional decision.

## Where the `ℝ≥0∞` arithmetic lives

Phase C stated every lemma here over `gaugeReal`/`Mem` but *proved* it through the
historical record, so that retyping the tree cost no proof work.  Phase D paid that debt: every proof below now runs on the canonical laws
directly, and this file no longer imports the adapter.

The design point is where the bill landed.  Turning an `ℝ≥0∞` law into an `ℝ` one needs
a finiteness side condition at each step -- `ENNReal.toReal_mono` wants the larger side
finite, `toReal_add` wants both summands finite -- and that reasoning appears **in this
file only**, not at the 117 call sites across 30 modules that a direct migration would
have had to re-prove.  Every `Mem` hypothesis below is exactly the finiteness those
conversions consume.

Completeness is the one law that genuinely needs `IsComplete`, so that instance is
assumed on `gaugeReal_complete` alone rather than on the section; the other laws hold
for any canonical symmetric family.
-/

open scoped ENNReal

namespace TauCeti

namespace SymmetricOperatorIdealFamily

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)


/-- Membership in the ideal: the gauge is finite.

The same predicate as `OperatorIdealFamily.carrier`, spelled as the `Mem` the
Davis--Kahan statements are written against. -/
abbrev Mem (A : E →L[𝕜] F) : Prop :=
  N.toOperatorIdealFamily.gauge A ≠ ∞

/-- The ideal gauge read in `ℝ`.  Meaningful on members; off the ideal the stored
gauge is `∞` and `ENNReal.toReal` sends it to `0`, which is why every lemma below
that needs a value carries a `Mem` hypothesis. -/
noncomputable abbrev gaugeReal (A : E →L[𝕜] F) : ℝ :=
  (N.toOperatorIdealFamily.gauge A).toReal

/-- `Mem` is exactly membership in the canonical carrier. -/
theorem mem_iff_mem_carrier (A : E →L[𝕜] F) :
    N.Mem A ↔ A ∈ N.toOperatorIdealFamily.carrier := Iff.rfl

/-- The real gauge is the `toReal` of the stored `ℝ≥0∞` gauge. -/
theorem gaugeReal_eq_toReal (A : E →L[𝕜] F) :
    N.gaugeReal A = (N.toOperatorIdealFamily.gauge A).toReal := rfl

/-! ### The ideal laws, in `ℝ` -/

/-- The zero operator lies in every ideal. -/
theorem zero_mem : N.Mem (0 : E →L[𝕜] F) :=
  N.toOperatorIdealFamily.carrier.zero_mem

/-- Ideals are closed under addition. -/
theorem add_mem {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) : N.Mem (A + B) :=
  N.toOperatorIdealFamily.carrier.add_mem hA hB

/-- Ideals are closed under scalar multiplication. -/
theorem smul_mem (c : 𝕜) {A : E →L[𝕜] F} (hA : N.Mem A) : N.Mem (c • A) :=
  N.toOperatorIdealFamily.carrier.smul_mem _ hA

/-- A symmetric ideal is closed under adjoints. -/
theorem adjoint_mem {A : E →L[𝕜] F} (hA : N.Mem A) : N.Mem A.adjoint :=
  N.adjoint_mem_carrier hA

/-- The two-sided ideal law: outer composition stays in the ideal. -/
theorem comp_mem (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E) (hA : N.Mem A) :
    N.Mem (L ∘L A ∘L R) :=
  N.toOperatorIdealFamily.comp_mem_carrier _ _ hA

/-- The real gauge is nonnegative on members. -/
theorem gaugeReal_nonneg {A : E →L[𝕜] F} (_hA : N.Mem A) : 0 ≤ N.gaugeReal A :=
  ENNReal.toReal_nonneg

/-- The zero operator has zero gauge. -/
theorem gaugeReal_zero : N.gaugeReal (0 : E →L[𝕜] F) = 0 := by
  simp [gaugeReal]

/-- A member of gauge zero is the zero operator. -/
theorem gaugeReal_eq_zero {A : E →L[𝕜] F} (hA : N.Mem A)
    (h : N.gaugeReal A = 0) : A = 0 :=
  N.toOperatorIdealFamily.gauge_eq_zero
    (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right hA)

/-- The real gauge is subadditive on members. -/
theorem gaugeReal_add_le {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gaugeReal (A + B) ≤ N.gaugeReal A + N.gaugeReal B := by
  rw [gaugeReal_eq_toReal, gaugeReal_eq_toReal, gaugeReal_eq_toReal,
    ← ENNReal.toReal_add hA hB]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
    (N.toOperatorIdealFamily.gauge_add_le _ _)

/-- The real gauge is absolutely homogeneous on members. -/
theorem gaugeReal_smul (c : 𝕜) {A : E →L[𝕜] F} (_hA : N.Mem A) :
    N.gaugeReal (c • A) = ‖c‖ * N.gaugeReal A := by
  rw [gaugeReal_eq_toReal, gaugeReal_eq_toReal,
    N.toOperatorIdealFamily.gauge_smul, ENNReal.toReal_mul, toReal_enorm]

/-- The real gauge is adjoint-invariant. -/
theorem gaugeReal_adjoint {A : E →L[𝕜] F} (_hA : N.Mem A) :
    N.gaugeReal A.adjoint = N.gaugeReal A := by
  rw [gaugeReal_eq_toReal, gaugeReal_eq_toReal, N.gauge_adjoint]

/-- The two-sided estimate, in `ℝ`. -/
theorem gaugeReal_comp_le (L : F →L[𝕜] G) (R : H →L[𝕜] E) {A : E →L[𝕜] F}
    (hA : N.Mem A) :
    N.gaugeReal (L ∘L A ∘L R) ≤ ‖L‖ * N.gaugeReal A * ‖R‖ := by
  have hbound := N.toOperatorIdealFamily.gauge_comp_le L A R
  have hfin : ‖L‖ₑ * N.toOperatorIdealFamily.gauge A * ‖R‖ₑ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA) (by simp)
  refine (ENNReal.toReal_mono hfin hbound).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm, toReal_enorm]

/-- The operator norm is dominated by the real gauge on members. -/
theorem opNorm_le_gaugeReal {A : E →L[𝕜] F} (hA : N.Mem A) : ‖A‖ ≤ N.gaugeReal A := by
  have h := ENNReal.toReal_mono hA (N.toOperatorIdealFamily.enorm_le_gauge A)
  rwa [toReal_enorm] at h

/-- The ideal is complete in its own gauge.  `M` rather than `N` for the
threshold index, since `N` is the family here. -/
theorem gaugeReal_complete [N.toOperatorIdealFamily.IsComplete]
    (A : ℕ → E →L[𝕜] F) (hmem : ∀ n, N.Mem (A n))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n, M ≤ m → M ≤ n →
      N.gaugeReal (A m - A n) < ε) :
    ∃ L, N.Mem L ∧ ∀ ε : ℝ, 0 < ε → ∃ M, ∀ n, M ≤ n →
      N.gaugeReal (A n - L) < ε := by
  -- Read the sequence inside the ideal, where the gauge *is* the norm.
  -- Hand `Elem.mk` the membership in its canonical `∈ carrier` form.  Passing `hmem n`
  -- directly leaves the `Mem` spelling in the term, and `Elem.val_mk` then will not match
  -- against it -- the two are only definitionally the same predicate.
  set a : ℕ → N.toOperatorIdealFamily.Elem E F :=
    fun n => OperatorIdealFamily.Elem.mk ((N.mem_iff_mem_carrier (A n)).mp (hmem n)) with ha
  have hdist : ∀ m n, dist (a m) (a n) = N.gaugeReal (A m - A n) := by
    intro m n
    rw [dist_eq_norm, ha, OperatorIdealFamily.Elem.norm_def]
    simp [gaugeReal, OperatorIdealFamily.Elem.val_mk]
  have hcs : CauchySeq a := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hcauchy ε hε
    exact ⟨M, fun m hm n hn => by rw [hdist]; exact hM m n hm hn⟩
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨l.val, l.val_mem, fun ε hε => ?_⟩
  rw [Metric.tendsto_atTop] at hl
  obtain ⟨M, hM⟩ := hl ε hε
  refine ⟨M, fun n hn => ?_⟩
  have := hM n hn
  rwa [dist_eq_norm, OperatorIdealFamily.Elem.norm_def, show (a n - l).val = A n - l.val from
    by simp [ha]] at this

/-! ### Consequences -/

/-- Ideals are closed under negation. -/
theorem neg_mem {A : E →L[𝕜] F} (hA : N.Mem A) : N.Mem (-A) := by
  simpa using N.smul_mem (-1 : 𝕜) hA

/-- The real gauge is unchanged by negation. -/
theorem gaugeReal_neg {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gaugeReal (-A) = N.gaugeReal A := by
  simpa using N.gaugeReal_smul (-1 : 𝕜) hA

/-- Membership is preserved by left composition with a bounded map. -/
theorem comp_left_mem (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.Mem (L ∘L A) := by
  simpa using N.comp_mem L (ContinuousLinearMap.id 𝕜 E) hA

/-- Left composition is bounded by the operator norm times the gauge. -/
theorem gaugeReal_comp_left_le_mul (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gaugeReal (L ∘L A) ≤ ‖L‖ * N.gaugeReal A := by
  have hraw := N.gaugeReal_comp_le L (ContinuousLinearMap.id 𝕜 E) hA
  calc
    N.gaugeReal (L ∘L A)
        = N.gaugeReal (L ∘L A ∘L ContinuousLinearMap.id 𝕜 E) := by simp
    _ ≤ ‖L‖ * N.gaugeReal A * ‖ContinuousLinearMap.id 𝕜 E‖ := hraw
    _ ≤ ‖L‖ * N.gaugeReal A * 1 :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E))
        (mul_nonneg (norm_nonneg L) (N.gaugeReal_nonneg hA))
    _ = ‖L‖ * N.gaugeReal A := by ring

/-- Left composition by a contraction does not increase the gauge. -/
theorem gaugeReal_comp_left_le (L : F →L[𝕜] G) {A : E →L[𝕜] F}
    (hA : N.Mem A) (hL : ‖L‖ ≤ 1) :
    N.gaugeReal (L ∘L A) ≤ N.gaugeReal A := by
  calc
    N.gaugeReal (L ∘L A) ≤ ‖L‖ * N.gaugeReal A := N.gaugeReal_comp_left_le_mul L hA
    _ ≤ 1 * N.gaugeReal A := mul_le_mul_of_nonneg_right hL (N.gaugeReal_nonneg hA)
    _ = N.gaugeReal A := one_mul _

/-- Membership is preserved by right composition with a bounded map. -/
theorem comp_right_mem {A : E →L[𝕜] F} (R : H →L[𝕜] E) (hA : N.Mem A) :
    N.Mem (A ∘L R) := by
  simpa using N.comp_mem (ContinuousLinearMap.id 𝕜 F) R hA

/-- Right composition is bounded by the gauge times the operator norm. -/
theorem gaugeReal_comp_right_le_mul {A : E →L[𝕜] F} (R : H →L[𝕜] E) (hA : N.Mem A) :
    N.gaugeReal (A ∘L R) ≤ N.gaugeReal A * ‖R‖ := by
  have hraw := N.gaugeReal_comp_le (ContinuousLinearMap.id 𝕜 F) R hA
  have hid : ‖ContinuousLinearMap.id 𝕜 F‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := F)
  calc
    N.gaugeReal (A ∘L R)
        = N.gaugeReal ((ContinuousLinearMap.id 𝕜 F) ∘L A ∘L R) := by simp
    _ ≤ ‖ContinuousLinearMap.id 𝕜 F‖ * N.gaugeReal A * ‖R‖ := hraw
    _ ≤ (1 * N.gaugeReal A) * ‖R‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hid (N.gaugeReal_nonneg hA))
        (norm_nonneg R)
    _ = N.gaugeReal A * ‖R‖ := by ring

/-- Right composition by a contraction does not increase the gauge. -/
theorem gaugeReal_comp_right_le {A : E →L[𝕜] F} (R : H →L[𝕜] E)
    (hA : N.Mem A) (hR : ‖R‖ ≤ 1) :
    N.gaugeReal (A ∘L R) ≤ N.gaugeReal A := by
  have hraw := N.gaugeReal_comp_le (ContinuousLinearMap.id 𝕜 F) R hA
  have hnonneg := N.gaugeReal_nonneg hA
  calc
    N.gaugeReal (A ∘L R)
        = N.gaugeReal ((ContinuousLinearMap.id 𝕜 F) ∘L A ∘L R) := by simp
    _ ≤ ‖ContinuousLinearMap.id 𝕜 F‖ * N.gaugeReal A * ‖R‖ := hraw
    _ ≤ 1 * N.gaugeReal A * 1 := by
      gcongr
      · exact ContinuousLinearMap.norm_id_le
    _ = N.gaugeReal A := by ring

/-- Two-sided composition by contractions does not increase the gauge. -/
theorem gaugeReal_comp_le_of_contractions (L : F →L[𝕜] G) {A : E →L[𝕜] F}
    (R : H →L[𝕜] E) (hA : N.Mem A) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    N.gaugeReal (L ∘L A ∘L R) ≤ N.gaugeReal A := by
  have hnonneg := N.gaugeReal_nonneg hA
  calc
    N.gaugeReal (L ∘L A ∘L R) ≤ ‖L‖ * N.gaugeReal A * ‖R‖ :=
      N.gaugeReal_comp_le L R hA
    _ ≤ 1 * N.gaugeReal A * 1 := by gcongr
    _ = N.gaugeReal A := by ring

/-- Ideals are closed under subtraction. -/
theorem sub_mem {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) : N.Mem (A - B) := by
  rw [sub_eq_add_neg]
  exact N.add_mem hA (N.neg_mem hB)

/-- The real gauge is subadditive for differences. -/
theorem gaugeReal_sub_le {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gaugeReal (A - B) ≤ N.gaugeReal A + N.gaugeReal B := by
  rw [sub_eq_add_neg]
  calc
    N.gaugeReal (A + -B) ≤ N.gaugeReal A + N.gaugeReal (-B) :=
      N.gaugeReal_add_le hA (N.neg_mem hB)
    _ = N.gaugeReal A + N.gaugeReal B := by rw [N.gaugeReal_neg hB]

/-- The gauge vanishes exactly on the zero operator. -/
theorem gaugeReal_eq_zero_iff {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gaugeReal A = 0 ↔ A = 0 := by
  refine ⟨N.gaugeReal_eq_zero hA, ?_⟩
  rintro rfl
  exact N.gaugeReal_zero

/-- **A gauge-Cauchy criterion from a real Cauchy majorant.**

If the gauge of `P m - P n` is bounded by `G m - G n` whenever `n ≤ m`, and `G` is Cauchy,
then the `P n` are Cauchy in gauge.  The `≤` hypothesis is one-sided on purpose -- that is
how such a bound arises, from a monotone partial-sum estimate -- so the proof splits on
`le_total` and flips the difference with `gaugeReal_neg` in the other case.

Both Neumann-series constructions need this, one bounded and one unbounded, and each had
written it out; they differed only in the name of the threshold. -/
theorem gaugeReal_sub_lt_of_cauchy_majorant {P : ℕ → E →L[𝕜] F} {G : ℕ → ℝ}
    (hPmem : ∀ n, N.Mem (P n))
    (hgap : ∀ {m n : ℕ}, n ≤ m → N.gaugeReal (P m - P n) ≤ G m - G n)
    (hGcauchy : CauchySeq G) :
    ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n, M ≤ m → M ≤ n → N.gaugeReal (P m - P n) < ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hGcauchy ε hε
  refine ⟨M, fun m n hm hn => ?_⟩
  rcases le_total n m with h | h
  · refine lt_of_le_of_lt (hgap h) ?_
    calc
      G m - G n ≤ |G m - G n| := le_abs_self _
      _ = dist (G m) (G n) := (Real.dist_eq _ _).symm
      _ < ε := hM m hm n hn
  · have hswap : N.gaugeReal (P m - P n) = N.gaugeReal (P n - P m) := by
      rw [show P m - P n = -(P n - P m) from by abel,
        N.gaugeReal_neg (N.sub_mem (hPmem n) (hPmem m))]
    rw [hswap]
    refine lt_of_le_of_lt (hgap h) ?_
    calc
      G n - G m ≤ |G n - G m| := le_abs_self _
      _ = dist (G n) (G m) := (Real.dist_eq _ _).symm
      _ < ε := hM n hn m hm

variable {ι : Type*}

/-- Ideals are closed under finite sums. -/
theorem finset_sum_mem (s : Finset ι) (A : ι → E →L[𝕜] F)
    (hA : ∀ i ∈ s, N.Mem (A i)) : N.Mem (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact N.add_mem (hA a (Finset.mem_insert_self a s))
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

/-- The gauge of a finite sum is bounded by the sum of the gauges. -/
theorem gaugeReal_finset_sum_le (s : Finset ι) (A : ι → E →L[𝕜] F)
    (hA : ∀ i ∈ s, N.Mem (A i)) :
    N.gaugeReal (∑ i ∈ s, A i) ≤ ∑ i ∈ s, N.gaugeReal (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [N.gaugeReal_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (N.gaugeReal_add_le
        (hA a (Finset.mem_insert_self a s))
        (N.finset_sum_mem s A fun i hi => hA i (Finset.mem_insert_of_mem hi))).trans
          (add_le_add le_rfl (ih fun i hi => hA i (Finset.mem_insert_of_mem hi)))

/-! ### The operator-norm family -/

/-- **The gauge bound a Sylvester fixed point satisfies.**

If `X = Inv ∘L (C + X ∘L B)` with `‖Inv‖ ≤ (ρ + δ)⁻¹` and `‖B‖ ≤ ρ`, then the gauge of `X`
obeys the corresponding scalar inequality.  The bounded and unbounded Sylvester
constructions both reach this point and had each written the same four-step `calc`; they
differ only in whether the left inverse arrives as `hA.inv` or as a supplied `J`, which is
what makes it a parameter here. -/
theorem gaugeReal_le_of_comp_add_comp_fixedPoint
    {Inv : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F} {rho delta : ℝ}
    (hpos : 0 < rho + delta) (hInv : ‖Inv‖ ≤ (rho + delta)⁻¹) (hB : ‖B‖ ≤ rho)
    (hC : N.Mem C) (hXmem : N.Mem X) (hXBmem : N.Mem (X ∘L B))
    (hfix : X = Inv ∘L (C + X ∘L B)) :
    N.gaugeReal X ≤ (rho + delta)⁻¹ * (N.gaugeReal C + N.gaugeReal X * rho) := by
  conv_lhs => rw [hfix]
  calc
    N.gaugeReal (Inv ∘L (C + X ∘L B))
        ≤ ‖Inv‖ * N.gaugeReal (C + X ∘L B) :=
      N.gaugeReal_comp_left_le_mul Inv (N.add_mem hC hXBmem)
    _ ≤ (rho + delta)⁻¹ * N.gaugeReal (C + X ∘L B) :=
      mul_le_mul_of_nonneg_right hInv (N.gaugeReal_nonneg (N.add_mem hC hXBmem))
    _ ≤ (rho + delta)⁻¹ * (N.gaugeReal C + N.gaugeReal X * rho) := by
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hpos.le)
      refine (N.gaugeReal_add_le hC hXBmem).trans (add_le_add le_rfl ?_)
      exact (N.gaugeReal_comp_right_le_mul B hXmem).trans
        (mul_le_mul_of_nonneg_left hB (N.gaugeReal_nonneg hXmem))

/-- **Partial sums differ in gauge by at most the majorant's partial sums.**

With `P n = ∑_{j<n} t j` and any real `c` dominating each `N.gaugeReal (t j)`, the gauge of
`P m - P n` is at most `∑_{j<m} c j - ∑_{j<n} c j`.  This is the hypothesis
`gaugeReal_sub_lt_of_cauchy_majorant` consumes, and both Neumann-series constructions --
bounded and unbounded -- had derived it inline from the same two `Finset.sum_Ico_eq_sub`
steps.  Stated over an arbitrary majorant `c` rather than the geometric `q ^ j * g₀` both
call sites use, because nothing in the argument looks at its shape. -/
theorem gaugeReal_sum_range_sub_le {t : ℕ → E →L[𝕜] F} {c : ℕ → ℝ}
    (htmem : ∀ n, N.Mem (t n)) (htgauge : ∀ n, N.gaugeReal (t n) ≤ c n)
    {m n : ℕ} (hnm : n ≤ m) :
    N.gaugeReal ((∑ j ∈ Finset.range m, t j) - ∑ j ∈ Finset.range n, t j)
      ≤ (∑ j ∈ Finset.range m, c j) - ∑ j ∈ Finset.range n, c j := by
  have hsum : (∑ j ∈ Finset.range m, t j) - ∑ j ∈ Finset.range n, t j
      = ∑ j ∈ Finset.Ico n m, t j := (Finset.sum_Ico_eq_sub _ hnm).symm
  have hG : ∑ j ∈ Finset.Ico n m, c j
      = (∑ j ∈ Finset.range m, c j) - ∑ j ∈ Finset.range n, c j :=
    Finset.sum_Ico_eq_sub _ hnm
  rw [hsum, ← hG]
  calc
    N.gaugeReal (∑ j ∈ Finset.Ico n m, t j)
        ≤ ∑ j ∈ Finset.Ico n m, N.gaugeReal (t j) :=
      N.gaugeReal_finset_sum_le (Finset.Ico n m) t fun j _ => htmem j
    _ ≤ ∑ j ∈ Finset.Ico n m, c j := Finset.sum_le_sum fun j _ => htgauge j

/-- Every bounded operator lies in the operator-norm ideal.  In the historical
record this was `True` by construction; canonically it is finiteness of `‖·‖ₑ`. -/
 theorem mem_operatorNormFamily (A : E →L[𝕜] F) :
    (operatorNormFamily.{u, v} 𝕜).Mem A := by
  change (operatorNormFamily.{u, v} 𝕜).toOperatorIdealFamily.gauge A ≠ ∞
  rw [gauge_operatorNormFamily]
  exact enorm_ne_top

/-- The real gauge of the operator-norm family is the operator norm. -/
@[simp] theorem gaugeReal_operatorNormFamily (A : E →L[𝕜] F) :
    (operatorNormFamily.{u, v} 𝕜).gaugeReal A = ‖A‖ := by
  rw [gaugeReal_eq_toReal, gauge_operatorNormFamily, toReal_enorm]

end SymmetricOperatorIdealFamily

end TauCeti
