/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 5
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.DavisKahan.Sylvester.ShiftedInverseGauge
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RealLowerBound

/-! # Gap Resolvent -/

open TauCeti.DavisKahan.Sylvester

/-!
# Norm-bounded gap resolvents

The unbounded Davis--Kahan development phrases spectral exteriority through the
proof-carrying predicate `TwoSidedShiftedInverseBound A c s`: a bounded
two-sided inverse of `A - c` with norm at most `s⁻¹`.  This module discharges
that predicate from a genuine spectral hypothesis — the spectrum of the operator
avoids the open interval `(c - s, c + s)`.

## History: this was the largest Spectra dependency in the tree

Until 2026-07-28 the bound was obtained from `vendor/Spectra` through the full
spectral-theorem stack: Stone's theorem (`genToGroup`) to manufacture a unitary
group from the self-adjoint operator, that group's projection-valued measure,
the bounded Borel functional calculus, the truncated symbol `(l - c)⁻¹`, and the
sharp calculus norm bound.  Two substantial intermediate theorems lived here to
support it — `spectralProjection_eq_zero_of_forall_mem_resolventSet` and
`exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero`.

**None of that is necessary.**  The bound is a C⋆-algebra fact about the
*bounded* operator `R = (A - c)⁻¹`:

* resolvent spectral mapping puts `spectrum R \ {0}` inside
  `(· - c)⁻¹ '' spectrum A` — elementary algebra with domain bookkeeping;
* the spectral gap therefore bounds `spectrum R` by `s⁻¹`;
* and for a **self-adjoint** element the norm *is* the spectral radius, which is
  Mathlib's `IsSelfAdjoint.spectralRadius_eq_nnnorm`.

The replacement lives in
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/{Resolvent,ResolventBound,SelfAdjointResolvent}.lean`
and is Spectra-free.  The two intermediate theorems were deleted rather than
kept: they were scaffolding for the PVM route, nothing outside this file used
them, and retaining them would have kept the whole projection-valued-measure
layer on the critical path of the completed Spectra removal.  They
remain in the history at `a58913e`.

This module is Spectra-free, and as the note here used to predict, it has been
relocated now that `Interop/Spectra/` is gone: it is spectral theory, and it sits
with the rest of it.
-/

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace TauCeti
namespace DavisKahan


/-- **A spectral gap gives a norm-bounded two-sided inverse.**  If the spectrum
of a self-adjoint `A` avoids `(c - s, c + s)`, then `A - c` has a bounded
two-sided inverse of norm at most `s⁻¹`. -/
theorem exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A) :
    ∃ R : H →L[ℂ] H, ‖R‖ ≤ s⁻¹ ∧
      (∀ ψ : A.domain, R (A ψ - (c : ℂ) • (ψ : H)) = (ψ : H)) ∧
      ∀ φ : H, ∃ hmem : R φ ∈ A.domain,
        A ⟨R φ, hmem⟩ - (c : ℂ) • R φ = φ := by
  -- The upstream theorem inverts `c • I - A`; the Davis--Kahan statement is about `A - c`,
  -- so the witness is the negated resolvent.  The norm bound is unaffected.
  obtain ⟨R, hnorm, hleft, hright⟩ :=
    TauCeti.LinearPMap.exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap hA hs hgap
  refine ⟨-R, by simpa using hnorm, fun ψ => ?_, fun φ => ?_⟩
  · have h := hleft ψ
    have harg : A ψ - (c : ℂ) • (ψ : H) = -((c : ℂ) • (ψ : H) - A ψ) := by module
    rw [_root_.neg_apply, harg, map_neg, h, neg_neg]
  · obtain ⟨hmem, hsolve⟩ := hright φ
    refine ⟨neg_mem hmem, ?_⟩
    have hneg : A (⟨(-R) φ, neg_mem hmem⟩ : A.domain) = -(A ⟨R φ, hmem⟩) :=
      _root_.LinearPMap.map_neg A ⟨R φ, hmem⟩
    rw [hneg]
    simp only [_root_.neg_apply]
    linear_combination (norm := module) hsolve

/-- **Genuine spectra discharge the shifted-inverse hypothesis.**  For a DK
closed operator whose canonical `LinearPMap` view is self-adjoint and whose
spectrum avoids `(c - s, c + s)`, the proof-carrying predicate
`TwoSidedShiftedInverseBound A c s` holds.  This connects the honest unbounded
Davis--Kahan hypotheses to the spectral theory. -/
theorem twoSidedShiftedInverseBound_of_spectrum_gap
    {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A) :
    TauCeti.DavisKahan.Sylvester.TwoSidedShiftedInverseBound
      A c s := by
  obtain ⟨R, hnorm, hleft, hright⟩ :=
    exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap hA hs hgap
  exact ⟨R, fun z => (hright z).choose,
    fun x => hleft x, fun z => (hright z).choose_spec, hnorm⟩

/-! ### A bounded perturbation cannot close a gap it is smaller than

This is the unbounded analogue of `realSpectrum_add_subset_of_gap`, and the only
genuinely new ingredient the unbounded Theorem 8.2 path needs.  The argument is
the Neumann one: a spectral gap of half-width `s` around `c` gives a bounded
inverse `R` of `c - A` with `‖R‖ ≤ s⁻¹`, and for `‖K‖ < s` the factorization

```text
c - (A + K) = (1 - K R) (c - A)   on dom A
```

has an invertible first factor, so the product is invertible too.
-/

/-- **A bounded perturbation of norm below the gap half-width leaves the centre
in the resolvent set.**

If the spectrum of the self-adjoint `A` avoids `(c - s, c + s)` and `‖K‖ < s`,
then `c` is not in the spectrum of `A + K`. -/
theorem notMem_spectrum_addBounded_of_spectrum_gap
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (K : H →L[ℂ] H)
    {c s : ℝ} (hs : 0 < s) (hK : ‖K‖ < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A) :
    ((c : ℝ) : ℂ) ∉
      TauCeti.LinearPMap.spectrum (TauCeti.LinearPMap.addBounded A K) := by
  rw [TauCeti.LinearPMap.notMem_spectrum_iff]
  obtain ⟨R, hnorm, hleft, hright⟩ :=
    TauCeti.LinearPMap.exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap hA hs hgap
  have hKR : ‖K ∘L R‖ < 1 := by
    have h1 : ‖K ∘L R‖ ≤ ‖K‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    have h2 : ‖K‖ * ‖R‖ ≤ ‖K‖ * s⁻¹ :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg K)
    have h3 : ‖K‖ * s⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ hs, one_mul]
      exact hK
    linarith
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hKR
  set V : H →L[ℂ] H := (↑u⁻¹ : H →L[ℂ] H) with hV
  have hUV : ∀ y : H, (1 - K ∘L R) (V y) = y := by
    intro y
    have : ((u : H →L[ℂ] H) * (↑u⁻¹ : H →L[ℂ] H)) y = y := by
      rw [← Units.val_mul, mul_inv_cancel]
      rfl
    rw [hV, ← hu]
    exact this
  have hVU : ∀ y : H, V ((1 - K ∘L R) y) = y := by
    intro y
    have : ((↑u⁻¹ : H →L[ℂ] H) * (u : H →L[ℂ] H)) y = y := by
      rw [← Units.val_mul, inv_mul_cancel]
      rfl
    rw [hV, ← hu]
    exact this
  refine ⟨R ∘L V, fun y => ?_, fun y => ?_, fun x => ?_⟩
  · exact (hright (V y)).choose
  · obtain ⟨hmem, hsolve⟩ := hright (V y)
    change ((c : ℝ) : ℂ) • (R ∘L V) y -
      (TauCeti.LinearPMap.addBounded A K) ⟨(R ∘L V) y, _⟩ = y
    have hadd : (TauCeti.LinearPMap.addBounded A K)
        (⟨R (V y), hmem⟩ : (TauCeti.LinearPMap.addBounded A K).domain)
        = A ⟨R (V y), hmem⟩ + K (R (V y)) := rfl
    change ((c : ℝ) : ℂ) • R (V y) -
      (TauCeti.LinearPMap.addBounded A K) ⟨R (V y), hmem⟩ = y
    rw [hadd]
    have hstep : ((c : ℝ) : ℂ) • R (V y) - A ⟨R (V y), hmem⟩ = V y := hsolve
    have : ((c : ℝ) : ℂ) • R (V y) - (A ⟨R (V y), hmem⟩ + K (R (V y)))
        = (1 - K ∘L R) (V y) := by
      simp only [sub_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply]
      linear_combination (norm := module) hstep
    rw [this, hUV y]
  · have hxA : ((x : H)) ∈ A.domain := x.2
    have hadd : (TauCeti.LinearPMap.addBounded A K) x
        = A ⟨(x : H), hxA⟩ + K (x : H) := rfl
    change (R ∘L V) (((c : ℝ) : ℂ) • (x : H) -
      (TauCeti.LinearPMap.addBounded A K) x) = (x : H)
    rw [hadd]
    have hw : R (((c : ℝ) : ℂ) • (x : H) - A ⟨(x : H), hxA⟩) = (x : H) :=
      hleft ⟨(x : H), hxA⟩
    have hsplit : ((c : ℝ) : ℂ) • (x : H) - (A ⟨(x : H), hxA⟩ + K (x : H))
        = (1 - K ∘L R) (((c : ℝ) : ℂ) • (x : H) - A ⟨(x : H), hxA⟩) := by
      simp only [sub_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply]
      rw [hw]
      abel
    simp only [ContinuousLinearMap.comp_apply]
    rw [hsplit, hVU, hw]

/-- **The unbounded analogue of `realSpectrum_add_subset_of_gap`.**

If the real spectrum of a self-adjoint `A` lies in `[β, α] ∪ exterior(β, α, δ)`
and `‖K‖ ≤ γ` with `2γ < δ`, then the real spectrum of `A + K` lies in the
`γ`-fattened band and the `2γ`-narrowed exterior.

This is the spectral-stability step the unbounded Theorem 8.2 path needs, and it
is a bounded-perturbation statement, not a continuation framework: each point of
the two open gaps is at distance more than `γ` from the spectrum of `A`, so
`notMem_spectrum_addBounded_of_spectrum_gap` removes it. -/
theorem spectrum_addBounded_subset_of_gap
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (K : H →L[ℂ] H)
    {alpha beta delta gam : ℝ} (hab : beta ≤ alpha) (_hdelta : 0 < delta)
    (hgam : ‖K‖ ≤ gam) (_hgamlt : 2 * gam < delta)
    (hgap : ∀ lam : ℝ, (lam : ℂ) ∈ TauCeti.LinearPMap.spectrum A →
      lam ∈ Set.Icc beta alpha ∪ {x : ℝ | x ≤ beta - delta ∨ alpha + delta ≤ x}) :
    ∀ lam : ℝ,
      (lam : ℂ) ∈ TauCeti.LinearPMap.spectrum (TauCeti.LinearPMap.addBounded A K) →
      lam ∈ Set.Icc (beta - gam) (alpha + gam) ∪
        {x : ℝ | x ≤ beta - gam - (delta - 2 * gam) ∨
          alpha + gam + (delta - 2 * gam) ≤ x} := by
  have hgam0 : 0 ≤ gam := le_trans (norm_nonneg K) hgam
  intro lam hlam
  by_contra hnot
  rw [Set.mem_union] at hnot
  have h1 : lam ∉ Set.Icc (beta - gam) (alpha + gam) := fun h => hnot (Or.inl h)
  have h2 : lam ∉ {x : ℝ | x ≤ beta - gam - (delta - 2 * gam) ∨
      alpha + gam + (delta - 2 * gam) ≤ x} := fun h => hnot (Or.inr h)
  have h2' : beta - delta + gam < lam ∧ lam < alpha + delta - gam := by
    constructor
    · by_contra hcon
      exact h2 (Or.inl (by simp only [not_lt] at hcon; linarith))
    · by_contra hcon
      exact h2 (Or.inr (by simp only [not_lt] at hcon; linarith))
  have h1' : lam < beta - gam ∨ alpha + gam < lam := by
    rcases lt_or_ge lam (beta - gam) with h | h
    · exact Or.inl h
    · exact Or.inr (by
        by_contra hcon
        exact h1 ⟨h, le_of_not_gt hcon⟩)
  -- in either open gap, choose the half-width and apply the perturbation lemma
  have hkey : ∀ s : ℝ, gam < s →
      (∀ mu ∈ Set.Ioo (lam - s) (lam + s), (mu : ℂ) ∉ TauCeti.LinearPMap.spectrum A) →
      False := by
    intro s hs hmiss
    exact notMem_spectrum_addBounded_of_spectrum_gap hA K
      (lt_of_le_of_lt hgam0 hs) (lt_of_le_of_lt hgam hs) hmiss hlam
  rcases h1' with hlow | hhigh
  · refine hkey (min (beta - lam) (lam - beta + delta)) (by
      refine lt_min ?_ ?_ <;> linarith [h2'.1]) ?_
    intro mu hmu hmem
    have hb : lam + min (beta - lam) (lam - beta + delta) ≤ beta := by
      have := min_le_left (beta - lam) (lam - beta + delta); linarith
    have hl : beta - delta ≤ lam - min (beta - lam) (lam - beta + delta) := by
      have := min_le_right (beta - lam) (lam - beta + delta); linarith
    have hmulo : beta - delta < mu := lt_of_le_of_lt hl hmu.1
    have hmuhi : mu < beta := lt_of_lt_of_le hmu.2 hb
    rcases hgap mu hmem with h | h
    · linarith [h.1]
    · rcases h with h | h
      · linarith
      · linarith
  · refine hkey (min (lam - alpha) (alpha + delta - lam)) (by
      refine lt_min ?_ ?_ <;> linarith [h2'.2]) ?_
    intro mu hmu hmem
    have ha : alpha ≤ lam - min (lam - alpha) (alpha + delta - lam) := by
      have := min_le_left (lam - alpha) (alpha + delta - lam); linarith
    have hr : lam + min (lam - alpha) (alpha + delta - lam) ≤ alpha + delta := by
      have := min_le_right (lam - alpha) (alpha + delta - lam); linarith
    have hmulo : alpha < mu := lt_of_le_of_lt ha hmu.1
    have hmuhi : mu < alpha + delta := lt_of_lt_of_le hmu.2 hr
    rcases hgap mu hmem with h | h
    · linarith [h.2]
    · rcases h with h | h
      · linarith
      · linarith

/-- **The bounded shifted inverse from coercivity against a reflection.**

This is the theorem GOAL.md section 6.2 asks for, in the form Theorem 8.1
consumes.  The bounded Section 8 argument reaches invertibility of `J (A - c)`
through `TauCeti.isUnit_of_coercive`, which needs `A` everywhere defined; that is
what blocks lifting `isQuarterAcute_of_orderedFormGap` to an unbounded ambient
operator.

No new Lax--Milgram is needed.  Coercivity against an isometry already forces the
norm lower bound `δ ‖x‖ ≤ ‖A x - c x‖`; the triangle inequality spreads it across
the whole interval `(c - δ, c + δ)` with constant `δ - |lam - c|`; each point is
then a resolvent point by `mem_resolventSet_and_norm_le_of_lower_bound`; and the existing gap
resolvent supplies the two-sided bounded inverse of norm at most `δ⁻¹`.

`J` is only required to preserve norms, so a reflection qualifies. -/
theorem twoSidedShiftedInverseBound_of_coercive_comp
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {J : H →L[ℂ] H} (hJ : ∀ y : H, ‖J y‖ = ‖y‖)
    {c δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ x : A.domain,
      δ * ‖(x : H)‖ ^ 2 ≤ (⟪J (A x - (c : ℂ) • (x : H)), (x : H)⟫_ℂ).re) :
    TauCeti.DavisKahan.Sylvester.TwoSidedShiftedInverseBound A c δ := by
  refine twoSidedShiftedInverseBound_of_spectrum_gap hA hδ ?_
  intro lam hlam
  have hbase := TauCeti.LinearPMap.norm_sub_smul_ge_of_coercive_comp hJ hcoer
  obtain ⟨h1, h2⟩ := hlam
  have hpos : 0 < δ - |lam - c| := by
    rcases abs_cases (lam - c) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  have hnorm : ∀ x : A.domain,
      (δ - |lam - c|) * ‖(x : H)‖ ≤ ‖A x - ((lam : ℝ) : ℂ) • (x : H)‖ := by
    intro x
    have hsplit : A x - ((lam : ℝ) : ℂ) • (x : H)
        = (A x - ((c : ℝ) : ℂ) • (x : H)) + (((c - lam : ℝ)) : ℂ) • (x : H) := by
      push_cast
      module
    have htri : ‖A x - ((c : ℝ) : ℂ) • (x : H)‖ - ‖(((c - lam : ℝ)) : ℂ) • (x : H)‖
        ≤ ‖A x - ((lam : ℝ) : ℂ) • (x : H)‖ := by
      rw [hsplit]
      simpa using
        norm_sub_norm_le (A x - ((c : ℝ) : ℂ) • (x : H)) (-((((c - lam : ℝ)) : ℂ) • (x : H)))
    have hsm : ‖(((c - lam : ℝ)) : ℂ) • (x : H)‖ = |c - lam| * ‖(x : H)‖ := by
      rw [norm_smul]
      congr 1
      exact Complex.norm_real (c - lam)
    have habs : |c - lam| = |lam - c| := abs_sub_comm c lam
    have hb := hbase x
    rw [hsm, habs] at htri
    -- `linarith` does not close this: the two sides carry different (defeq) `ℝ` order
    -- instances, so its atoms do not match.  Chain the two bounds directly.
    calc (δ - |lam - c|) * ‖(x : H)‖
        = δ * ‖(x : H)‖ - |lam - c| * ‖(x : H)‖ := by ring
      _ ≤ ‖A x - ((c : ℝ) : ℂ) • (x : H)‖ - |lam - c| * ‖(x : H)‖ :=
          sub_le_sub_right hb _
      _ ≤ ‖A x - ((lam : ℝ) : ℂ) • (x : H)‖ := htri
  have hres := (TauCeti.LinearPMap.mem_resolventSet_and_norm_le_of_lower_bound hA
    hpos hnorm).1
  simpa [TauCeti.LinearPMap.spectrum] using hres

end DavisKahan
end TauCeti
