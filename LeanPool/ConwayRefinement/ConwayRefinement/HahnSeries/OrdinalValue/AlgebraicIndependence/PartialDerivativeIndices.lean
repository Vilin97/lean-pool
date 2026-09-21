/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.LowDegreeParts
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.ComponentsSpan
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.HomogeneousSpan

/-!
# Indices contributing to a partial derivative

For a variable `B'` such that `(deg B')_{<β} ≼ λ₀` in the algebraic order, put
`λ' := λ₀ ⊖ (deg B')_{<β}` and `τ := (α ⊖ deg B')_{≥β} ⊕ λ'`. The contributing derivatives
are `∂F/∂X_B` for variables `B` whose low-degree part equals `α_{<β}`, or whose proper
low-degree part does not precede `λ₀` and satisfies `deg B > deg B'`. Each `∂F/∂X_B` is
homogeneous of degree `σ_B := α ⊖ deg B`.

* Every `σ_B` is a nonzero limit ordinal; `λ' < ω^β`, `τ + 1 < α ⊖ deg B'`, and
  `α' = τ ⊕ deg B'`.
* If `σ_B ≼ α ⊖ deg B'`—equivalently, `deg B' ≼ deg B`—then the separation condition holds for
  `((α ⊖ deg B') ⊖ σ_B, σ_B, τ)`. When the low-degree part equals `α_{<β}`,
  `(σ_B)_{<β} = 0` and the last term of `σ_B` has exponent `ε ≥ β`; otherwise,
  `(λ₀)_{≥ε} = (α_{<β})_{≥ε}` at the exponent `ε` of the last term of `(σ_B)_{<β}`; in both
  cases `(α ⊖ deg B')_{≥ε} ≤ τ`.
* If `σ_B \not\preccurlyeq α ⊖ deg B'`, it precedes no degree
  `e ∈ [τ, α ⊖ deg B')`, so `∂F/∂X_B` contributes nothing to the components of those degrees of an
  element of the ideal (`componentsGE_mem_span_subtype`).
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded DirectSum

public noncomputable section

namespace Berarducci

section Dropping

variable {σ : Type*} {K : Type v} [Field K] (wt : σ → NatOrdinal)

/-- **Generators contributing nothing in `[τ, h)`.** If the components of degree at least `τ` of
`P` lie in the ideal of the homogeneous generators `q j`, of degrees `c j`, `P` has degree below
`h`, and for every generator outside `A` the degree `c j` precedes no degree
`e ∈ [τ, h)`, then those components lie in the ideal of the generators in `A`. -/
theorem componentsGE_mem_span_subtype {ι : Type w} [Finite ι] {q : ι → MvPolynomial σ K}
    {c : ι → NatOrdinal} (hq : ∀ j, IsWeightedHomogeneous wt (q j) (c j)) {P : MvPolynomial σ K}
    {τ h : NatOrdinal} (hP : componentsGE wt τ P ∈ Ideal.span (Set.range q))
    (hdeg : DegreeLT wt P h) (A : ι → Prop)
    (hdrop : ∀ j, ¬ A j → ∀ e, τ ≤ e → e < h → ¬ ∃ β, β + c j = e) :
    componentsGE wt τ P ∈ Ideal.span (Set.range fun j : {j // A j} ↦ q j.1) := by
  classical
  cases nonempty_fintype ι
  letI := weightedGradedAlgebra K wt
  have hdec : ∀ (R : MvPolynomial σ K) (e : NatOrdinal),
      (DirectSum.decompose (weightedHomogeneousSubmodule K wt) R e : MvPolynomial σ K) =
        weightedHomogeneousComponent wt e R := fun R e ↦ by
    rw [← decompose'_apply]
    rfl
  rw [componentsGE_eq_sum_weightedHomogeneousComponent]
  refine Ideal.sum_mem _ fun e he ↦ ?_
  obtain ⟨he', hτe⟩ := Finset.mem_filter.mp he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he'
  have heh : Finsupp.weight wt d < h := degreeLT_iff.mp hdeg d hd
  have hmem : weightedHomogeneousComponent wt (Finsupp.weight wt d) P ∈ Ideal.span (Set.range q) :=
    weightedHomogeneousComponent_mem_span_of_componentsGE_mem wt hq hP hτe
  obtain ⟨u, -, hu0, hsum⟩ := exists_decompose_eq_sum_mul_of_mem_span
    (𝒜 := weightedHomogeneousSubmodule K wt)
    (fun j ↦ (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hq j)) hmem (Finsupp.weight wt d)
  rw [hdec] at hsum
  have hcomp : weightedHomogeneousComponent wt (Finsupp.weight wt d)
      (weightedHomogeneousComponent wt (Finsupp.weight wt d) P) =
        weightedHomogeneousComponent wt (Finsupp.weight wt d) P := by
    rw [weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_mem wt P _), ite_eq_left rfl]
  rw [← hcomp, hsum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ A]
  have hzero : ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ A j), q j * u j = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [hu0 j (hdrop j (Finset.mem_filter.mp hj).2 _ hτe heh), mul_zero]
  rw [hzero, add_zero]
  exact Ideal.sum_mem _ fun j hj ↦ Ideal.mul_mem_right _ _
    (Ideal.subset_span ⟨⟨j, (Finset.mem_filter.mp hj).2⟩, rfl⟩)

end Dropping

variable {K : Type v} [Field K] {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts.LimitOrdinalRelationAtCutoff

variable {σ : Lifts wt x} {α : NatOrdinal} (S : σ.LimitOrdinalRelationAtCutoff α)
  (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
include S hx

/-! ### The degree `σ_B = α ⊖ deg B` of `∂F/∂X_B` -/

theorem α_constantCoeff : α.constantCoeff = 0 := by
  have h := congrArg NatOrdinal.constantCoeff S.hdegHD
  rw [NatOrdinal.constantCoeff_add, NatOrdinal.constantCoeff_nsmul, S.vars_limit _ S.mem,
    mul_zero, add_zero] at h
  rw [← h, ← NatOrdinal.partGE_eq_self_of_forall_le S.degHD_terms,
    NatOrdinal.constantCoeff_partGE (S.β_ne_zero hx)]

section Cofactor

variable {v : ι} (hv : v ∈ S.F.vars) {c : NatOrdinal} (hc : c + wt v = α)
include hv hc

omit hx in
/-- The degree `σ_B := α ⊖ deg B` of `∂F/∂X_B` (the binder `c`, with `c ⊕ wt v = α`) is
nonzero. -/
theorem cdeg_ne_zero : c ≠ 0 := by
  rintro rfl
  rw [zero_add] at hc
  exact (S.vars_lt v hv).ne hc

omit hv in
/-- The degree `σ_B` is a limit. -/
theorem cdeg_constantCoeff : c.constantCoeff = 0 := by
  have h := congrArg NatOrdinal.constantCoeff hc
  rw [NatOrdinal.constantCoeff_add, S.α_constantCoeff hx] at h
  omega

omit hx hv in
/-- `∂F/∂X_B` is homogeneous of degree `σ_B`. -/
theorem pderiv_hom : IsWeightedHomogeneous wt (pderiv v S.F) c :=
  isWeightedHomogeneous_pderiv wt S.hom v hc

omit hx hv in
/-- `(σ_B)_{<β} ⊕ (deg B)_{<β} = α_{<β}`. -/
theorem partLT_cdeg_add_degLT : NatOrdinal.partLT S.β c + S.degLT v = S.αLT := by
  have e : NatOrdinal.partLT S.β α = NatOrdinal.partLT S.β (c + wt v) := congrArg _ hc.symm
  rw [S.αLT_def, e, NatOrdinal.partLT_add, S.degLT_def]

omit hx hv in
theorem partGE_cdeg_add :
    NatOrdinal.partGE S.β c + NatOrdinal.partGE S.β (wt v) = S.αGE := by
  have e : NatOrdinal.partGE S.β α = NatOrdinal.partGE S.β (c + wt v) := congrArg _ hc.symm
  rw [S.αGE_def, e, NatOrdinal.partGE_add]

omit hx hv in
/-- If the low-degree part of `B` equals `α_{<β}`, then `(σ_B)_{<β} = 0`. -/
theorem partLT_cdeg_eq_zero_of_lowDegreePartEq (htop : S.LowDegreePartEq v) :
    NatOrdinal.partLT S.β c = 0 := by
  have h := S.partLT_cdeg_add_degLT hc
  rw [(S.lowDegreePartEq_iff v).mp htop] at h
  exact add_eq_right.mp h

omit hx hv in
theorem partGE_cdeg_eq_self_of_lowDegreePartEq (htop : S.LowDegreePartEq v) :
    NatOrdinal.partGE S.β c = c := by
  have := NatOrdinal.partGE_add_partLT S.β c
  rwa [S.partLT_cdeg_eq_zero_of_lowDegreePartEq hc htop, add_zero] at this

omit hx hv in
/-- If the low-degree part of `B` is not `α_{<β}`, then `(σ_B)_{<β} ≠ 0`. -/
theorem partLT_cdeg_ne_zero (htop : ¬ S.LowDegreePartEq v) : NatOrdinal.partLT S.β c ≠ 0 := by
  intro h
  have h' := S.partLT_cdeg_add_degLT hc
  rw [h, zero_add] at h'
  exact htop ((S.lowDegreePartEq_iff v).mpr h')

end Cofactor

/-! ### The degree `τ` when the low-degree part precedes `λ₀` -/

section Tau

variable {v' : ι} {h : NatOrdinal} (hh : h + wt v' = α) {lam' : NatOrdinal}
  (hlam' : S.degLT v' + lam' = S.lam₀)
include hlam'

omit hx in
theorem lam'_lt_wpow : lam' < ω^ S.β :=
  (le_add_of_nonneg_left zero_le).trans_lt (hlam' ▸ S.lam₀_lt_wpow)

omit hx in
theorem partGE_τ (h : NatOrdinal) :
    NatOrdinal.partGE S.β (NatOrdinal.partGE S.β h + lam') =
      NatOrdinal.partGE S.β h := by
  rw [NatOrdinal.partGE_add, NatOrdinal.partGE_partGE,
    NatOrdinal.partGE_eq_zero_of_lt (S.lam'_lt_wpow hlam'), add_zero]

omit hx in
theorem partLT_τ (h : NatOrdinal) :
    NatOrdinal.partLT S.β (NatOrdinal.partGE S.β h + lam') = lam' := by
  have := NatOrdinal.partGE_add_partLT S.β (NatOrdinal.partGE S.β h + lam')
  rw [S.partGE_τ hlam' h] at this
  exact add_left_cancel this

include hh

omit hx hlam' in
/-- `(α ⊖ deg B')_{<β} ⊕ (deg B')_{<β} = α_{<β}` (the binder `h` is `α ⊖ deg B'`). -/
theorem partLT_h_add_degLT : NatOrdinal.partLT S.β h + S.degLT v' = S.αLT :=
  S.partLT_cdeg_add_degLT hh

omit hx in
/-- `λ' < (α ⊖ deg B')_{<β}`. -/
theorem lam'_lt_partLT_h : lam' < NatOrdinal.partLT S.β h := by
  have h1 := S.partLT_h_add_degLT hh
  have h2 : S.degLT v' + lam' < S.degLT v' + NatOrdinal.partLT S.β h := by
    rw [hlam', add_comm _ (NatOrdinal.partLT S.β h), h1]
    rw [S.αLT_def]; exact S.lam₀_lt
  exact lt_of_add_lt_add_left h2

/-- `τ + 1 < α ⊖ deg B'`. -/
theorem τ_add_one_lt : NatOrdinal.partGE S.β h + lam' + 1 < h := by
  have hlt := S.lam'_lt_partLT_h hh hlam'
  have hcc : (NatOrdinal.partLT S.β h).constantCoeff = 0 := by
    rw [NatOrdinal.constantCoeff_partLT (S.β_ne_zero hx)]
    have := congrArg NatOrdinal.constantCoeff hh
    rw [NatOrdinal.constantCoeff_add, S.α_constantCoeff hx] at this
    omega
  have h1 : lam' + 1 < NatOrdinal.partLT S.β h := by
    refine lt_of_le_of_ne (Order.add_one_le_of_lt hlt) fun heq ↦ ?_
    have := congrArg NatOrdinal.constantCoeff heq
    rw [hcc, show lam' + 1 = lam' + ((1 : ℕ) : NatOrdinal) by rw [Nat.cast_one],
      NatOrdinal.constantCoeff_add_natCast] at this
    omega
  conv_rhs => rw [← NatOrdinal.partGE_add_partLT S.β h]
  rw [add_assoc]
  exact add_lt_add_right h1 _

omit hx in
/-- `α' = α_{≥β} ⊕ λ₀ = τ ⊕ deg B'`. -/
theorem αGE_add_lam₀_eq : S.αGE + S.lam₀ = NatOrdinal.partGE S.β h + lam' + wt v' := by
  have e : NatOrdinal.partGE S.β α = NatOrdinal.partGE S.β (h + wt v') :=
    congrArg _ hh.symm
  rw [← hlam', S.αGE_def, e, NatOrdinal.partGE_add]
  conv_rhs => rw [← S.partGE_add_degLT v']
  abel

omit hx hh in
/-- Every degree `e ∈ [τ, α ⊖ deg B')` has the same part at or above `β` as `α ⊖ deg B'`. -/
theorem partGE_eq_of_τ_le {e : NatOrdinal}
    (hτe : NatOrdinal.partGE S.β h + lam' ≤ e) (heh : e < h) :
    NatOrdinal.partGE S.β e = NatOrdinal.partGE S.β h :=
  le_antisymm (NatOrdinal.partGE_mono heh.le) (by
    have := NatOrdinal.partGE_mono (β := S.β) hτe
    rwa [S.partGE_τ hlam' h] at this)

end Tau

/-! ### The separation condition (n) at the generators considered at `B'` -/

section PartialDerivativeIndices

variable {v : ι} (hv : v ∈ S.F.vars) {c : NatOrdinal} (hc : c + wt v = α)
  {v' : ι} {h : NatOrdinal} (hh : h + wt v' = α) {lam' : NatOrdinal}
  (hlam' : S.degLT v' + lam' = S.lam₀)
include hv hc hh hlam'

omit hx hh hlam' in
/-- If the low-degree part of `B` equals `α_{<β}` and `ω^ε` is the last term of `σ_B`, then
`ε ≥ β`, so `h_{≥ε} ≤ h_{≥β} ⊕ λ'` for every ordinal `h`. -/
theorem partGE_le_τ_of_lowDegreePartEq (htop : S.LowDegreePartEq v) {ε : NatOrdinal}
    (hε : NatOrdinal.leastTerm c = ω^ ε) (h : NatOrdinal) :
    NatOrdinal.partGE ε h ≤ NatOrdinal.partGE S.β h + lam' := by
  have hβε : S.β ≤ ε := by
    have h1 := NatOrdinal.wpow_le_leastTerm_partGE (β := S.β) (a := c)
      (by rw [S.partGE_cdeg_eq_self_of_lowDegreePartEq hc htop]; exact S.cdeg_ne_zero hv hc)
    rw [S.partGE_cdeg_eq_self_of_lowDegreePartEq hc htop, hε, NatOrdinal.wpow_le_wpow] at h1
    exact h1
  exact (NatOrdinal.partGE_le_partGE_of_le hβε h).trans (le_add_of_nonneg_right zero_le)

omit hv in
/-- If the proper low-degree part of `B` does not precede `λ₀` and `ω^ε` is the last term of
`(σ_B)_{<β}`, then `(α ⊖ deg B')_{≥ε} ≤ τ`. -/
theorem partGE_le_τ_of_hasProperLowDegreePartNotAlgebraicLE
    (hL : S.HasProperLowDegreePartNotAlgebraicLE v) {ε : NatOrdinal}
    (hε : NatOrdinal.leastTerm (NatOrdinal.partLT S.β c) = ω^ ε) :
    NatOrdinal.partGE ε h ≤ NatOrdinal.partGE S.β h + lam' := by
  have hεβ : ε ≤ S.β := by
    have h1 := NatOrdinal.leastTerm_le
      (S.partLT_cdeg_ne_zero hc
        ((S.hasProperLowDegreePartNotAlgebraicLE_iff v).mp hL).2.2.1)
    rw [hε] at h1
    exact (NatOrdinal.wpow_lt_wpow.mp (h1.trans_lt (NatOrdinal.partLT_lt _ _))).le
  -- `(λ₀)_{≥ε} = (α_{<β})_{≥ε}`
  have h5 := S.partGE_lam₀_eq_of_hasProperLowDegreePartNotAlgebraicLE
    hx hL (S.partLT_cdeg_add_degLT hc) hε
  -- `λ'_{≥ε} = ((α ⊖ deg B')_{<β})_{≥ε}`
  have hlamε : NatOrdinal.partGE ε lam' =
      NatOrdinal.partGE ε (NatOrdinal.partLT S.β h) := by
    have e1 := congrArg (NatOrdinal.partGE ε) hlam'
    have e2 := congrArg (NatOrdinal.partGE ε) (S.partLT_h_add_degLT hh)
    rw [NatOrdinal.partGE_add] at e1 e2
    rw [h5, ← e2, add_comm (NatOrdinal.partGE ε (NatOrdinal.partLT S.β h))] at e1
    exact add_left_cancel e1
  calc NatOrdinal.partGE ε h
      = NatOrdinal.partGE ε (NatOrdinal.partGE S.β h) +
          NatOrdinal.partGE ε (NatOrdinal.partLT S.β h) := by
        conv_lhs => rw [← NatOrdinal.partGE_add_partLT S.β h]
        rw [NatOrdinal.partGE_add]
    _ = NatOrdinal.partGE S.β h + NatOrdinal.partGE ε lam' := by
        rw [NatOrdinal.partGE_partGE_of_ge hεβ, hlamε]
    _ ≤ NatOrdinal.partGE S.β h + lam' := add_le_add_right (NatOrdinal.partGE_le _ _) _

omit hx hv hh in
/-- If the low-degree part of `B` equals `α_{<β}` and
`σ_B \not\preccurlyeq α ⊖ deg B'`, then `σ_B` precedes no degree in
`[τ, α ⊖ deg B')` in the algebraic order. -/
theorem not_algebraicLE_of_lowDegreePartEq_of_not (htop : S.LowDegreePartEq v)
    (hdrop : ¬ NatOrdinal.AlgebraicLE c h)
    {e : NatOrdinal} (hτe : NatOrdinal.partGE S.β h + lam' ≤ e) (heh : e < h) :
    ¬ NatOrdinal.AlgebraicLE c e := by
  intro hce
  apply hdrop
  have h1 := hce.partGE S.β
  rw [S.partGE_eq_of_τ_le hlam' hτe heh,
    S.partGE_cdeg_eq_self_of_lowDegreePartEq hc htop] at h1
  exact h1.trans (NatOrdinal.algebraicLE_partGE _ _)

omit hv in
/-- If the proper low-degree part of `B` does not precede `λ₀` and
`σ_B \not\preccurlyeq α ⊖ deg B'`, then `σ_B` precedes no degree in
`[τ, α ⊖ deg B')` in the algebraic order. -/
theorem not_algebraicLE_of_hasProperLowDegreePartNotAlgebraicLE_of_not
    (hL : S.HasProperLowDegreePartNotAlgebraicLE v)
    (hdrop : ¬ NatOrdinal.AlgebraicLE c h)
    {e : NatOrdinal} (hτe : NatOrdinal.partGE S.β h + lam' ≤ e) (heh : e < h) :
    ¬ NatOrdinal.AlgebraicLE c e := by
  intro hce
  apply hdrop
  have hGE := S.partGE_eq_of_τ_le hlam' hτe heh
  -- the parts at or above `β`
  have h1 : NatOrdinal.AlgebraicLE (NatOrdinal.partGE S.β c) (NatOrdinal.partGE S.β h) := by
    have := hce.partGE S.β
    rwa [hGE] at this
  -- the parts below `β`: `s := e_{<β} ∈ [λ', (α ⊖ deg B')_{<β})`
  set s := NatOrdinal.partLT S.β e with hsdef
  have hlamεs : lam' ≤ s := by
    have h2 : NatOrdinal.partGE S.β h + lam' ≤ NatOrdinal.partGE S.β h + s := by
      calc NatOrdinal.partGE S.β h + lam' ≤ e := hτe
        _ = NatOrdinal.partGE S.β e + NatOrdinal.partLT S.β e :=
            (NatOrdinal.partGE_add_partLT S.β e).symm
        _ = NatOrdinal.partGE S.β h + s := by rw [hGE]
    exact le_of_add_le_add_left h2
  have hsh : s < NatOrdinal.partLT S.β h :=
    NatOrdinal.partLT_lt_of_lt_of_partGE_eq heh hGE
  -- the exponent `ε` of the last term of `(σ_B)_{<β}`
  obtain ⟨ε, hε⟩ :=
    NatOrdinal.exists_leastTerm_eq_wpow
      (S.partLT_cdeg_ne_zero hc
        ((S.hasProperLowDegreePartNotAlgebraicLE_iff v).mp hL).2.2.1)
  have h5 := S.partGE_lam₀_eq_of_hasProperLowDegreePartNotAlgebraicLE
    hx hL (S.partLT_cdeg_add_degLT hc) hε
  have hlamε : NatOrdinal.partGE ε lam' =
      NatOrdinal.partGE ε (NatOrdinal.partLT S.β h) := by
    have e1 := congrArg (NatOrdinal.partGE ε) hlam'
    have e2 := congrArg (NatOrdinal.partGE ε) (S.partLT_h_add_degLT hh)
    rw [NatOrdinal.partGE_add] at e1 e2
    rw [h5, ← e2, add_comm (NatOrdinal.partGE ε (NatOrdinal.partLT S.β h))] at e1
    exact add_left_cancel e1
  have hs : NatOrdinal.partGE ε s = NatOrdinal.partGE ε (NatOrdinal.partLT S.β h) :=
    le_antisymm (NatOrdinal.partGE_mono hsh.le)
      (hlamε ▸ NatOrdinal.partGE_mono hlamεs)
  -- `(σ_B)_{<β}`, all of whose terms are at least `ω^ε`, precedes `s`, hence precedes
  -- `(α ⊖ deg B')_{<β}`
  have h2 : NatOrdinal.AlgebraicLE (NatOrdinal.partLT S.β c) (NatOrdinal.partLT S.β h) := by
    have h3 := (hce.partLT S.β).partGE ε
    rw [NatOrdinal.partGE_eq_self_of_leastTerm_eq
      (S.partLT_cdeg_ne_zero hc
        ((S.hasProperLowDegreePartNotAlgebraicLE_iff v).mp hL).2.2.1) hε,
      ← hsdef, hs] at h3
    exact h3.trans (NatOrdinal.algebraicLE_partGE _ _)
  exact NatOrdinal.algebraicLE_of_partGE_of_partLT h1 h2

end PartialDerivativeIndices

end Lifts.LimitOrdinalRelationAtCutoff

end Berarducci
