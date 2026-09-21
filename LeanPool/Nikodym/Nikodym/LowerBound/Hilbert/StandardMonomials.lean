/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Defs
import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Shadow

/-!
# Standard monomials and the Hilbert function

This file implements blueprint node **H01** of the lower-bound side of the sharp finite-field
Nikodym exponent.

We fix the degree-compatible monomial order `MonomialOrder.degLex` on `Fin d`. For an ideal `I` of
`P_d = MvPolynomial (Fin d) K` we define

* `Nikodym.LowerBound.leadingExponents I`: the exponents of leading monomials of nonzero elements
  of `I` (the exponents of the initial ideal);
* `Nikodym.LowerBound.standardExponents I`: its complement, the *standard exponents* `S_I`;
* `Nikodym.LowerBound.standardLE I t`: the finset of standard exponents of degree at most `t`;
* `Nikodym.LowerBound.standardSet I`: `S_I` viewed as a set of functions `Fin d → ℕ`, the shape
  used by the shadow inequality of node H02.

The main results are

* `standardExponents_downClosed`: `S_I` is closed under taking divisors;
* `mk_mem_span_standard`: the class of a polynomial of total degree `≤ t` lies in the span of the
  standard monomials of degree `≤ t` (leading-term cancellation and well-founded induction);
* `linearIndependent_standard`: the classes of the standard monomials are linearly independent
  in `P_d ⧸ I`;
* `restrictionSpace_eq_span_standardLE` and `hilbert_eq_card_standardLE`:
  the standard monomials of degree `≤ t` form a basis of `V_I(t)`, so
  `H_I(t) = #{α ∈ S_I | |α| ≤ t}`;
* `hilbert_eq_sum_layerCard`: `H_I(t) = ∑_{s ≤ t} #(layer (standardSet I) s)`, the bridge to
  node H03.

No Gröbner basis algorithm is used: leading-term cancellation against an arbitrary element of `I`
with the same leading exponent suffices.
-/

namespace Nikodym.LowerBound

open MvPolynomial MonomialOrder Finset

open scoped MonomialOrder

variable {K : Type*} [Field K] {d : ℕ}

/-! ### Leading and standard exponents -/

/-- Blueprint H01: the set of leading exponents (with respect to `degLex`) of nonzero elements of
`I`, i.e. the exponents of the monomials in the initial ideal of `I`. -/
def leadingExponents (I : Ideal (MvPolynomial (Fin d) K)) : Set (Fin d →₀ ℕ) :=
  {α | ∃ f ∈ I, f ≠ 0 ∧ degLex.degree f = α}

/-- Blueprint H01: the standard exponents `S_I`, the exponents that are not leading exponents of
elements of `I`. -/
def standardExponents (I : Ideal (MvPolynomial (Fin d) K)) : Set (Fin d →₀ ℕ) :=
  (leadingExponents I)ᶜ

variable {I : Ideal (MvPolynomial (Fin d) K)}

/-- Blueprint H01: membership in `leadingExponents I`. -/
theorem mem_leadingExponents {α : Fin d →₀ ℕ} :
    α ∈ leadingExponents I ↔ ∃ f ∈ I, f ≠ 0 ∧ degLex.degree f = α :=
  Iff.rfl

/-- Blueprint H01: membership in `standardExponents I`. -/
theorem mem_standardExponents {α : Fin d →₀ ℕ} :
    α ∈ standardExponents I ↔ α ∉ leadingExponents I :=
  Iff.rfl

/-- Blueprint H01: the leading exponent of a nonzero element of `I` is a leading exponent. -/
theorem degree_mem_leadingExponents {f : MvPolynomial (Fin d) K} (hf : f ∈ I) (hf0 : f ≠ 0) :
    degLex.degree f ∈ leadingExponents I :=
  ⟨f, hf, hf0, rfl⟩

/-- Blueprint H01: the leading exponents are closed under adding exponent vectors (the initial
ideal is a monomial ideal). -/
theorem leadingExponents_add_mem {α : Fin d →₀ ℕ} (hα : α ∈ leadingExponents I)
    (γ : Fin d →₀ ℕ) : α + γ ∈ leadingExponents I := by
  classical
  obtain ⟨f, hf, hf0, rfl⟩ := hα
  have hm : (monomial γ (1 : K) : MvPolynomial (Fin d) K) ≠ 0 := by
    rw [Ne, monomial_eq_zero]
    exact one_ne_zero
  refine ⟨monomial γ 1 * f, I.mul_mem_left _ hf, mul_ne_zero hm hf0, ?_⟩
  rw [degree_mul hm hf0, degree_monomial, if_neg one_ne_zero, add_comm]

/-- Blueprint H01: the standard exponents are closed under taking divisors. -/
theorem standardExponents_downClosed (I : Ideal (MvPolynomial (Fin d) K)) :
    ∀ α ∈ standardExponents I, ∀ β : Fin d →₀ ℕ, (∀ i, β i ≤ α i) → β ∈ standardExponents I := by
  intro α hα β hβ hβI
  apply hα
  have hle : β ≤ α := Finsupp.le_def.mpr hβ
  have := leadingExponents_add_mem hβI (α - β)
  rwa [add_tsub_cancel_of_le hle] at this

/-! ### Leading-term cancellation -/

/-- Blueprint H01 (auxiliary): subtracting a polynomial with the same leading exponent and the
same leading coefficient strictly decreases the `degLex` degree, unless the difference is zero. -/
private lemma degree_sub_lt_of_degree_eq {f g : MvPolynomial (Fin d) K}
    (hdeg : degLex.degree g = degLex.degree f)
    (hlc : degLex.leadingCoeff g = degLex.leadingCoeff f) (hfg : f - g ≠ 0) :
    degLex.degree (f - g) ≺[degLex] degLex.degree f := by
  refine lt_of_le_of_ne ?_ ?_
  · refine degree_sub_le.trans ?_
    rw [hdeg, sup_idem]
  · intro h
    have h' : degLex.degree (f - g) = degLex.degree f := degLex.toSyn.injective h
    have hmem := degLex.degree_mem_support hfg
    rw [h', mem_support_iff, coeff_sub] at hmem
    apply hmem
    simp only [leadingCoeff, hdeg] at hlc
    rw [hlc, sub_self]

/-- Blueprint H01 (auxiliary): removing the leading term does not increase the total degree, since
`degLex` is degree-compatible. -/
private lemma totalDegree_le_of_degree_le {f g : MvPolynomial (Fin d) K}
    (h : degLex.degree g ≼[degLex] degLex.degree f) : g.totalDegree ≤ f.totalDegree :=
  degLex_totalDegree_monotone h

/-- Blueprint H01 (auxiliary): the class of `c • X^α` in the quotient. -/
private lemma mk_smul_monomial (I : Ideal (MvPolynomial (Fin d) K)) (α : Fin d →₀ ℕ) (c : K) :
    Ideal.Quotient.mk I (monomial α c) = c • Ideal.Quotient.mk I (monomial α (1 : K)) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul, smul_monomial, smul_eq_mul, mul_one]

/-- Blueprint H01: the class of a polynomial of total degree at most `t` lies in the span of the
classes of the standard monomials of degree at most `t`. Proof by well-founded induction on the
`degLex` degree, cancelling the leading term either against a standard monomial or against an
element of `I` with the same leading exponent. -/
theorem mk_mem_span_standard (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ)
    (f : MvPolynomial (Fin d) K) (hf : f.totalDegree ≤ t) :
    Ideal.Quotient.mk I f ∈ Submodule.span K
      ((fun α ↦ Ideal.Quotient.mk I (monomial α (1 : K))) ''
        {α ∈ standardExponents I | α.degree ≤ t}) := by
  set V := Submodule.span K
    ((fun α ↦ Ideal.Quotient.mk I (monomial α (1 : K))) ''
      {α ∈ standardExponents I | α.degree ≤ t}) with hV
  suffices H : ∀ s : (degLex : MonomialOrder (Fin d)).syn, ∀ f : MvPolynomial (Fin d) K,
      degLex.toSyn (degLex.degree f) = s → f.totalDegree ≤ t → Ideal.Quotient.mk I f ∈ V from
    H _ f rfl hf
  intro s
  induction s using WellFoundedLT.induction with
  | ind s ih =>
  intro f hs hft
  by_cases hf0 : f = 0
  · rw [hf0, map_zero]
    exact V.zero_mem
  -- the leading exponent and coefficient of `f`
  set α := degLex.degree f with hα
  have hαdeg : α.degree = f.totalDegree := degree_degLexDegree
  by_cases hαI : α ∈ leadingExponents I
  · -- cancel against an element of `I` with the same leading exponent
    obtain ⟨g, hgI, hg0, hgα⟩ := hαI
    set r : K := degLex.leadingCoeff f / degLex.leadingCoeff g with hr
    have hr0 : r ≠ 0 := div_ne_zero (leadingCoeff_ne_zero_iff.mpr hf0)
      (leadingCoeff_ne_zero_iff.mpr hg0)
    have hC0 : (C r : MvPolynomial (Fin d) K) ≠ 0 := by
      rw [Ne, C_eq_zero]
      exact hr0
    have hdeg : degLex.degree (C r * g) = degLex.degree f := by
      rw [degree_mul hC0 hg0, degree_C, zero_add, hgα]
    have hlc : degLex.leadingCoeff (C r * g) = degLex.leadingCoeff f := by
      rw [leadingCoeff_mul, leadingCoeff_C, hr,
        div_mul_cancel₀ _ (leadingCoeff_ne_zero_iff.mpr hg0)]
    have hmk : Ideal.Quotient.mk I f = Ideal.Quotient.mk I (f - C r * g) := by
      rw [Ideal.Quotient.eq, sub_sub_cancel]
      exact I.mul_mem_left _ hgI
    rw [hmk]
    by_cases hfg : f - C r * g = 0
    · rw [hfg, map_zero]
      exact V.zero_mem
    have hlt := degree_sub_lt_of_degree_eq hdeg hlc hfg
    exact ih _ (hs ▸ hlt) _ rfl ((totalDegree_le_of_degree_le hlt.le).trans hft)
  · -- the leading exponent is standard: cancel against the standard monomial `X^α`
    have hαS : α ∈ standardExponents I := hαI
    have hmono : Ideal.Quotient.mk I (monomial α (1 : K)) ∈ V :=
      Submodule.subset_span ⟨α, ⟨hαS, hαdeg ▸ hft⟩, rfl⟩
    have hsplit : f = (f - degLex.leadingTerm f) + degLex.leadingTerm f := (sub_add_cancel _ _).symm
    have hLT : Ideal.Quotient.mk I (degLex.leadingTerm f) ∈ V := by
      rw [leadingTerm, mk_smul_monomial]
      exact V.smul_mem _ hmono
    rw [hsplit, map_add]
    refine V.add_mem ?_ hLT
    by_cases hfg : f - degLex.leadingTerm f = 0
    · rw [hfg, map_zero]
      exact V.zero_mem
    have hlt : degLex.degree (f - degLex.leadingTerm f) ≺[degLex] degLex.degree f :=
      degree_sub_leadingTerm_lt_degree (degree_ne_zero_of_sub_leadingTerm_ne_zero hfg)
    exact ih _ (hs ▸ hlt) _ rfl ((totalDegree_le_of_degree_le hlt.le).trans hft)

/-! ### Linear independence -/

/-- Blueprint H01: a polynomial supported on the standard exponents lies in `I` only if it is
zero. -/
theorem eq_zero_of_support_subset_standard {f : MvPolynomial (Fin d) K}
    (hsupp : ↑f.support ⊆ standardExponents I) (hf : f ∈ I) : f = 0 := by
  by_contra hf0
  exact hsupp (degLex.degree_mem_support hf0) (degree_mem_leadingExponents hf hf0)

/-- Blueprint H01: the classes of the standard monomials are linearly independent in `P_d ⧸ I`. -/
theorem linearIndependent_standard (I : Ideal (MvPolynomial (Fin d) K)) :
    LinearIndependent K
      (fun α : standardExponents I ↦ Ideal.Quotient.mk I (monomial (α : Fin d →₀ ℕ) (1 : K))) := by
  have hmon : LinearIndependent K (fun α : standardExponents I ↦
      (monomial (α : Fin d →₀ ℕ) (1 : K) : MvPolynomial (Fin d) K)) := by
    have := (basisMonomials (Fin d) K).linearIndependent.comp
      (fun α : standardExponents I ↦ (α : Fin d →₀ ℕ)) Subtype.val_injective
    simpa [Function.comp_def, coe_basisMonomials] using this
  have key := hmon.map (f := (Ideal.Quotient.mkₐ K I).toLinearMap) ?_
  · simpa [Function.comp_def, Ideal.Quotient.mkₐ_eq_mk] using key
  · rw [Submodule.disjoint_def]
    intro g hg hgker
    have hsupp : ↑g.support ⊆ standardExponents I := by
      have hspan : Submodule.span K
          (Set.range fun α : standardExponents I ↦
            (monomial (α : Fin d →₀ ℕ) (1 : K) : MvPolynomial (Fin d) K)) ≤
          restrictSupport K (standardExponents I) := by
        rw [restrictSupport_eq_span]
        exact Submodule.span_mono (Set.range_subset_iff.mpr fun α ↦ ⟨α, α.2, rfl⟩)
      exact (mem_restrictSupport_iff K).mp (hspan hg)
    have hgI : g ∈ I := by
      rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem] at hgker
      exact hgker
    exact eq_zero_of_support_subset_standard hsupp hgI

/-! ### The basis of `V_I(t)` and the Hilbert function -/

/-- Blueprint H01: the finset of standard exponents of degree at most `t`. -/
noncomputable def standardLE (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    Finset (Fin d →₀ ℕ) := by
  classical exact (exponentsLE d t).filter (· ∈ standardExponents I)

/-- Blueprint H01: membership in `standardLE I t`. -/
theorem mem_standardLE {t : ℕ} {α : Fin d →₀ ℕ} :
    α ∈ standardLE I t ↔ α ∈ standardExponents I ∧ α.degree ≤ t := by
  classical
  simp [standardLE, mem_exponentsLE, and_comm]

/-- Blueprint H01: `standardLE I t` as a set. -/
theorem coe_standardLE (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    (↑(standardLE I t) : Set (Fin d →₀ ℕ)) = {α ∈ standardExponents I | α.degree ≤ t} := by
  ext α
  simp only [Finset.mem_coe, mem_standardLE, Set.mem_setOf_eq]

/-- Blueprint H01: `V_I(t)` is spanned by the classes of the standard monomials of degree at most
`t`. -/
theorem restrictionSpace_eq_span_standardLE (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    restrictionSpace I t = Submodule.span K
      ((fun α ↦ Ideal.Quotient.mk I (monomial α (1 : K))) '' ↑(standardLE I t)) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨f, hf, rfl⟩ := exists_repr_of_mem_restrictionSpace hv
    rw [coe_standardLE]
    exact mk_mem_span_standard I t f (mem_restrictTotalDegree_iff.mp hf)
  · rw [Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    exact mem_restrictionSpace_mk
      ((totalDegree_monomial_le α 1).trans (mem_standardLE.mp hα).2)

/-- Blueprint H01: the classes of the standard monomials of degree at most `t` are linearly
independent. -/
theorem linearIndependent_standardLE (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    LinearIndependent K
      (fun α : standardLE I t ↦ Ideal.Quotient.mk I (monomial (α : Fin d →₀ ℕ) (1 : K))) := by
  have := (linearIndependent_standard I).comp
    (fun α : standardLE I t ↦ (⟨α, (mem_standardLE.mp α.2).1⟩ : standardExponents I))
    (fun α β h ↦ Subtype.ext (Subtype.mk.inj h))
  simpa [Function.comp_def] using this

/-- Blueprint H01: `H_I(t) = #{α ∈ S_I | |α| ≤ t}`. -/
theorem hilbert_eq_card_standardLE (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    hilbert I t = (standardLE I t).card := by
  have himg : (fun α ↦ Ideal.Quotient.mk I (monomial α (1 : K))) '' ↑(standardLE I t) =
      Set.range (fun α : standardLE I t ↦
        Ideal.Quotient.mk I (monomial (α : Fin d →₀ ℕ) (1 : K))) :=
    (Set.image_eq_range _ _).trans rfl
  rw [hilbert, restrictionSpace_eq_span_standardLE, himg,
    finrank_span_eq_card (linearIndependent_standardLE I t), Fintype.card_coe]

/-! ### Bridge to the shadow inequality -/

/-- Blueprint H01: the standard exponents as a set of functions `Fin d → ℕ`, the shape used by the
shadow inequality of node H02. -/
def standardSet (I : Ideal (MvPolynomial (Fin d) K)) : Set (Fin d → ℕ) :=
  {a | Finsupp.equivFunOnFinite.symm a ∈ standardExponents I}

/-- Blueprint H01: membership in `standardSet I`. -/
theorem mem_standardSet {a : Fin d → ℕ} :
    a ∈ standardSet I ↔ Finsupp.equivFunOnFinite.symm a ∈ standardExponents I :=
  Iff.rfl

/-- Blueprint H01: `standardSet I` is closed under taking divisors. -/
theorem standardSet_downClosed (I : Ideal (MvPolynomial (Fin d) K)) :
    ∀ a ∈ standardSet I, ∀ b : Fin d → ℕ, (∀ i, b i ≤ a i) → b ∈ standardSet I := by
  intro a ha b hb
  exact standardExponents_downClosed I _ ha _ fun i ↦ by
    simpa [Finsupp.coe_equivFunOnFinite_symm] using hb i

/-- Blueprint H01: the standard exponents of degree exactly `s` correspond to the degree-`s`
layer of `standardSet I`. -/
private lemma card_filter_standardLE_degree (I : Ideal (MvPolynomial (Fin d) K)) {t s : ℕ}
    (hs : s ≤ t) :
    ((standardLE I t).filter fun α ↦ α.degree = s).card = layerCard (standardSet I) s := by
  classical
  rw [layerCard]
  refine Finset.card_equiv Finsupp.equivFunOnFinite fun α ↦ ?_
  rw [Finset.mem_filter, mem_standardLE, mem_layer, mem_standardSet, Equiv.symm_apply_apply,
    Finsupp.degree_eq_sum]
  simp only [Finsupp.equivFunOnFinite_apply]
  constructor
  · rintro ⟨⟨hα, -⟩, hαs⟩
    exact ⟨hαs, hα⟩
  · rintro ⟨hαs, hα⟩
    exact ⟨⟨hα, hαs ▸ hs⟩, hαs⟩

/-- Blueprint H01: `H_I(t) = ∑_{s ≤ t} #(layer (standardSet I) s)`, the form of the Hilbert
function used with the shadow inequality (node H02) in node H03. -/
theorem hilbert_eq_sum_layerCard (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    hilbert I t = ∑ s ∈ range (t + 1), layerCard (standardSet I) s := by
  classical
  rw [hilbert_eq_card_standardLE,
    card_eq_sum_card_fiberwise (f := fun α : Fin d →₀ ℕ ↦ α.degree) (t := range (t + 1))
      fun α hα ↦ mem_range.mpr (Nat.lt_succ_of_le (mem_standardLE.mp hα).2)]
  exact Finset.sum_congr rfl fun s hs ↦
    card_filter_standardLE_degree I (Nat.lt_succ_iff.mp (mem_range.mp hs))

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
