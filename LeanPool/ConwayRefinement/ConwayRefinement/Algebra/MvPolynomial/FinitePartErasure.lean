/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import Mathlib.Algebra.MvPolynomial.Supported
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.FinitePartVars

/-!
# Erasing variables with a fixed constant Cantor coefficient

Setting `X_i` to zero whenever the coefficient of `1 = ω^0` in the Cantor normal form of its weight
is `k` defines the algebra map `eraseFinitePart wt k`. It preserves weighted homogeneity and its
image contains none of those variables.

Its defect from the identity is exactly the monomials the successor step needs to see. In a
monomial whose degree `δ` has positive constant Cantor coefficient `n`, a variable with constant
Cantor coefficient `n` occupies the whole coefficient on its own: it occurs to the first power,
and no other such variable occurs beside it. This gives the identity

`F' + ∑_i X_i ∂F/∂X_i = F`,

the sum over the variables of `F` carrying the finite part.

Nothing here depends on where the variables are evaluated, so both the real-exponent development
and the Cantor–Bendixson germ argument use it unchanged.
-/

universe u v

open scoped NatOrdinal

public noncomputable section

namespace Finsupp

variable {ι : Type u} {wt : ι → NatOrdinal}

/-- In a monomial whose degree `δ` has positive constant Cantor coefficient `n`, a variable whose
weight has constant Cantor coefficient `n` occurs with multiplicity one, and no other such variable
occurs. -/
theorem eq_one_and_eq_zero_of_constantCoeff_eq {d : ι →₀ ℕ} {δ : NatOrdinal}
    (hδ : 0 < δ.constantCoeff) (hd : Finsupp.weight wt d = δ) {i : ι} (hi : i ∈ d.support)
    (hik : (wt i).constantCoeff = δ.constantCoeff) :
    d i = 1 ∧ ∀ j, j ≠ i → (wt j).constantCoeff = δ.constantCoeff → d j = 0 := by
  classical
  have hsum : ∑ j ∈ d.support, d j * (wt j).constantCoeff = δ.constantCoeff := by
    rw [← Finsupp.constantCoeff_weight, hd]
  have hterm : ∀ j ∈ d.support, d j * (wt j).constantCoeff ≤ δ.constantCoeff := fun j hj ↦
    hsum ▸ Finset.single_le_sum (f := fun j ↦ d j * (wt j).constantCoeff)
      (fun _ _ ↦ Nat.zero_le _) hj
  have hdi : d i = 1 := by
    have h1 := hterm i hi
    rw [hik] at h1
    have h2 : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    nlinarith
  refine ⟨hdi, fun j hji hjk ↦ ?_⟩
  by_contra hdj
  have hj : j ∈ d.support := Finsupp.mem_support_iff.mpr hdj
  -- two distinct variables carrying the finite part would contribute at least twice it
  have h2 : d i * (wt i).constantCoeff + d j * (wt j).constantCoeff ≤ δ.constantCoeff := by
    rw [← hsum]
    exact Finset.add_le_sum (f := fun j ↦ d j * (wt j).constantCoeff)
      (fun _ _ ↦ Nat.zero_le _) hi hj hji.symm
  rw [hdi, one_mul, hik, hjk] at h2
  have h3 : 1 ≤ d j := Nat.one_le_iff_ne_zero.mpr hdj
  nlinarith

end Finsupp

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommRing R] (wt : σ → NatOrdinal) (k : ℕ)

/-- Set `X_i` to zero when the constant Cantor coefficient of its weight is `k`. -/
def eraseFinitePart : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ if (wt i).constantCoeff = k then 0 else X i

theorem eraseFinitePart_X {i : σ} :
    eraseFinitePart (R := R) wt k (X i) = if (wt i).constantCoeff = k then 0 else X i := by
  rw [eraseFinitePart, aeval_X]

theorem eraseFinitePart_monomial (d : σ →₀ ℕ) (r : R) :
    eraseFinitePart wt k (monomial d r) =
      if ∃ i ∈ d.support, (wt i).constantCoeff = k then 0 else monomial d r := by
  classical
  rw [eraseFinitePart, aeval_monomial]
  split_ifs with h
  · obtain ⟨i, hi, hik⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hi (by
      rw [ite_eq_left hik, zero_pow (Finsupp.mem_support_iff.mp hi)]), mul_zero]
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    beta_reduce
    rw [ite_eq_right fun hik ↦ h ⟨i, hi, hik⟩]

/-- The substitution fixes a polynomial none of whose variable weights has constant Cantor
coefficient `k`. -/
theorem eraseFinitePart_eq_self {G : MvPolynomial σ R}
    (hG : ∀ i ∈ G.vars, (wt i).constantCoeff ≠ k) :
    eraseFinitePart wt k G = G := by
  classical
  conv_rhs => rw [G.as_sum]
  conv_lhs => rw [G.as_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [eraseFinitePart_monomial, ite_eq_right]
  rintro ⟨i, hi, hik⟩
  exact hG i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩) hik

/-- The substitution preserves homogeneity of any degree. -/
theorem isWeightedHomogeneous_eraseFinitePart {G : MvPolynomial σ R} {β : NatOrdinal}
    (hG : IsWeightedHomogeneous wt G β) : IsWeightedHomogeneous wt (eraseFinitePart wt k G) β := by
  classical
  induction hG using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero R wt β
  | add p q _ _ ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hd =>
    rw [eraseFinitePart_monomial]
    split_ifs
    · exact isWeightedHomogeneous_zero R wt β
    · exact isWeightedHomogeneous_monomial wt d r hd

/-- The image contains no variable whose weight has constant Cantor coefficient `k`. -/
theorem eraseFinitePart_mem_supported [Nontrivial R] (G : MvPolynomial σ R) :
    eraseFinitePart wt k G ∈ supported R {i | (wt i).constantCoeff ≠ k} := by
  classical
  induction G using MvPolynomial.induction_on with
  | C r => rw [← algebraMap_eq, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i ih =>
    rw [map_mul, eraseFinitePart_X]
    split_ifs with hi
    · rw [mul_zero]; exact zero_mem _
    · exact mul_mem ih ((X_mem_supported (R := R)).mpr hi)

variable {wt k}

/-- Decomposition of a weighted-homogeneous polynomial using the variables whose weights have the
same positive constant Cantor coefficient as its degree. -/
@[blueprint "lem:relation-shape"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Weighted Euler decomposition at the $\\omega^0$ coefficient")
  (statement := /--
    Let $F$ be weighted homogeneous of degree $\delta$, and let $n>0$ be the
    coefficient of $1=\omega^0$ in the Cantor normal form of $\delta$. Then
    \[
      F_0+\sum_{\substack{i\in\operatorname{vars}(F)\\
          \operatorname{coeff}_{\omega^0}(\operatorname{wt}(i))=n}}
          X_i\,\frac{\partial F}{\partial X_i}=F,
    \]
    where $F_0$ is obtained by setting precisely those variables to zero.
  -/)
  (proof := /--
  Expand $F$ into monomials. If a monomial contains a variable whose weight has
  constant Cantor coefficient $n$, additivity of that coefficient under
  Hessenberg sum shows that the variable occurs exactly once and all other
  variable weights have constant Cantor coefficient zero. Otherwise the
  monomial is fixed by the substitution. Summing over the monomials gives the
  formula.
  -/)]
theorem eraseFinitePart_add_sum_X_mul_pderiv {F : MvPolynomial σ R} {δ : NatOrdinal}
    (hδ : 0 < δ.constantCoeff) (hF : IsWeightedHomogeneous wt F δ) :
    eraseFinitePart wt δ.constantCoeff F + ∑ t ∈ varsOfFinitePart wt F δ, X t * pderiv t F = F := by
  classical
  -- naming the index set keeps the `as_sum` rewrite from reaching inside it
  set T := varsOfFinitePart wt F δ with hT
  conv_rhs => rw [F.as_sum]
  conv_lhs => rw [F.as_sum, map_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hwd : Finsupp.weight wt d = δ := hF (mem_support_iff.mp hd)
  simp only [X_mul_pderiv_monomial, eraseFinitePart_monomial]
  split_ifs with h
  · obtain ⟨i, hi, hik⟩ := h
    obtain ⟨hdi, hdj⟩ := Finsupp.eq_one_and_eq_zero_of_constantCoeff_eq hδ hwd hi hik
    have hiT : i ∈ T := by
      rw [hT]
      exact mem_varsOfFinitePart_iff.mpr ⟨(mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩, hik⟩
    rw [zero_add, Finset.sum_eq_single i]
    · rw [hdi, one_smul]
    · intro t ht hti
      rw [hdj t hti (mem_varsOfFinitePart_iff.mp (hT ▸ ht)).2, zero_smul]
    · intro hno
      exact absurd hiT hno
  · rw [Finset.sum_eq_zero, add_zero]
    intro t ht
    have hdt : d t = 0 := by
      by_contra hdt
      exact h ⟨t, Finsupp.mem_support_iff.mpr hdt, (mem_varsOfFinitePart_iff.mp (hT ▸ ht)).2⟩
    rw [hdt, zero_smul]

end MvPolynomial

end
