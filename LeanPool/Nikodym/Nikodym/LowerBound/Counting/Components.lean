/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.PrivateFamily
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface
import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.WeightedSelection

/-!
# Assigning lines among proper-cut components

This file implements blueprint node **C06** of the lower-bound side of the sharp finite-field
Nikodym exponent, and combines it with the weighted selection **C07**.

Let `P : PrivateFamily F d E` be a private family of `L = Fintype.card E` lines, all contained in
a prime `I` of quotient dimension at least two, and let `g ∉ I` be a polynomial of total degree at
most `T` vanishing on every line of the family (the cutting polynomial of node C04, taken here as
an input). The proper cut `H.proper_cut` (B03) produces finitely many prime components `J` of
`I + (g)` of quotient dimension `quotDim I - 1`, positive degree and total degree at most
`T · deg I`. Every line ideal `P.lineIdeal e` is a prime containing `I + (g)`, hence contains some
component; we assign each index `e` one such component `c e`. The fibers of `c` partition `E`, so
the assigned counts `L_J = #{e | c e = J}` sum to `L`, and the weighted selection C07 yields a
component `J` with `L_J > 0` and `L · deg J ≤ L_J · (T · deg I)`.

Main declarations:

* `PrivateFamily.restrict_lineIdeal`: the line ideals of a subfamily are those of the family;
* `PrivateFamily.exists_component`: the component `J` together with the finset `s` of indices
  assigned to it (so `L_J = #s`), with `J ≤ P.lineIdeal e` for `e ∈ s`;
* `PrivateFamily.exists_component_family`: the same, packaged for the induction of node C09 with
  the private subfamily `P.restrict s` of `#s` lines lying on `J`.
-/

namespace Nikodym.LowerBound

open Finset

namespace PrivateFamily

variable {K : Type*} [Field K] {d : ℕ}
variable {F : Type*} [Field F] {E : Type*} [Fintype E] [Algebra F K] (P : PrivateFamily F d E)

/-- Blueprint C06: the line ideals of the subfamily `P.restrict s` are the line ideals of `P`. -/
@[simp]
theorem restrict_lineIdeal (s : Finset E) (e : s) :
    (P.restrict s).lineIdeal (K := K) e = P.lineIdeal (K := K) e :=
  rfl

/-- Blueprint C06: if `I` is contained in every line ideal of a nonempty private family and `g`
vanishes on every line of the family, then `I + (g)` is a proper ideal. -/
theorem sup_span_ne_top {I : Ideal (MvPolynomial (Fin d) K)} [Nonempty E]
    (hIP : ∀ e, I ≤ P.lineIdeal (K := K) e) {g : MvPolynomial (Fin d) K}
    (hg : ∀ e, g ∈ P.lineIdeal (K := K) e) : I ⊔ Ideal.span {g} ≠ ⊤ := by
  obtain ⟨e⟩ := ‹Nonempty E›
  exact ne_top_of_le_ne_top (P.lineIdeal_ne_top e)
    (sup_le (hIP e) ((Ideal.span_singleton_le_iff_mem _).mpr (hg e)))

/-- Blueprint C06 + C07: assigning the lines of a private family among the components of a proper
cut and selecting a component. Given a prime `I` of quotient dimension at least two containing
every line of the private family `P`, and a polynomial `g ∉ I` of total degree at most `T`
vanishing on every line of `P`, there are a prime component `J` of `I + (g)`, of quotient
dimension `quotDim I - 1` and positive degree, and a nonempty finset `s` of indices whose lines
lie on `J`, such that `L · deg J ≤ #s · (T · deg I)` where `L = Fintype.card E`. -/
theorem exists_component (H : AlgebraInterface K d)
    {I : Ideal (MvPolynomial (Fin d) K)} (hI : I.IsPrime) (hk : 2 ≤ quotDim I)
    (hIP : ∀ e, I ≤ P.lineIdeal (K := K) e) [Nonempty E]
    {g : MvPolynomial (Fin d) K} {T : ℕ} (hgI : g ∉ I) (hgT : g.totalDegree ≤ T)
    (hg : ∀ e, g ∈ P.lineIdeal (K := K) e) :
    ∃ (J : Ideal (MvPolynomial (Fin d) K)) (s : Finset E),
      J.IsPrime ∧ quotDim J + 1 = quotDim I ∧ 0 < degree J ∧
      s.Nonempty ∧ (∀ e ∈ s, J ≤ P.lineIdeal (K := K) e) ∧
      Fintype.card E * degree J ≤ #s * (T * degree I) := by
  classical
  obtain ⟨S, hSprime, -, hSdim, hSdeg, hSsum, hSmin⟩ :=
    H.proper_cut I hI hk g T hgI hgT (P.sup_span_ne_top hIP hg)
  -- assign each index a component contained in its line ideal
  have hchoice : ∀ e : E, ∃ J ∈ S, J ≤ P.lineIdeal (K := K) e := fun e ↦
    hSmin _ (P.lineIdeal_isPrime e)
      (sup_le (hIP e) ((Ideal.span_singleton_le_iff_mem _).mpr (hg e)))
  choose c hcS hcle using hchoice
  -- the assigned counts sum to the number of lines
  have hsum : ∑ J ∈ S, #{e | c e = J} = Fintype.card E := by
    rw [← card_univ, card_eq_sum_card_fiberwise (t := S) fun e _ ↦ hcS e]
  obtain ⟨J, hJS, hJpos, hJle⟩ := exists_weighted_index S (fun J ↦ #{e | c e = J})
    (fun J ↦ degree J) (T * degree I) (by rw [hsum]; exact Fintype.card_pos) hSdeg hSsum
  refine ⟨J, univ.filter fun e ↦ c e = J, hSprime J hJS, hSdim J hJS, hSdeg J hJS,
    card_pos.mp hJpos, fun e he ↦ ?_, ?_⟩
  · rw [← (mem_filter.mp he).2]
    exact hcle e
  · rw [hsum] at hJle
    exact hJle

/-- Blueprint C06 + C07, packaged for the induction of node C09: the selected component `J` carries
the private subfamily `P.restrict s` of `#s > 0` lines, with `L · deg J ≤ #s · (T · deg I)`. -/
theorem exists_component_family (H : AlgebraInterface K d)
    {I : Ideal (MvPolynomial (Fin d) K)} (hI : I.IsPrime) (hk : 2 ≤ quotDim I)
    (hIP : ∀ e, I ≤ P.lineIdeal (K := K) e) [Nonempty E]
    {g : MvPolynomial (Fin d) K} {T : ℕ} (hgI : g ∉ I) (hgT : g.totalDegree ≤ T)
    (hg : ∀ e, g ∈ P.lineIdeal (K := K) e) :
    ∃ (J : Ideal (MvPolynomial (Fin d) K)) (s : Finset E),
      J.IsPrime ∧ quotDim J + 1 = quotDim I ∧ 0 < degree J ∧ 0 < #s ∧
      (∀ e : s, J ≤ (P.restrict s).lineIdeal (K := K) e) ∧
      Fintype.card E * degree J ≤ #s * (T * degree I) := by
  obtain ⟨J, s, hJ, hdim, hdeg, hs, hle, hcard⟩ := P.exists_component H hI hk hIP hgI hgT hg
  exact ⟨J, s, hJ, hdim, hdeg, card_pos.mpr hs, fun e ↦ hle e e.2, hcard⟩

end PrivateFamily

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
