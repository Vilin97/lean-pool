/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.HypersurfaceDegree
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LinearNormalization
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.PolyAsymptotics

/-!
# Degree sum over the components of a hypersurface section

This file implements blueprint node **B02** of the algebra backend, for the polynomial ring
`P := MvPolynomial (Fin N) K` with its standard grading `homogeneousSubmodule (Fin N) K`. The
inclusion–exclusion identity B02(i) `homHilbert_inf_add_homHilbert_sup` lives in
`GradedLemmas.lean`.

## Main declarations

* B02(ii) `homHilbert_le_mul_choose`: for `K` infinite and `J ≠ ⊤` homogeneous with
  `quotDim J ≤ m + 1`, `homHilbert J t ≤ C * (t + m).choose m` for some `C` and all `t`. From the
  linear normalization (A02) `y₁, …, y_s` (`s = quotDim J`) with `𝔪 ^ r ≤ J ⊔ (y)`, the degree-`t`
  part of `P ⧸ J` is spanned by the classes of `y ^ α * X ^ β` with `|β| < r`, `|α| + |β| = t`
  (`mk_mem_span_normalizationGens`), and there are at most `(r + N).choose N * (t + m).choose m` of
  these (`card_normalizationGens_le`).
* B02(iii) `quotDim_le_of_le_of_le`, `quotDim_sup_le_of_ne`: a prime containing two distinct primes
  of the same quotient dimension `k` has quotient dimension `≤ k - 1`; the sum-over-a-finset bound
  `exists_sum_homHilbert_le_homHilbert_inf_add`: for a finset `𝒬` of homogeneous primes of quotient
  dimension `m + 2`, `∑_{Q ∈ 𝒬} homHilbert Q t ≤ homHilbert (⨅ 𝒬) t + C * (t + m).choose m`.
* B02(iv)+(v) `sum_coeff_le_of_components`: the main statement, purely in terms of `homHilbert` and
  eventual polynomials: if `Q₀` is a homogeneous prime of quotient dimension `n + 2`, `G ∉ Q₀` a
  form of degree `e`, and `𝒬` a finset of homogeneous primes of quotient dimension `n + 1`
  containing `Q₀ ⊔ (G)`, with eventual Hilbert polynomials `p₀` (degree `≤ n + 1`) and `p Q`
  (degree `≤ n`), then `∑_{Q ∈ 𝒬} (p Q).coeff n ≤ e * (n + 1) * p₀.coeff (n + 1)`.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial Module Filter

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {N : ℕ}

/-! ### B02(ii): the growth bound -/

section Growth

/-- Blueprint B02(ii), counting: the number of exponent vectors `α : Fin s →₀ ℕ` of degree exactly
`v` is at most `(t + m).choose m` when `v ≤ t` and `s ≤ m + 1`. -/
theorem card_finsuppAntidiag_le_choose {s m v t : ℕ} (hs : s ≤ m + 1) (hv : v ≤ t) :
    ((Finset.univ : Finset (Fin s)).finsuppAntidiag v).card ≤ (t + m).choose m := by
  rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ, Fintype.card_fin,
    Nat.multichoose_eq]
  have hpos : 1 ≤ (t + m).choose m := Nat.choose_pos (by omega)
  rcases s with _ | s
  · rcases v with _ | v
    · simpa using hpos
    · rw [Nat.zero_add, Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self v)]
      exact Nat.zero_le _
  · have h1 : s + 1 + v - 1 = v + s := by omega
    rw [h1]
    calc (v + s).choose v ≤ (v + m).choose v := Nat.choose_le_choose v (by omega)
      _ = (v + m).choose m := Nat.choose_symm_add
      _ ≤ (t + m).choose m := Nat.choose_le_choose m (by omega)

open scoped Classical in
/-- Blueprint B02(ii): the finite set of classes in `P ⧸ J` of the products `y ^ α * X ^ β`
(`y ^ α := aeval y (monomial α 1)`) with `|β| < r` and `|α| + |β| = t`. For linear forms `y` with
`𝔪 ^ r ≤ J ⊔ (y)` these span the degree-`t` part of `P ⧸ J` (`mk_mem_span_normalizationGens`). -/
noncomputable def normalizationGens (J : Ideal (MvPolynomial (Fin N) K)) {s : ℕ}
    (y : Fin s → MvPolynomial (Fin N) K) (r t : ℕ) : Finset (MvPolynomial (Fin N) K ⧸ J) :=
  ((exponentsLE N t).filter fun β ↦ β.degree < r).biUnion fun β ↦
    ((Finset.univ : Finset (Fin s)).finsuppAntidiag (t - β.degree)).image
      fun α : Fin s →₀ ℕ ↦ Ideal.Quotient.mk J (aeval y (monomial α (1 : K)) * monomial β 1)

/-- Blueprint B02(ii): membership in `normalizationGens`. -/
theorem mem_normalizationGens {J : Ideal (MvPolynomial (Fin N) K)} {s : ℕ}
    {y : Fin s → MvPolynomial (Fin N) K} {r t : ℕ} {α : Fin s →₀ ℕ} {β : Fin N →₀ ℕ}
    (hβ : β.degree < r) (hαβ : α.degree + β.degree = t) :
    Ideal.Quotient.mk J (aeval y (monomial α (1 : K)) * monomial β 1) ∈
      normalizationGens J y r t := by
  classical
  rw [normalizationGens, Finset.mem_biUnion]
  refine ⟨β, Finset.mem_filter.mpr ⟨mem_exponentsLE.mpr (by omega), hβ⟩,
    Finset.mem_image.mpr ⟨α, ?_, rfl⟩⟩
  rw [Finset.mem_finsuppAntidiag]
  refine ⟨?_, Finset.subset_univ _⟩
  rw [← Finsupp.degree_eq_sum]
  omega

/-- Blueprint B02(ii): `normalizationGens J y r t` has at most `(r + N).choose N * (t + m).choose m`
elements when `s ≤ m + 1`. -/
theorem card_normalizationGens_le {J : Ideal (MvPolynomial (Fin N) K)} {s : ℕ}
    {y : Fin s → MvPolynomial (Fin N) K} {r t m : ℕ} (hs : s ≤ m + 1) :
    (normalizationGens J y r t).card ≤ (r + N).choose N * (t + m).choose m := by
  classical
  rw [normalizationGens]
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((t + m).choose m) fun β _ ↦ ?_).trans ?_
  · exact Finset.card_image_le.trans (card_finsuppAntidiag_le_choose hs (Nat.sub_le _ _))
  · rw [smul_eq_mul]
    refine Nat.mul_le_mul_right _ ?_
    rw [← card_exponentsLE N r]
    refine Finset.card_le_card fun β hβ ↦ ?_
    rw [Finset.mem_filter] at hβ
    exact mem_exponentsLE.mpr hβ.2.le

/-- Blueprint B02(ii): **the classes of `y ^ α * X ^ β` span the graded pieces of `P ⧸ J`.** For
`J ≠ ⊤` homogeneous and linear forms `y` with `𝔪 ^ r ≤ J ⊔ (y)`, the class of every form of
degree `t` lies in the `K`-span of `normalizationGens J y r t`. By strong induction on `t`: for
`t < r` a form is a combination of monomials `X ^ β` with `|β| = t`; for `t ≥ r` it is
`G + ∑ i, y i * H i` with `G ∈ J` and forms `H i` of degree `t - 1` (A02.h), and multiplication by
`y i` sends the generators of degree `t - 1` to generators of degree `t`. -/
theorem mk_mem_span_normalizationGens {J : Ideal (MvPolynomial (Fin N) K)} (hJ : J ≠ ⊤)
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin N) K)) {s r : ℕ}
    {y : Fin s → MvPolynomial (Fin N) K} (hy : ∀ i, (y i).IsHomogeneous 1)
    (hr : idealOfVars (Fin N) K ^ r ≤ J ⊔ Ideal.span (Set.range y)) (t : ℕ)
    {F : MvPolynomial (Fin N) K} (hF : F.IsHomogeneous t) :
    Ideal.Quotient.mk J F ∈
      Submodule.span K (normalizationGens J y r t : Set (MvPolynomial (Fin N) K ⧸ J)) := by
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      subst h0
      exact sup_span_range_ne_top hJ hJh hy (top_le_iff.mp (by simpa using hr))
    · exact h0
  induction t using Nat.strong_induction_on generalizing F with
  | _ t ih =>
    by_cases ht : t < r
    · -- a form of degree `t < r` is a combination of monomials of degree `t`
      rw [F.as_sum, map_sum]
      refine Submodule.sum_mem _ fun β hβ ↦ ?_
      have hdeg : β.degree = t := degree_eq_of_isHomogeneous hF hβ
      have hmem : Ideal.Quotient.mk J
          (aeval y (monomial (0 : Fin s →₀ ℕ) (1 : K)) * monomial β 1) ∈
            normalizationGens J y r t :=
        mem_normalizationGens (by omega) (by rw [map_zero, zero_add, hdeg])
      have heq : Ideal.Quotient.mk J (monomial β (F.coeff β)) = F.coeff β •
          Ideal.Quotient.mk J (aeval y (monomial (0 : Fin s →₀ ℕ) (1 : K)) * monomial β 1) := by
        rw [monomial_zero', C_1, map_one, one_mul]
        change _ = Ideal.Quotient.mk J (F.coeff β • monomial β (1 : K))
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
    · -- a form of degree `t ≥ r` is `G + ∑ i, y i * H i`
      replace ht := not_lt.mp ht
      obtain ⟨G, H, hG, hH, hFGH⟩ := exists_eq_add_sum_mul_of_pow_idealOfVars_le hJh hy hr ht hF
      rw [hFGH, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hG, zero_add, map_sum]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [map_mul]
      -- multiplication by `y i` maps the generators of degree `t - 1` into those of degree `t`
      have hmap : (Submodule.span K (normalizationGens J y r (t - 1) :
            Set (MvPolynomial (Fin N) K ⧸ J))).map
            (LinearMap.mulLeft K (Ideal.Quotient.mk J (y i))) ≤
          Submodule.span K (normalizationGens J y r t : Set (MvPolynomial (Fin N) K ⧸ J)) := by
        rw [Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        classical
        rw [Finset.mem_coe, normalizationGens, Finset.mem_biUnion] at hx
        obtain ⟨β, hβ, hx⟩ := hx
        obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_filter, mem_exponentsLE] at hβ
        rw [Finset.mem_finsuppAntidiag, ← Finsupp.degree_eq_sum] at hα
        rw [Finset.mem_coe, LinearMap.mulLeft_apply, ← map_mul, ← mul_assoc, ← aeval_X (R := K) y i,
          ← map_mul (aeval y), ← pow_one (X i), ← monomial_single_add]
        refine mem_normalizationGens hβ.2 ?_
        rw [map_add, Finsupp.degree_single]
        omega
      exact hmap (Submodule.mem_map_of_mem (ih (t - 1) (by omega) (hH i)))

/-- Blueprint B02(ii): **growth bound.** For `K` infinite and `J ≠ ⊤` homogeneous with
`quotDim J ≤ m + 1`, there is `C` with `homHilbert J t ≤ C * (t + m).choose m` for all `t`. -/
theorem homHilbert_le_mul_choose [Infinite K] {J : Ideal (MvPolynomial (Fin N) K)} (hJ : J ≠ ⊤)
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin N) K)) {m : ℕ} (hm : quotDim J ≤ m + 1) :
    ∃ C : ℕ, ∀ t, homHilbert J t ≤ C * (t + m).choose m := by
  obtain ⟨y, hy, -, r, hr⟩ := exists_linear_normalization J hJ hJh
  refine ⟨(r + N).choose N, fun t ↦ ?_⟩
  have hspan : (homogeneousSubmodule (Fin N) K t).map (Ideal.Quotient.mkₐ K J).toLinearMap ≤
      Submodule.span K (normalizationGens J y r t : Set (MvPolynomial (Fin N) K ⧸ J)) := by
    rw [Submodule.map_le_iff_le_comap]
    intro F hF
    exact mk_mem_span_normalizationGens hJ hJh hy hr t hF
  have : Module.Finite K
      (Submodule.span K (normalizationGens J y r t : Set (MvPolynomial (Fin N) K ⧸ J))) :=
    Module.Finite.span_of_finite K (Finset.finite_toSet _)
  calc homHilbert J t
      ≤ finrank K (Submodule.span K (normalizationGens J y r t :
          Set (MvPolynomial (Fin N) K ⧸ J))) := Submodule.finrank_mono hspan
    _ ≤ (normalizationGens J y r t).card := finrank_span_finset_le_card _
    _ ≤ (r + N).choose N * (t + m).choose m := card_normalizationGens_le hm

end Growth

/-! ### B02(iii): the correction ideals have smaller dimension -/

section Correction

/-- Blueprint B02(iii): a prime `q` containing two distinct primes `Q ≠ Q'` of the same quotient
dimension `k` has `quotDim q ≤ k - 1`: one of the inclusions `Q ≤ q`, `Q' ≤ q` is strict. -/
theorem quotDim_le_of_le_of_le {Q Q' q : Ideal (MvPolynomial (Fin N) K)} [Q.IsPrime] [Q'.IsPrime]
    [q.IsPrime] {k : ℕ} (hQ : quotDim Q = k) (hQ' : quotDim Q' = k) (hne : Q ≠ Q') (hQq : Q ≤ q)
    (hQ'q : Q' ≤ q) : quotDim q ≤ k - 1 := by
  rcases hQq.lt_or_eq with hlt | heq
  · have := quotDim_lt_of_lt hlt
    omega
  · subst heq
    have := quotDim_lt_of_lt (lt_of_le_of_ne hQ'q hne.symm)
    omega

/-- Blueprint B02(iii): for distinct primes `Q ≠ Q'` of the same quotient dimension `k`,
`quotDim (Q ⊔ Q') ≤ k - 1` (with the junk value `quotDim ⊤ = 0` if `Q ⊔ Q' = ⊤`). -/
theorem quotDim_sup_le_of_ne {Q Q' : Ideal (MvPolynomial (Fin N) K)} [Q.IsPrime] [Q'.IsPrime]
    {k : ℕ} (hQ : quotDim Q = k) (hQ' : quotDim Q' = k) (hne : Q ≠ Q') :
    quotDim (Q ⊔ Q') ≤ k - 1 := by
  by_cases htop : Q ⊔ Q' = ⊤
  · rw [htop, quotDim_top]
    exact Nat.zero_le _
  · refine quotDim_le_of_forall_isPrime (fun q hq hle ↦ ?_) htop
    have := hq
    exact quotDim_le_of_le_of_le hQ hQ' hne (le_sup_left.trans hle) (le_sup_right.trans hle)

/-- Blueprint B02(iii): **sum over a finset of components.** For `K` infinite and a finset `𝒬` of
homogeneous primes of quotient dimension `m + 2`, there is `C` with
`∑_{Q ∈ 𝒬} homHilbert Q t ≤ homHilbert (⨅ 𝒬) t + C * (t + m).choose m` for all `t`. Induction on
`𝒬` with the inclusion–exclusion identity `homHilbert_inf_add_homHilbert_sup`: the correction
ideal `Q ⊔ ⨅ 𝒬'` has quotient dimension `≤ m + 1` (every prime over it contains `Q` and some
`Q' ∈ 𝒬'`, `Q' ≠ Q`), so its Hilbert function is `O((t + m).choose m)` by B02(ii). -/
theorem exists_sum_homHilbert_le_homHilbert_inf_add [Infinite K] {m : ℕ}
    (𝒬 : Finset (Ideal (MvPolynomial (Fin N) K)))
    (h𝒬 : ∀ Q ∈ 𝒬, Q.IsPrime ∧ Q.IsHomogeneous (homogeneousSubmodule (Fin N) K) ∧
      quotDim Q = m + 2) :
    ∃ C : ℕ, ∀ t, ∑ Q ∈ 𝒬, homHilbert Q t ≤ homHilbert (𝒬.inf id) t + C * (t + m).choose m := by
  classical
  induction 𝒬 using Finset.induction_on with
  | empty => exact ⟨0, fun t ↦ by simp⟩
  | insert Q s hQs ih =>
    obtain ⟨C, hC⟩ := ih fun Q' hQ' ↦ h𝒬 Q' (Finset.mem_insert_of_mem hQ')
    obtain ⟨hQp, hQh, hQd⟩ := h𝒬 Q (Finset.mem_insert_self Q s)
    have hAh : (s.inf id).IsHomogeneous (homogeneousSubmodule (Fin N) K) :=
      Finset.inf_induction (Ideal.IsHomogeneous.top _) (fun _ ha _ hb ↦ ha.inf hb)
        fun Q' hQ' ↦ (h𝒬 Q' (Finset.mem_insert_of_mem hQ')).2.1
    have hkey := homHilbert_inf_add_homHilbert_sup hQh hAh
    obtain ⟨C', hC'⟩ : ∃ C' : ℕ, ∀ t, homHilbert (Q ⊔ s.inf id) t ≤ C' * (t + m).choose m := by
      by_cases htop : Q ⊔ s.inf id = ⊤
      · exact ⟨0, fun t ↦ by rw [htop, homHilbert_top]; exact Nat.zero_le _⟩
      · refine homHilbert_le_mul_choose htop (hQh.sup hAh) ?_
        refine quotDim_le_of_forall_isPrime (fun q hq hle ↦ ?_) htop
        have := hq
        obtain ⟨Q', hQ's, hQ'q⟩ := (Ideal.IsPrime.inf_le' hq).mp (le_sup_right.trans hle)
        obtain ⟨hQ'p, -, hQ'd⟩ := h𝒬 Q' (Finset.mem_insert_of_mem hQ's)
        have := hQp
        have := hQ'p
        have hne : Q ≠ Q' := fun h ↦ hQs (h ▸ hQ's)
        have := quotDim_le_of_le_of_le hQd hQ'd hne (le_sup_left.trans hle) hQ'q
        omega
    refine ⟨C + C', fun t ↦ ?_⟩
    rw [Finset.sum_insert hQs, Finset.inf_insert, id_eq, add_mul]
    have h1 := hC t
    have h2 := hkey t
    have h3 := hC' t
    omega

end Correction

/-! ### B02(iv)+(v): the main statement -/

section Main

/-- Blueprint B02(v): for `natDegree p ≤ n + 1`, the difference `p - p.comp (X - C e)` has
`natDegree ≤ n` (the top coefficients cancel). -/
theorem natDegree_sub_comp_X_sub_C_le {p : Polynomial ℚ} {n : ℕ} (hp : p.natDegree ≤ n + 1)
    (e : ℚ) : (p - p.comp (Polynomial.X - Polynomial.C e)).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro M hM
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [Polynomial.coeff_sub_comp_X_sub_C (hp.trans (by omega)) e,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

/-- Blueprint B02: **degree sum over the components of a hypersurface section.** Let `Q₀` be a
homogeneous prime of `MvPolynomial (Fin N) K` (`K` infinite) of quotient dimension `n + 2`, `G ∉ Q₀`
a form of degree `e`, and `𝒬` a finset of homogeneous primes of quotient dimension `n + 1`
containing `Q₀ ⊔ (G)`. If the homogeneous Hilbert functions of `Q₀` and of the `Q ∈ 𝒬` are
eventually given by polynomials `p₀` (of degree `≤ n + 1`) and `p Q` (of degree `≤ n`), then
`∑_{Q ∈ 𝒬} (p Q).coeff n ≤ e * (n + 1) * p₀.coeff (n + 1)`.

For large `t`, `∑_Q p_Q(t) = ∑_Q homHilbert Q t ≤ homHilbert (⨅ 𝒬) t + C (t + n - 1).choose (n - 1)`
(B02(iii)) `≤ homHilbert (Q₀ ⊔ (G)) t + …` (`homHilbert_anti`) `= p₀(t) - p₀(t - e) + …` (B01);
compare the coefficients of `X ^ n` (`Polynomial.coeff_le_coeff_of_eventually_le`,
`Polynomial.coeff_sub_comp_X_sub_C`). -/
theorem sum_coeff_le_of_components [Infinite K] {n : ℕ} (hn : 1 ≤ n)
    {Q₀ : Ideal (MvPolynomial (Fin N) K)} [Q₀.IsPrime]
    (hQ₀ : Q₀.IsHomogeneous (homogeneousSubmodule (Fin N) K)) (hdim₀ : quotDim Q₀ = n + 2)
    {G : MvPolynomial (Fin N) K} {e : ℕ} (hG : G.IsHomogeneous e) (hGQ : G ∉ Q₀)
    (𝒬 : Finset (Ideal (MvPolynomial (Fin N) K)))
    (h𝒬 : ∀ Q ∈ 𝒬, Q.IsPrime ∧ Q.IsHomogeneous (homogeneousSubmodule (Fin N) K) ∧
      quotDim Q = n + 1 ∧ Q₀ ⊔ Ideal.span {G} ≤ Q)
    {p₀ : Polynomial ℚ} (hp₀ : ∀ᶠ t : ℕ in Filter.atTop, (homHilbert Q₀ t : ℚ) = p₀.eval (t : ℚ))
    (hd₀ : p₀.natDegree ≤ n + 1)
    {p : Ideal (MvPolynomial (Fin N) K) → Polynomial ℚ}
    (hp : ∀ Q ∈ 𝒬, ∀ᶠ t : ℕ in Filter.atTop, (homHilbert Q t : ℚ) = (p Q).eval (t : ℚ))
    (hd : ∀ Q ∈ 𝒬, (p Q).natDegree ≤ n) :
    ∑ Q ∈ 𝒬, (p Q).coeff n ≤ e * (n + 1) * p₀.coeff (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨C, hC⟩ := exists_sum_homHilbert_le_homHilbert_inf_add 𝒬 fun Q hQ ↦
    ⟨(h𝒬 Q hQ).1, (h𝒬 Q hQ).2.1, (h𝒬 Q hQ).2.2.1⟩
  have hle : Q₀ ⊔ Ideal.span {G} ≤ 𝒬.inf id := Finset.le_inf fun Q hQ ↦ (h𝒬 Q hQ).2.2.2
  -- the comparison polynomial
  have hqdeg : (p₀ - p₀.comp (Polynomial.X - Polynomial.C (e : ℚ)) +
      Polynomial.C (C : ℚ) * choosePoly m).natDegree ≤ m + 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans
      (max_le (natDegree_sub_comp_X_sub_C_le hd₀ _) ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_choosePoly]
    omega
  have hSdeg : (∑ Q ∈ 𝒬, p Q).natDegree ≤ m + 1 := Polynomial.natDegree_sum_le_of_forall_le _ _ hd
  have hev : ∀ᶠ t : ℕ in atTop, (∑ Q ∈ 𝒬, p Q).eval (t : ℚ) ≤
      (p₀ - p₀.comp (Polynomial.X - Polynomial.C (e : ℚ)) +
        Polynomial.C (C : ℚ) * choosePoly m).eval (t : ℚ) := by
    have h1 := (Filter.eventually_all_finset 𝒬).mpr hp
    have h2 : ∀ᶠ t : ℕ in atTop, (homHilbert Q₀ (t - e) : ℚ) = p₀.eval ((t - e : ℕ) : ℚ) :=
      (Filter.tendsto_sub_atTop_nat e).eventually hp₀
    filter_upwards [h1, hp₀, h2, Filter.eventually_ge_atTop e] with t ht hp₀t hp₀t' hte
    have hB : (homHilbert (Q₀ ⊔ Ideal.span {G}) t : ℚ) + homHilbert Q₀ (t - e) =
        homHilbert Q₀ t := by
      exact_mod_cast homHilbert_sup_span_singleton_add hQ₀ hG hGQ hte
    have hsum : ((∑ Q ∈ 𝒬, homHilbert Q t : ℕ) : ℚ) ≤
        ((homHilbert (Q₀ ⊔ Ideal.span {G}) t + C * (t + m).choose m : ℕ) : ℚ) := by
      exact_mod_cast (hC t).trans (Nat.add_le_add_right (homHilbert_anti hle t) _)
    push_cast at hsum
    rw [Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp_X_sub_C_natCast p₀ hte, choosePoly_eval_natCast]
    calc ∑ Q ∈ 𝒬, (p Q).eval (t : ℚ) = ∑ Q ∈ 𝒬, (homHilbert Q t : ℚ) :=
          Finset.sum_congr rfl fun Q hQ ↦ (ht Q hQ).symm
      _ ≤ _ := by linarith
  have hcoeff := Polynomial.coeff_le_coeff_of_eventually_le hSdeg hqdeg hev
  have hchoose : (choosePoly m).coeff (m + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_choosePoly]; omega)
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_add, Polynomial.coeff_C_mul, hchoose, mul_zero,
    add_zero, Polynomial.coeff_sub_comp_X_sub_C hd₀] at hcoeff
  exact hcoeff.trans_eq (by ring)

end Main

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
