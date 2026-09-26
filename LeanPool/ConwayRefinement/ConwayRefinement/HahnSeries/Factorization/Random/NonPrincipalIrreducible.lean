/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.ClassIrreducible
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.GradedIrreducible
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentTensor
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeSum
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeInitialForm

/-!
# Irreducibility of non-principal series of finite degree

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Proposition 3.2, for `α = n < ω`: let `b = ∑ᵢ bᵢ t^{γᵢ} + r` with `b₁, …, bₘ ∈ P_n`,
`γ₁ < ⋯ < γₘ ≤ 0`, `deg(r) < n`, `sup(b) = 0`, and `Q(b₁, …, bₘ)`. Then `b` is irreducible.

The source reduces to LM24, Lemma 7.1.1 (`b` is irreducible when `rv(b)/p(rv(b))` is
irreducible and `p(b) = 1`) and Lemma 3.1 (`p(b) = 1`). The proof here keeps its shape but does
not pass through the maximal finite-support divisor: the initial form of `b` in the
degree-graded ring `RV̂` is `t^{γₘ} · B` for the block form `B = ∑ᵢ rv_J(bᵢ) t^{γᵢ - γₘ}`, which
is irreducible by `ConwayRefinement.HahnSeries.Factorization.Random.GradedIrreducible` because
`rv_J(bₘ)` is irreducible in `P̂` (Corollary 4.5, from `Q(bₘ)`); a factorisation `b = a c`
gives `in(a) in(c) = t^{γₘ} B`, so
one factor, say `a`, has initial form a monomial `k t^x`, hence `a = k t^x`; and `x < 0` is
impossible because `sup(b) = 0`, while `x = 0` makes `a` a unit. The hypothesis `sup(b) = 0` is
exactly what the source uses to pass from `p(b) ∣ t^{γₘ}` to `p(b) = 1`.

The source's "`a ∈ J + K` without loss of generality" is the step `deg_J(a) = 0` obtained from
the irreducibility of `rv(bₘ)`; the step "`deg_J(aᵢ) = 0` for every `i`, hence `a ∈ K(ℝ^{≤0})`"
is the coordinate-functional argument of the graded module.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci HahnSeries.Nonpositive

variable {K : Type v} [Field K]

/-- The series `∑ᵢ bᵢ t^{γᵢ} + r` of FLLM24, Proposition 3.2. -/
def blockSum {ι : Type*} [Fintype ι] (b : ι → Series K) (γ : ι → ℝ) (hγ : ∀ i, γ i ≤ 0)
    (r : Series K) : Series K :=
  ∑ i, b i * single (γ i) (1 : K) (hγ i) + r

theorem blockSum_def {ι : Type*} [Fintype ι] (b : ι → Series K) (γ : ι → ℝ) (hγ : ∀ i, γ i ≤ 0)
    (r : Series K) :
    blockSum b γ hγ r = ∑ i, b i * single (γ i) (1 : K) (hγ i) + r :=
  (rfl)

/-- The monomial `t^γ` as a finite-support series, for `γ ≤ 0`. -/
private theorem coe_monomial (γ : ℝ) (hγ : γ ≤ 0) :
    ((finiteSupportMonomial (K := K) (⟨γ, hγ⟩ : exponentMonoid ℝ) :
      Berarducci.FiniteSupportRing (K := K)) : Series K) = single γ (1 : K) hγ :=
  Subtype.ext ((coe_finiteSupportMonomial _).trans (coe_single _ _ _).symm)

variable [CharZero K]

omit [CharZero K] in
/-- The image of a finite-support series in `RV̂` is its class in grade zero, for any proof of
membership in the weak filtration at zero. -/
private theorem finiteSupportGradedEmbedding_eq_homogeneousMk'
    (p : Berarducci.FiniteSupportRing (K := K))
    (h : (p : Series K) ∈ (degreeValuation K).filtrationLE 0) :
    finiteSupportGradedEmbedding K p = (degreeValuation K).homogeneousMk 0 ⟨(p : Series K), h⟩ := by
  rw [finiteSupportGradedEmbedding_eq_homogeneousMk]
  exact congrArg _ (Subtype.ext (coe_finiteSupportFiltrationRepresentative p))

/-- The image of a principal series `p` of degree `n` in `RV̂` through `P̂`: its degree-initial
form is the image of its class `rv_J(p)`. -/
private theorem principalSubringEmbedding_rvJ_of_isPrincipal {n : NatOrdinal} {p : Series K}
    (hp : IsPrincipal p) (hpDegree : (p : K⟦ℝ⟧).degree = (n : WithBot NatOrdinal)) :
    principalSubringEmbedding K (rvJ p) = (degreeValuation K).initialForm p := by
  have hval : ordinalValue p = ω^ n := ordinalValue_eq_wpow_of_isPrincipal hp hpDegree
  have hcut : ordinalValue p < ω^ (n + 1) := by
    rw [hval]; exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one n)
  rw [rvJ_eq_gradeClass hval, gradeClass_of_lt hcut, principalSubringEmbedding_of,
    principalComponentToHahnDegreeLayer_mk n p hp hpDegree hcut, degreeLayerMk_eq_componentMk,
    ← MaxAddDegree.homogeneousMk_apply]
  apply MaxAddDegree.homogeneousMk_eq_initialForm_of_degree_eq
  rw [degreeValuation_apply, hpDegree]

/-- FLLM24, Proposition 3.2, for `α = n ≥ 1`: if `b₁, …, bₘ ∈ P_n` are hereditarily
`rv_J`-independent, `γ₁, …, γₘ ≤ 0` are distinct with maximum `γₘ`, `deg(r) < n`, and
`b = ∑ᵢ bᵢ t^{γᵢ} + r` has `sup(b) = 0`, then `b` is irreducible in `K((ℝ^{≤0}))`. -/
theorem irreducible_blockSum {n : ℕ} (hn : 1 ≤ n) {ι : Type} [Fintype ι]
    {b : ι → Series K} (hb : ∀ i, IsPrincipal (b i)) (hQ : HereditarilyRVIndependent n b)
    {γ : ι → ℝ} (hγ : ∀ i, γ i ≤ 0) (hinj : Function.Injective γ) (m : ι)
    (hm : ∀ i, γ i ≤ γ m) {r : Series K} (hr : (r : K⟦ℝ⟧).degree < ((n : NatOrdinal) : WithBot
      NatOrdinal)) (hsup : supportSup (blockSum b γ hγ r) = 0) :
    Irreducible (blockSum b γ hγ r) := by
  classical
  set B := blockSum b γ hγ r with hBdef
  have hval : ∀ i, ordinalValue (b i) = ω^ (n : NatOrdinal) := hQ.ordinalValue_eq
  have hdeg : ∀ i, ((b i : Series K) : K⟦ℝ⟧).degree = ((n : NatOrdinal) : WithBot NatOrdinal) :=
    fun i ↦ by
      rw [← ordinalValueDegree_eq_degree_of_isPrincipal (hb i), ordinalValueDegree_eq_coe_iff]
      exact hval i
  have hcut : ∀ i, ordinalValue (b i) < ω^ ((n : NatOrdinal) + 1) := fun i ↦ by
    rw [hval i]; exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)
  -- The classes and the exponents of the block form.
  let x : ι → PrincipalComponent K (n : NatOrdinal) :=
    fun i ↦ principalComponentMk _ (b i) (hcut i)
  have hx : ∀ i,
      rvJ (b i) = DirectSum.of (PrincipalComponent K) (n : NatOrdinal) (x i) := fun i ↦ by
    rw [rvJ_eq_gradeClass (hval i), gradeClass_of_lt (hcut i)]
  have hli : LinearIndependent K
      (fun i ↦ DirectSum.of (PrincipalComponent K) (n : NatOrdinal) (x i)) := by
    simpa only [hx] using hQ.linearIndependent
  let δ : ι → exponentMonoid ℝ := fun i ↦ ⟨γ i - γ m, sub_nonpos.mpr (hm i)⟩
  have hδm : δ m = 0 := Subtype.ext (sub_self (γ m))
  have hδ : ∀ i, δ i = 0 → i = m := fun i hi ↦ hinj (sub_eq_zero.mp (congrArg Subtype.val hi))
  let γm : exponentMonoid ℝ := ⟨γ m, hγ m⟩
  have hirr : Irreducible (DirectSum.of (PrincipalComponent K) (n : NatOrdinal) (x m)) := by
    rw [← hx]
    exact irreducible_rvJ_of_hereditarilyRVIndependent hn
      (hQ.comp_injective (fun _ : Unit ↦ m) fun _ _ _ ↦ rfl)
  set Bform := blockForm K (fun i ↦ DirectSum.of (PrincipalComponent K) (n : NatOrdinal) (x i)) δ
    with hBform
  -- The degree-`n` class of `B` is `t^{γₘ} · Bform`.
  have hle : ∀ i, ((b i * single (γ i) (1 : K) (hγ i) : Series K) : K⟦ℝ⟧).degree ≤
      ((n : NatOrdinal) : WithBot NatOrdinal) := fun i ↦ by
    rw [degree_mul, hdeg i]
    have h0 : ((single (γ i) (1 : K) (hγ i) : Series K) : K⟦ℝ⟧).degree ≤ 0 := by
      rw [HahnSeries.degree_le_zero_iff, coe_single]
      exact (Set.finite_singleton (γ i)).subset HahnSeries.support_single_subset
    calc ((n : NatOrdinal) : WithBot NatOrdinal) + ((single (γ i) (1 : K) (hγ i) : Series K) :
          K⟦ℝ⟧).degree ≤ (n : NatOrdinal) + (0 : WithBot NatOrdinal) := add_le_add le_rfl h0
      _ = (n : NatOrdinal) := add_zero _
  have hsum_le : degreeValuation K (∑ i, b i * single (γ i) (1 : K) (hγ i)) ≤
      ((n : NatOrdinal) : WithBot NatOrdinal) :=
    MaxAddDegree.map_sum_le_of_forall_le _ _ _ _ fun i _ ↦ by
      rw [degreeValuation_apply]; exact hle i
  have hBmem : B ∈ (degreeValuation K).filtrationLE (n : NatOrdinal) := by
    rw [MaxAddDegree.mem_filtrationLE_iff, hBdef, blockSum_def]
    exact ((degreeValuation K).map_add_le_max _ _).trans (max_le hsum_le (by
      rw [degreeValuation_apply]; exact hr.le))
  have hclass : (degreeValuation K).homogeneousMk (n : NatOrdinal) ⟨B, hBmem⟩ =
      finiteSupportGradedEmbedding K (finiteSupportMonomial γm) * Bform := by
    have hsum_mem : ∑ i, b i * single (γ i) (1 : K) (hγ i) ∈
        (degreeValuation K).filtrationLE (n : NatOrdinal) :=
      (MaxAddDegree.mem_filtrationLE_iff _ _ _).mpr hsum_le
    have hr_mem : r ∈ (degreeValuation K).filtrationLE (n : NatOrdinal) := by
      rw [MaxAddDegree.mem_filtrationLE_iff, degreeValuation_apply]; exact hr.le
    have hsplit : (degreeValuation K).homogeneousMk (n : NatOrdinal) ⟨B, hBmem⟩ =
        (degreeValuation K).homogeneousMk (n : NatOrdinal) ⟨_, hsum_mem⟩ +
          (degreeValuation K).homogeneousMk (n : NatOrdinal) ⟨r, hr_mem⟩ := by
      rw [← map_add]; rfl
    have hr_zero : (degreeValuation K).homogeneousMk (n : NatOrdinal) ⟨r, hr_mem⟩ = 0 :=
      (degreeValuation K).homogeneousMk_eq_zero_of_degree_lt hr_mem
        (by rw [degreeValuation_apply]; exact hr)
    rw [hsplit, hr_zero, add_zero, MaxAddDegree.homogeneousMk_finsetSum _ _ _
      (fun i _ ↦ (MaxAddDegree.mem_filtrationLE_iff _ _ _).mpr
        (by rw [degreeValuation_apply]; exact hle i)), hBform, blockForm_def, Finset.mul_sum,
      ← Finset.sum_attach Finset.univ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    -- Each term is `in(bᵢ) · t^{γᵢ}` with `t^{γᵢ} = t^{γₘ} t^{γᵢ - γₘ}`.
    have hbi_mem : b i ∈ (degreeValuation K).filtrationLE (n : NatOrdinal) := by
      rw [MaxAddDegree.mem_filtrationLE_iff, degreeValuation_apply, hdeg i]
    have hti_mem : ((finiteSupportMonomial (K := K) (⟨γ i, hγ i⟩ : exponentMonoid ℝ) :
        Berarducci.FiniteSupportRing (K := K)) : Series K) ∈
        (degreeValuation K).filtrationLE 0 := by
      rw [MaxAddDegree.mem_filtrationLE_iff, degreeValuation_apply, WithBot.coe_zero,
        HahnSeries.degree_le_zero_iff]
      exact (mem_finiteSupportSubring_iff _).mp (finiteSupportMonomial _).2
    have hbi_form : (degreeValuation K).homogeneousMk (n : NatOrdinal) ⟨b i, hbi_mem⟩ =
        principalSubringEmbedding K
          (DirectSum.of (PrincipalComponent K) (n : NatOrdinal) (x i)) := by
      rw [← hx i, principalSubringEmbedding_rvJ_of_isPrincipal (hb i) (hdeg i)]
      exact (degreeValuation K).homogeneousMk_eq_initialForm_of_degree_eq hbi_mem
        (by rw [degreeValuation_apply, hdeg i])
    rw [(degreeValuation K).homogeneousMk_mul_of_coe_eq (add_zero (n : NatOrdinal)).symm
      ⟨b i, hbi_mem⟩ ⟨_, hti_mem⟩ _ (by
        change b i * single (γ i) (1 : K) (hγ i) = b i * _
        rw [coe_monomial]),
      ← finiteSupportGradedEmbedding_eq_homogeneousMk' _ hti_mem, hbi_form,
      show (⟨γ i, hγ i⟩ : exponentMonoid ℝ) =
          ⟨(γm : ℝ) + ((δ i : exponentMonoid ℝ) : ℝ), (exponentMonoid ℝ).add_mem γm.2 (δ i).2⟩ from
        Subtype.ext (by change γ i = γ m + (γ i - γ m); ring),
      ← finiteSupportMonomial_mul, map_mul]
    ring
  -- The block form and the monomial are nonzero, so `B` has degree exactly `n`.
  have hBform_ne : Bform ≠ 0 := by
    intro h
    have hproj := rvProjection_blockForm
      (fun i ↦ DirectSum.of (PrincipalComponent K) (n : NatOrdinal) (x i)) δ m hδm hδ
    rw [← hBform, h, map_zero] at hproj
    exact hirr.ne_zero hproj.symm
  have hγm_ne : finiteSupportGradedEmbedding K (finiteSupportMonomial (K := K) γm) ≠ 0 := by
    intro h
    rw [← map_zero (finiteSupportGradedEmbedding K)] at h
    have h1 := finiteSupportGradedEmbedding_injective K h
    have h2 := congrArg (fun q : Berarducci.FiniteSupportRing (K := K) ↦
      ((q : Series K) : K⟦ℝ⟧).coeff (γ m)) h1
    simp only [coe_finiteSupportMonomial, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h2
    rw [show ((γm : exponentMonoid ℝ) : ℝ) = γ m from rfl, HahnSeries.coeff_single_same] at h2
    exact one_ne_zero h2
  have hBclass_ne : (degreeValuation K).homogeneousMk (n : NatOrdinal) ⟨B, hBmem⟩ ≠ 0 := by
    rw [hclass]; exact mul_ne_zero hγm_ne hBform_ne
  have hBdeg : degreeValuation K B = ((n : NatOrdinal) : WithBot NatOrdinal) := by
    have hle' : degreeValuation K B ≤ (n : NatOrdinal) :=
      (MaxAddDegree.mem_filtrationLE_iff _ _ _).mp hBmem
    rcases hle'.lt_or_eq with hlt | heq
    · exact absurd ((degreeValuation K).homogeneousMk_eq_zero_iff _ _ |>.mpr hlt) hBclass_ne
    · exact heq
  have hinit : (degreeValuation K).initialForm B =
      finiteSupportGradedEmbedding K (finiteSupportMonomial γm) * Bform := by
    rw [← hclass]
    exact ((degreeValuation K).homogeneousMk_eq_initialForm_of_degree_eq hBmem hBdeg).symm
  -- `B` is not a unit: the units are the constants, of degree zero.
  refine ⟨fun hunit ↦ ?_, fun a c hac ↦ ?_⟩
  · have hconst := eq_C_constantCoeff_of_isUnit hunit
    have h0 : degreeValuation K B ≤ 0 := by
      rw [hconst, degreeValuation_apply]
      exact degree_C_le_zero _
    rw [hBdeg] at h0
    exact absurd (WithBot.coe_le_coe.mp h0) (not_le.mpr (Nat.cast_pos.mpr hn))
  -- A factorisation: one factor has a monomial initial form, hence is a monomial.
  have hprod : (degreeValuation K).initialForm a * (degreeValuation K).initialForm c =
      finiteSupportGradedEmbedding K (finiteSupportMonomial γm) * Bform := by
    rw [← MaxAddDegree.initialForm_mul, ← hac, hinit]
  obtain ⟨p, hp, hpa⟩ := exists_isMonomial_factor_of_mul_eq x hli δ m hδm hδ hirr γm hprod
  have hp0 : p ≠ 0 := by
    intro h
    obtain ⟨g, l, hg, hl, hpeq⟩ := isMonomial_iff.mp hp
    rw [h] at hpeq
    have hcoeff := congrArg (fun q : Series K ↦ (q : K⟦ℝ⟧).coeff g) hpeq
    exact hl (by simpa [coe_single] using hcoeff.symm)
  -- A monomial factor of `B` is a unit, because `sup(B) = 0`.
  have hunit_of : ∀ a' : Series K, a' = (p : Series K) → a' ∣ B → IsUnit a' := by
    intro a' ha' hdvd
    obtain ⟨g, l, hg, hl, hpeq⟩ := isMonomial_iff.mp hp
    rw [ha', hpeq]
    rcases hg.lt_or_eq with hneg | hzero
    · exfalso
      have hJ : B ∈ negativeMonomialIdeal K := by
        have hmem : single g l hg ∈ negativeMonomialIdeal K := by
          rw [mem_negativeMonomialIdeal_iff_supportSup_lt_zero, supportSup_single hl hg]
          exact WithBot.coe_lt_coe.mpr hneg
        rw [ha', hpeq] at hdvd
        exact Ideal.mem_of_dvd _ hdvd hmem
      rw [mem_negativeMonomialIdeal_iff_supportSup_lt_zero, hsup] at hJ
      exact lt_irrefl _ hJ
    · subst hzero
      exact (isUnit_single_iff hl le_rfl).mpr rfl
  rcases hpa with ha | hc
  · exact Or.inl (hunit_of a (eq_of_initialForm_eq_finiteSupportGradedEmbedding hp0 ha)
      (Dvd.intro c hac.symm))
  · exact Or.inr (hunit_of c (eq_of_initialForm_eq_finiteSupportGradedEmbedding hp0 hc)
      (Dvd.intro_left a hac.symm))

end FLLM24

end
