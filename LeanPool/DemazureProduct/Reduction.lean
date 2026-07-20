/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import LeanPool.DemazureProduct.ReducedProducts

/-! # Reduction theorems

This file formalizes the main theorems from the introduction of
[An extended Demazure product](https://arxiv.org/abs/2206.14227): Theorem B
(`thm:starGreedy`) characterizes `α ⋆ β` as a greedy maximum, and Theorem C
(`thm:reduce`) reduces inequalities `α ⋆ β ≥ γ` to equalities of reduced products.
It corresponds roughly to Section 6 of the paper. -/

namespace LeanPool.DemazureProduct


namespace Reduction

open AspPerm

/-! ### Bookkeeping helpers -/

/-- Multiplying `α ⋆ β` on the right by `β⁻¹` recovers a permutation that lies
weakly below `α` in Bruhat order, has the same shift as `α`, and whose
product with `β` (ordinary or Demazure) returns `α ⋆ β`. -/
lemma star_left_witness (α β : AspPerm) :
    let α₁ := (α ⋆ β) * β⁻¹
    α₁ * β = α ⋆ β ∧ α₁ ⋆ β = α ⋆ β ∧ α₁ ≤χ α := by
  set α₁ := (α ⋆ β) * β⁻¹ with hα₁_def
  have h_mul : α₁ * β = α ⋆ β := by
    rw [hα₁_def, mul_assoc, inv_mul_cancel, mul_one]
  have rf : ReducedFact α₁ β (α ⋆ β) :=
    ReducedFact.of_mul_lel h_mul (Submodular.lel_of_dprod α β)
  suffices α₁ ≤χ α by exact ⟨h_mul, rf.star_eq, this⟩
  constructor
  · rw [hα₁_def, ← rf.lres_eq]
    exact (ge_star_iff_ge_lres α β (α ⋆ β)).mpr (le_refl _)
  · rw [hα₁_def, AspPerm.chi_mul, AspPerm.chi_star, AspPerm.chi_dual]
    rw [add_assoc, add_neg_cancel, add_zero]

/-- Multiplying `α ⋆ β` on the left by `α⁻¹` recovers a permutation that lies
weakly below `β` in Bruhat order, has the same shift as `β`, and whose
product with `α` (ordinary or Demazure) returns `α ⋆ β`. -/
lemma star_right_witness (α β : AspPerm) :
    let β₁ := α⁻¹ * (α ⋆ β)
    α * β₁ = α ⋆ β ∧ α ⋆ β₁ = α ⋆ β ∧ β₁ ≤χ β := by
  -- Proof written by GPT 5.5.
  obtain ⟨h_mul, h_star, h_leχ⟩ := star_left_witness β⁻¹ α⁻¹
  simp only [inv_inv] at h_mul h_star h_leχ
  refine ⟨?_, ?_, ?_⟩
  · simp_all
  · simpa only [AspPerm.inverse_star, mul_inv_rev, inv_inv] using
      congrArg (fun τ : AspPerm => τ⁻¹) h_star
  · simpa only [mul_inv_rev, AspPerm.inverse_star, inv_inv] using
      (AspPerm.le_chi_inv_iff ((β⁻¹ ⋆ α⁻¹) * α) β⁻¹).mp h_leχ

/-- The ordinary product of Bruhat-smaller factors lies below the Demazure
product of the original factors. This is the ASP form of the bound used in
the equation labeled `eq:astarbBound` in
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
lemma mul_le_star_of_le {α₁ α₂ β₁ β₂ : AspPerm}
    (hα : α₁ ≤ α₂) (hβ : β₁ ≤ β₂) : α₁ * β₁ ≤ α₂ ⋆ β₂ :=
  le_trans (ReducedProducts.mul_le_star α₁ β₁) (star_mono hα hβ)

/-! ### Theorem B: greedy characterization of `⋆` -/

/-- *Theorem B (`thm:starGreedy`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/3,
formula `eq:starGreedyAlpha`.*

`α ⋆ β` is the Bruhat-maximum of the set
$\{ \alpha_1 \beta : \alpha_1 \leq_\chi \alpha\}$. -/
theorem starGreedy_alpha (α β : AspPerm) :
    IsGreatest { α₁ * β | (α₁ : AspPerm) (_ : α₁ ≤χ α) }
      (α ⋆ β) := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨h_mul, _, h_chi⟩ := star_left_witness α β
  refine ⟨⟨(α ⋆ β) * β⁻¹, h_chi, h_mul⟩, ?_⟩
  rintro τ ⟨α₁, hα₁_le, rfl⟩
  exact mul_le_star_of_le hα₁_le.1 (le_refl β)

/-- *Theorem B (`thm:starGreedy`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/3,
formula `eq:starGreedyBeta`.*

`α ⋆ β` is the Bruhat-maximum of the set
$\{ \alpha \beta_1 : \beta_1 \leq_\chi \beta\}$. -/
theorem starGreedy_beta (α β : AspPerm) :
    IsGreatest { α * β₁ | (β₁ : AspPerm) (_ : β₁ ≤χ β) }
      (α ⋆ β) := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨h_mul, _, h_chi⟩ := star_right_witness α β
  refine ⟨⟨α⁻¹ * (α ⋆ β), h_chi, h_mul⟩, ?_⟩
  rintro τ ⟨β₁, hβ₁_le, rfl⟩
  exact mul_le_star_of_le (le_refl α) hβ₁_le.1

/-- *Theorem B (`thm:starGreedy`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/3,
formula `eq:starGreedy`.*

`α ⋆ β` is the Bruhat-maximum of the set
$\{ \alpha_1 \beta_1 : \alpha_1 \leq \alpha, \beta_1 \leq \beta\}$. -/
theorem starGreedy (α β : AspPerm) :
    IsGreatest
      { α₁ * β₁ | (α₁ : AspPerm) (_ : α₁ ≤ α) (β₁ : AspPerm) (_ : β₁ ≤ β) }
      (α ⋆ β) := by
  -- Proof written by Claude Opus 4.7.
  -- Membership: the witness from `starGreedy_alpha` works with `β₁ = β`.
  obtain ⟨⟨α₁, ⟨hα₁_le, _⟩, h_mul⟩, _⟩ := starGreedy_alpha α β
  refine ⟨⟨α₁, hα₁_le, β, le_refl β, h_mul⟩, ?_⟩
  rintro τ ⟨α₁, hα₁_le, β₁, hβ₁_le, rfl⟩
  exact mul_le_star_of_le hα₁_le hβ₁_le

/-! ### Theorem C: reduction theorem for `α ⋆ β ≥ γ` -/

/-- *Theorem C (`thm:reduce`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), second paragraph,
Bruhat component, part 1/3.*

If `α ⋆ β ≥ γ`, then `α₁ = γ ◃ β⁻¹` and `β₁ = α₁⁻¹ ▹ γ` satisfy
`α₁ ⋆ β₁ = α₁ * β₁ = γ` and `α₁ ≤ α`, `β₁ ≤ β`. -/
theorem reduce_witness (α β γ : AspPerm) (h : α ⋆ β ≥ γ) :
    let α₁ := γ ◃ β⁻¹
    let β₁ := α₁⁻¹ ▹ γ
    α₁ * β₁ = γ ∧ α₁ ⋆ β₁ = γ ∧ α₁ ≤ α ∧ β₁ ≤ β := by
  set α₁ := γ ◃ β⁻¹
  have α₁_le : α₁ ≤ α := (ge_star_iff_ge_lres α β γ).mpr h
  have h_alpha1_star_ge : α₁ ⋆ β ≥ γ :=
    (ge_star_iff_ge_lres α₁ β γ).mp (le_refl _)
  have : α₁ ≤R γ := Submodular.ler_of_lres γ β⁻¹
  set β₁ := α₁⁻¹ ▹ γ with hβ₁_def
  have β₁_le : β₁ ≤ β :=
    (ge_star_iff_ge_rres α₁ β γ).mpr h_alpha1_star_ge
  have rf := ReducedFact.of_ler_rres this hβ₁_def
  exact ⟨rf.mul_eq, rf.star_eq, α₁_le, β₁_le⟩

/-- *Theorem C (`thm:reduce`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), second paragraph, including the
shift identities, part 2/3.* Under the additional hypothesis $\chi_\alpha + \chi_\beta =
\chi_\gamma$ (which makes both shift equalities meaningful), we further have
$\alpha_1 \leq_\chi \alpha$ and $\beta_1 \leq_\chi \beta$. -/
theorem reduce_witness_chi (α β γ : AspPerm) (hχ : α.χ + β.χ = γ.χ)
    (h : α ⋆ β ≥ γ) :
    let α₁ := γ ◃ β⁻¹
    let β₁ := α₁⁻¹ ▹ γ
    α₁ * β₁ = γ ∧ α₁ ⋆ β₁ = γ ∧ α₁ ≤χ α ∧ β₁ ≤χ β := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨h_mul, h_star, h_alpha1_le, h_beta1_le⟩ := reduce_witness α β γ h
  set α₁ := γ ◃ β⁻¹ with hα₁_def
  set β₁ := α₁⁻¹ ▹ γ with hβ₁_def
  have h_chi_alpha : α₁.χ = α.χ := by
    rw [hα₁_def, AspPerm.chi_lres, AspPerm.chi_dual]
    linarith
  have h_chi_beta : β₁.χ = β.χ := by
    rw [hβ₁_def, AspPerm.chi_rres, AspPerm.chi_dual, h_chi_alpha]
    linarith
  exact ⟨h_mul, h_star, ⟨h_alpha1_le, h_chi_alpha⟩, ⟨h_beta1_le, h_chi_beta⟩⟩

/-- *Theorem C (`thm:reduce`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), first paragraph,
ASP form, part 3/3.*

For all `α, β, γ ∈ ASP` with `α.χ + β.χ = γ.χ`, the inequality `α ⋆ β ≥ γ`
is equivalent to the existence of `α₁, β₁` with `α₁ ≤χ α`, `β₁ ≤χ β`, and
`α₁ ⋆ β₁ = α₁ * β₁ = γ`. -/
theorem reduce (α β γ : AspPerm) (hχ : α.χ + β.χ = γ.χ) :
    α ⋆ β ≥ γ ↔
      ∃ α₁ β₁ : AspPerm,
        α₁ ≤χ α ∧ β₁ ≤χ β ∧ α₁ ⋆ β₁ = γ ∧ α₁ * β₁ = γ := by
  -- Proof written by Claude Opus 4.7.
  constructor
  · intro h
    obtain ⟨h_mul, h_star, h_chi_α, h_chi_β⟩ := reduce_witness_chi α β γ hχ h
    exact ⟨_, _, h_chi_α, h_chi_β, h_star, h_mul⟩
  · rintro ⟨α₁, β₁, ⟨hα₁_le, _⟩, ⟨hβ₁_le, _⟩, h_star, _⟩
    rw [← h_star]
    exact star_mono hα₁_le hβ₁_le

/-! ### Theorem 6.1 (`resLStingy`): stingy characterization of `◃`

The dual story for `◃`, mirroring Theorem B. This is the formula labeled
`eq:resLGreedyAlpha` in
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/

/-- The residual `α ◃ β⁻¹` is monotone in `α` for fixed `β`.

This is the ASP-level lift of `SlipFace.lres_mono`. -/
private lemma lres_inv_mono_alpha {α α' β : AspPerm} (hα : α ≤ α') :
    α ◃ β⁻¹ ≤ α' ◃ β⁻¹ := by
  -- Proof written by Claude Opus 4.7.
  apply (s_le_iff (α ◃ β⁻¹) (α' ◃ β⁻¹)).mp
  rw [lres_spec, lres_spec, ← s_dual]
  exact SlipFace.lres_mono ((s_le_iff α α').mpr hα) (le_refl β.s)

/-- The residual `α ◃ β⁻¹` is anti-monotone in `β`: if `β' ≤ β` then
`α ◃ β⁻¹ ≤ α ◃ β'⁻¹`. -/
private lemma lres_inv_antimono_beta {α β β' : AspPerm} (hβ : β' ≤ β) :
    α ◃ β⁻¹ ≤ α ◃ β'⁻¹ := by
  -- Proof written by Claude Opus 4.7.
  apply (s_le_iff (α ◃ β⁻¹) (α ◃ β'⁻¹)).mp
  rw [lres_spec, lres_spec, ← s_dual, ← s_dual]
  exact SlipFace.lres_mono (le_refl α.s) ((s_le_iff β' β).mpr hβ)

/-- Bounding the two factors puts an ordinary product above a left residual.
This is the ASP form of the bound labeled `eq:aresLbBound` in
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
private lemma lres_inv_le_mul {α α' β β' : AspPerm}
    (hα : α ≤ α') (hβ : β' ≤ β) : α ◃ β⁻¹ ≤ α' * β'⁻¹ := by
  -- Proof written by GPT 5.5.
  exact le_trans (lres_inv_mono_alpha hα) <|
    le_trans (lres_inv_antimono_beta hβ)
      (ReducedProducts.lres_le_mul α' β'⁻¹)

/-- *Theorem 6.1 (`thm:resLStingy`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/3,
formula `eq:resLGreedyAlpha`.*

`α ◃ β⁻¹` is the Bruhat-minimum of the set
$\{\alpha_1 \beta^{-1}: \alpha_1 \geq_\chi \alpha\}$. -/
theorem lres_stingy_alpha (α β : AspPerm) :
    IsLeast { α₁ * β⁻¹ | (α₁ : AspPerm) (_ : α ≤χ α₁) } (α ◃ β⁻¹) := by
  -- Proof written by GPT 5.5.
  -- Membership: take α₁ = (α ◃ β⁻¹) * β.
  set α₁ := (α ◃ β⁻¹) * β with hα₁_def
  have h_red : AspPerm.ReducedProduct (α ◃ β⁻¹) β := by
    have := Submodular.reducedProduct_of_lres α β⁻¹
    simpa using this
  have rf : ReducedFact (α ◃ β⁻¹) β α₁ :=
    ReducedFact.of_mul_reduced hα₁_def.symm h_red
  have h_alpha_le_alpha1 : α ≤ α₁ := by
    rw [← rf.star_eq]
    exact (ge_star_iff_ge_lres (α ◃ β⁻¹) β α).mp (le_refl _)
  have h_chi : α.χ = α₁.χ := by
    rw [← rf.mul_eq, AspPerm.chi_mul, AspPerm.chi_lres, AspPerm.chi_dual]
    ring
  have h_α₁β_eq : α₁ * β⁻¹ = α ◃ β⁻¹ := by
    rw [← rf.mul_eq, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨⟨α₁, ⟨h_alpha_le_alpha1, h_chi⟩, h_α₁β_eq⟩, ?_⟩
  -- Lower bound: any candidate is ≥ α ◃ β⁻¹.
  rintro τ ⟨α₂, hα₂_le, rfl⟩
  exact lres_inv_le_mul hα₂_le.1 (le_refl β)

/-- *Theorem 6.1 (`thm:resLStingy`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/3,
formula `eq:resLGreedyBeta`.*

`α ◃ β⁻¹` is the Bruhat-minimum of the set
$\{\alpha \beta_1^{-1}: \beta_1 \leq_\chi \beta\}$. -/
theorem lres_stingy_beta (α β : AspPerm) :
    IsLeast { α * β₁⁻¹ | (β₁ : AspPerm) (_ : β₁ ≤χ β) } (α ◃ β⁻¹) := by
  -- Proof written by GPT 5.5.
  set δ := α ◃ β⁻¹ with hδ_def
  set β₁ := δ⁻¹ ▹ α with hβ₁_def
  have h_ler : δ ≤R α := by
    rw [hδ_def]
    exact Submodular.ler_of_lres α β⁻¹
  have rf : ReducedFact δ β₁ α :=
    ReducedFact.of_ler_rres h_ler hβ₁_def.symm
  have h_mul : α * β₁⁻¹ = δ := by
    rw [← rf.mul_eq, mul_assoc, mul_inv_cancel, mul_one]
  have h_chi : β₁.χ = β.χ := by
    rw [hβ₁_def, AspPerm.chi_rres, AspPerm.chi_dual,
      hδ_def, AspPerm.chi_lres, AspPerm.chi_dual]
    ring
  have h_β1_le : β₁ ≤ β := by
    rw [hβ₁_def]
    apply (ge_star_iff_ge_rres δ β α).mpr
    apply (ge_star_iff_ge_lres δ β α).mp
    rw [hδ_def]
  refine ⟨⟨β₁, ⟨h_β1_le, h_chi⟩, by simpa [hδ_def] using h_mul⟩, ?_⟩
  -- Lower bound.
  rintro τ ⟨β₂, hβ₂_le, rfl⟩
  exact lres_inv_le_mul (le_refl α) hβ₂_le.1

/-- *Theorem 6.1 (`thm:resLStingy`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/3,
formula `eq:resLGreedy`.*

`α ◃ β⁻¹` is the Bruhat-minimum of the set
$\{\alpha_1 \beta_1^{-1}: \alpha_1 \geq \alpha,\, \beta_1 \leq \beta\}$. -/
theorem lres_stingy (α β : AspPerm) :
    IsLeast
      { α₁ * β₁⁻¹ | (α₁ : AspPerm) (_ : α ≤ α₁) (β₁ : AspPerm) (_ : β₁ ≤ β) }
      (α ◃ β⁻¹) := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨⟨α₁, ⟨hα₁_le, _⟩, h_α₁β_eq⟩, _⟩ := lres_stingy_alpha α β
  refine ⟨⟨α₁, hα₁_le, β, le_refl β, h_α₁β_eq⟩, ?_⟩
  rintro τ ⟨α₂, hα₂_ge, β₂, hβ₂_le, rfl⟩
  exact lres_inv_le_mul hα₂_ge hβ₂_le

/-! ### Theorem 6.5 (`reduceSeveral`): three- and many-fold reduction

The reduction theorem for products of three or more permutations follows
from `reduce` by induction. The list form below packages that induction. -/

/-- If `γ ≤ id` and `γ` has shift zero, then `γ = id`.

This is the shift-zero special case of the antisymmetry of Bruhat order. -/
private lemma eq_id_of_le_id_chi_zero {γ : AspPerm} (h : γ ≤ AspPerm.id)
    (hχ : γ.χ = 0) : γ = AspPerm.id := by
  -- Proof written by GPT 5.5.
  have h_id_le : AspPerm.id ≤ γ := by
    apply AspPerm.id_le_of_chi_nonneg
    rw [hχ]
  exact le_antisymm h h_id_le

/-- *Theorem 6.5 (`thm:reduceSeveral`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), ASP-level (list version).*

For any list of permutations `αs` and a target `γ ∈ ASP` with matching total
shift, if the Demazure product over `αs` is Bruhat-≥ `γ`, then there exists a
list of "reduced witnesses" `βs` of the same length, with `βᵢ ≤χ αᵢ`
pointwise, whose Demazure product and ordinary product both equal `γ`. -/
theorem reduceList :
    ∀ (αs : List AspPerm) (γ : AspPerm),
      (αs.map AspPerm.χ).sum = γ.χ →
      DProd αs ≥ γ →
      ∃ βs : List AspPerm,
        List.Forall₂ (fun α β => β ≤χ α) αs βs ∧
        DProd βs = γ ∧ OrdProd βs = γ
  | [], γ, hχ, h => by
      -- Proof written by Claude Opus 4.7.
      -- Base case: γ ≤ id and γ.χ = 0, hence γ = id.
      simp only [List.map_nil, List.sum_nil, DProd_nil] at hχ h
      have hγ : γ = AspPerm.id := eq_id_of_le_id_chi_zero h hχ.symm
      simp_all
  | (α :: αs), γ, hχ, h => by
      -- Proof written by Claude Opus 4.7.
      -- Inductive step: apply `reduce` to split off `α` from the suffix.
      have hsuff : α.χ + (DProd αs).χ = γ.χ := by
        rw [AspPerm.chi_DProd]
        simpa [List.map_cons, List.sum_cons] using hχ
      have h' : α ⋆ DProd αs ≥ γ := by
        simpa only [DProd_cons] using h
      obtain ⟨α₁, π, hα₁, hπ, h_star, h_mul⟩ :=
        (reduce α (DProd αs) γ hsuff).mp h'
      -- Inductive hypothesis on the suffix targeting `π`.
      have hπ_χ : (αs.map AspPerm.χ).sum = π.χ := by
        rw [← AspPerm.chi_DProd, hπ.2]
      obtain ⟨βs, hβs_forall, hβs_star, hβs_mul⟩ :=
        reduceList αs π hπ_χ hπ.1
      refine ⟨α₁ :: βs, List.Forall₂.cons hα₁ hβs_forall, ?_, ?_⟩
      · simp only [DProd_cons, hβs_star, h_star]
      · simp only [OrdProd_cons, hβs_mul, h_mul]

end Reduction

end LeanPool.DemazureProduct
