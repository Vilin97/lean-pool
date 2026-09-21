/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SchurVanishing
import LeanPool.RegtsSevenster.RS.Classical.Deligne.IdempotentLength
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FactorialBeats
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PieriPos
import LeanPool.RegtsSevenster.RS.Classical.Deligne.BlockUnits
import LeanPool.RegtsSevenster.RS.Classical.Deligne.WhiskerFaithful
import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitSimple
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorPowZero

/-!
# Moderate growth forces Schur vanishing

Deligne's 1.20 (Catégories tensorielles): if no Schur functor kills
`X`, then for every `n` the tensor power `X ^ ⊗ n` carries, through
`permAlg`, one nonzero idempotent for each unit of each block —
`∑_{μ ⊢ n} dim μ` many, pairwise orthogonal — so its length is at
least `√(n!) − 1`, which outgrows every geometric progression.
Contrapositive: moderate length growth yields a shape whose Schur
functor vanishes.

The two block-theoretic inputs — completeness and orthogonality of
the central idempotents at each size — are named `Prop`s here and
discharged for the tree's package where the block theory lives.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

/-- **Completeness of the blocks**: at every size the central
idempotents sum to the identity of the group algebra. -/
def SchurPackage.Complete (P : SchurPackage.{u}) : Prop :=
  ∀ n : ℕ, ∑ μ : Shape n, Shape.e P μ = 1

/-- **Orthogonality of the blocks**: distinct shapes of one size
have orthogonal central idempotents. -/
def SchurPackage.Orthogonal (P : SchurPackage.{u}) : Prop :=
  ∀ (n : ℕ) (μ ν : Shape n), μ ≠ ν →
    Shape.e P μ * Shape.e P ν = 0

variable {A : Type u}

/-- **Moderate growth forces Schur vanishing** (Catégories
tensorielles, 1.20), assembly form: the block-theoretic inputs —
completeness, orthogonality, the block units — and the
nonvanishing transport up the standard embedding are hypotheses,
discharged elsewhere. -/
theorem exists_schurKilled_of_lengthLE
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [Linear ℂ A]
    (P : SchurPackage.{v}) (hO : P.Orthogonal)
    (hunits : ∀ μ : YoungDiagram,
      ∃ u : Fin (P.dim μ) → SymGroupAlgebra μ.card,
        (∀ i, u i * u i = u i) ∧
        (∀ i j, i ≠ j → u i * u j = 0) ∧
        (∀ i, P.e μ * u i = u i) ∧
        (∀ i, u i * P.e μ = u i) ∧
        (∀ i, u i ≠ 0))
    (hsum : ∀ n : ℕ,
      Real.sqrt n.factorial ≤ ((∑ μ : Shape n, P.dim μ.val : ℕ) : ℝ))
    (X : A)
    (hup : ∀ {m n : ℕ} (h : m ≤ n) (x : SymGroupAlgebra m),
      permAlg X m x ≠ 0 → permAlg X n (symCast h x) ≠ 0)
    {C c : ℕ}
    (hlen : ∀ N : ℕ, LengthLE (tensorPow A X N) (C * c ^ N)) :
    ∃ μ : YoungDiagram, SchurKilled P X μ := by
  by_contra hall
  push Not at hall
  -- ═══════ STAGE 1: CHOOSE THE SIZE ═══════
  -- A size at which `√(n!)` clears the growth bound with room for
  -- the `+ 1` of the idempotent count.
  obtain ⟨n, hn⟩ :=
    exists_lt_sqrt_factorial ((C : ℝ) + 1) ((c : ℝ) + 1)
  have hclear : ((C * c ^ n : ℕ) : ℝ) + 1 < Real.sqrt n.factorial := by
    refine lt_of_le_of_lt ?_ hn
    push_cast
    have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    have h1 : (1 : ℝ) ≤ ((c : ℝ) + 1) ^ n :=
      one_le_pow₀ (by linarith)
    have h2 : (c : ℝ) ^ n ≤ ((c : ℝ) + 1) ^ n :=
      pow_le_pow_left₀ hc0 (by linarith) n
    nlinarith [h1, h2, (Nat.cast_nonneg C : (0 : ℝ) ≤ (C : ℝ))]
  -- ═══════ STAGE 2: THE ORTHOGONAL FAMILY ═══════
  -- One idempotent per block unit, all recast into `S_n` and pushed
  -- through the action.
  choose u hui huo hue hue' hun using hunits
  set F := fun p : (μ : Shape n) × Fin (P.dim μ.val) =>
    permAlg X n (symCast (le_of_eq p.1.prop) (u p.1.val p.2))
    with hF
  have hcastu : ∀ (μ : Shape n) (i : Fin (P.dim μ.val)),
      symCast (le_of_eq μ.prop) (u μ.val i) * Shape.e P μ =
        symCast (le_of_eq μ.prop) (u μ.val i) := by
    intro μ i
    rw [Shape.e, ← map_mul, hue']
  have hcastu' : ∀ (μ : Shape n) (i : Fin (P.dim μ.val)),
      Shape.e P μ * symCast (le_of_eq μ.prop) (u μ.val i) =
        symCast (le_of_eq μ.prop) (u μ.val i) := by
    intro μ i
    rw [Shape.e, ← map_mul, hue]
  have hFidem : ∀ p, F p * F p = F p := by
    intro ⟨μ, i⟩
    rw [hF, ← map_mul, ← map_mul, hui]
  have hForth : ∀ p q, p ≠ q → F p * F q = 0 := by
    rintro ⟨μ, i⟩ ⟨ν, j⟩ hpq
    rw [hF, ← map_mul]
    by_cases hμν : μ = ν
    · subst hμν
      have hij : i ≠ j := fun h => hpq (by rw [h])
      rw [← map_mul, huo _ _ _ hij, map_zero, map_zero]
    · rw [show symCast (le_of_eq μ.prop) (u μ.val i) *
            symCast (le_of_eq ν.prop) (u ν.val j) =
          (symCast (le_of_eq μ.prop) (u μ.val i) * Shape.e P μ) *
            (Shape.e P ν * symCast (le_of_eq ν.prop) (u ν.val j))
          from by rw [hcastu, hcastu'],
        mul_assoc, ← mul_assoc (Shape.e P μ), hO n μ ν hμν,
        zero_mul, mul_zero, map_zero]
  have hFne : ∀ p, F p ≠ 0 := by
    intro ⟨μ, i⟩
    refine hup (le_of_eq μ.prop) _ ?_
    intro hz
    have hlowe : permAlg X μ.val.card (P.e μ.val) ≠ 0 := hall μ.val
    have : permAlg X μ.val.card (P.e μ.val * u μ.val i) = 0 := by
      rw [hue, hz]
    have hzero := P.block_faithful μ.val _ _ hlowe _ this
    rw [← SchurPackage.e_def, hue] at hzero
    exact hun μ.val i hzero
  -- ═══════ STAGE 3: COUNT AGAINST THE LENGTH ═══════
  have hcard :
      Fintype.card ((μ : Shape n) × Fin (P.dim μ.val)) =
        ∑ μ : Shape n, P.dim μ.val := by
    simp [Fintype.card_sigma]
  set k := ∑ μ : Shape n, P.dim μ.val with hk
  have hbound : k ≤ C * c ^ n + 1 := by
    have := le_of_orthogonal_idempotents (hlen n)
      (F ∘ (Fintype.equivFin _).symm)
      (fun i => hFidem _)
      (fun i j hij => hForth _ _
        (fun h => hij ((Fintype.equivFin _).symm.injective h)))
      (fun i => hFne _)
    rwa [hcard] at this
  -- ═══════ STAGE 4: THE CONTRADICTION ═══════
  -- `√(n!) ≤ k ≤ C·cⁿ + 1 < √(n!)`.
  have hkr : ((k : ℕ) : ℝ) ≤ ((C * c ^ n : ℕ) : ℝ) + 1 := by
    exact_mod_cast hbound
  exact absurd (lt_of_le_of_lt (le_trans (hsum n) hkr) hclear)
    (lt_irrefl _)

/-- **Moderate growth forces Schur vanishing** (Catégories
tensorielles, 1.20), final form: every hypothesis slot discharged —
orthogonality and the dimension bound from the package's block
theory, the block units from its matrix structure, and the
transport from whisker faithfulness.  Only simplicity of the unit
and nonvanishing of `X` remain, both facts of the ambient
category. -/
theorem exists_schurKilled_of_moderateGrowth
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (P : SchurPackage.{v}) (hs : Simple (𝟙_ A)) {X : A}
    (hX : ¬ Limits.IsZero X) {C c : ℕ}
    (hlen : ∀ N : ℕ, LengthLE (tensorPow A X N) (C * c ^ N)) :
    ∃ μ : YoungDiagram, SchurKilled P X μ := by
  refine exists_schurKilled_of_lengthLE P
    (fun n μ ν h => P.shape_e_orthogonal μ ν h) ?_
    P.sqrt_factorial_le_sum_dim X
    (fun {m n} h x hx => permAlg_symCast_ne_zero hs hX h x hx)
    hlen
  intro μ
  obtain ⟨u, h1, h2, h3, h4, _, h6⟩ := P.exists_block_units μ
  exact ⟨u, h1, h2, h3, h4, h6⟩

/-- **The completeness collapse**: if every shape of size `k` kills
`X`, the `k`-th tensor power is zero — the central idempotents sum
to the identity, and each acts as zero. -/
theorem isZero_tensorPow_of_schurKilled
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    (P : SchurPackage.{v}) {X : A} {k : ℕ}
    (h : ∀ μ : Shape k, SchurKilled P X μ.val) :
    Limits.IsZero (tensorPow A X k) := by
  rw [Limits.IsZero.iff_id_eq_zero, ← End.one_def]
  calc (1 : End (tensorPow A X k))
      = permAlg X k 1 := (map_one _).symm
    _ = permAlg X k (∑ μ : Shape k, Shape.e P μ) := by
        rw [P.sum_shape_e_eq_one]
    _ = ∑ μ : Shape k, permAlg X k (Shape.e P μ) := map_sum _ _ _
    _ = 0 := Finset.sum_eq_zero fun μ _ =>
        permAlg_compat X (le_of_eq μ.prop) _ (h μ)

/-- The moderate-growth dichotomy over a scalar unit: with
`End (𝟙) = ℂ` the simplicity hypothesis discharges as well, leaving
only nonvanishing of the generator. -/
theorem exists_schurKilled_of_moderateGrowth'
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (P : SchurPackage.{v}) (hu : HasScalarUnit A) {X : A}
    (hX : ¬ Limits.IsZero X) {C c : ℕ}
    (hlen : ∀ N : ℕ, LengthLE (tensorPow A X N) (C * c ^ N)) :
    ∃ μ : YoungDiagram, SchurKilled P X μ :=
  exists_schurKilled_of_moderateGrowth P
    (simple_unit_of_hasScalarUnit hu) hX hlen

/-- Under moderate growth every object has finite length: evaluate
the growth bound at the first tensor power. -/
theorem exists_lengthLE_of_moderateGrowth {C : Type*} [Category C]
    [MonoidalCategory C] (h : ModerateLengthGrowth C) (X : C) :
    ∃ N : ℕ, LengthLE X N := by
  obtain ⟨c₀, c, hN⟩ := h X
  exact ⟨c₀ * c ^ 1, (hN 1).of_iso (λ_ X)⟩

/-- A zero object is killed by every Schur functor of positive
size: its positive tensor powers are zero. -/
theorem SchurKilled.of_isZero
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [Linear ℂ A]
    [MonoidalPreadditive A]
    (P : SchurPackage.{v}) {X : A} (hX : Limits.IsZero X)
    {lam : YoungDiagram} (hcard : 0 < lam.card) :
    SchurKilled P X lam := by
  rw [SchurKilled]
  obtain ⟨n, hn⟩ : ∃ n, lam.card = n + 1 :=
    ⟨lam.card - 1, by omega⟩
  have hzero : Limits.IsZero (tensorPow A X lam.card) := by
    rw [hn]
    rw [Limits.IsZero.iff_id_eq_zero]
    rw [show 𝟙 (tensorPow A X (n + 1)) =
      tensorPow A X n ◁ 𝟙 X from
      (MonoidalCategory.whiskerLeft_id _ _).symm]
    rw [Limits.IsZero.iff_id_eq_zero] at hX
    rw [hX, MonoidalPreadditive.whiskerLeft_zero]
    rfl
  exact hzero.eq_of_src _ _

/-- **Every object is Schur-killed under moderate growth** — the
hypothesis of Deligne 2.1 in the form the pinned statement
supplies it. -/
theorem forall_exists_schurKilled
    [Category.{v} A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [Linear ℂ A]
    [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A] (P : SchurPackage.{v})
    (hu : HasScalarUnit A) (hg : ModerateLengthGrowth A) :
    ∀ X : A, ∃ μ : YoungDiagram, SchurKilled P X μ := by
  intro X
  by_cases hX : Limits.IsZero X
  · refine ⟨(colShape 2).val, SchurKilled.of_isZero P hX ?_⟩
    rw [(colShape 2).prop]
    omega
  · obtain ⟨c₀, c, hN⟩ := hg X
    exact exists_schurKilled_of_moderateGrowth' P hu hX hN

/-- Containment of the single row. -/
theorem rowShape_le_iff {m : ℕ} {lam : YoungDiagram} :
    (rowShape m).val ≤ lam ↔ m ≤ lam.rowLen 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · omega
    · have := h (show ((0, m - 1) : ℕ × ℕ) ∈ (rowShape m).val by
        rw [YoungDiagram.mem_iff_lt_rowLen, rowShape_rowLen_zero]
        omega)
      rw [YoungDiagram.mem_iff_lt_rowLen] at this
      omega
  · intro h c hc
    obtain ⟨i, j⟩ := c
    rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [rowShape_rowLen_zero] at hc
      omega
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [rowShape_rowLen_succ] at hc
      omega

/-- Containment of the single column. -/
theorem colShape_le_iff {m : ℕ} {lam : YoungDiagram} :
    (colShape m).val ≤ lam ↔ m ≤ lam.colLen 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · omega
    · have := h (show ((m - 1, 0) : ℕ × ℕ) ∈ (colShape m).val by
        rw [YoungDiagram.mem_iff_lt_rowLen,
          colShape_rowLen_lt m (by omega)]
        omega)
      rw [YoungDiagram.mem_iff_lt_colLen] at this
      omega
  · intro h c hc
    obtain ⟨i, j⟩ := c
    rw [YoungDiagram.mem_iff_lt_rowLen] at hc
    by_cases him : i < m
    · rw [colShape_rowLen_lt m him] at hc
      have hj : j = 0 := by omega
      subst hj
      rw [YoungDiagram.mem_iff_lt_colLen]
      omega
    · rw [colShape_rowLen_le m (by omega)] at hc
      omega

/-- A cell's coordinates are bounded by the cell count. -/
theorem cell_lt_card {lam : YoungDiagram} {p q : ℕ}
    (h : (p, q) ∈ lam) : p < lam.card ∧ q < lam.card := by
  constructor
  · have h0 : (p, 0) ∈ lam :=
      lam.up_left_mem le_rfl (Nat.zero_le _) h
    have hlt : p < lam.colLen 0 := by
      rw [← YoungDiagram.mem_iff_lt_colLen]
      exact h0
    have hle : lam.colLen 0 ≤ lam.card := by
      rw [YoungDiagram.colLen_eq_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · have h0 : (p, 0) ∈ lam :=
      lam.up_left_mem le_rfl (Nat.zero_le _) h
    have h1 : (0, q) ∈ lam :=
      lam.up_left_mem (Nat.zero_le _) le_rfl h
    have hlt : q < lam.rowLen 0 := by
      rw [← YoungDiagram.mem_iff_lt_rowLen]
      exact h1
    have hle : lam.rowLen 0 ≤ lam.card := by
      rw [YoungDiagram.rowLen_eq_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    omega

/-- The bounding-box count: a diagram fits in the rectangle of its
first row and column. -/
theorem card_le_colLen_mul_rowLen (lam : YoungDiagram) :
    lam.card ≤ lam.colLen 0 * lam.rowLen 0 := by
  classical
  have hsub : lam.cells ⊆
      Finset.range (lam.colLen 0) ×ˢ Finset.range (lam.rowLen 0) := by
    intro c hc
    obtain ⟨i, j⟩ := c
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have hmem : (i, j) ∈ lam := hc
    constructor
    · rw [← YoungDiagram.mem_iff_lt_colLen]
      exact lam.up_left_mem le_rfl (Nat.zero_le _) hmem
    · rw [← YoungDiagram.mem_iff_lt_rowLen]
      exact lam.up_left_mem (Nat.zero_le _) le_rfl hmem
  calc lam.card ≤ (Finset.range (lam.colLen 0) ×ˢ
      Finset.range (lam.rowLen 0)).card := Finset.card_le_card hsub
    _ = lam.colLen 0 * lam.rowLen 0 := by
        rw [Finset.card_product, Finset.card_range,
          Finset.card_range]

end RS
