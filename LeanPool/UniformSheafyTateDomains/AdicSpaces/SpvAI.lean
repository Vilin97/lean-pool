/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationContinuity
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationSpectrum
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CharacteristicSubgroup
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Lemma745
public import Mathlib.Combinatorics.Pigeonhole

/-!
# `Spv(A, I)` infrastructure (Wedhorn §7.1) — T-COMPACT-NO-HARCH foundation

Per round-22 reviewer (ChatGPT Pro, 2026-05-16): the no-`hArch` compactness
of rational opens in `Spa(A, A⁺)` for Tate rings goes via Wedhorn's
spectral space `Spv(A, I)`, **not** via the project's existing
Boolean-product encoding (which conflates Fσ cofinality with closed
conditions).

This file establishes the **definitional infrastructure** for `Spv(A, I)`
and the cofinality predicate used in Wedhorn 7.10's reverse direction.

## Main definitions

* `Valuation.CofinalValue v a` : `v(a)` is *cofinal* in `Γ_v ∪ {0}`, in
  the sense that for every `γ ∈ Γ_v` with `γ > 0`, there exists `n : ℕ`
  with `v(a)^n < γ`. This is the algebraic cofinality condition that
  Wedhorn 7.10's reverse direction uses to bridge `v(I) < 1` →
  continuity.

* `Spv.IsInSpvAI v I` : the disjunctive characterisation of
  `v ∈ Spv(A, I)` per Wedhorn Lemma 7.4: either every `a ∈ I` has
  `v(a)` cofinal in `Γ_v`, or `Γ_v = c Γ_v` (microbial).

## References

* Wedhorn, *Adic Spaces*, §7.1 (Definition 7.3, Lemma 7.4),
  arXiv:1910.05934.
-/

@[expose] public section

open Pointwise

namespace Valuation

variable {A : Type*} [CommRing A]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Cofinality of `v(a)` in `Γ_v` (algebraic form, Wedhorn 7.4 prep).**
A value `v(a)` is *cofinal* if for every `γ : Γ₀` with `γ > 0`, some
power `v(a)^n` is strictly less than `γ`.

This is the algebraic predicate that Wedhorn 7.10's reverse direction
uses: combined with `v(a) < 1` it gives continuity of `v` (in the
`f`-adic / Tate setting). -/
def CofinalValue (v : Valuation A Γ₀) (a : A) : Prop :=
  ∀ γ : Γ₀, 0 < γ → ∃ n : ℕ, v a ^ n < γ

/-- `CofinalValue` implies `v(a) ≤ 1` (in fact `v(a) < 1`, unless `v(a) = 0`). -/
theorem CofinalValue.le_one {v : Valuation A Γ₀} {a : A} (h : CofinalValue v a) :
    v a ≤ 1 := by
  by_contra h_gt
  push Not at h_gt
  -- v(a) > 1 means v(a)^n ≥ 1 for all n.
  have h_pow_ge : ∀ n : ℕ, 1 ≤ v a ^ n := fun n ↦ Left.one_le_pow_of_le h_gt.le n
  -- Take γ = 1. Cofinality gives ∃ n, v(a)^n < 1. Contradicts h_pow_ge.
  obtain ⟨n, hn⟩ := h 1 zero_lt_one
  exact absurd hn (not_lt_of_ge (h_pow_ge n))

end Valuation

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **`v ∈ Spv(A, I)` (Wedhorn 7.4 disjunction).** For `v : Spv A` and
`I : Ideal A`, `v` is *in `Spv(A, I)`* if either
- every `a ∈ I` has `v(a)` cofinal in `Γ_v`, or
- `v` is **microbial** (`Γ_v = c Γ_v` in Wedhorn 4.13 notation): every
  positive value of `v` is bounded by some `(v t)^±1` with `v t ≥ 1`.

This is the disjunctive characterisation per Wedhorn Lemma 7.4(ii). -/
def Spv.IsInSpvAI (v : Spv A) (I : Ideal A) : Prop :=
  letI : ValuativeRel A := v.toValuativeRel
  (∀ a ∈ I, Valuation.CofinalValue (ValuativeRel.valuation A) a) ∨
  Valuation.IsMicrobial (ValuativeRel.valuation A)

/-- **Per-`v` uniform decay on `I^n` from per-generator cofinality.**
Given `v : Valuation A Γ₀` with `v ≤ 1` on `P.A₀` and `CofinalValue v c`
for each generator `c` of `P.I`, conclude: for every `γ > 0`, there is
`n : ℕ` such that `v(a) < γ` for every `a ∈ P.I^n`. This discharges the
hypothesis of `Valuation.isContinuous_of_ideal_pow_lt` without
`MulArchimedean`.

The proof uses **the same pigeonhole + monomial-bound technique as the
P3 domination lemma** (`exists_ideal_pow_generators_dominated_for_half_space`),
specialised to a single `v` (no compactness needed).

This is the algebraic heart of Wedhorn 7.10's reverse direction. -/
theorem cofinalValue_ideal_pow_lt {A : Type*} [CommRing A] [TopologicalSpace A]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation A Γ₀}
    (P : PairOfDefinition A)
    (h_le_one : ∀ a : P.A₀, v (P.A₀.subtype a) ≤ 1)
    (h_cofinal : ∀ c : P.A₀, c ∈ P.I → Valuation.CofinalValue v (P.A₀.subtype c))
    (γ : Γ₀) (hγ : 0 < γ) :
    ∃ n : ℕ, ∀ a : P.A₀, a ∈ P.I ^ n → v (P.A₀.subtype a) < γ := by
  classical
  -- Extract FG generators S of P.I.
  obtain ⟨S, hS_span⟩ := P.fg
  -- Per-generator: ∀ c ∈ S, ∃ N_c with v(c)^{N_c} < γ.
  have h_per_c : ∀ c ∈ S, ∃ N : ℕ, v (P.A₀.subtype c) ^ N < γ := by
    intro c hc
    apply h_cofinal c (hS_span ▸ Ideal.subset_span hc) γ hγ
  choose N_c hN_c using h_per_c
  -- N_max := max over S of N_c.
  let N_max : ℕ := (S.attach.image (fun ⟨c, hc⟩ ↦ N_c c hc)).sup id + 1
  -- n₀ := (S.card + 1) * N_max.
  let n₀ : ℕ := (S.card + 1) * N_max
  refine ⟨n₀, fun a ha ↦ ?_⟩
  -- a ∈ P.I^n₀ = (Ideal.span S)^n₀ = Ideal.span (S^n₀ as Set).
  -- We bound v(a) ≤ max over monomials of v(monomial), and each monomial < γ.
  --
  -- Use `Submodule.span_induction` to reduce to the spanning set.
  have h_span_eq : (S : Set P.A₀) = ↑S := rfl
  have ha' : a ∈ Ideal.span ((S ^ n₀ : Finset P.A₀) : Set P.A₀) := by
    rw [Finset.coe_pow]
    rw [show (Ideal.span ((↑S : Set P.A₀) ^ n₀) : Ideal P.A₀) =
        (Ideal.span (↑S : Set P.A₀)) ^ n₀ from
      (Submodule.span_pow (↑S : Set P.A₀) n₀).symm]
    rw [hS_span]
    exact ha
  -- Now bound via induction on the span structure.
  refine Submodule.span_induction
    (M := P.A₀) (R := P.A₀)
    (s := ((S ^ n₀ : Finset P.A₀) : Set P.A₀))
    (p := fun x _ ↦ v (P.A₀.subtype x) < γ) ?_ ?_ ?_ ?_ ha'
  · -- Generator case: x ∈ S^n₀ as Finset.
    intro x hx
    -- x ∈ S^n₀ → ∃ f : Fin n₀ → ↥S with (List.ofFn fun i => ↑(f i)).prod = x.
    rw [show ((S ^ n₀ : Finset P.A₀) : Set P.A₀) = ((S ^ n₀ : Finset P.A₀) : Set P.A₀)
        from rfl] at hx
    have hx_mem : x ∈ (S ^ n₀ : Finset P.A₀) := hx
    rw [Finset.mem_pow] at hx_mem
    obtain ⟨f, hf⟩ := hx_mem
    -- Express v(P.A₀.subtype x) as ∏ via List.prod_ofFn + map_prod.
    have hx_eq : (P.A₀.subtype x : A) =
        ∏ i : Fin n₀, (P.A₀.subtype (↑(f i) : P.A₀) : A) := by
      have h_map : (P.A₀.subtype : P.A₀ →+* A)
          ((List.ofFn fun i ↦ (↑(f i) : P.A₀)).prod) =
          ((List.ofFn fun i ↦ (↑(f i) : P.A₀)).map P.A₀.subtype).prod :=
        map_list_prod P.A₀.subtype _
      rw [← hf, h_map, List.map_ofFn, List.prod_ofFn]
      rfl
    rw [hx_eq, map_prod]
    -- v(∏ i, P.A₀.subtype (↑(f i))) = ∏ i, v(P.A₀.subtype (↑(f i)))
    -- Pigeonhole: some c ∈ S has count ≥ N_max.
    by_cases hS_ne : S.Nonempty
    · haveI : Nonempty ↥S := hS_ne.coe_sort
      have h_card_le : Fintype.card ↥S * N_max ≤ Fintype.card (Fin n₀) := by
        simp only [Fintype.card_fin, Fintype.card_coe]
        change S.card * N_max ≤ (S.card + 1) * N_max
        calc S.card * N_max ≤ S.card * N_max + N_max := Nat.le_add_right _ _
          _ = (S.card + 1) * N_max := by ring
      obtain ⟨c_star, hc_count⟩ :=
        Fintype.exists_le_card_fiber_of_mul_le_card (f := f) (n := N_max) h_card_le
      -- Group by fiber.
      rw [show (∏ i : Fin n₀, v (P.A₀.subtype (↑(f i) : P.A₀))) =
          ∏ c : ↥S, ∏ i : Fin n₀ with f i = c,
            v (P.A₀.subtype (↑c : P.A₀)) by
        rw [Finset.prod_fiberwise' (s := Finset.univ) (g := f)
          (f := fun c : ↥S ↦ v (P.A₀.subtype (↑c : P.A₀)))]]
      have h_inner : ∀ c : ↥S, (∏ i ∈ Finset.univ.filter (fun i ↦ f i = c),
          v (P.A₀.subtype (↑c : P.A₀))) =
          v (P.A₀.subtype (↑c : P.A₀)) ^
          (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c)).card := by
        intro c
        rw [Finset.prod_const]
      rw [Finset.prod_congr rfl fun c _ ↦ h_inner c]
      rw [← Finset.prod_erase_mul (Finset.univ : Finset ↥S) _ (Finset.mem_univ c_star)]
      -- Bound `others ≤ 1` and `c_star_factor < γ`.
      have h_v_c_le_one : ∀ c : ↥S, v (P.A₀.subtype (↑c : P.A₀)) ≤ 1 := fun c ↦
        h_le_one (↑c : P.A₀)
      have h_others_le_one :
          (∏ c ∈ (Finset.univ : Finset ↥S).erase c_star,
            v (P.A₀.subtype (↑c : P.A₀)) ^
            (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c)).card) ≤ 1 := by
        refine Finset.prod_le_one' ?_
        intro c _
        exact Left.pow_le_one_of_le (h_v_c_le_one c) _
      have h_c_star_lt : v (P.A₀.subtype (↑c_star : P.A₀)) ^
          (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card < γ := by
        set count := (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card
        set N_star := N_c (↑c_star : P.A₀) c_star.2
        have h_N_max_ge : N_max ≥ N_star + 1 := by
          change (S.attach.image (fun ⟨c, hc⟩ ↦ N_c c hc)).sup id + 1 ≥ N_star + 1
          apply Nat.add_le_add_right
          have h_mem_image : N_star ∈ S.attach.image (fun ⟨c, hc⟩ ↦ N_c c hc) := by
            rw [Finset.mem_image]
            refine ⟨⟨(↑c_star : P.A₀), c_star.2⟩, Finset.mem_attach _ _, rfl⟩
          exact Finset.le_sup (f := id) h_mem_image
        have h_count_ge_N : count ≥ N_star := by
          calc count ≥ N_max := hc_count
            _ ≥ N_star + 1 := h_N_max_ge
            _ ≥ N_star := Nat.le_succ _
        have h_v_c_le_one_star : v (P.A₀.subtype (↑c_star : P.A₀)) ≤ 1 :=
          h_v_c_le_one c_star
        have h_pow_mono :
            v (P.A₀.subtype (↑c_star : P.A₀)) ^ count ≤
            v (P.A₀.subtype (↑c_star : P.A₀)) ^ N_star := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h_count_ge_N
          rw [hk, pow_add]
          conv_rhs => rw [← mul_one (v (P.A₀.subtype (↑c_star : P.A₀)) ^ N_star)]
          exact mul_le_mul_right (Left.pow_le_one_of_le h_v_c_le_one_star k) _
        calc v (P.A₀.subtype (↑c_star : P.A₀)) ^ count
            ≤ v (P.A₀.subtype (↑c_star : P.A₀)) ^ N_star := h_pow_mono
          _ < γ := hN_c (↑c_star : P.A₀) c_star.2
      calc (∏ c ∈ (Finset.univ : Finset ↥S).erase c_star,
              v (P.A₀.subtype (↑c : P.A₀)) ^
              (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c)).card) *
            v (P.A₀.subtype (↑c_star : P.A₀)) ^
              (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card
          ≤ 1 * v (P.A₀.subtype (↑c_star : P.A₀)) ^
              (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card := by
            exact mul_le_mul_left h_others_le_one _
        _ = v (P.A₀.subtype (↑c_star : P.A₀)) ^
              (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card := one_mul _
        _ < γ := h_c_star_lt
    · -- S empty: f vacuous, contradiction.
      exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hS_ne
      have hn₀_pos : 0 < n₀ := by
        change 0 < (S.card + 1) * N_max
        apply Nat.mul_pos
        · exact Nat.succ_pos _
        · change 0 < (S.attach.image _).sup id + 1
          exact Nat.succ_pos _
      exact (Finset.eq_empty_iff_forall_notMem.mp hS_ne) _ (f ⟨0, hn₀_pos⟩).2
  · -- Zero case: v(0) = 0 < γ.
    simp [map_zero]; exact hγ
  · -- Add case: v(x + y) ≤ max v(x) v(y) < γ.
    intro x y _ _ hx hy
    simp only [map_add]
    calc v (P.A₀.subtype x + P.A₀.subtype y)
        ≤ max (v (P.A₀.subtype x)) (v (P.A₀.subtype y)) := v.map_add _ _
      _ < γ := max_lt hx hy
  · -- Scale case: v(r · x) = v(r) · v(x) ≤ v(x) < γ (since v(r) ≤ 1).
    intro r x _ hx
    rw [show P.A₀.subtype (r • x) = P.A₀.subtype r * P.A₀.subtype x by
      simp [smul_eq_mul]]
    rw [map_mul]
    have hr_le : v (P.A₀.subtype r) ≤ 1 := h_le_one r
    calc v (P.A₀.subtype r) * v (P.A₀.subtype x)
        ≤ 1 * v (P.A₀.subtype x) := by
          exact mul_le_mul_left hr_le _
      _ = v (P.A₀.subtype x) := one_mul _
      _ < γ := hx

/-- **Per-`v` uniform decay on `I^n` for a PRINCIPAL ideal of definition, from
`v ≤ 1` on topologically nilpotent elements (NOT on all of `A₀`).** When `P.I =
(π)` is principal, an element `a ∈ I^n = (π^n)` factors as `a = π^(n-1)·(π·b)`
with `π·b ∈ I ⊆ A°°` (topologically nilpotent), so `v(a) = v(π)^(n-1)·v(π·b) ≤
v(π)^(n-1)`, and cofinality of `v(π)` finishes. This is the **faithful** form of
Huber's bound (huber2.txt:599-602: products of `A°°`-elements, no `A₀`-coefficient
decomposition), avoiding the over-strong `v ≤ 1 on A₀` hypothesis of
`cofinalValue_ideal_pow_lt`. -- INFRASTRUCTURE (principal-ideal specialisation). -/
theorem cofinalValue_principal_pow_lt {A : Type*} [CommRing A] [TopologicalSpace A]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation A Γ₀} (P : PairOfDefinition A) {π : P.A₀} (hπ : P.I = Ideal.span {π})
    (h_le : ∀ a : A, IsTopologicallyNilpotent a → v a ≤ 1)
    (h_cof : Valuation.CofinalValue v (P.A₀.subtype π))
    (γ : Γ₀) (hγ : 0 < γ) :
    ∃ n : ℕ, ∀ a : P.A₀, a ∈ P.I ^ n → v (P.A₀.subtype a) < γ := by
  obtain ⟨m, hm⟩ := h_cof γ hγ
  refine ⟨m + 1, fun a ha => ?_⟩
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  obtain ⟨b, hb⟩ := ha
  -- `π · b ∈ P.I = (π)`, hence topologically nilpotent.
  have hπb_mem : π * b ∈ P.I := by
    rw [hπ]; exact Ideal.mul_mem_right b _ (Ideal.mem_span_singleton_self π)
  have hπb_nilp : IsTopologicallyNilpotent (P.A₀.subtype (π * b)) :=
    P.isTopologicallyNilpotent_of_mem hπb_mem
  have hπb_le : v (P.A₀.subtype (π * b)) ≤ 1 := h_le _ hπb_nilp
  -- `subtype a = subtype π ^ m * subtype (π * b)`.
  have ha_eq : P.A₀.subtype a = P.A₀.subtype π ^ m * P.A₀.subtype (π * b) := by
    rw [hb]
    simp only [map_mul, map_pow]
    rw [pow_succ]
    ring
  rw [ha_eq, map_mul, map_pow]
  calc v (P.A₀.subtype π) ^ m * v (P.A₀.subtype (π * b))
      ≤ v (P.A₀.subtype π) ^ m * 1 := by
        exact mul_le_mul_right hπb_le _
    _ = v (P.A₀.subtype π) ^ m := mul_one _
    _ < γ := hm

/-- **Wedhorn 7.10 reverse direction (project form, cofinality disjunct
case).** For an `f`-adic ring `A` with pair of definition `P`, if
`v : Spv A` satisfies the **cofinality disjunct** of `Spv.IsInSpvAI`
(every `I`-image element has cofinal value) and `v ≤ 1` on `P.A₀`, then
`v` is continuous.

This handles the simpler case of Wedhorn 7.10. The microbial case
(`Γ_v = c Γ_v`) is a separate, more technical argument; the combined
result (both disjuncts) is `Spv.isContinuous_of_isInSpvAI_of_lt_one`
(currently TODO). -/
theorem Spv.isContinuous_of_cofinal_disjunct [TopologicalSpace A]
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (v : Spv A)
    (h_cofinal : letI : ValuativeRel A := v.toValuativeRel
      ∀ a : P.A₀, a ∈ P.I →
        Valuation.CofinalValue (ValuativeRel.valuation A) (P.A₀.subtype a))
    (h_le_one : letI : ValuativeRel A := v.toValuativeRel
      ∀ a : P.A₀, (ValuativeRel.valuation A) (P.A₀.subtype a) ≤ 1) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A).IsContinuous := by
  letI : ValuativeRel A := v.toValuativeRel
  exact Valuation.isContinuous_of_ideal_pow_lt P (ValuativeRel.valuation A)
    (fun γ hγ ↦ cofinalValue_ideal_pow_lt P h_le_one h_cofinal γ hγ)

/-- **Wedhorn 7.10 reverse direction (project form).** Full proof using
both disjuncts of `Spv.IsInSpvAI`.

Cofinality disjunct: direct application of `cofinalValue_ideal_pow_lt`
+ `Valuation.isContinuous_of_ideal_pow_lt`.

Microbial disjunct (Wedhorn p. 59): for each `c ∈ P.I` and `γ' > 0`,
use `IsMicrobial.exists_inv_le` to find `t ∈ A` with `v(t)⁻¹ ≤ γ'`.
Then `c` topologically nilpotent + `exists_pow_mul_mem_A₀` gives
`c^{n₀} · t ∈ P.A₀`. Hence `c^{n₀+1} · t ∈ P.I`, so `v(c^{n₀+1} · t) < 1`
from `h_lt_one`, giving `v(c)^{n₀+1} < v(t)⁻¹ ≤ γ'`. -/
theorem Spv.isContinuous_of_isInSpvAI_of_lt_one [TopologicalSpace A]
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (v : Spv A)
    (h_in : Spv.IsInSpvAI v (Ideal.map P.A₀.subtype P.I))
    (h_le_one : ∀ a : P.A₀,
      letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A) (P.A₀.subtype a) ≤ 1)
    (h_lt_one : ∀ a ∈ P.I,
      letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A) (P.A₀.subtype a) < 1) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A).IsContinuous := by
  letI : ValuativeRel A := v.toValuativeRel
  set wv := ValuativeRel.valuation A with hwv_def
  -- Reduce to per-generator cofinality, then dispatch via Wedhorn 7.10.
  refine Valuation.isContinuous_of_ideal_pow_lt P wv ?_
  intro γ hγ
  apply cofinalValue_ideal_pow_lt P h_le_one ?_ γ hγ
  intro c hc
  -- Goal: CofinalValue wv (P.A₀.subtype c), i.e., ∀ γ' > 0, ∃ n, wv(c)^n < γ'.
  -- Case-split on h_in: cofinality disjunct or microbial disjunct.
  rcases h_in with h_cof | h_micr
  · -- Cofinality disjunct: P.A₀.subtype c is already in the I-image.
    apply h_cof
    exact Ideal.mem_map_of_mem _ hc
  · -- Microbial disjunct: Wedhorn 7.10's microbial argument.
    intro γ' hγ'
    -- IsMicrobial: ∃ t ∈ A with wv(t) ≠ 0 and wv(t)⁻¹ ≤ γ'.
    obtain ⟨t, h_vt_ne, h_vt_inv_le⟩ := h_micr.exists_inv_le hγ'
    -- c is topologically nilpotent in A.
    have hc_topnilp : IsTopologicallyNilpotent (P.A₀.subtype c) :=
      P.isTopologicallyNilpotent_of_mem hc
    -- ∃ n_0, (P.A₀.subtype c)^n_0 * t ∈ P.A₀.
    obtain ⟨n_0, hn_0⟩ := PairOfDefinition.exists_pow_mul_mem_A₀ P hc_topnilp t
    refine ⟨n_0 + 1, ?_⟩
    -- Construct b := c * ⟨c^n_0 * t, hn_0⟩ ∈ P.I (as P.A₀-ideal).
    let b : P.A₀ := c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩
    have hb_mem_I : b ∈ P.I :=
      Ideal.mul_mem_right _ _ hc
    -- v(b) < 1 from h_lt_one.
    have hb_lt_one : wv (P.A₀.subtype b) < 1 := h_lt_one b hb_mem_I
    -- v(b) = v(c)^(n_0+1) * v(t).
    have hb_eq : wv (P.A₀.subtype b) =
        wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t := by
      change wv (P.A₀.subtype (c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩)) = _
      rw [show (P.A₀.subtype (c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩) : A) =
          P.A₀.subtype c * ((P.A₀.subtype c)^n_0 * t) from by
        simp]
      rw [map_mul, map_mul, map_pow]
      -- wv(c) * (wv(c)^n_0 * wv(t)) = wv(c)^(n_0+1) * wv(t).
      rw [show wv (P.A₀.subtype c) ^ (n_0 + 1) = wv (P.A₀.subtype c) * wv (P.A₀.subtype c) ^ n_0
        from by rw [pow_succ']]
      rw [mul_assoc]
    rw [hb_eq] at hb_lt_one
    -- v(c)^(n_0+1) * v(t) < 1 → v(c)^(n_0+1) < v(t)⁻¹.
    -- Multiply both sides by v(t)⁻¹ > 0 (v(t) ≠ 0).
    have h_pow_lt_inv : wv (P.A₀.subtype c) ^ (n_0 + 1) < (wv t)⁻¹ := by
      have h_vt_pos : 0 < wv t := zero_lt_iff.mpr h_vt_ne
      have h_inv_pos : 0 < (wv t)⁻¹ := inv_pos.mpr h_vt_pos
      -- x * y < 1, y > 0 → x < y⁻¹.
      -- Rewrite: x = (x * y) * y⁻¹ < 1 * y⁻¹ = y⁻¹.
      have h_x_eq : wv (P.A₀.subtype c) ^ (n_0 + 1) =
          (wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t) * (wv t)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ h_vt_ne, mul_one]
      rw [h_x_eq]
      calc (wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t) * (wv t)⁻¹
          < 1 * (wv t)⁻¹ := by
            rw [mul_comm _ ((wv t)⁻¹), mul_comm 1 ((wv t)⁻¹)]
            exact (mul_lt_mul_iff_right₀ h_inv_pos).mpr hb_lt_one
        _ = (wv t)⁻¹ := one_mul _
    -- v(c)^(n_0+1) < v(t)⁻¹ ≤ γ'.
    exact lt_of_lt_of_le h_pow_lt_inv h_vt_inv_le

/-- **Wedhorn 7.10 reverse direction, A°°-form via a PRINCIPAL pair (faithful to
Huber Thm 3.1).** Same conclusion as `isContinuous_of_isInSpvAI_of_lt_one`, but for
a principal ideal of definition `P.I = (π)` and with the boundedness hypothesis on
the **topologically nilpotent elements** (`A°°`) rather than on all of the ring of
definition `A₀`. This matches Huber's actual hypothesis (Thm 3.1, huber2.txt:586:
`Cont A = {v ∈ Spv(A, A°°·A) | v(a) ≤ 1 ∀ a ∈ A°°}`) — the `A₀`-form is over-strong.
The cofinality of `v(π)` (the single generator) comes from the `IsInSpvAI` disjunct
exactly as in `isContinuous_of_isInSpvAI_of_lt_one`; the `I^n` decay uses the
principal bound `cofinalValue_principal_pow_lt`. -/
theorem Spv.isContinuous_of_isInSpvAI_of_lt_one_principal [TopologicalSpace A]
    [IsTopologicalRing A]
    (P : PairOfDefinition A) {π : P.A₀} (hπ : P.I = Ideal.span {π}) (v : Spv A)
    (h_in : Spv.IsInSpvAI v (Ideal.map P.A₀.subtype P.I))
    (h_le_AOO : ∀ a : A, IsTopologicallyNilpotent a →
      letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A) a ≤ 1)
    (h_lt_one : ∀ a ∈ P.I,
      letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A) (P.A₀.subtype a) < 1) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A).IsContinuous := by
  letI : ValuativeRel A := v.toValuativeRel
  set wv := ValuativeRel.valuation A with hwv_def
  refine Valuation.isContinuous_of_ideal_pow_lt P wv ?_
  intro γ hγ
  apply cofinalValue_principal_pow_lt P hπ h_le_AOO ?_ γ hγ
  -- Goal: `CofinalValue wv (P.A₀.subtype π)`.
  rcases h_in with h_cof | h_micr
  · exact h_cof _ (Ideal.mem_map_of_mem _ (hπ ▸ Ideal.mem_span_singleton_self π))
  · -- Microbial disjunct: the t-trick with `c := π` (as in the A₀-form proof).
    intro γ' hγ'
    obtain ⟨t, h_vt_ne, h_vt_inv_le⟩ := h_micr.exists_inv_le hγ'
    have hπ_topnilp : IsTopologicallyNilpotent (P.A₀.subtype π) :=
      P.isTopologicallyNilpotent_of_mem (hπ ▸ Ideal.mem_span_singleton_self π)
    obtain ⟨n_0, hn_0⟩ := PairOfDefinition.exists_pow_mul_mem_A₀ P hπ_topnilp t
    refine ⟨n_0 + 1, ?_⟩
    let b : P.A₀ := π * ⟨(P.A₀.subtype π) ^ n_0 * t, hn_0⟩
    have hb_mem_I : b ∈ P.I := by
      rw [hπ]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
    have hb_lt_one : wv (P.A₀.subtype b) < 1 := h_lt_one b hb_mem_I
    have hb_eq : wv (P.A₀.subtype b) =
        wv (P.A₀.subtype π) ^ (n_0 + 1) * wv t := by
      change wv (P.A₀.subtype (π * ⟨(P.A₀.subtype π) ^ n_0 * t, hn_0⟩)) = _
      rw [show (P.A₀.subtype (π * ⟨(P.A₀.subtype π) ^ n_0 * t, hn_0⟩) : A) =
          P.A₀.subtype π * ((P.A₀.subtype π) ^ n_0 * t) from by simp]
      rw [map_mul, map_mul, map_pow]
      rw [show wv (P.A₀.subtype π) ^ (n_0 + 1)
          = wv (P.A₀.subtype π) * wv (P.A₀.subtype π) ^ n_0 from by rw [pow_succ']]
      rw [mul_assoc]
    rw [hb_eq] at hb_lt_one
    have h_pow_lt_inv : wv (P.A₀.subtype π) ^ (n_0 + 1) < (wv t)⁻¹ := by
      have h_vt_pos : 0 < wv t := zero_lt_iff.mpr h_vt_ne
      have h_inv_pos : 0 < (wv t)⁻¹ := inv_pos.mpr h_vt_pos
      have h_x_eq : wv (P.A₀.subtype π) ^ (n_0 + 1) =
          (wv (P.A₀.subtype π) ^ (n_0 + 1) * wv t) * (wv t)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ h_vt_ne, mul_one]
      rw [h_x_eq]
      calc (wv (P.A₀.subtype π) ^ (n_0 + 1) * wv t) * (wv t)⁻¹
          < 1 * (wv t)⁻¹ := by
            rw [mul_comm _ ((wv t)⁻¹), mul_comm 1 ((wv t)⁻¹)]
            exact (mul_lt_mul_iff_right₀ h_inv_pos).mpr hb_lt_one
        _ = (wv t)⁻¹ := one_mul _
    exact lt_of_lt_of_le h_pow_lt_inv h_vt_inv_le

/-- **Wedhorn 7.11(1) forward / 7.10 forward direction.** For a continuous
valuation `v : Spv A` on an `f`-adic ring with pair of definition `P`,
`v(a)` is cofinal in `Γ_v` for every `a` in the ideal-of-definition
image.

This is the algebraic content of Wedhorn 7.11(1): continuity implies
cofinality of `v(I)`. -/
theorem Spv.cofinalValue_of_isContinuous [TopologicalSpace A]
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (v : Spv A)
    (hv_cont : letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A).IsContinuous)
    (a : P.A₀) (ha : a ∈ P.I) :
    letI : ValuativeRel A := v.toValuativeRel
    Valuation.CofinalValue (ValuativeRel.valuation A) (P.A₀.subtype a) := by
  letI : ValuativeRel A := v.toValuativeRel
  intro γ hγ
  -- v continuous → {x : v(x) < γ} open in A.
  have h_open : IsOpen {x : A | (ValuativeRel.valuation A) x < γ} := hv_cont γ
  have h_zero_mem : (0 : A) ∈ {x : A | (ValuativeRel.valuation A) x < γ} := by
    change (ValuativeRel.valuation A) 0 < γ
    rw [map_zero]; exact hγ
  have h_nhds : {x : A | (ValuativeRel.valuation A) x < γ} ∈ nhds (0 : A) :=
    h_open.mem_nhds h_zero_mem
  -- a ∈ P.I → P.A₀.subtype a is topologically nilpotent.
  have ha_topnilp : IsTopologicallyNilpotent (P.A₀.subtype a) :=
    P.isTopologicallyNilpotent_of_mem ha
  -- eventually (P.A₀.subtype a)^n is in the open neighborhood.
  obtain ⟨n, hn⟩ := (ha_topnilp.eventually h_nhds).exists
  -- hn : v((P.A₀.subtype a)^n) < γ. Convert to v(P.A₀.subtype a)^n < γ.
  rw [map_pow] at hn
  exact ⟨n, hn⟩

/-- **Pigeonhole decay on pure generator-products** (Huber [Hu2] Thm 3.1 step (1) +
Lemma 2.4, huber2.txt:598-604 + 432-438). For a finite set `S` with `v ≤ 1` and
`CofinalValue v` on each generator, some length `m` makes every product of `m` elements
of `S` have `v < γ`: pigeonhole forces one generator to appear often enough that its
cofinality drives the product below `γ` while the other factors stay `≤ 1`. -/
private theorem pow_gen_prod_lt {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) (S : Finset R)
    (h_le_one : ∀ c ∈ S, v c ≤ 1) (h_cofinal : ∀ c ∈ S, Valuation.CofinalValue v c)
    (γ : Γ₀) (hγ : 0 < γ) :
    ∃ m : ℕ, ∀ f : Fin m → ↥S, v (∏ i, (↑(f i) : R)) < γ := by
  classical
  by_cases hS : S.Nonempty
  · have h_per : ∀ c ∈ S, ∃ N : ℕ, v c ^ N < γ := fun c hc => h_cofinal c hc γ hγ
    choose N_c hN_c using h_per
    set N_max : ℕ := (S.attach.image (fun x => N_c x.1 x.2)).sup id + 1 with hN_max_def
    refine ⟨(S.card + 1) * N_max, fun f => ?_⟩
    rw [map_prod]
    haveI : Nonempty ↥S := hS.coe_sort
    have h_card_le : Fintype.card ↥S * N_max ≤
        Fintype.card (Fin ((S.card + 1) * N_max)) := by
      simp only [Fintype.card_fin, Fintype.card_coe]
      calc S.card * N_max ≤ S.card * N_max + N_max := Nat.le_add_right _ _
        _ = (S.card + 1) * N_max := by ring
    obtain ⟨c_star, hc_count⟩ :=
      Fintype.exists_le_card_fiber_of_mul_le_card (f := f) (n := N_max) h_card_le
    rw [show (∏ i, v (↑(f i) : R)) =
        ∏ c : ↥S, ∏ _i ∈ Finset.univ.filter (fun i => f i = c), v (↑c : R) by
      rw [Finset.prod_fiberwise' (s := Finset.univ) (g := f)
        (f := fun c : ↥S => v (↑c : R))]]
    have h_inner : ∀ c : ↥S,
        (∏ _i ∈ Finset.univ.filter (fun i => f i = c), v (↑c : R)) =
        v (↑c : R) ^ (Finset.univ.filter
          (fun i : Fin ((S.card + 1) * N_max) => f i = c)).card :=
      fun c => Finset.prod_const _
    rw [Finset.prod_congr rfl fun c _ => h_inner c,
      ← Finset.prod_erase_mul (Finset.univ : Finset ↥S) _ (Finset.mem_univ c_star)]
    have h_v_le_one : ∀ c : ↥S, v (↑c : R) ≤ 1 := fun c => h_le_one ↑c c.2
    have h_others : (∏ c ∈ (Finset.univ : Finset ↥S).erase c_star, v (↑c : R) ^
        (Finset.univ.filter
          (fun i : Fin ((S.card + 1) * N_max) => f i = c)).card) ≤ 1 :=
      Finset.prod_le_one' fun c _ => Left.pow_le_one_of_le (h_v_le_one c) _
    have h_star_lt : v (↑c_star : R) ^ (Finset.univ.filter
        (fun i : Fin ((S.card + 1) * N_max) => f i = c_star)).card < γ := by
      set count := (Finset.univ.filter
        (fun i : Fin ((S.card + 1) * N_max) => f i = c_star)).card
      have h_N_max_ge : N_c (↑c_star : R) c_star.2 + 1 ≤ N_max := by
        rw [hN_max_def]
        apply Nat.add_le_add_right
        exact Finset.le_sup (f := id) (Finset.mem_image.mpr
          ⟨⟨(↑c_star : R), c_star.2⟩, Finset.mem_attach _ _, rfl⟩)
      have h_count_ge : N_c (↑c_star : R) c_star.2 ≤ count :=
        le_trans (Nat.le_succ _) (le_trans h_N_max_ge hc_count)
      calc v (↑c_star : R) ^ count
          ≤ v (↑c_star : R) ^ N_c (↑c_star : R) c_star.2 := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h_count_ge
            rw [hk, pow_add]
            conv_rhs => rw [← mul_one (v (↑c_star : R) ^ N_c (↑c_star : R) c_star.2)]
            exact mul_le_mul_right (Left.pow_le_one_of_le (h_v_le_one c_star) k) _
        _ < γ := hN_c (↑c_star : R) c_star.2
    calc (∏ c ∈ (Finset.univ : Finset ↥S).erase c_star, v (↑c : R) ^
            (Finset.univ.filter
              (fun i : Fin ((S.card + 1) * N_max) => f i = c)).card) *
          v (↑c_star : R) ^ (Finset.univ.filter
            (fun i : Fin ((S.card + 1) * N_max) => f i = c_star)).card
        ≤ 1 * v (↑c_star : R) ^ (Finset.univ.filter
            (fun i : Fin ((S.card + 1) * N_max) => f i = c_star)).card :=
          mul_le_mul_left h_others _
      _ = _ := one_mul _
      _ < γ := h_star_lt
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    exact ⟨1, fun f => absurd (f 0).2 (Finset.notMem_empty _)⟩

/-- **Ideal-power valuation decay from a bound on the ideal alone** (Huber [Hu2] Thm 3.1,
general form). For a finitely generated ideal `I` with `v ≤ 1` and `CofinalValue v` on
every element of `I`, some power `n` makes `v < γ` on all of `I^n` — with the bound
required only on `I`, never on ambient coefficients. Coefficients are absorbed into the
ideal: writing `a ∈ I^{m+1}` as a combination of pure `(m+1)`-fold generator products
`p = s₀·(s₁⋯s_m)`, each `c_p·p = (c_p·s₀)·(s₁⋯s_m)` has `c_p·s₀ ∈ I` (so `v ≤ 1`) and
the tail is an `m`-fold generator product (so `v < γ` by `pow_gen_prod_lt`). -/
theorem exists_pow_lt_of_forall_le_one_cofinal {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {I : Ideal R} (hfg : I.FG)
    (h_le_one : ∀ a ∈ I, v a ≤ 1) (h_cofinal : ∀ a ∈ I, Valuation.CofinalValue v a)
    (γ : Γ₀) (hγ : 0 < γ) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, v a < γ := by
  classical
  obtain ⟨S, hS⟩ := hfg
  have hSI : ∀ c ∈ S, c ∈ I := fun c hc => hS ▸ Ideal.subset_span hc
  obtain ⟨m, hm⟩ := pow_gen_prod_lt v S (fun c hc => h_le_one c (hSI c hc))
    (fun c hc => h_cofinal c (hSI c hc)) γ hγ
  refine ⟨m + 1, fun a ha => ?_⟩
  have ha' : a ∈ Ideal.span (↑(S ^ (m + 1)) : Set R) := by
    rw [Finset.coe_pow]
    rw [show (Ideal.span ((↑S : Set R) ^ (m + 1)) : Ideal R) =
        (Ideal.span (↑S : Set R)) ^ (m + 1) from
      (Submodule.span_pow (↑S : Set R) (m + 1)).symm]
    rw [hS]
    exact ha
  rw [Submodule.mem_span_finset] at ha'
  obtain ⟨cf, _hsupp, hsum⟩ := ha'
  rw [← hsum]
  refine Valuation.map_sum_lt v hγ.ne' fun p hp => ?_
  rw [Finset.mem_pow] at hp
  obtain ⟨g, hg⟩ := hp
  have hg' : (∏ i, (↑(g i) : R)) = p := by rw [← List.prod_ofFn]; exact hg
  have hp_eq : p = (↑(g 0) : R) * ∏ i : Fin m, (↑(g i.succ) : R) := by
    rw [← hg', Fin.prod_univ_succ]
  have hg0I : (↑(g 0) : R) ∈ I := hSI _ (g 0).2
  have habs : cf p • p = (cf p * (↑(g 0) : R)) * ∏ i : Fin m, (↑(g i.succ) : R) := by
    rw [smul_eq_mul, hp_eq, mul_assoc]
  rw [habs, map_mul]
  calc v (cf p * (↑(g 0) : R)) * v (∏ i : Fin m, (↑(g i.succ) : R))
      ≤ 1 * v (∏ i : Fin m, (↑(g i.succ) : R)) :=
        mul_le_mul_left (h_le_one _ (I.mul_mem_left (cf p) hg0I)) _
    _ = v (∏ i : Fin m, (↑(g i.succ) : R)) := one_mul _
    _ < γ := hm fun i => g i.succ

/-- **Per-`v` uniform decay on `I^n` from per-generator cofinality — `A°°`-form**
(Huber [Hu2] Thm 3.1's decay step). De-`A₀`'d `cofinalValue_ideal_pow_lt`: the bound is
required only on the ideal of definition `P.I`, not on `P.A₀`. Instantiates the general
`exists_pow_lt_of_forall_le_one_cofinal` at `v.comap P.A₀.subtype` and `I := P.I`. -/
theorem cofinalValue_ideal_pow_lt_of_le_one_on_ideal {A : Type*} [CommRing A]
    [TopologicalSpace A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation A Γ₀} (P : PairOfDefinition A)
    (h_le_one : ∀ c : P.A₀, c ∈ P.I → v (P.A₀.subtype c) ≤ 1)
    (h_cofinal : ∀ c : P.A₀, c ∈ P.I → Valuation.CofinalValue v (P.A₀.subtype c))
    (γ : Γ₀) (hγ : 0 < γ) :
    ∃ n : ℕ, ∀ a : P.A₀, a ∈ P.I ^ n → v (P.A₀.subtype a) < γ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_forall_le_one_cofinal (v.comap P.A₀.subtype) P.fg
    (fun a ha => h_le_one a ha) (fun a ha => h_cofinal a ha) γ hγ
  exact ⟨n, fun a ha => hn a ha⟩

/-- **Huber [Hu2] Theorem 3.1, reverse direction — general f-adic ring, `A°°`-form**
(huber2.txt:585-586: "Cont A = {v ∈ Spv(A, A°°·A) | v(a) < 1 for every a ∈ A°°}").
Continuity of `v` from `Spv(A, I)`-membership plus boundedness on the **topologically
nilpotent elements only** — no bound on the ring of definition `P.A₀` is assumed
(`A₀ ⊄ B⁺` in the Lemma-3.3(i) application, so the `A₀`-form
`isContinuous_of_isInSpvAI_of_lt_one` cannot serve there). Generalizes
`isContinuous_of_isInSpvAI_of_lt_one_principal` from principal `P.I = (π)` (Tate) to
arbitrary finitely generated ideals of definition (general Huber). -/
theorem Spv.isContinuous_of_isInSpvAI_of_lt_one_AOO [TopologicalSpace A]
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (v : Spv A)
    (h_in : Spv.IsInSpvAI v (Ideal.map P.A₀.subtype P.I))
    (h_le_AOO : ∀ a : A, IsTopologicallyNilpotent a →
      letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A) a ≤ 1)
    (h_lt_one : ∀ a ∈ P.I,
      letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A) (P.A₀.subtype a) < 1) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A).IsContinuous := by
  letI : ValuativeRel A := v.toValuativeRel
  set wv := ValuativeRel.valuation A with hwv_def
  -- Reduce to per-generator cofinality via the A°°-form decay (T904): the bound
  -- hypothesis is only `≤ 1` on `P.I`, supplied by `h_lt_one`. (`h_le_AOO` is not
  -- consumed by this route — kept for statement-parity with Huber Thm 3.1.)
  refine Valuation.isContinuous_of_ideal_pow_lt P wv ?_
  intro γ hγ
  apply cofinalValue_ideal_pow_lt_of_le_one_on_ideal P
    (fun c hc => (h_lt_one c hc).le) ?_ γ hγ
  intro c hc
  rcases h_in with h_cof | h_micr
  · -- Cofinality disjunct: P.A₀.subtype c is already in the I-image.
    apply h_cof
    exact Ideal.mem_map_of_mem _ hc
  · -- Microbial disjunct: Wedhorn 7.10's microbial argument.
    intro γ' hγ'
    -- IsMicrobial: ∃ t ∈ A with wv(t) ≠ 0 and wv(t)⁻¹ ≤ γ'.
    obtain ⟨t, h_vt_ne, h_vt_inv_le⟩ := h_micr.exists_inv_le hγ'
    -- c is topologically nilpotent in A.
    have hc_topnilp : IsTopologicallyNilpotent (P.A₀.subtype c) :=
      P.isTopologicallyNilpotent_of_mem hc
    -- ∃ n_0, (P.A₀.subtype c)^n_0 * t ∈ P.A₀.
    obtain ⟨n_0, hn_0⟩ := PairOfDefinition.exists_pow_mul_mem_A₀ P hc_topnilp t
    refine ⟨n_0 + 1, ?_⟩
    -- Construct b := c * ⟨c^n_0 * t, hn_0⟩ ∈ P.I (as P.A₀-ideal).
    let b : P.A₀ := c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩
    have hb_mem_I : b ∈ P.I :=
      Ideal.mul_mem_right _ _ hc
    -- v(b) < 1 from h_lt_one.
    have hb_lt_one : wv (P.A₀.subtype b) < 1 := h_lt_one b hb_mem_I
    -- v(b) = v(c)^(n_0+1) * v(t).
    have hb_eq : wv (P.A₀.subtype b) =
        wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t := by
      change wv (P.A₀.subtype (c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩)) = _
      rw [show (P.A₀.subtype (c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩) : A) =
          P.A₀.subtype c * ((P.A₀.subtype c)^n_0 * t) from by
        simp]
      rw [map_mul, map_mul, map_pow]
      -- wv(c) * (wv(c)^n_0 * wv(t)) = wv(c)^(n_0+1) * wv(t).
      rw [show wv (P.A₀.subtype c) ^ (n_0 + 1) = wv (P.A₀.subtype c) * wv (P.A₀.subtype c) ^ n_0
        from by rw [pow_succ']]
      rw [mul_assoc]
    rw [hb_eq] at hb_lt_one
    -- v(c)^(n_0+1) * v(t) < 1 → v(c)^(n_0+1) < v(t)⁻¹.
    -- Multiply both sides by v(t)⁻¹ > 0 (v(t) ≠ 0).
    have h_pow_lt_inv : wv (P.A₀.subtype c) ^ (n_0 + 1) < (wv t)⁻¹ := by
      have h_vt_pos : 0 < wv t := zero_lt_iff.mpr h_vt_ne
      have h_inv_pos : 0 < (wv t)⁻¹ := inv_pos.mpr h_vt_pos
      -- x * y < 1, y > 0 → x < y⁻¹.
      -- Rewrite: x = (x * y) * y⁻¹ < 1 * y⁻¹ = y⁻¹.
      have h_x_eq : wv (P.A₀.subtype c) ^ (n_0 + 1) =
          (wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t) * (wv t)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ h_vt_ne, mul_one]
      rw [h_x_eq]
      calc (wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t) * (wv t)⁻¹
          < 1 * (wv t)⁻¹ := by
            rw [mul_comm _ ((wv t)⁻¹), mul_comm 1 ((wv t)⁻¹)]
            exact (mul_lt_mul_iff_right₀ h_inv_pos).mpr hb_lt_one
        _ = (wv t)⁻¹ := one_mul _
    -- v(c)^(n_0+1) < v(t)⁻¹ ≤ γ'.
    exact lt_of_lt_of_le h_pow_lt_inv h_vt_inv_le

end ValuationSpectrum
